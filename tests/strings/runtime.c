// Included after the generated runtime by runtime.py, which tracks corpus
// allocations: ASan alone cannot see frees inside the custom heap.
#include <assert.h>

#define SNIL term_pak(CID_SNIL, 0)
#define zero_live() assert(track_live == 0)
typedef unsigned long long ull;

static void expect_bytes(Env e, Term s, const char* text, u64 len) {
  u64 n;
  char* bytes = io_cstr(e, s, &n);
  assert(n == len && memcmp(bytes, text, n) == 0 && bytes[n] == 0);
  free(bytes);
}

static void expect_text(Env e, Term s, const char* text) {
  expect_bytes(e, s, text, strlen(text));
}

static Term str(Env e, const char* text) { return io_str(e, text, strlen(text)); }

static void ownership(Env e) {
  // Static image: a descriptor + a one-word payload of 1-byte cells, since a
  // literal is packed at the width of its content.
  assert(STAT_LEN == 3);
  Term lit = term_make(TAG_STR, CID_SCON, STAT_OFF + 1);
  assert(str_peek(e, lit).len == 6 && str_nar(str_peek(e, lit)) == 2);
  expect_text(e, str_transform_take(e, lit, 1), "ABCDEF");
  expect_text(e, lit, "abcdef");
  zero_live();
  // Even a dynamic count wrapper cannot make static payload writable.
  StrParts wrapped = str_peek(e, lit);
  wrapped.data = rfc_wrap(e, wrapped.data, 1);
  expect_text(e, str_transform_take(e, str_view_owned(e, wrapped), 0), "fedcba");
  expect_text(e, lit, "abcdef");
  zero_live();

  // Aliased metadata: the payload still has ONE ref before opening, so a
  // payload-only write test would mutate both aliases here.
  Term s = str(e, "abcdef");
  Term data = str_peek(e, s).data;
  Term alias = term_keep(e, s);
  assert((rfc_view(e, term_loc(data)) & RFC_CNT) == 1);
  Term upper = str_transform_take(e, s, 1);
  assert(str_peek(e, upper).data != data);
  expect_text(e, upper, "ABCDEF");
  expect_text(e, alias, "abcdef");
  zero_live();

  // Unique transforms keep the payload; snapshots and overlapping slices
  // detach. An empty window releases both descriptor and payload.
  s = str(e, "abcdef"); data = str_peek(e, s).data;
  s = str_transform_take(e, s, 0);
  assert(str_peek(e, s).data == data);
  alias = term_keep(e, s);
  Term a = str_slice_take(e, s, 1, 5);
  Term b = str_slice_take(e, alias, 2, 6);
  assert(str_peek(e, a).data == data && str_peek(e, b).data == data);
  expect_text(e, str_transform_take(e, a, 1), "EDCB");
  expect_text(e, b, "dcba");
  zero_live();
  s = str_slice_take(e, str(e, "abc"), 1ull << 32, ~0ull);
  assert(s == SNIL && track_live == 0);

  // A tiny zero-copy view pins its slab: copy allocates just a class-0
  // payload, and dropping the view releases the large slab.
  s = str_repeat_take(e, lit, 65536);
  data = str_peek(e, s).data;
  u64 cap = str_cap(data);
  a = str_slice_take(e, s, 2, 5);
  assert(str_peek(e, a).data == data && cap >= 393216);
  b = str_copy_take(e, term_keep(e, a));
  assert(blk_cls(str_peek(e, b).data) == 0 && str_nar(str_peek(e, b)) == 2);
  assert(str_peek(e, b).data != data);
  u64 pinned = track_bytes;
  term_sink(e, a);
  assert(pinned - track_bytes >= cap);
  expect_text(e, b, "cde");
  zero_live();

  // Unique SCon reconstruction reuses the headroom, uncons included.
  s = str_prepend_take(e, 'a', SNIL);
  for (u32 i = 0; i < 1000; i++) { s = str_prepend_take(e, 'b', s); }
  data = str_peek(e, s).data;
  Term fields[2]; str_uncons(e, s, fields);
  s = str_prepend_take(e, (u32)fields[0], fields[1]);
  assert(str_peek(e, s).data == data);
  term_sink(e, s);
  zero_live();

  // A unique descriptor advances in place, so a token walk allocates
  // nothing; a shared one must not: the alias still reads the whole text.
  s = str(e, "abcd");
  u64 walk = track_allocs;
  str_uncons(e, s, fields);
  assert(fields[0] == 'a' && fields[1] == s && track_allocs == walk);
  alias = term_keep(e, fields[1]);
  str_uncons(e, fields[1], fields);
  assert(fields[0] == 'b' && fields[1] != alias);
  expect_text(e, alias, "bcd");
  expect_text(e, fields[1], "cd");
  // The last cell releases descriptor and payload.
  s = str(e, "z");
  str_uncons(e, s, fields);
  assert(fields[0] == 'z' && fields[1] == SNIL);
  zero_live();

  // A unique one-direction chain grows by copying O(n) payload cells in all.
  for (u32 front = 0; front < 2; front++) {
    s = SNIL;
    u64 before = track_payload_words;
    for (u32 i = 0; i < 8192; i++) {
      s = front ? str_prepend_take(e, 'x', s)
        : str_append_take(e, s, str_slice_take(e, lit, 0, 1));
    }
    assert(str_peek(e, s).len == 8192);
    assert(track_payload_words - before < 2 * 8192);
    term_sink(e, s);
    zero_live();
  }

  // Split fields are views of one payload; dropping their list visits every
  // descriptor and payload owner without reading off/len as a Term.
  s = str(e, "ab,,cd,"); data = str_peek(e, s).data;
  Term list = str_split_take(e, s, ',', false);
  u32 fields_seen = 0;
  for (Term t = list; term_aux(t) == CID_CON;) {
    Loc l = term_peek(e, t);
    StrParts p = str_peek(e, e.mem[l]);
    assert(p.len == 0 || p.data == data);
    fields_seen++; t = e.mem[l + 1];
  }
  assert(fields_seen == 4);
  term_sink(e, list);
  zero_live();
}

static Term cells_at(Env e, const u32* xs, u32 n, u32 nar) {
  StrParts p = str_alloc(e, n, nar);
  for (u32 i = 0; i < n; i++) { str_put(e, p, i, xs[i]); }
  return str_view_owned(e, p);
}

// Any width at least as wide as the content is a valid representation: cycle
// through them so the oracles compare and combine payloads of mixed widths.
static Term cells(Env e, const u32* xs, u32 n) {
  static u32 turn;
  u32 nar = 2;
  for (u32 i = 0; i < n; i++) { if (str_fit(xs[i]) < nar) { nar = str_fit(xs[i]); } }
  if (turn++ % 3 < nar) { nar = turn % 3; }
  return cells_at(e, xs, n, nar);
}

static void expect_cells(Env e, Term s, const u32* xs, u32 n) {
  StrParts p = str_peek(e, s);
  assert(p.len == n);
  for (u32 i = 0; i < n; i++) { assert(str_at_peek(e, p, i) == xs[i]); }
}

// Independent deliberately naive oracle, also used on non-scalar U32 cells.
static bool matches(const u32* s, u32 n, const u32* p, u32 m, u32 i) {
  return i <= n && m <= n - i && memcmp(s + i, p, m * sizeof(u32)) == 0;
}

static void search_case(Env e, const u32* s, u32 n, const u32* p, u32 m) {
  const u32 r[] = {'$', '&', 'a'};
  Term text = cells(e, s, n), needle = cells(e, p, m);
  Term data = str_peek(e, text).data;
  u64 first = STR_ABSENT, last = STR_ABSENT, count = 0, kmp = m > 1 && m <= n;
  for (u32 i = 0; i <= n; i++) {
    if (matches(s, n, p, m, i)) { if (first == STR_ABSENT) { first = i; } last = i; }
  }
  // One non-overlapping scan: the count, and the replaced text.
  u32 want[128], used = 0;
  for (u32 i = 0; i <= n;) {
    bool hit = matches(s, n, p, m, i);
    count += hit;
    if (hit) { for (u32 j = 0; j < 3; j++) { want[used++] = r[j]; } }
    if ((!hit || !m) && i < n) { want[used++] = s[i]; }
    i += hit && m ? m : 1;
  }
  const u64 expected[] = {first, last, count};
  for (u32 mode = 0; mode < 3; mode++) {
    u64 builds = track_kmp_builds;
    assert(str_search_take(e, term_keep(e, text), term_keep(e, needle), mode) == expected[mode]);
    assert(track_kmp_builds - builds == kmp);
    assert(track_kmp_live == 0);
  }
  for (u32 mode = 0; mode < 2; mode++) {
    Term got = str_find_take(e, term_keep(e, text), term_keep(e, needle), mode != 0);
    assert(term_aux(got) == (expected[mode] == STR_ABSENT ? CID_NONE : CID_SOME));
    if (expected[mode] != STR_ABSENT) { assert(e.mem[term_peek(e, got)] == expected[mode]); }
    term_sink(e, got);
  }
  u64 builds = track_kmp_builds;
  Term got = str_replace_take(e, term_keep(e, text), term_keep(e, needle), cells(e, r, 3));
  expect_cells(e, got, want, used); term_sink(e, got);
  assert(track_kmp_builds - builds == kmp);
  Term list = str_split_on_take(e, term_keep(e, text), term_keep(e, needle));
  Term cur = list;
  u32 lo = 0;
  for (u32 i = 0; i <= n; i++) {
    if (i != n && (!m || !matches(s, n, p, m, i))) { continue; }
    assert(term_aux(cur) == CID_CON);
    Loc l = term_peek(e, cur);
    expect_cells(e, e.mem[l], s + lo, i - lo);
    StrParts view = str_peek(e, e.mem[l]);
    assert(!view.len || view.data == data);
    cur = e.mem[l + 1];
    if (i == n) { break; }
    lo = i + m; i = lo - 1;
  }
  assert(term_aux(cur) == CID_NIL);
  term_sink(e, list);
  got = str_partition_take(e, term_keep(e, text), term_keep(e, needle));
  Loc outer = term_peek(e, got), inner = term_peek(e, e.mem[outer + 1]);
  bool found = m && first != STR_ABSENT;
  u32 cut = found ? (u32)first : n, end = found ? cut + m : n;
  expect_cells(e, e.mem[outer], s, cut);
  expect_cells(e, e.mem[inner], p, found ? m : 0);
  expect_cells(e, e.mem[inner + 1], s + end, n - end);
  term_sink(e, got);
  // No consuming helper may mutate the retained originals.
  expect_cells(e, text, s, n); expect_cells(e, needle, p, m);
  term_sink(e, text); term_sink(e, needle);
  assert(track_live == 0 && track_kmp_live == 0);
}

static void search_oracle(Env e) {
  u32 s[16], p[16];
  u64 cases = 0;
  for (u32 n = 0; n <= 6; n++) {
    for (u32 a = 0; a < (1u << n); a++) {
      for (u32 i = 0; i < n; i++) { s[i] = 'a' + ((a >> i) & 1); }
      for (u32 m = 0; m <= 4; m++) {
        for (u32 b = 0; b < (1u << m); b++) {
          for (u32 i = 0; i < m; i++) { p[i] = 'a' + ((b >> i) & 1); }
          search_case(e, s, n, p, m); cases++;
        }
      }
    }
  }
  const u32 alphabet[] = {0, 'a', 'b', 0x1f600, 0xd800, 0xdc00, 0xffffffff};
  u32 rng = 12345;
  for (u32 t = 0; t < 500; t++) {
    u32 n = t % 16, m = (t / 16) % 8;
    for (u32 i = 0; i < n + m; i++) {
      rng = rng * 1664525u + 1013904223u;
      if (i < n) { s[i] = alphabet[rng % 7]; } else { p[i - n] = alphabet[rng % 7]; }
    }
    search_case(e, s, n, p, m); cases++;
  }
  printf("KMP/replace/split/partition naive oracle: ok (%llu cases)\n", (ull)cases);
}

static Term a_then_b(Env e, u32 n) {
  StrParts p = str_alloc(e, n, 2);
  for (u32 i = 0; i < n; i++) { str_put(e, p, i, i + 1 < n ? 'a' : 'b'); }
  return str_view_owned(e, p);
}

static void adversarial(Env e) {
  u64 reads[2];
  for (u32 scale = 0; scale < 2; scale++) {
    u32 n = 131072u << scale, m = 8192u << scale;
    Term s = a_then_b(e, n), p = a_then_b(e, m);
    u64 before = track_str_reads, builds = track_kmp_builds;
    assert(str_search_take(e, s, p, 1) == n - m);
    reads[scale] = track_str_reads - before;
    assert(reads[scale] < 8ull * (n + m));
    assert(track_kmp_builds == builds + 1 && track_live == 0);
  }
  assert(reads[1] <= reads[0] * 2 + 16);
  printf("Adversarial a...ab: %llu / %llu cell reads (2x input), linear bound passed\n",
    (ull)reads[0], (ull)reads[1]);
}

static void new_ownership(Env e) {
  Term s = str(e, "abc::def::ghi"), alias = term_keep(e, s);
  Term out = str_split_on_take(e, s, str(e, "::"));
  term_sink(e, alias); term_sink(e, out); zero_live();
  s = str(e, "-42"); Term data = str_peek(e, s).data;
  alias = term_keep(e, s);
  out = str_pad_take(e, s, 8, '0', 2);
  assert(str_peek(e, out).data != data);
  expect_text(e, alias, "-42"); expect_text(e, out, "-0000042");
  const u32 raw[] = {0xd800, 0xffffffff, 'a', 'B'};
  out = str_transform_take(e, cells(e, raw, 4), 3);
  const u32 lower[] = {0xd800, 0xffffffff, 'a', 'b'};
  expect_cells(e, out, lower, 4); term_sink(e, out);
  u32 hash = 2166136261u;
  for (u32 i = 0; i < 4; i++) {
    for (u32 j = 0; j < 4; j++) { hash = (hash ^ ((raw[i] >> (8 * j)) & 255)) * 16777619u; }
  }
  assert(str_hash_take(e, cells(e, raw, 4)) == hash);
  zero_live();
}

static void bulk_builders(Env e) {
  const u32 cell[] = {'a'};
  Term a = cells(e, cell, 1);
  for (u32 separated = 0; separated < 2; separated++) {
    Term xs = term_pak(CID_NIL, 0);
    for (u32 i = 0; i < 8192; i++) { xs = str_cons(e, term_keep(e, a), xs); }
    u64 before = track_payload_words;
    Term out = str_join_take(e, xs, separated ? term_keep(e, a) : SNIL);
    u32 size = separated ? 16383 : 8192;
    assert(str_peek(e, out).len == size);
    assert(track_payload_words - before < 2ull * size);
    term_sink(e, out);
  }
  u64 before = track_payload_words;
  u32 nar = str_nar(str_peek(e, a));
  Term out = str_repeat_take(e, a, 8192);
  // One exact allocation at the source's width: 8192 cells of 4, 2 or 1 bytes.
  assert(str_peek(e, out).len == 8192
    && track_payload_words - before == 4096u >> nar);
  term_sink(e, out);
  zero_live();
  printf("concat/join/repeat: linear payload allocation bounds passed\n");
}

// Sticky device-style allocation failure without a huge allocation.
// runtime.py changes only err_seen and the allocation wrapper for this mode.
#define ON(name) if (!strcmp(op, name))
static void fault(Env e, const char* op, int after) {
  Term s = str(e, "abcdef"), b = str(e, "ghijkl");
  Term cs = str_to_list_take(e, term_keep(e, s));
  Term xs = str_split_take(e, term_keep(e, s), 'c', false);
  Term needle = str(e, "cd"), replacement = str(e, "cdcd");
  Term lines = str(e, "ab\ncd\r\nef");
  u64 guard[H_BANK];
  memcpy(guard, e.mem, sizeof guard);
  track_fail_after = after;
  ON("repeat") { str_repeat_take(e, s, 8192); }
  else ON("prepend") { str_prepend_take(e, '!', s); }
  else ON("append") { str_append_take(e, s, b); }
  else ON("copy") { str_copy_take(e, s); }
  else ON("transform") { str_transform_take(e, s, 1); }
  else ON("split") { str_split_take(e, s, 'c', false); }
  else ON("from-list") { str_from_list_take(e, cs); }
  else ON("join") { str_join_take(e, xs, b); }
  else ON("slice") { str_slice_take(e, s, 1, 4); }
  else ON("find") { str_find_take(e, s, needle, false); }
  else ON("count") { str_search_take(e, s, needle, 2); }
  else ON("replace") { str_replace_take(e, s, needle, replacement); }
  else ON("split_on") { str_split_on_take(e, s, needle); }
  else ON("partition") { str_partition_take(e, s, needle); }
  else ON("splitlines") { str_splitlines_take(e, lines); }
  else ON("pad") { str_pad_take(e, s, 20, 0xffffffff, 0); }
  // Decoding widens twice: every payload, count cell and descriptor may fail.
  else ON("decode") { str(e, "a\xce\xbb\xf0\x9f\x98\x80"); }
  else { assert(false); }
  assert(e.mem[H_ERROR_CODE] == ERR_HEAP);
  assert(track_kmp_live == 0);
  for (u32 i = 0; i < H_BANK; i++) {
    if (i != H_BUMP && i != H_CAP && i != H_ERROR_CODE) { assert(e.mem[i] == guard[i]); }
  }
}

// Pops a unique Con: its head, the tail left in xs.
static Term pop(Env e, Term* xs) {
  Term f[2]; spare_free(e, 1, ctr_take(e, *xs, 2, f));
  *xs = f[1];
  return f[0];
}

// Structural acceptance at the benchmark's input sizes. Live block counts
// include payload/count/list allocations, so bounding all blocks also bounds
// descriptors. This probe does not substitute for the compiled Bend timings.
static void acceptance(Env e) {
  const char unit[] = "  alpha beta\n gamma\t\n";
  for (u32 scale = 0; scale < 3; scale++) {
    u32 n = 1u << (20 + 3 * scale);
    u64 allocs = track_allocs;
    StrParts p = str_alloc(e, n, 2);
    for (u32 i = 0; i < n; i++) { str_put(e, p, i, unit[i % 21]); }
    Term s = str_view_owned(e, p);
    u64 source_allocs = track_allocs - allocs;
    assert(source_allocs <= 4 && track_live <= 4);

    u64 reads = track_str_reads, copies = track_copy_cells;
    allocs = track_allocs;
    assert(str_length_take(e, term_keep(e, s)) == n);
    Term c = str_get_take(e, term_keep(e, s), n - 1, false);
    term_sink(e, c);
    Term view = str_slice_take(e, term_keep(e, s), n - 3, n);
    assert(str_peek(e, view).data == p.data);
    term_sink(e, view);
    u64 access_allocs = track_allocs - allocs;
    assert(track_str_reads - reads == 1 && track_copy_cells == copies);
    assert(access_allocs <= 4);

    u64 payloads = track_payload_words;
    track_peak_live = track_live;
    while (str_peek(e, s).len) {
      Term block = str_slice_take(e, term_keep(e, s), 0, 21 * 256);
      s = str_slice_take(e, s, 21 * 256, STR_LIMIT);
      Term fields = str_split_take(e, block, '\n', false);
      while (term_aux(fields) == CID_CON) {
        Term trimmed = str_trim_take(e, pop(e, &fields), 3);
        StrParts t = str_peek(e, trimmed);
        assert(!t.len || t.data == p.data);
        Term words = str_split_take(e, trimmed, 0, true);
        while (term_aux(words) == CID_CON) {
          Term w = pop(e, &words);
          assert(str_peek(e, w).data == p.data);
          term_sink(e, w);
        }
        term_sink(e, words);
      }
      term_sink(e, fields);
    }
    term_sink(e, s);
    assert(track_live == 0 && track_peak_live < 2100);
    assert(track_payload_words == payloads && track_copy_cells == copies);
    printf("Structural %u cells: source allocations=%llu; length/get/slice "
      "reads=%llu allocations=%llu; scan peak live blocks=%llu; payload copies=0\n",
      n, (ull)source_allocs, (ull)(track_str_reads - reads), (ull)access_allocs,
      (ull)track_peak_live);
  }
}

// Streaming decode. The law: for every byte string and every partition of
// it, the chunks decoded through file_read_text_go_dec (carry first), then
// the end-of-file call, append to io_str of the whole. cuts bit i set means
// a chunk ends after byte i; when idle is set, every chunk first runs as a
// 0-byte read, which must change nothing.
static u32 stream_run(Env e, const u8* b, u32 n, u64 cuts, bool idle, u32* out) {
  char buf[64 + 4];
  u32 pend = 0, need = 0, len = 0;
  for (u32 i = 0; i <= n;) {
    u32 j = i;
    while (j < n && !((cuts >> j) & 1)) { j++; }
    j = j < n ? j + 1 : n;
    for (u32 pass = idle ? 0 : 1; pass < 2; pass++) {
      u32 take = pass ? j - i : 0, was_pend = pend, had = need;
      bool eof = pass && i == n;
      for (u32 m = 0; m < had; m++) { buf[m] = (char)(pend >> (8 * m)); }
      memcpy(buf + had, b + i, take);
      Term s = file_read_text_go_dec(e, buf, had + take, eof, &pend, &need);
      StrParts p = str_peek(e, s);
      if (!pass) { assert(p.len == 0 && pend == was_pend && need == had); }
      if (eof) { assert(need == 4 && pend == 0); } else { assert(need <= 3); }
      // Consumed bytes always show: output, or a longer carry.
      if (take && !eof) { assert(p.len > 0 || need > had); }
      for (u32 k = 0; k < p.len; k++) { out[len++] = str_at_peek(e, p, k); }
      term_sink(e, s);
    }
    if (i == n) { break; }
    i = j;
  }
  zero_live();
  return len;
}

static void stream_check(Env e, const u8* b, u32 n, u64 cuts) {
  u32 got[64 + 4], len = stream_run(e, b, n, cuts, (cuts ^ n) & 1, got);
  Term s = io_str(e, (const char*)b, n);
  expect_cells(e, s, got, len);
  term_sink(e, s);
}

static u64 lcg(u64* x) {
  return *x = *x * 6364136223846793005ull + 1442695040888963407ull;
}

static u64 stream_law(Env e) {
  static const u8 abc[12] = "\x00\x41\x80\xbf\xc2\xe0\xed\xf0\xf4\xa0\x90\xff";
  u64 runs = 0;
  // Exhaustive: every string of <= 4 alphabet bytes x every partition.
  for (u32 n = 0; n <= 4; n++) {
    u32 total = 1;
    for (u32 i = 0; i < n; i++) { total *= 12; }
    for (u32 w = 0; w < total; w++) {
      u8 b[4];
      for (u32 i = 0, x = w; i < n; i++, x /= 12) { b[i] = abc[x % 12]; }
      for (u64 cuts = 0; cuts < (1ull << (n ? n - 1 : 0)); cuts++) { stream_check(e, b, n, cuts); runs++; }
    }
  }
  // Random: 2,000 strings biased to leads and continuations, under random
  // cuts and as 1-byte chunks.
  u64 x = 0xB3D5EED;
  for (u32 t = 0; t < 2000; t++) {
    u8 b[64];
    u32 n = 1 + (u32)(lcg(&x) >> 58);
    for (u32 i = 0; i < n; i++) {
      u32 r = (u32)(lcg(&x) >> 33), v = r >> 8;
      b[i] = (u8)(r % 3 == 0 ? abc[v % 12] : r % 3 == 1 ? 0x80 | (v & 0x7f) : v);
    }
    stream_check(e, b, n, lcg(&x)); stream_check(e, b, n, ~0ull); runs += 2;
  }
  // The pinned specimen: every single split point, and 1-byte chunks.
  static const u8 pin[20] = "\xef\xbb\xbf\x41\x00\xf0\x9f\x98\x80\xc0"
    "\x80\xed\xa0\x80\xf4\x90\x80\x80\xe2\x82";
  for (u32 i = 0; i < 20; i++) { stream_check(e, pin, 20, 1ull << i); runs++; }
  stream_check(e, pin, 20, ~0ull); runs++;
  // Boundary errors, spelled out.
  const u32 F = 0xfffd;
  const struct { const char* b; u64 cuts; u32 len, want[3]; } edge[6] = {
    {"\xe2\x82\xac", 2, 1, {0x20ac}}, {"\xe2\x82\x41", 2, 3, {F, F, 0x41}},
    {"\xf0\x9f", 0, 2, {F, F}}, {"\xe2\x41", 0, 2, {F, 0x41}},
    {"\xed\xa0\x80", 1, 3, {F, F, F}}, {"\xed\xa0\x80", 2, 3, {F, F, F}},
  };
  for (u32 i = 0; i < 6; i++) {
    u32 got[8], n = (u32)strlen(edge[i].b);
    assert(stream_run(e, (const u8*)edge[i].b, n, edge[i].cuts, false, got) == edge[i].len
      && !memcmp(got, edge[i].want, 4 * edge[i].len));
  }
  return runs + 6;
}

// Width is chosen by content and is invisible: the same cells at any width
// compare, hash and print alike; a wider write widens, a view never does,
// and copy compacts to the content of the visible range.
static void widths(Env e) {
  const char* text[] = {"abc", "caf\xc3\xa9", "\xce\xbb\xe6\xbc\xa2", "a\xf0\x9f\x98\x80"};
  const u32 nar[] = {2, 2, 1, 0}, len[] = {3, 4, 2, 2};
  for (u32 i = 0; i < 4; i++) {
    u32 bytes = (u32)strlen(text[i]);
    Term s = io_str(e, text[i], bytes);
    StrParts p = str_peek(e, s);
    assert(str_nar(p) == nar[i] && p.len == len[i]);
    // Sized by the bytes left when the width was met, never by 4-byte cells.
    assert(blk_cls(p.data) <= cls_fit((bytes + (1u << nar[i]) - 1) >> nar[i]));
    // The same cells in every wider payload are the same string.
    u32 xs[4];
    for (u32 j = 0; j < p.len; j++) { xs[j] = str_at_peek(e, p, j); }
    for (u32 w = 0; w <= nar[i]; w++) {
      Term t = cells_at(e, xs, p.len, w);
      assert(str_order_peek(e, s, t) == 1);
      assert(str_hash_take(e, term_keep(e, s)) == str_hash_take(e, term_keep(e, t)));
      for (Nat b = 0; b < 33ull * p.len + 2; b++) {
        assert(str_bit_peek(e, s, b) == str_bit_peek(e, t, b));
      }
      expect_text(e, str_copy_take(e, t), text[i]);
    }
    term_sink(e, s);
    zero_live();
  }
  // A unique narrow payload widens on a wide write, at either end, once.
  Term s = str_prepend_take(e, 0x3bb, str(e, "abc"));
  assert(str_nar(str_peek(e, s)) == 1);
  s = str_append_take(e, s, str(e, "\xf0\x9f\x98\x80"));
  assert(str_nar(str_peek(e, s)) == 0);
  s = str_pad_take(e, s, 7, 0xffffffffu, 1);
  const u32 want[] = {0x3bb, 'a', 'b', 'c', 0x1f600, 0xffffffffu, 0xffffffffu};
  expect_cells(e, s, want, 7);
  // A view of the ASCII middle stays a 4-byte view; its copy is 1-byte cells.
  Term data = str_peek(e, s).data;
  Term mid = str_slice_take(e, s, 1, 4);
  assert(str_peek(e, mid).data == data && str_nar(str_peek(e, mid)) == 0);
  mid = str_copy_take(e, mid);
  assert(str_nar(str_peek(e, mid)) == 2);
  // Narrow text absorbs a wide separator and stays equal to the wide build.
  Term joined = str_join_take(e, str_cons(e, term_keep(e, mid), str_cons(e, mid,
    term_pak(CID_NIL, 0))), str(e, "\xe6\xbc\xa2"));
  const u32 both[] = {'a', 'b', 'c', 0x6f22, 'a', 'b', 'c'};
  expect_cells(e, joined, both, 7);
  assert(str_nar(str_peek(e, joined)) == 1);
  // In-place uncons reads cells of every width.
  for (u32 i = 0; i < 7; i++) {
    Term out[2]; str_uncons(e, joined, out);
    assert(out[0] == both[i]); joined = out[1];
  }
  assert(joined == SNIL && track_live == 0);
}

int main(int argc, char** argv) {
  Corpus h = corpus_setup(false, 1, 0);
  Env e = {h, ALC[0]};
  if (argc == 3 && !strncmp(argv[1], "fault-", 6)) {
    fault(e, argv[1] + 6, atoi(argv[2]));
    return 0;
  }
  // err_post must end these: the return is the failure.
  if (argc == 2) {
    const char* op = argv[1];
    u64 n;
    ON("limit-pad") { str_pad_take(e, str(e, "a"), 1ull << 32, '.', 0); }
    else ON("limit-repeat") { str_repeat_take(e, str(e, "ab"), 1ull << 31); }
    else ON("raw-output") { free(io_cstr(e, str_prepend_take(e, 0xd800, SNIL), &n)); }
    return 1;
  }
  ownership(e);
  search_oracle(e);
  adversarial(e);
  new_ownership(e);
  bulk_builders(e);
  acceptance(e);
  expect_bytes(e, io_str(e, "a\0b", 3), "a\0b", 3);
  zero_live();
  utf8_cases(e);
  u64 parts = stream_law(e);
  widths(e);
  assert(!err_seen(h) && track_live == 0);
  printf("streaming partition law: ok (%llu partitions, zero live)\n", (ull)parts);
  printf("runtime ownership + UTF-8: ok (%llu allocations, zero live)\n", (ull)track_allocs);
  return 0;
}
