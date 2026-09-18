// Included after the generated runtime by runtime.py. Corpus allocations are
// tracked there, since ASan alone cannot see frees inside the custom heap.
#include <assert.h>

static void expect_text(Env e, Term s, const char* text) {
  u64 n;
  char* bytes = io_cstr(e, s, &n);
  assert(n == strlen(text) && memcmp(bytes, text, n) == 0 && bytes[n] == 0);
  free(bytes);
}

static void ownership(Env e) {
  // Static image is one full class-3 payload (four words) + one descriptor.
  assert(STAT_LEN == 6);
  Term lit = term_make(TAG_STR, CID_SCON, STAT_OFF + 4);
  assert(str_peek(e, lit).len == 6);
  expect_text(e, str_transform_take(e, lit, 1), "ABCDEF");
  expect_text(e, lit, "abcdef");
  assert(track_live == 0);
  // Even a dynamic count wrapper cannot make static payload writable.
  StrParts wrapped = str_peek(e, lit);
  wrapped.data = rfc_wrap(e, wrapped.data, 1);
  expect_text(e, str_transform_take(e, str_view_owned(e, wrapped), 0), "fedcba");
  expect_text(e, lit, "abcdef");
  assert(track_live == 0);

  // Aliased metadata: the payload still has ONE ref before opening. A
  // payload-only write test would mutate both aliases here.
  Term s = io_str(e, "abcdef", 6);
  Term data = str_peek(e, s).data;
  Term alias = term_keep(e, s);
  assert((rfc_view(e, term_loc(data)) & RFC_CNT) == 1);
  Term upper = str_transform_take(e, s, 1);
  assert(str_peek(e, upper).data != data);
  expect_text(e, upper, "ABCDEF");
  expect_text(e, alias, "abcdef");
  assert(track_live == 0);

  // Unique transforms retain the same payload; snapshots and overlapping
  // slices detach. Empty windows release both descriptor and payload.
  s = io_str(e, "abcdef", 6); data = str_peek(e, s).data;
  s = str_transform_take(e, s, 0);
  assert(str_peek(e, s).data == data);
  alias = term_keep(e, s);
  Term a = str_slice_take(e, s, 1, 5);
  Term b = str_slice_take(e, alias, 2, 6);
  assert(str_peek(e, a).data == data && str_peek(e, b).data == data);
  expect_text(e, str_transform_take(e, a, 1), "EDCB");
  expect_text(e, b, "dcba");
  assert(track_live == 0);
  s = str_slice_take(e, io_str(e, "abc", 3), 1ull << 32, ~0ull);
  assert(s == term_pak(CID_SNIL, 0) && track_live == 0);

  // A tiny zero-copy view pins its slab. copy allocates just a class-2
  // payload, and dropping the old view releases that retained large slab.
  s = str_repeat_take(e, lit, 65536);
  data = str_peek(e, s).data;
  u64 cap = 1ull << blk_cls(data);
  a = str_slice_take(e, s, 2, 5);
  assert(str_peek(e, a).data == data && cap >= 393216);
  b = str_copy_take(e, term_keep(e, a));
  assert(blk_cls(str_peek(e, b).data) == 2);
  assert(str_peek(e, b).data != data);
  u64 pinned = track_bytes;
  term_sink(e, a);
  assert(pinned - track_bytes >= cap * 4);
  expect_text(e, b, "cde");
  assert(track_live == 0);

  // Unique SCon reconstruction uses existing headroom, including uncons.
  s = str_prepend_take(e, 'a', term_pak(CID_SNIL, 0));
  for (u32 i = 0; i < 1000; i++) { s = str_prepend_take(e, 'b', s); }
  data = str_peek(e, s).data;
  Term fields[2]; str_uncons(e, s, fields);
  s = str_prepend_take(e, (u32)fields[0], fields[1]);
  assert(str_peek(e, s).data == data);
  term_sink(e, s);
  assert(track_live == 0);

  // Growth copies O(n) total payload cells on a unique one-direction chain.
  for (u32 front = 0; front < 2; front++) {
    s = term_pak(CID_SNIL, 0);
    u64 before = track_payload_words;
    for (u32 i = 0; i < 8192; i++) {
      s = front ? str_prepend_take(e, 'x', s)
        : str_append_take(e, s, str_slice_take(e, lit, 0, 1));
    }
    assert(str_peek(e, s).len == 8192);
    assert(track_payload_words - before < 2 * 8192);
    term_sink(e, s);
    assert(track_live == 0);
  }

  // Split fields are views of the same payload; dropping their list visits
  // all descriptors/payload owners without treating off/len as a Term.
  s = io_str(e, "ab,,cd,", 7); data = str_peek(e, s).data;
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
  assert(track_live == 0);
}

static void roundtrip(Env e) {
  const char nul[] = {'a', 0, 'b'};
  u64 n;
  char* bytes = io_cstr(e, io_str(e, nul, 3), &n);
  assert(n == 3 && !memcmp(bytes, nul, 3) && bytes[3] == 0);
  free(bytes);
  assert(track_live == 0);
}

static Term cells(Env e, const u32* xs, u32 n) {
  StrParts p = str_alloc(e, n);
  for (u32 i = 0; i < n; i++) { str_put(e, p, i, xs[i]); }
  return str_view_owned(e, p);
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
  u64 first = STR_ABSENT, last = STR_ABSENT, count = 0;
  for (u32 i = 0; i <= n; i++) {
    if (matches(s, n, p, m, i)) { if (first == STR_ABSENT) { first = i; } last = i; }
  }
  for (u32 i = 0; i <= n;) {
    bool hit = matches(s, n, p, m, i);
    count += hit;
    i += hit && m ? m : 1;
  }
  const u64 expected[] = {first, last, count};
  for (u32 mode = 0; mode < 3; mode++) {
    u64 builds = track_kmp_builds;
    assert(str_search_take(e, term_keep(e, text), term_keep(e, needle), mode) == expected[mode]);
    assert(track_kmp_builds - builds == (m > 1 && m <= n));
    assert(track_kmp_live == 0);
  }
  for (u32 mode = 0; mode < 2; mode++) {
    Term got = str_find_take(e, term_keep(e, text), term_keep(e, needle), mode != 0);
    assert(term_aux(got) == (expected[mode] == STR_ABSENT ? CID_NONE : CID_SOME));
    if (expected[mode] != STR_ABSENT) { assert(e.mem[term_peek(e, got)] == expected[mode]); }
    term_sink(e, got);
  }
  u32 want[128], used = 0;
  for (u32 i = 0; i <= n;) {
    bool hit = matches(s, n, p, m, i);
    if (hit) { for (u32 j = 0; j < 3; j++) { want[used++] = r[j]; } }
    if ((!hit || !m) && i < n) { want[used++] = s[i]; }
    i += hit && m ? m : 1;
  }
  u64 builds = track_kmp_builds;
  Term got = str_replace_take(e, term_keep(e, text), term_keep(e, needle), cells(e, r, 3));
  expect_cells(e, got, want, used); term_sink(e, got);
  assert(track_kmp_builds - builds == (m > 1 && m <= n));
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
  // None of the consuming helpers may mutate the retained original aliases.
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
  printf("KMP/replace/split/partition naive oracle: ok (%llu cases)\n", (unsigned long long)cases);
}

static void adversarial(Env e) {
  u64 reads[2];
  for (u32 scale = 0; scale < 2; scale++) {
    u32 n = 131072u << scale, m = 8192u << scale;
    StrParts a = str_alloc(e, n), b = str_alloc(e, m);
    for (u32 i = 0; i < n; i++) { str_put(e, a, i, 'a'); }
    for (u32 i = 0; i < m; i++) { str_put(e, b, i, 'a'); }
    str_put(e, a, n - 1, 'b'); str_put(e, b, m - 1, 'b');
    Term s = str_view_owned(e, a), p = str_view_owned(e, b);
    u64 before = track_str_reads, builds = track_kmp_builds;
    assert(str_search_take(e, s, p, 1) == n - m);
    reads[scale] = track_str_reads - before;
    assert(reads[scale] < 8ull * (n + m));
    assert(track_kmp_builds == builds + 1 && track_live == 0);
  }
  assert(reads[1] <= reads[0] * 2 + 16);
  printf("Adversarial a...ab: %llu / %llu cell reads (2x input), linear bound passed\n",
    (unsigned long long)reads[0], (unsigned long long)reads[1]);
}

static void new_ownership(Env e) {
  Term s = io_str(e, "abc::def::ghi", 13), alias = term_keep(e, s);
  Term out = str_split_on_take(e, s, io_str(e, "::", 2));
  term_sink(e, alias); term_sink(e, out); assert(track_live == 0);
  s = io_str(e, "-42", 3); Term data = str_peek(e, s).data;
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
  assert(track_live == 0);
}

static void bulk_builders(Env e) {
  const u32 cell[] = {'a'};
  Term a = cells(e, cell, 1);
  for (u32 separated = 0; separated < 2; separated++) {
    Term xs = term_pak(CID_NIL, 0);
    for (u32 i = 0; i < 8192; i++) { xs = str_cons(e, term_keep(e, a), xs); }
    u64 before = track_payload_words;
    Term out = str_join_take(e, xs, separated ? term_keep(e, a) : term_pak(CID_SNIL, 0));
    u32 size = separated ? 16383 : 8192;
    assert(str_peek(e, out).len == size);
    assert(track_payload_words - before < 2ull * size);
    term_sink(e, out);
  }
  u64 before = track_payload_words;
  Term out = str_repeat_take(e, a, 8192);
  assert(str_peek(e, out).len == 8192 && track_payload_words - before == 4096);
  term_sink(e, out);
  assert(track_live == 0);
  printf("concat/join/repeat: linear payload allocation bounds passed\n");
}

// Exercise sticky device-style allocation failure without a huge allocation.
// Runtime.py changes only err_seen and the allocation wrapper for this mode.
static void fault(Env e, const char* op, int after) {
  Term s = io_str(e, "abcdef", 6), b = io_str(e, "ghijkl", 6);
  Term cs = str_to_list_take(e, term_keep(e, s));
  Term xs = str_split_take(e, term_keep(e, s), 'c', false);
  Term needle = io_str(e, "cd", 2), replacement = io_str(e, "cdcd", 4);
  Term lines = io_str(e, "ab\ncd\r\nef", 9);
  u64 guard[H_BANK];
  for (u32 i = 0; i < H_BANK; i++) { guard[i] = e.mem[i]; }
  track_fail_after = after;
  if (!strcmp(op, "repeat")) { str_repeat_take(e, s, 8192); }
  else if (!strcmp(op, "prepend")) { str_prepend_take(e, '!', s); }
  else if (!strcmp(op, "append")) { str_append_take(e, s, b); }
  else if (!strcmp(op, "copy")) { str_copy_take(e, s); }
  else if (!strcmp(op, "transform")) { str_transform_take(e, s, 1); }
  else if (!strcmp(op, "split")) { str_split_take(e, s, 'c', false); }
  else if (!strcmp(op, "from-list")) { str_from_list_take(e, cs); }
  else if (!strcmp(op, "join")) { str_join_take(e, xs, b); }
  else if (!strcmp(op, "slice")) { str_slice_take(e, s, 1, 4); }
  else if (!strcmp(op, "find")) { str_find_take(e, s, needle, false); }
  else if (!strcmp(op, "count")) { str_search_take(e, s, needle, 2); }
  else if (!strcmp(op, "replace")) { str_replace_take(e, s, needle, replacement); }
  else if (!strcmp(op, "split_on")) { str_split_on_take(e, s, needle); }
  else if (!strcmp(op, "partition")) { str_partition_take(e, s, needle); }
  else if (!strcmp(op, "splitlines")) { str_splitlines_take(e, lines); }
  else if (!strcmp(op, "pad")) { str_pad_take(e, s, 20, 0xffffffff, 0); }
  else { assert(false); }
  assert(e.mem[H_ERROR_CODE] == ERR_HEAP);
  assert(track_kmp_live == 0);
  for (u32 i = 0; i < H_BANK; i++) {
    if (i != H_BUMP && i != H_CAP && i != H_ERROR_CODE) { assert(e.mem[i] == guard[i]); }
  }
}

// Structural acceptance at the benchmark's input sizes. Live block counts
// include payload/count/list allocations, so bounding all blocks also bounds
// descriptors. This probe does not substitute for the compiled Bend timings.
static void acceptance(Env e) {
  const char unit[] = "  alpha beta\n gamma\t\n";
  for (u32 scale = 0; scale < 3; scale++) {
    u32 n = 1u << (20 + 3 * scale);
    u64 allocs = track_allocs;
    StrParts p = str_alloc(e, n);
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
        Term f[2]; spare_free(e, 1, ctr_take(e, fields, 2, f));
        fields = f[1];
        Term trimmed = str_trim_take(e, f[0], 3);
        StrParts t = str_peek(e, trimmed);
        assert(!t.len || t.data == p.data);
        Term words = str_split_take(e, trimmed, 0, true);
        while (term_aux(words) == CID_CON) {
          Term w[2]; spare_free(e, 1, ctr_take(e, words, 2, w));
          words = w[1];
          assert(str_peek(e, w[0]).data == p.data);
          term_sink(e, w[0]);
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
      n, (unsigned long long)source_allocs,
      (unsigned long long)(track_str_reads - reads),
      (unsigned long long)access_allocs, (unsigned long long)track_peak_live);
  }
}

int main(int argc, char** argv) {
  Corpus h = corpus_setup(false, 1, 0);
  Env e = {h, ALC[0]};
  if (argc == 2 && !strcmp(argv[1], "limit-pad")) {
    str_pad_take(e, io_str(e, "a", 1), 1ull << 32, '.', 0); return 1;
  }
  if (argc == 2 && !strcmp(argv[1], "limit-repeat")) {
    str_repeat_take(e, io_str(e, "ab", 2), 1ull << 31); return 1;
  }
  if (argc == 3 && !strncmp(argv[1], "fault-", 6)) {
    fault(e, argv[1] + 6, atoi(argv[2]));
    return 0;
  }
  if (argc > 1 && strcmp(argv[1], "raw-output") == 0) {
    u64 n;
    free(io_cstr(e, str_prepend_take(e, 0xd800, term_pak(CID_SNIL, 0)), &n));
    return 1;
  }
  ownership(e);
  search_oracle(e);
  adversarial(e);
  new_ownership(e);
  bulk_builders(e);
  acceptance(e);
  roundtrip(e);
  utf8_cases(e);
  assert(!err_seen(h) && track_live == 0);
  printf("runtime ownership + UTF-8: ok (%llu allocations, zero live)\n", (unsigned long long)track_allocs);
  return 0;
}
