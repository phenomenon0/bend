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

// Exercise sticky device-style allocation failure without a huge allocation.
// Runtime.py changes only err_seen and the allocation wrapper for this mode.
static void fault(Env e, const char* op, int after) {
  Term s = io_str(e, "abcdef", 6), b = io_str(e, "ghijkl", 6);
  Term cs = str_to_list_take(e, term_keep(e, s));
  Term xs = str_split_take(e, term_keep(e, s), 'c', false);
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
  else { assert(false); }
  assert(e.mem[H_ERROR_CODE] == ERR_HEAP);
  for (u32 i = 0; i < H_BANK; i++) {
    if (i != H_BUMP && i != H_CAP && i != H_ERROR_CODE) { assert(e.mem[i] == guard[i]); }
  }
}

int main(int argc, char** argv) {
  Corpus h = corpus_setup(false, 1, 0);
  Env e = {h, ALC[0]};
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
  roundtrip(e);
  utf8_cases(e);
  assert(!err_seen(h) && track_live == 0);
  printf("runtime ownership + UTF-8: ok (%llu allocations, zero live)\n", (unsigned long long)track_allocs);
  return 0;
}
