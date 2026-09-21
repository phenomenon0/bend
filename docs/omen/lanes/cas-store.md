# cas-store — BendHub in a box (2026-09-20)

A content-addressed store, as a daemon, in Bend: PUT a body and it is chunked,
addressed and de-duplicated; GET a byte range and every block of the answer
carries the sibling hashes that fold it up to the blob's root — and the daemon
*checks that fold itself, before the bytes go out*. A response that fails the
check is not sent. That last clause is the whole lane: the store cannot serve a
byte it cannot prove, because the proof is on the write path, not the read path.

It is composition, not invention. FastCDC and BLAKE3 were already in `power/`;
the TCP effs were already in the kit; the answer-plus-witness shape is the one
`proof.bend` uses. What this lane wrote is the layer between them.

    demos/io_cas_store/cas.bend    748  the store: chunk, address, dedup, prove, check
    demos/io_cas_store/serve.bend  217  the pure HTTP half: request text in, response text out
    demos/io_cas_store/main.bend   108  the socket loop
    demos/io_cas_store/LAWS.bend    40  four laws
    demos/io_cas_store/PROOF.bend   20  their proofs
    tests/cas/*.bend               401  five tests, four lanes each

## Architecture

    PUT  body -> Cdc.split(bits=12) -> cut offsets
              -> per cut: B3.hash_all -> Cv  (the chunk's address)
              -> find(store, cv)? reuse its id : append it
              -> leaves -> up -> up -> ... -> root (the blob's address)
              -> Blob{root, n, size, ids}

    GET  /blob/<hex>/<off>/<len>
              -> blob_of(store, hex)              404-equivalent if absent
              -> parts(blob, off, len)            which chunks the range touches
              -> per part: leaf = hash(the bytes we are about to send)
                           sibs = prove(leaves, i, n)
                           check(root, n, i, leaf, sibs)   <-- here
                           yes: append the block; no: abandon the whole walk

Three records and no more: `Chk{cv, data}`, `Blob{root, n, size, ids}`,
`Store{chks, kept, seen, dupb, blobs}`. The store is one `Data` value threaded
through the accept loop, which is what lets it be affine and mutable at once.

### The Merkle layer

`up` takes a level to the next one: pairs join with `B3.parent(l, r, 0)`, and a
node with no partner is **promoted**, never duplicated — duplicating it is the
classic way to give two different leaf lists one root, i.e. to make an address
that is not an address. `root` iterates `up` to a single node. `prove(xs, i, n)`
walks the same levels collecting the sibling at each one; `check(r, n, i, leaf,
sibs)` folds the leaf back up with those siblings and compares to `r`.

Domain separation is free: BLAKE3 already flags a leaf (ROOT) differently from a
join (PARENT), so a witness cannot present a chunk address where a join belongs.

### The proof-checking path, in full

`gs.part` is the only door to a part of a GET response:

    def gs.part(...):
      +data = at.data(chk_at(cs, id))       # the bytes we would send
      +leaf = hash_str(data)                # hashed HERE, not looked up
      +sibs = prove(lv, i, n)
      gs.send(..., check(rt, n, i, leaf, sibs))

and `gs.send` on `False` returns `GsNo{"proof refused at part i"}` — a state the
walk cannot leave, carrying no `out` string at all. The 200 path is reachable
only through `GsGo`/`GsEnd`, which are only reachable through a `True` from
`check`. There is no branch that writes bytes and skips the check, because the
bytes and the check are produced by the same expression.

The leaf is hashed from the data on the way out rather than read from `Chk.cv`.
That is deliberate: if the store's own index were corrupt — a manifest pointing
at the wrong chunk — reading the stored `cv` would confirm the corruption and
the check would pass. Hashing the outgoing bytes catches it. `tests/cas/range.bend`
plants exactly that fault (`lie` swaps two manifest ids in an otherwise valid
blob) and gets `refused: proof refused at part 0`.

### The laws

`LAWS.bend` pins the two shapes the honesty rests on, and `PROOF.bend` proves
all four by computation:

- `promote_alone` — `up([a]) == [a]`: the odd node is carried up, not doubled.
- `pair_joins` — `up([a,b]) == [parent(a,b,0)]`: a join is a join.
- `root_of_one` — `root([a],1) == a`: a one-chunk blob is its chunk.
- `body_after_blank` — every response is *some head*, then `\r\n\r\n`, then the
  body exactly: a client that cuts at the blank line reads what it was sent.
  (`resp` was split into `resp.head` + the join so this law is one step away.)

## Composed vs written

**Composed** — used as they stood, not touched:

- `power/cdc.bend` — `Cdc.split(c, off, end, bits)` gives ascending cut offsets.
  The whole chunking policy is one call and one constant (`BITS() = 12`).
- `power/blake3.bend` — `hash_all`, `parent`, `hex`, `Cv`. Every address in the
  system is a `B3.Cv`; the tree levels are `parent` and nothing else.
- `power/bytes.bend`, `power/vec.bend` — the byte buffer `hash_all` eats.
- Base — `String.partition` is the entire HTTP parser's engine; `String.is_ascii`
  is the socket-edge guard; `U32.read`/`U32.show` are the path and header numbers.
- `bend2/effs/` TCP — `listen`, `accept`, `recv`, `send`, `close`, unmodified.
- `demos/io_http_server` — read as the map for the socket loop and the LAWS/PROOF
  convention; no code taken.

**Written** — this lane:

- the Merkle layer: `up`, `root`, `prove`, `check` and their fuel loops.
- the store: records, `find` (linear dedup scan), the PUT walk `pt.*`/`put.*`,
  the GET walk `gs.*`, and the counters that make the dedup ratio observable.
- the pure HTTP half: `resp`/`resp.head`, `clen`, `req.done`, the routes.
- the socket loop with its recv reassembly.
- five tests and the four-lane harness over them.

**Nothing outside `demos/` and `tests/` was touched.** `bend.ts`, `comp.ts`,
`base.bend`, `power/` and the effs are all unmodified — `git status` on this
branch shows only `demos/io_cas_store/` and `tests/cas/`.

## Test evidence

Five tests, each run in five ways (strict check, interpreter, emitted JS, C, and
the same C binary on one thread — a schedule must not change an answer):

    ok   chunk    [check] [interpret] [js] [c] [c1]
    ok   http     [check] [interpret] [js] [c] [c1]
    ok   loopback [check] [interpret] [js] [c] [c1]
    ok   proof    [check] [interpret] [js] [c] [c1]
    ok   range    [check] [interpret] [js] [c] [c1]

    cas PASS: 25 FAIL: 0

- `proof.bend` — the checker alone, over a hand-built 5-leaf tree (5 → 3 → 2 → 1
  is odd at every level, so the promotion rule is exercised three times). For
  each leaf: the true witness says yes, a **tampered** leaf says no, a **forged**
  sibling says no, a **short** witness says no. Then the negative controls that
  are not about bytes at all: a valid witness replayed at the wrong index
  (`moved 0->1`, `moved 4->0`) is refused, an index past the end is refused, and
  a witness over budget (40 siblings, `MAXP` is 64 but the tree is 3 deep) is
  refused. A checker that only ever said yes would fail 11 of those 20 lines.
- `chunk.bend` — a periodic payload: 10 chunks, 7 kept, 41 duplicate bytes, and
  the manifest `0 1 2 3 4 5 1 2 3 6` — the repeat is visibly the same ids.
- `range.bend` — a two-part GET, then three refusals: past the end, unknown
  address, and the lying store above.
- `http.bend` — the framing and the routes with no socket in sight: Content-Length
  parsing, `req.done` over head-only / short body / full body, 400 / 404 / 201 /
  200, and a PUT-then-GET through `serve` end to end.
- `loopback.bend` — a real socket: listener, client, `read.go` reassembly,
  `serve`, response back. `request 131 chars -> HTTP/1.1 201 Created`.

### Live, against the compiled daemon

`bun bend2/main.ts demos/io_cas_store/main.bend -o /tmp/cas_store`, then real
HTTP on 127.0.0.1:8089. 256 KiB laid out as A|B|A|A — half of it a planted
duplicate — with chunks averaging 4 KiB:

    PUT 201 | stored 61b3bcd8...ada56 | chunks 53 size 262144
            | unique 31 seen 53 dupbytes 110162 | 19 ms

**22 of 53 chunks were already in the store; 110,162 of 262,144 bytes — 42.0% —
were never stored a second time.** The ceiling for this payload is 50% (two of
the four 64 KiB blocks are repeats); CDC gives back 84% of what is there to get,
the gap being the chunks that straddle a block boundary and so are genuinely new.

PUT the same blob again: same address, `unique` still 31 — **zero new chunks** —
`seen 106 dupbytes 372306`. Content addressing doing its one job.

    GET /blob/<hex>/12000/50   200, range 12000 50 parts 1, sibs 6 ... verified
    GET /blob/<hex>/5000/9000  200, range 5000 9000 parts 2, each ... verified
    GET /blob/<hex>/999999/10  409  refused: range past the end of the blob
    GET /blob/<0*64>/0/10      409  refused: no blob with that address
    PUT non-ASCII body         400  body is not ASCII; the socket edge is UTF-8
    GET /nope                  404

The daemon survived all of it and served the next request.

## Findings

Four, and the first is the one worth carrying out of this lane.

### 1. The socket edge is UTF-8, and that breaks *framing*, not just fidelity

`io_str`/`io_cstr` in `comp.ts` decode what `TCP.recv` returns and encode what
`TCP.send` takes, so only 0x00–0x7F survives a round trip. That a binary blob
comes back mangled is the obvious half and was known going in. The other half
was not, and it hangs a daemon:

**Content-Length counts bytes; `String.length` counts characters.** For a body
with any byte above 0x7F the two are never equal, so a length-driven reader
waits forever on a socket that will never send again. One `curl -X PUT -d 'café'`
parks a connection until the fuel runs out. `done.at` therefore treats a
non-ASCII body as complete, which lets `route.put` answer 400 instead of hanging.
Verified live: 400, and the daemon takes the next request.

`File.read_bytes`/`write_bytes` are byte-exact; it is the socket effs alone.
A binary-clean daemon needs a `TCP.recv_bytes`/`send_bytes` pair — a core
change, out of scope here, and the concrete ask this lane produces.

### 2. A recv is one `recv(2)`

`bend2/effs/tcp_recv.c` is a single syscall: partial reads are real, and any
reader that assumes one recv is one request is wrong on a body of any size.
`read.go` reassembles until `req.done` or the peer goes quiet.

### 3. The checker rules that shaped every loop here

Three of them, each verified against the checker rather than assumed:

- **no mutual recursion** — and a forward `law` declaration does not rescue it:
  *"an unfilled law is a dead claim: live code cannot use it"*.
- **no forward references.**
- **a do line cannot destructure a pair** — `m <- act` then `(a,b) = m` is out.

One idiom answers all three: **the continuation parameter**. A helper that must
both take a pair apart and continue a loop receives the rest of the loop as a
runtime function, and the recursive def passes itself in:

    def read.go(fuel, s, acc):
      ...  m <- TCP.recv(s, RECV())
           read.on(s2 => a2 => read.go(f, s2, a2), acc, m)

Note `k: A -> B -> IO(C)` and not `~k`: a tilde means comptime/closed and fails
with *"a template applied to closed ~ arguments"*. Every loop in `main.bend` and
the walks in `cas.bend` are this shape.

### 4. The store as one threaded `Data` value

Affinity and a shared mutable store look like a fight. They are not, if the loop
is serial: `serve.loop(l, st)` hands the new store to its own next iteration, so
there is exactly one owner at every moment and no lock, no `IO.spawn`, nothing to
race. Verified live that a GET on one connection sees a blob PUT on another.
The cost is concurrency, which is below.

## Not built — v0, deliberately

Say it plainly, all of it:

- **No persistence.** The store is memory. Kill the daemon, lose everything.
  No file backing was written; the File effs would carry it, but it is not here.
- **No GC.** Nothing is ever deleted. No refcounts, no sweep, no unreferenced
  chunk reclamation. The store grows until the process ends.
- **No crash consistency.** There is no journal, no fsync, no atomic rename,
  nothing to be consistent *with* — see "no persistence".
- **No auth.** Any client can PUT and GET anything. No tokens, no TLS, no
  rate limiting, no body size cap beyond what the recv fuel implies.
- **No concurrency.** One connection at a time, serially. A slow client blocks
  every other client. There is no read timeout either, so a client that opens a
  socket and says nothing occupies the daemon for 1024 empty recvs — slowloris
  works. The fuel is the only defence and it is not a good one.
- **Binary bodies.** ASCII in, ASCII out, by the guard in finding 1.
- **HTTP is the four lines it has to be.** No chunked transfer-encoding, no
  keep-alive, no HEAD, no headers beyond Content-Length, no percent-decoding.
- **Dedup is a linear scan.** `find` walks every stored chunk per incoming
  chunk — O(n·m). Fine at 53 chunks, not fine at 53,000. A hash index is the
  fix and is not written.
- **`MAXP() = 64`** caps witness length; the four lanes never reach a tree deep
  enough to test the cap from the *serving* side (`proof.bend` tests the
  checker's refusal directly).
- **Ranges are chunk-aligned in what they send.** A part sends its whole chunk,
  because a partial chunk cannot be hashed back to its leaf. The response says
  the true `off`/`len` per part and the client trims. This is inherent to
  proving, not laziness.

## Follow-ons, in the order they would pay

1. **`TCP.recv_bytes`/`TCP.send_bytes`** in the effs — the one core change that
   turns this from an ASCII store into a store. Everything else is userland.
2. **Persistence** — `Chk.data` to a file per address, the manifest to a small
   journal. The File effs are byte-exact, so this is a demos-only change once (1)
   is not blocking it.
3. **A hash index for `find`** — replace the linear scan; the dedup ratio does
   not change, the time does.
4. **GC** — mark from the blob list, sweep the chunk list. Needs (2) first to
   mean anything.
5. **Concurrency** — the real question is what owns the store when two
   connections are live. A single owner actor taking messages keeps the affine
   story; `IO.spawn` per connection does not.
6. **Auth and limits** — a token header and a body cap, both trivial once there
   is a reason to protect anything.
