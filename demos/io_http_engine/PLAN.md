# io_http_engine: the plan

A review of this branch (2026-09-22) and the work it implies, in the
order it should be done. Correctness first, then representation, then
API; speed last. `[c]` marks what was reproduced against the running
binary; the rest was found by reading the code, with the line cited.

## Phase 1: framing (smuggling and desync)

Any disagreement with a proxy about where a request ends is a
smuggling primitive. Each of these is one.

- [ ] **Names compared by hash alone.** FNV-1a-32 is invertible per
  step; `x-v5fged` collides with `content-length` and is honoured as
  one [c]. The same holds for `transfer-encoding`, `connection`,
  `upgrade`, the version and the method (`main.bend:111`, `:382`,
  `:459`, `:448`, `:1705`). Keep the hash as a filter, confirm by bytes.
- [ ] **Duplicate Content-Length: last wins** [c] (`:236`). Differing
  values are a 400 (RFC 9112 §6.3).
- [ ] **Content-Length wraps at U32**: `4294967301` reads as 5 [c]
  (`:472`; the cap at `:403` runs after the wrap). Refuse on overflow.
- [ ] **Malformed fields accepted.** Space before the colon ignored [c];
  obs-fold accepted [c]; HTAB or trailing OWS in a length drops it and
  frames the body as 0 (`:348`, `:463`); a line with no colon swallows
  the CRLF into the name (`:457`); a bare LF inside a value (`:479`).
  Each is a 400. `Ows` must skip HTAB.
- [ ] **Pipelining past `/events` or a 101** writes HTTP into the
  stream, and bytes after the upgrade are dropped (`:1725`, `:1742`,
  `:1769`). The upgrade must end the batch and hand `p2` to the frames.
- [ ] **`connection: keep-alive` on every reply** [c], 400s and replies
  to `Connection: close` included (`:570`, `:622`). Say close when closing.
- [ ] `Connection` is one token only (`:352`): Firefox's `keep-alive,
  Upgrade` gets a 426, `close, foo` is not a close. Parse the list.
- [ ] A leading CRLF before the request line is a 405 (`:441`); §2.2
  says ignore it.
- [ ] The request target keeps CR and LF and is logged verbatim
  (`:445`, `:1556`): log injection. Refuse control bytes in the target.

Each item lands with a `check.c` case and a `fuzz.c` mutation, and the
control changes with the engine so the fuzzer keeps them equal.

## Phase 2: the runtime and the wire

- [ ] **Plain TCP effects bypass the wire.** `tcp_send.c`, `tcp_recv.c`,
  `tcp_poll.c`, `tcp_recv_text_go.c` call `send`/`recv` directly: on a
  TLS socket that is cleartext mid-session. Route every socket effect
  through `io_wire_*`.
- [ ] **`tls_call()`**: clear `errno` and `ERR_clear_error()` before each
  `SSL_*` call (`tls_listen.c:51-75`). Today a stale EAGAIN turns an EOF
  into a hot spin on OpenSSL 1.1.1, and one connection's error queue
  misreports the next. No `SSL_shutdown` after a fatal error (`:127`).
  Set `SSL_OP_IGNORE_UNEXPECTED_EOF`, `SSL_OP_NO_RENEGOTIATION`,
  `SSL_MODE_RELEASE_BUFFERS`.
- [ ] **Accept errors stop the server** (`tcp_accept_poll.c:18`, then
  `accept.got`). EMFILE, ENFILE, ENOBUFS, ENOMEM, ECONNABORTED and the
  accept(2) network errors are retries; keep a spare descriptor so EMFILE
  is not a busy loop.
- [ ] **No send deadline** (`tcp_send_bytes.c` parks with time 0). A
  peer that stops reading holds a slot forever. Give sends the idle
  deadline.
- [ ] **SIGTERM unseen under load**: it is asked only after 250 ms with
  no arrival (`accept.on`, `:2057`). Ask on every turn of the accept
  loop, or put a signalfd in the poller. Make the flag's read-and-clear
  an atomic exchange (`signal_pending.c:32`).
- [ ] **One waiter per descriptor.** `EPOLL_CTL_MOD` replaces `data.ptr`
  (`comp.ts:7043`), so a second waiter is lost and `io_fds` drifts.
  Unreachable while sockets are linear; reached by the first full-duplex
  API. A per-fd `{reader, writer}` record behind `data.ptr`.
- [ ] **OpenSSL's buffered bytes are invisible** to `recv_bytes` and
  `accept`, which park on POLLIN before reading. Ask `SSL_pending` in
  `io_step`, or read first as `poll_bytes` does.
- [ ] `Listener.close` leaves `tls_ctx[lfd]` set: the next plain listener
  on that number is TLS with the old certificate. Shut it.
- [ ] `SSL_new` failing serves the socket in plaintext (`tls_listen.c:151`).
  Fail closed.
- [ ] JS `IO.signal_pending` never fires (the loop never yields) and its
  handler disables the default SIGTERM.
- [ ] `max = 0` reads as EOF in `recv_bytes` and `poll_bytes`.
- [ ] Accepted sockets: `accept4(SOCK_NONBLOCK|SOCK_CLOEXEC)`,
  `TCP_NODELAY`. Listeners: a bind address and IPv6 (today `0.0.0.0`
  only, while the banner says `127.0.0.1`).
- [ ] `main.ts`: find OpenSSL with `pkg-config`, so TLS builds on macOS.

## Phase 3: laws that constrain

41 of the 47 laws are closed terms the checker evaluates; the six
universal ones are shallow (`feed_split` holds for any left fold,
correct or not). The laws worth having:

- [ ] **Unique framing**: the parser agrees with a reference grammar of
  RFC 9112 message framing, so a byte stream has one request sequence.
  This is the law Phase 1 is missing.
- [ ] **Replies do not depend on chunking**: at the plan level, not the
  reader's; the IO loop (`plan.*`, `conn`) has no law today.
- [ ] **Content-Length equals the body** for every reply `reply()`
  builds, echo and files included.
- [ ] **Containment for every path**: the normaliser never climbs out,
  over all inputs (the lemma over classified segments the README names).
- [ ] **No route shadows another**, prefixes included, for any table.
  `distinct` compares exact bytes and cannot see `/` shadowing.
- [ ] `unmask(mask(m, k), k) = m`; a SHA-1 vector past 64 bytes.
- [ ] **The gate cannot be edited by the code's author**: pin a hash of
  LAWS.bend in `.github/workflows/http.yml`, keep a manifest of required
  law names, and run the demo through `tests/kernels/proof.ts`, which
  refuses `@unsafe` and writes a receipt.

## Phase 4: bytes

Every byte is a 16-byte list cell. A 4 MiB file is ~64 MiB of heap, a
1 MiB body ~32 MiB, and the path and the WebSocket key are unbounded
(~16 MiB a connection under the wait budget). This is the 4 MiB file
cap, most of the pipeline-8 gap to C, and the memory attacks at once.

- [ ] A packed `Bytes` in the runtime and `base.bend`, with the byte
  effects carrying it. The one change with the most leverage.
- [ ] Files streamed in pieces, not one `read()` against an earlier
  `File.size` (a short read desyncs keep-alive, `:1479`).
- [ ] Bounds as laws: request line, header count, header bytes (431),
  `Sec-WebSocket-Key` at 24 (a 1 MiB key goes into bit-at-a-time SHA-1),
  connections per peer.
- [ ] The wait budget counts bytes, not reads: 64 reads cuts a WAN body
  of 100-300 KB (`:1986`).

## Phase 5: a library, not a demo

`Act` is a closed set of six (`:1063`), `Req` carries no headers, and
only `Page` may do IO.

- [ ] `Handler = Req -> IO(Resp)`; `Req` with method, path, query,
  headers, body; a response builder; streaming bodies as a first-class
  segment.
- [ ] Routes with a method and path parameters; the shadowing law over
  them.
- [ ] The laws on the library's contract, so every app inherits them.
- [ ] Protocol: HTTP/1.0 (a 400 today [c]); query strings (a 404 [c]);
  POST, PUT, DELETE; chunked request bodies; `Expect: 100-continue`;
  percent-decoding; Host required; `Date`; ETag, 304, Range; 501 for an
  unknown method and 404 before 405.
- [ ] Static files: no dotfiles (`/.env`, `/.git`), no symlink out of
  the root (`O_NOFOLLOW` or `openat` beneath it), a wider MIME table.
- [ ] WebSocket: fragments, UTF-8 on text, control frames of 125 bytes
  at most (`ws.bend:86`), close codes validated before echo
  (`ws.bend:275`), one close only (`ws.bend:318`), `Sec-WebSocket-Version`
  and `Origin` checked, server pings, server-initiated sends.
- [ ] TLS: SNI and several certificates, reload, `TLS.connect`.
- [ ] kqueue on macOS and BSD; the JS backend's wire.
- [ ] HTTP/2 after `Bytes` and the handler API, not before.

## The README, corrected

- The binary links `libssl` and `libcrypto` too, since `main.bend`
  imports TLS; "libc and libm alone" holds only for a build without it.
- The checker names three defs on unsafe or foreign code (`accept`,
  `run`, `main`), not one.
- The all-digits length rule does disagree with proxies (Phase 1).

## Held, and why it is fine

The heap, the ADD/MOD fallback for a reused descriptor, one loop thread
for all of it, partial `SSL_write`, per-descriptor TLS beside plain
sockets, `..` refused, SHA-1 and base64 checked by hand, the extended
length's overflow, and 6.4 MB RSS under a 20,000-request pipeline that
is never read. The laws import `main.bend` itself, so they cannot drift
from what runs.

## Reproducing the confirmed items

    bun bend2/main.ts demos/io_http_engine/main.bend -o httpd && ./httpd &
    printf 'GET /echo HTTP/1.1\r\nx-v5fged: 5\r\n\r\nhelloGET /health HTTP/1.1\r\n\r\n' | nc -q1 127.0.0.1 8080
    printf 'GET /echo HTTP/1.1\r\nContent-Length: 3\r\nContent-Length: 5\r\n\r\nabcde' | nc -q1 127.0.0.1 8080
    printf 'GET /echo HTTP/1.1\r\nContent-Length: 4294967301\r\n\r\nhello' | nc -q1 127.0.0.1 8080
    printf 'GET /health HTTP/1.0\r\n\r\n' | nc -q1 127.0.0.1 8080
    printf 'GET /health?x=1 HTTP/1.1\r\n\r\n' | nc -q1 127.0.0.1 8080

The first echoes `hello`: a header no proxy reads as a length was one.
