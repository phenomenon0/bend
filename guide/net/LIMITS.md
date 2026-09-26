# Limits and Laws

Every default `net/` keeps, what its laws guarantee, and what it does not do
yet. The tour is `bend guide networking`.

## The Defaults

Every default is a bound. Each one exists so that a peer, slow or hostile,
cannot hold a resource forever.

| | default | past it | why |
| --- | --- | --- | --- |
| idle (no request in progress) | 5 s | closed, nothing said | an open, silent connection holds a slot |
| a head, from its first byte | 10 s | 408, closed | a head sent a byte at a time cannot hold a connection |
| a request, head and body | 30 s | 408, closed | nor can a body sent slowly |
| a send's progress | 10 s | closed | a peer that never reads cannot hold a response |
| a head, past the read it began in | 16 KiB | 431, closed | a head is held in memory whole |
| a target | 8 KiB | 414, closed | the same, for the request line |
| a body | 1 MiB (the most) | 413, before it is read | a body is held in memory whole |
| a streamed body | 1 GiB (`max_stream`; chunked, 256 MiB) | 413 | a stream route's body is read a chunk at a time |
| a streamed body's reads | 10 s each (`progress`) | 408, closed | a body sent a byte a minute cannot hold a connection |
| a body a stream handler left | 1 MiB drained | answered, closed | its bytes are never read as a request |
| a handler's answer, from its first effect | 30 s (`handler`) | 503, closed; the handler let go | a handler waiting on something that never comes cannot hold a connection |
| a streamed response's writes | each send within 10 s (`send`) | `ETime`, closed | a client that stops reading cannot hold a producer |
| connections | 1024 | the next waits for a slot | each holds memory and a descriptor |
| SIGTERM | listener closed; idle connections let go within a second | the rest end, or grace (5 s) is up | a deploy does not cut requests in flight |
| client: connect (DNS aside; shared among a name's addresses) | 10 s | `Timeout` | a host that does not answer |
| client: an exchange | 30 s | `Timeout` | a server that answers slowly, or never |
| client: a response's head, body | 64 KiB, 10 MiB | `TooLarge` | a response is held in memory whole |
| client: redirects | 10 | `TooManyRedirects` | a redirect loop ends |
| client: idle connections | 8 an origin, 32 origins, 4 s idle, 60 s old | closed | a pool does not grow without end, or keep a dead connection |
| client: TLS | verified (system store, or `ca`), name checked | `Tls` | no connection to a server that is not who the URL names |
| WebSocket: connect, recv, close | 10 s, 30 s, 5 s | `ETime` | the same as the client's |
| WebSocket: a message, the answer's head | 64 MiB, 16 KiB | 1009, `EHead` | a message is held in memory whole |
| WebSocket server: a message | 1 MiB | 1009 | a message is held in memory whole |
| WebSocket server: quiet, then no answer to the ping | 20 s, 20 s | a ping; then 1011 | a vanished client does not hold its connection |
| WebSocket server: a recv, the closing handshake, a send | 60 s, 5 s, 10 s | `ETime`, closed | the same as the client's |
| WebSocket server: SIGTERM | 1001 on each recv | the client's answer, or grace (5 s) | a deploy says goodbye |
| WebSocket server: an inbox (`Hub`) | 1024 messages | the newest dropped | a member that never reads does not hold the room's traffic |

A few rules are not numbers. A malformed request is a 400 that closes, and
nothing after it on the connection is read. A response the server cannot write
safely (a field with a line end in it, a 1xx) goes out as a 500. A URL with a
user or password in it is refused, and so is an IPv6 zone ID. A JSON body is
parsed under the budget you pass, at most 64 containers deep. A command line
read by `Server.argv` holds only flags the program declared.

## What the Laws Guarantee

`net/LAWS.bend` states them and `net/PROOF.bend` proves them. In plain words:

- `handler_framed`: a handler only sees requests the RFC 9112 spec frames,
  however TCP cut the bytes into reads.
- `respond_framed`: every response the server writes reads back as exactly one
  response, with the handler's status and body, or as the 500.
- `route_first`: the first matching route wins, and a 405's `Allow` lists
  exactly the methods that would have matched, once each. `wrap_pats`: a table
  wrapped in middleware keeps every route's methods and pattern.
- `pool_clean`: the client reuses a connection only when its response did not
  close it and nothing came after it.
- `redirect_cap`: a chain allowed k redirects sends at most k + 1 requests.
- `redirect_creds`: credentials never go to an origin other than the first
  request's.
- `stream_body`: the chunks a stream handler reads, joined, are the body RFC
  9112's framing finds, however TCP cut the stream.
- `stream_bounded`: between reads, a streamed body holds at most the last read.
- `stream_next`: after a streamed request the connection goes on only once
  the body has ended, with exactly the bytes after it.
- `handler_late`: a handler still waiting when its time is up is answered
  with a 503 that closes the connection, after what was waiting, and nothing
  it answers later is written. `handler_in_time`: one in time is written as
  ever. `late_framed`: the 503 reads back as one response.
- `ws_version`, `ws_route_methods`: a request with no `Sec-WebSocket-Version`,
  or one not 13, is answered 426 by a WebSocket route, and a POST that asked
  to upgrade is refused by the handshake (400), as a HEAD is.
- `pour_chunked`, `pour_length`: a response written as it is made reads back
  as exactly one response, its body the producer's writes joined; `pour_capped`:
  a declared length is never written past; `pour_quiet`: after a failure
  nothing more is written; `pour_bounded`: a write goes out as itself and at
  most 120 bytes of framing.
- `stream_head`: the head a stream handler gets (its fields, its framing, or a
  400) is the one RFC 9112's spec reads at the same byte.
- the vectors: percent-encoding, the query, URLs and Locations, the router's
  patterns, IPv6's text and IP-literal URLs, the command line (`argv_vectors`:
  what `Server.argv` refuses and passes; the flag readers) and JSON's typed
  fields (each type, paths, `Json.or`, `Json.fails`).

`net/ws_laws.bend` states the WebSocket client's and server's, and
`net/ws_proof.bend` proves them: every frame a client sends is masked and every
frame a server sends is not, forbidden frames are refused with their close
code, pings are answered, the handshake is checked as RFC 6455 says on both
ends, the messages a server's handler receives are the spec's reassembly of
the input however TCP cut it, and a close is answered once. To run them:

```bash
bend net/PROOF.bend            # prints: All terms check.
bend net/ws_proof.bend
python3 net/mutants.py         # broken servers, clients, flags and getters; the proof must refuse each
python3 net/ws_mutants.py
python3 net/check.py           # the examples, checked from outside against every default
```

What is not proven: the IO loops themselves, and the deadlines and limits.
`net/check.py` checks those from outside.

## Speed

On one thread, with `wrk -t2 -c32`, `hello` answers about 40k requests a
second. The HTTP engine's literal `/health` answers 58k. The difference is the
checked response writer that `respond_framed` is about (`net/README.md`).

## Not Built Yet

- A WebSocket handler that parks on its socket and a channel at once. A room's
  members (and `WsServer.broadcast`) wait in slices of 50 ms. It needs an
  effect that waits for either a socket's bytes or a channel's value and, when
  one comes, withdraws the other wait, so no value is taken and dropped:
  `IO.within` races one act against a deadline and lets the loser run on,
  which would lose a message.
- A streamed client response's head before its body: `Client.stream` tells the
  status once the body is through.
- A streamed response on a stream route (an upload's answer) or to a method
  but GET.
- A chunked streamed body past 256 MiB. A Content-Length body can reach 4 GiB.
- WebSocket compression (`permessage-deflate`): offered, it is declined.
- HTTP/2 in `net/`. `demos/io_http2` is an HTTP/2 server of its own.
- Happy Eyeballs (RFC 8305): a name's addresses are tried one after another,
  never raced. IPv6 zone IDs are refused.
