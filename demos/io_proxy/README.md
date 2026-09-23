# bend-proxy

A reverse proxy on bend-wire that cannot be desynchronised: the upstream
never sees a request boundary the proxy did not frame, and a client never
sees a response boundary the proxy did not send. No byte a client or an
upstream sends is passed through; every request and every response is
framed by a reader proven equal to its RFC 9112 spec, rebuilt from what
was read, checked, and only then written.

    bend demos/io_proxy/main.bend -o proxyd
    ./proxyd --port 8080 --upstream 127.0.0.1:9000
    ./proxyd --port 8443 --tls-cert cert.pem --tls-key key.pem \
      --upstream example.org:443 --upstream-tls --upstream-sni example.org --ca ca.pem

| flag | default | |
| --- | --- | --- |
| `--port N` | 8080 | listen here |
| `--upstream H:P` | | the upstream, an address or a name |
| `--upstream-tls`, `--upstream-sni NAME`, `--ca FILE` | | TLS upstream, the name sent and verified, the CAs trusted |
| `--host NAME` | the client's | the Host sent upstream |
| `--idle-ms N` | 5000 | a client's idle time |
| `--connect-ms N` | 3000 | a connect's deadline (then 504) |
| `--upstream-ms N` | 30000 | a response's deadline (then 504) |
| `--pool N` | 64 | idle keep-alive upstream connections kept |
| `--head-cap N` | 65536 | the most bytes of a request head (then 431) |
| `--max-conns N`, `--grace-ms N` | 4096, 5000 | clients at once; drain on SIGTERM |
| `--shared` | | SO_REUSEPORT: one copy per core (the runtime's `--workers N` forks them) |
| `--tls-cert F --tls-key F` | | serve TLS |

## What it does

A request: the client's stream is stepped through the HTTP engine's
reader (`demos/io_http_engine`, held to its `spec.bend` by `frame_sim`)
a byte at a time from a fresh reader until it completes one; the bytes it
took are re-read by `spec.bend`'s own views (request line, field lines
split at the colon, names lowercased, values trimmed), and the proxy
sends a request it builds (`core.bend`): the request line rebuilt, one
Host (the client's or `--host`), the end-to-end fields one per line,
X-Forwarded-For/-Proto/-Host and Via added, one Content-Length counted
from the framed body (a chunked body goes up de-chunked). Connection and
every field it names, Keep-Alive, Proxy-Connection, TE,
Transfer-Encoding, Upgrade, Trailer and Expect never go up. Before it
goes, the request is checked against what the upstream's framing needs
(`valid`); a refused request (400) or a head past its cap (431) sends
nothing upstream. Upstream, over a pooled keep-alive connection
(`wire/pool.bend`), with connect and response deadlines; an idempotent
request that meets a stale pooled connection is retried once on a fresh
one. `Expect: 100-continue` is answered by the proxy.

A response: read by `wire/client.bend`'s exchange (`wire/http1/resp.bend`,
held to `wire/http1/spec.bend` by `resp_sim`; interim 1xx heads skipped),
its head read again from its bytes, and a response rebuilt: the status
line, the end-to-end fields, Via, a Content-Length from the framed body
(a chunked or close-delimited body goes back with a length; HEAD keeps
the upstream's), `Connection: close` when the proxy closes. It is checked
(`rvalid`) before it goes; an upstream that cannot be reached, hangs,
closes early or answers with nothing the check passes is a 502 or a 504,
with no partial response.

## The laws (LAWS.bend, proven in PROOF.bend)

- `scan_is_spec`: however the client's stream is cut into reads, the
  proxy frames it as `spec.bend`'s walk does, a request at a time, and
  refuses where it refuses.
- `frames_agree`: that framing is `spec.bend`'s `frame()` itself.
- `forward_canonical`: the bytes sent upstream are exactly
  `serialize(parse(r))` of the requests `frame()` framed: never a byte
  of the client's.
- `no_smuggle`: the upstream stream read back by `frame()` is exactly
  the requests forwarded, one for one (method, target, body), and
  nothing after the last: parse after serialize is the identity.
- `hop_by_hop_removed`, `hop_by_hop_removed_rsp`: no forwarded request
  or response carries a hop-by-hop field or one its Connection named
  (the list spelled out in LAWS.bend, not taken from `core.bend`).
- `rsp_reframed`: what goes back to a client, read by
  `wire/http1/spec.bend`'s `response()`, is one final response with the
  upstream's status and body (none where its framing says none), closing
  exactly when the proxy closes, and not a byte more; or the proxy's own
  502.
- `refused_not_forwarded`: a stream refused before its first request
  ends sends nothing upstream.

`python3 demos/io_proxy/mutants.py` breaks `core.bend` fifteen ways (raw
passthrough, TE kept, Connection-named fields kept, reading on after a
refusal, requests or responses sent unchecked, a length that is not the
body's, a body after a bodyless response, a 101 taken as final, a close
not announced, a 502 with a body to HEAD, ...) and the proof refuses each.

Not proven: the IO loop in `main.bend` (it calls `fwd`, `wire.at`,
`rsp.of` and `reply`; the laws are about those functions), the pool's
choice of connection, deadlines and the retry; the head re-read of a
response from the bytes the exchange read (the check, not a law, keeps
anything it misreads from going out); the laws take the client's body
cap as the reader's largest.

## Checks

    python3 demos/io_proxy/check.py ./proxyd 20120 [--nginx]

runs the smuggling vectors (CL.TE, TE.CL, TE.TE obfuscations, doubled or
listed or signed Content-Length, obs-fold, bare LF and CR, NUL, an
HTTP/2 preface, a request hidden in a body, byte-at-a-time variants)
against an upstream that records every byte, and checks hop-by-hop
removal both ways, re-framing, HEAD, pipelining, pooling (20 client
connections, one upstream connection), 100-continue, 502/504 paths and
the stale-connection retry. With `--nginx` the same vectors run through
nginx beside it.
