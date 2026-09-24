# bend-net

HTTP for Bend programs: a server and a client in a few lines, with every
timeout, limit and safe default on from the start, and the promises
that matter proven (`net/LAWS.bend`). It is a front door over engines
that already exist and are proven: the HTTP engine's reader
(`demos/io_http_engine`, `frame_sim`), bend-proxy's scan and response
writer (`demos/io_proxy`, `scan_is_spec`, `rsp_reframed`) and bend-wire's
loops, client exchange and pool (`wire/`).

```python
import Base
import ../net/http.bend as Http
import ../net/server.bend as Server

def hello(req: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "Hello, world!\n"))

def main() -> IO(Unit):
  Server.serve(~hello, Server.config(8080))
```

```python
import ../net/client.bend as Client
...
  r : Client.Res() <- Client.get("https://example.com/")
  match r:
    case Done{resp}: ...  # Http.status(resp), Http.resp.header(resp, "content-type"), Http.resp.body(resp)
    case Fail{e}: ...     # Client.error.show(e)
```

## The API

    net/http.bend     Http: the types, their accessors and builders
    net/server.bend   Server: serve, the configuration, the router, middleware
    net/client.bend   Client: get, post, request, sessions (pooled), NetError
    net/url.bend      URLs: parse, parse.ws, resolve, origin
    net/json.bend     Json: JSON bodies on power/json_value.bend
    net/ws.bend       Ws: a WebSocket connection, either end: connect, send, recv, close
    net/ws_server.bend WsServer: WebSocket routes, accept/refuse, options, the Hub
    net/ws_net.bend   the WebSocket client's Ws.Err as a NetError

**Http.** `Request{method, path, query, headers, body, remote, params}`
(`Http.method(r)`, `Http.header(r, "x-name")`, `Http.param(r, "id")`,
`Http.query.get(r, "q")`, `Http.body(r)`, ...): the method's bytes, the
target before its `?` and after it (neither decoded), the fields in
order (names lowercase, values trimmed; the framing's own --
Content-Length, Transfer-Encoding, Connection, Upgrade -- are the
server's), the body (whole, at most `max_body`), the peer's address,
and the router's params. `Response{status, headers, body}`, built by
`Http.text/html/json/bytes(status, ...)`, `Http.file(root, path)`,
`Http.plain(status)`, `Http.redirect(status, loc)`,
`Http.with.header(r, n, v)`; `Http.reply(r)` is `IO.pure`. Headers:
`Http.get/set/add/del/has`. Percent-encoding: `Http.pct.encode`,
`Http.pct.decode`, `Http.form.decode` ('+' a space too);
`Http.query.pairs(q)`. `Http.write(...)` is the bytes a response goes out
as (the server's writer, `respond_framed`'s).

**Server.** `Server.serve(~app, cfg)` with `app: Http.Request ->
IO(Http.Response)`; `Server.serve.with(~E, ~app, env, cfg)` hands `env`
(a channel, a configuration: shared state) to every call. `cfg` is
`Server.config(port)` changed by `Server.set.host/idle/head/body/send/
max_head/max_body/conns/grace/tls(cert, key)/shared`, or read from the
command line (`xs` is `IO.args()`) by `Server.args(xs, cfg)` (`--host
--port --idle-ms --head-ms --body-ms --max-head --max-body --max-conns
--grace-ms --tls-cert --tls-key --shared`; `Server.flag(xs, name, d)`
reads one of your own). Precedence: a flag given wins over `cfg`, and a
`set.*` applied to what `args` answers wins over the flag. The server
binds `host` (0.0.0.0, every IPv4 interface, by default) and says so on
stderr; a certificate or key that does not load ends it with `TLS setup
failed` and the file.
Router: `Server.route(routes, req)` over `[Server.get(pat, h),
Server.post(...), put, patch, delete, Server.on(methods, pat, h),
Server.static(prefix, root)]`, patterns of literals, `:name` and a last
`*`; no match is a 404, a path with other methods a 405 with `Allow`,
and GET answers HEAD. `Server.serve.routes(~E, ~rs, env, cfg)` serves the
routes `rs(env)` directly, and then a `Server.Sock` route (a GET one;
`WsServer.ws` makes them) may take its connection over: it is told
whether the request asked to switch protocols, and answers a response
or the head that switches it and what runs on the socket. Middleware is Handler -> Handler as a template:
`~Server.logged(~app)` (a line per request on stderr),
`~Server.secured(~app)` (nosniff, DENY, no-referrer, CSP 'self', each
unless set), `~Server.recovered(~app)` (a handler answering
`Result<Bytes(), Response>`, a failure a plain 500); they nest
(`~Server.logged(~Server.secured(~app))`), and each has a `.around` form
over a handler's IO (`Server.logged.around(r, io)`) for handlers with an
environment.

**Client.** `Client.get(url)`, `Client.post(url, ctype, body)`,
`Client.request(Client.Req{method, url, headers, body}, opts)`: each
`IO(Result<NetError, Response>)` on a session of its own;
`Client.session(opts)`, `Client.fetch(s, req)`, `Client.close(s)` keep
connections between requests. `NetError = Timeout | Refused | Dns | Tls
| Protocol | TooLarge | Closed | BadUrl | TooManyRedirects | Io`.
`Client.opts()` changed by `Client.with.connect/timeout/max_body/
redirects/ca/gzip` (each a `U32` but `ca`, a file, and `gzip`, a `Bool`).

Results: an error is always reusable (`&2`), and so is a value that is
`Data`: `Client.Res()` is `Result<&2, &2, NetError, Response>`. Only a
value that holds a handle is affine: `Ws.connect` answers `Result<&2,
&1, Ws.Err, Ws.Conn>`. A command line is what `IO.args()` answers,
`List<String>`, and every flag reader takes it as it is.

**WebSockets.** `Ws.connect(url, Ws.opts())` is a client's connection;
`WsServer.ws(pat, h)` is a route (beside `Server.get` and the rest, served by
`WsServer.serve(~routes, cfg)` or `WsServer.serve.with(~E, ~routes, env, cfg)`,
which is `Server.serve.routes`) whose `h: Http.Request -> IO(WsServer.Take)`
answers `WsServer.accept(proto, run)` or `WsServer.refuse(resp)`, and `run:
Ws.Conn -> IO(Ws.Conn)` gets a server's connection. Either end has the same
verbs and messages: `Ws.send_text/send_bytes/ping` (`Ws.Out(Unit)`),
`Ws.recv/recv_for` (`Ws.Out(F.Msg)`: `Text{s}`, `Binary{b}`, `Closed{code,
reason}`), `Ws.protocol`, `Ws.end(c, code, reason)` (the closing handshake,
the connection handed back), `Ws.close` (the same, then released).
`WsServer.choose(r, ours)` picks a subprotocol the client offered;
`WsServer.ws.with(o, pat, h)` takes `WsServer.opts()` changed by
`opts.max_msg/keepalive(ping, pong)/timeouts(recv, close, send)/origins`.
A `WsServer.Hub` is a room: `hub.new`, `join`, `leave`, `publish`, `inbox`,
`relay`.

**Json.** `Json.respond(status, j)`, `Json.body(req, budget)`,
`Json.of(resp, budget)` (`Result<J.Why, J.Json>`), `Json.obj/kv/arr/
str/yes/no/null`, numbers by `Json.num` (a `U32`), `Json.i64` (an `I64`)
and `Json.f64` (an `F64`; NaN and infinities are null), `Json.get`,
`Json.get.str`, `Json.refused(why)`.

## The defaults

| | default | past it |
| --- | --- | --- |
| idle (no request in progress) | 5 s | closed, nothing said |
| a head, from its first byte | 10 s | 408, closed |
| a request, head and body | 30 s | 408, closed |
| a send's progress | 10 s | closed |
| a head, past the read it began in | 16 KiB (reads of 16 KiB) | 431, closed |
| a target | 8 KiB | 414, closed |
| a body | 1 MiB (the engine's cap, the most) | 413 before it is read |
| connections | 1024 | the next waits for a slot |
| SIGTERM | listener closed, idle connections let go within a second | the process ends when the rest end, or after grace (5 s) |
| client: connect (DNS aside) | 10 s | Timeout |
| client: an exchange | 30 s | Timeout |
| client: a response's head, body | 64 KiB, 10 MiB | TooLarge |
| client: redirects | 10 | TooManyRedirects |
| client: idle connections | 8 an origin, 32 origins, 4 s, 60 s old | closed |
| client: TLS | verified (system store, or `ca`), name checked | Tls |
| WebSocket server: a message | 1 MiB | 1009 |
| WebSocket server: quiet, then the ping unanswered | 20 s, 20 s | a ping, then 1011 |
| WebSocket server: a recv, the closing handshake, a send | 60 s, 5 s, 10 s | ETime, closed |
| WebSocket server: SIGTERM | 1001 on each recv | the client's answer, or grace |
| WebSocket server: a Hub inbox | 1024 messages | the newest dropped |

A malformed request is a 400 that closes, and nothing after it on the
connection is read. The client sends a request again only when a pooled
connection proved stale before anything came back, and only for an
idempotent method. Credentials (Authorization, Cookie,
Proxy-Authorization) go only to the first request's origin. A URL with
a user or password in it is refused.

## The laws

`bend net/PROOF.bend` prints `All terms check.`, and the second kernel
passes its export. `net/LAWS.bend`:

- `handler_framed`: a handler is only handed what RFC 9112 frames: for
  every stream however cut into reads, the requests the server's scan
  takes, adapted, are spec.bend's `frame()` of the stream, adapted as
  LAWS.bend spells out.
- `respond_framed`: every response the server writes, read by
  wire/http1's spec, is one final response -- the handler's status and
  body (none for HEAD, 204, 304; its length the body's), closing as the
  server decided, nothing after -- or the 500 when the handler's fails
  the check (a line end in a value, a 1xx).
- `route_first`: the first route matching path and method wins; a 405's
  Allow is exactly the methods of the routes matching the path, once
  each, in order.
- `pool_clean`: the client pools a connection only when its response
  did not close it and nothing came after it, for every peer.
- `redirect_cap`, `redirect_creds`: a chain allowed k redirects sends at
  most k + 1 requests, and no credential to an origin but the first.
- vectors: percent-encoding over every byte, the query, URLs and
  Locations, the router's patterns, the response check.

`bend net/ws_proof.bend` is the WebSocket gate (`net/ws_laws.bend`): the
client's laws, and the server's -- `srv_hs_valid` (every request that
asked well gets RFC 6455 4.2.2's 101, the Accept its key earns),
`srv_hs_refused` (every other a 400 or 426), `srv_hs_proto` (no
subprotocol the client did not offer), `srv_frame_unmasked` (no frame the
server writes is masked), `srv_unmasked_refused` (an unmasked client
frame breaks the framing: 1002), `srv_reads` (the acts a handler's
connection takes are the spec's reassembly of the input, for every cut
of it into reads), `srv_close_once` and `srv_close_after` (at most one
close written, none after this end's own), and vectors.

`python3 net/mutants.py`: twenty broken servers and clients, each
refused; `python3 net/ws_mutants.py`: the WebSocket ones. Not proven: the IO loops (they call the functions the laws are
about), the deadlines and limits (checked by `check.py`).

## The examples

    net/examples/hello.bend        one handler
    net/examples/json_api.bend     a JSON API over a router, a channel as its store
    net/examples/file_server.bend  files under a root, the browser's headers
    net/examples/fetch.bend        a command-line client
    net/examples/greet.bend        a query, a handler that can fail, middleware, a config in code
    net/examples/notes_client.bend json_api's client: JSON out and in, NetError by kind
    net/examples/tls_server.bend   a server over TLS
    net/examples/relay.bend        fetch JSON upstream on a pooled session, serve part of it
    net/examples/ws_chat.bend      a WebSocket chat client
    net/examples/chat_server.bend  its room: a WebSocket route, a Hub, broadcast
    net/examples/ws_echo.bend      a WebSocket echo (the one Autobahn runs against)

`guide/NETWORKING.md` (`bend guide networking`) walks through them.

`python3 net/check.py` builds every example and checks, from outside: framing,
pipelining, HEAD, keep-alive, HTTP/1.0, 400/408/413/414/431, the idle,
head and body timeouts, the connection limit, 100-continue, SIGTERM,
404/405, JSON and files, the middleware, `--host` and its banner, a TLS
certificate that does not load; and the client against Python peers: pooling,
refused, DNS, the deadline, redirects (cap, 303, 307, credentials),
gzip, the body cap, a field with a line end refused, TLS refused
self-signed, trusted by `--ca`, the name checked, and the server over
TLS; and WebSockets on the server: the chat room's broadcast between two
ws_chat clients, its 426, 400 and 101, SIGTERM's 1001.
`python3 net/ws_check.py ./wsc ./httpd PORT --server ./echo --autobahn`
checks both ends against a raw peer, Python's websockets and the Autobahn
suite (301 / 301 cases each way, compression's excluded).

On one thread, `wrk -t2 -c32`, hello answers about 40k requests a
second where the engine's literal `/health` answers 58k; with the
response written as a literal the loop matches the engine, so the
difference is the checked writer (`respond_framed`'s).

Not yet: streaming request and response bodies (wire/stream.bend has the
machinery), bodies past 1 MiB, a deadline on the handler itself,
WebSocket compression (permessage-deflate is declined).
