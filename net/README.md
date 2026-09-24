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
`Http.get/set/add/del/has`. `Http.decode`, `Http.form`, `Http.encode`
(percent-encoding), `Http.query.pairs(q)`.

**Server.** `Server.serve(~app, cfg)` with `app: Http.Request ->
IO(Http.Response)`; `Server.serve.with(~E, ~app, env, cfg)` hands `env`
(a channel, a configuration: shared state) to every call. `cfg` is
`Server.config(port)` changed by `Server.set.idle/head/body/send/
max_head/max_body/conns/grace/tls(cert, key)/shared`, or read from the
command line by `Server.args(xs, cfg)` (`--port --idle-ms --head-ms
--body-ms --max-head --max-body --max-conns --grace-ms --tls-cert
--tls-key --shared`; `Server.argv()`, `Server.flag(xs, name, d)`).
Router: `Server.route(routes, req)` over `[Server.get(pat, h),
Server.post(...), put, patch, delete, Server.on(methods, pat, h),
Server.static(prefix, root)]`, patterns of literals, `:name` and a last
`*`; no match is a 404, a path with other methods a 405 with `Allow`,
and GET answers HEAD. Middleware is Handler -> Handler as a template:
`~Server.logged(~app)` (a line per request on stderr),
`~Server.secured(~app)` (nosniff, DENY, no-referrer, CSP 'self', each
unless set), `~Server.recover(~app)` (a handler answering
`Result<Bytes(), Response>`, a failure a plain 500); each has an
`*.around` form over a handler's IO for handlers with an environment.

**Client.** `Client.get(url)`, `Client.post(url, ctype, body)`,
`Client.request(Client.Req{method, url, headers, body}, opts)`: each
`IO(Result<NetError, Response>)` on a session of its own;
`Client.session(opts)`, `Client.fetch(s, req)`, `Client.close(s)` keep
connections between requests. `NetError = Timeout | Refused | Dns | Tls
| Protocol | TooLarge | Closed | BadUrl | TooManyRedirects | Io`.
`Client.opts()` changed by `Client.with.connect/timeout/max_body/
redirects/ca/gzip`.

**Json.** `Json.respond(status, j)`, `Json.body(req, budget)`,
`Json.of(resp, budget)` (`Result<J.Why, J.Json>`), `Json.obj/kv/arr/
str/num/yes/no/null`, `Json.get`, `Json.get.str`, `Json.refused(why)`.

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

`python3 net/mutants.py`: twenty broken servers and clients, each
refused. Not proven: the IO loops (they call the functions the laws are
about), the deadlines and limits (checked by `check.py`).

## The examples

    net/examples/hello.bend        one handler
    net/examples/json_api.bend     a JSON API over a router, a channel as its store
    net/examples/file_server.bend  files under a root, the browser's headers
    net/examples/fetch.bend        a command-line client

`python3 net/check.py` builds them and checks, from outside: framing,
pipelining, HEAD, keep-alive, HTTP/1.0, 400/408/413/414/431, the idle,
head and body timeouts, the connection limit, 100-continue, SIGTERM,
404/405, JSON and files; and the client against Python peers: pooling,
refused, DNS, the deadline, redirects (cap, 303, 307, credentials),
gzip, the body cap, a field with a line end refused, TLS refused
self-signed, trusted by `--ca`, the name checked, and the server over
TLS.

On one thread, `wrk -t2 -c32`, hello answers about 40k requests a
second where the engine's literal `/health` answers 58k; with the
response written as a literal the loop matches the engine, so the
difference is the checked writer (`respond_framed`'s).

Not yet: streaming request and response bodies (wire/stream.bend has the
machinery), bodies past 1 MiB, the server's Upgrade, a deadline on the
handler itself.
