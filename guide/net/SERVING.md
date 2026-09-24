# Serving

The server in `net/server.bend`: requests and responses, the configuration
and the command line, the router, middleware, the handler's time, shared
state, files and TLS. The tour is `bend guide networking`.

## Requests and Responses

A `Request` is `Request{method, path, query, headers, body, remote, params}`.
Read it with `Http.method(r)`, `Http.path(r)`, `Http.query(r)`,
`Http.header(r, "x-name")` (a `Maybe`), `Http.body(r)`, `Http.remote(r)` (the
peer's address) and `Http.param(r, "id")`. The path and query come as they were
sent: split at the first `?`, not decoded. Header names are lowercase and
values are trimmed. The framing's own fields (Content-Length,
Transfer-Encoding, Connection, Upgrade) belong to the server and are not passed
on. The body is whole, and at most `max_body` bytes.

A `Response` is `Response{status, headers, body}`. Build one with
`Http.text`, `Http.html`, `Http.json` (a JSON text as it is) or
`Http.bytes(status, ctype, body)`; `Http.plain(status)` (the status's reason
as the body), `Http.redirect(status, loc)` and `Http.file(root, path)`. Add a
field with `Http.with.header(resp, name, value)`. `Http.reply(resp)` is
`IO.pure`. The server writes the length; a HEAD gets GET's length and no body.

The server listens on every IPv4 interface (`0.0.0.0`) unless `Server.set.host`
or `--host` names one, and says where on stderr. The address may be IPv6:
`--host ::1` is this machine alone, and `--host ::` every interface of both
families. The banner then brackets it, `http://[::1]:8080`, and a request's
`Http.remote` is the peer's address in RFC 5952's text (`::1`).

## Configuration

`Server.config(port)` is the defaults. `Server.set.host`, `idle`, `head`,
`body`, `send`, `max_head`, `max_body`, `conns`, `grace`, `handler`,
`tls(cert, key)` and `shared` change one each:

```python
# 2 s of idle, bodies of at most 64 KiB, at most 256 connections
def config() -> Server.Cfg:
  Server.set.conns(Server.set.max_body(Server.set.idle(Server.config(8080), 2000), 65536), 256)
```

A `max_body` past 1 MiB is cut to 1 MiB, the engine's cap. Larger bodies are
streamed (`bend guide net/streams`).

## The Command Line

`Server.argv(own)` asks `IO.args()` once and checks it: every flag must be one
of the server's or one of `own`, the program's, each written as a usage line
writes it: `"--root DIR"` takes a value, `"--verbose"` none, and a value named
`N` must be a number. A flag neither knows, a flag without its value, a number
that is not one, or a word that is no flag's value ends the program with the
reason and a usage line (exit 2):

```python
def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv(["--root DIR"])
    Server.serve.routes(~Bytes(), ~routes, Server.flag(xs, "--root", "www"), Server.args(xs, Server.config(8080)))
```

```
$ ./files --prot 80
unknown flag --prot
usage: [--root DIR] [--host A] [--port N] [--idle-ms N] ... [--tls-cert FILE] [--tls-key FILE] [--shared]
```

What it answers is `Data`, so every reader takes it as often as it likes.
`Server.args(xs, cfg)` reads the server's flags over `cfg`: `--host`,
`--port`, `--idle-ms`, `--head-ms`, `--body-ms`, `--max-head`, `--max-body`,
`--max-conns`, `--grace-ms`, `--handler-ms`, `--tls-cert`, `--tls-key` and
`--shared`. A flag given wins over `cfg`; a `Server.set` applied to what
`args` answers wins over the flag. `Server.flag(xs, "--root", "www")` reads a
value of your own, `Server.flag.num(xs, "--every", 1000)` a number and
`Server.flag.on(xs, "--verbose")` a flag with no value. `Stream.argv` and
`Stream.args` add the stream's flags (`--max-stream`, `--progress-ms`).

## The Router

```python
def routes(+db: Chan(Store)) -> List<Server.Route>:
  [Server.get("/health", health),
   Server.get("/notes", r => list(db, r)),
   Server.post("/notes", r => add(db, r)),
   Server.get("/notes/:id", r => one(db, r)),
   Server.delete("/notes/:id", r => del(db, r))]
```

`Server.route(routes, req)` runs the first route whose pattern matches the path
and whose methods hold the request's. A pattern is a path cut at `/`: a literal
segment matches itself, `:name` matches one non-empty segment, and a last `*`
matches the rest. `Server.get` answers HEAD too. `Server.post`, `put`, `patch`,
`delete` and `Server.on(methods, pat, h)` make the others. No match is a 404. A
path that matches with another method is a 405 whose `Allow` lists the methods
that would work. `Server.serve.routes(~E, ~routes, env, cfg)` serves a table
made from `env` directly.

A `:name` arrives percent-decoded, by `Http.param`:

```python
def one(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  +id = Http.param(r, "id")
  locked(db, st => one.of(id, st))
```

A query value arrives decoded too, by `Http.query.get`. It answers a `Maybe`:

```python
# GET /greet?name=...: the query's value, percent-decoded, or a default
def greet(r: Http.Request) -> IO(Http.Response):
  +name = Maybe.default(&2, Bytes(), Http.query.get(r, "name"), "stranger")
  Http.reply(Http.text(200, Bytes.concat(["Hello, ", name, "!\n"])))
```

`Http.query.pairs(q)` answers every pair in order, and `Http.pct.decode`,
`Http.form.decode` (`+` is a space too) and `Http.pct.encode` do
percent-encoding by hand.

## Middleware

Middleware is a template from handler to handler, and they nest.
`~Server.logged(~app)` writes a line per request on stderr: the method, the
path, the status, the body's length and the time the handler took.
`~Server.secured(~app)` adds the headers a browser should see (nosniff, `DENY`
framing, no referrer, a CSP of `'self'`, which refuses inline scripts and
styles), each unless the handler set it:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv([])
    Server.serve(~Server.logged(~Server.secured(~app)), Server.args(xs, config()))
```

A handler that takes an environment is no template argument, so each also has
an `.around` form over the IO a handler returns. `Server.logged.around` reads
the request twice, so the request is reusable (`+r`) there:

```python
# the routes, each request logged, the browser's headers added
def app.go(+db: Chan(Store), +r: Http.Request) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(Server.route(routes(db), r)))
```

`Server.wrap(~mw, routes)` puts one middleware, an `.around` form or several
nested, around every route of a table: plain routes, `Server.static`,
`Stream.get` and `WsServer.ws` routes alike, so one line logs and secures a
whole app, its files and its WebSocket too:

```python
# each request logged, the browser's headers added
def mw(+r: Http.Request, io: IO(Http.Response)) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(io))

def routes(+root: Bytes()) -> List<&1, Server.Route>:
  Server.wrap(~mw, [Server.get("/health", health), Server.static("", root)])
```

A `Stream.get` or WebSocket route's answer passes through `mw` once its handler
gave it: a response as itself, a pour as its status and fields (the fields `mw`
adds go out in its head), an accepted WebSocket as a 101 (its head is the
handshake's). When `mw` answers another status in their place, that response
is the answer. The router's own 404 and 405 are no route's; to see those,
wrap the whole handler (`~Server.logged(~app)`).

A handler that can fail answers `Result<&2, &2, Bytes(), Http.Response>`.
`~Server.recovered(~h)`, or `Server.recovered.around`, turns a `Fail` into a
plain 500. The message goes to stderr, not to the client. It catches only a
`Fail` the handler answers: Bend has no exceptions.

```python
def routes() -> List<Server.Route>:
  [Server.get("/greet", greet), Server.get("/add/:a/:b", r => Server.recovered.around(add(r))),
    Server.get("/stall", stall)]
```

## The Handler's Time

A handler has `handler` ms, 30 s by default, to answer (`Server.set.handler`,
`--handler-ms`). Past it the server answers 503 with `Connection: close`,
after the responses already waiting, and closes; whatever the handler
answers later is dropped. 503, not 504: the server could not handle the
request in time, where 504 says an upstream it reached as a gateway did
not answer.

```python
# GET /stall: a handler that waits and never answers (49 days is never);
# when the handler's time is up (Server.set.handler, --handler-ms; 30 s)
# the server answers 503, closes, and lets it go
def stall(r: Http.Request) -> IO(Http.Response):
  IO.bind(Unit, Http.Response, IO.sleep(4294967295), u => Http.reply(Http.text(200, "awake\n")))
```

Nothing preempts a Bend computation: it yields only at an effect. So the
deadline lets go a handler that waits (a sleep, a channel, a socket, an
upstream), which runs on, unseen, until it ends. A handler that computes
for a minute without an effect holds the event loop for that minute, and
its answer is written. The time runs from the handler's first effect until
it answers: a response, a `Stream.get` handler's `Stream.Reply`, a WebSocket
handler's accept or refusal. A pour or a WebSocket session, once begun, is not
under it: each send has 10 s (`send`) to make progress. Underneath is
`IO.within(A, ms, act)`, which answers `Some` of `act`'s answer, or `None` when
`act` still waits `ms` after its first effect.

## Shared State

`Server.serve.with(~E, ~app, env, cfg)` hands `env` to every call of the
handler. `E` must be `Data`: a configuration, a client session, or a channel.
A channel of one is a lock. A handler takes the value out, changes it and puts
it back, so two requests never see half a change:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv([])
    +db : Chan(Store) <- Chan.new(Store, 1)
    ok : Bool <- Chan.send(Store, db, Store{1, Map.new(&2, Bytes())})
    Server.serve.with(~Chan(Store), ~app, db, Server.args(xs, Server.config(8080)))
```

A `Chan(File)` of one shares a log file between computations the same way.
Work beside the server (a loop per job) is `IO.spawn`; such a loop keeps the
process alive, so it should end when `IO.signal_seen(15)` says SIGTERM came,
and sleep in slices short enough to see it.

## Static Files

`Server.static(prefix, root)` (in the `Server.wrap` snippet above) serves the
files under `root` at `prefix/...`. The path is normalised, a climb out of the
root or a dotfile is a 404, no link is followed, and `/` is `index.html`. The
kernel sends the file (sendfile), so a file is not bound by `max_body`.
`Server.static.at(root, r)` is its handler, for a route of your own.

## TLS

```python
def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv([])
    Server.serve(~app, Server.args(xs, Server.set.tls(Server.config(8443), "cert.pem", "key.pem")))
```

```bash
openssl req -x509 -newkey rsa:2048 -nodes -days 30 -subj /CN=localhost \
  -keyout key.pem -out cert.pem
bend net/examples/tls_server.bend -o tls && ./tls --port 8443 --tls-cert cert.pem --tls-key key.pem
curl --cacert cert.pem https://localhost:8443/
```

`Server.set.tls(cfg, cert, key)` takes two PEM files, and `--tls-cert` and
`--tls-key`, read over it, win. The server then speaks TLS 1.2 or later, with
ALPN `http/1.1`. A certificate or key that cannot be loaded ends the program
before it listens, with `TLS setup failed` and the file at fault.
