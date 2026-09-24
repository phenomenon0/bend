# Networking in Bend

Bend's networking library is `net/`. It is an HTTP/1.1 server, an HTTP/1.1
client, a WebSocket client and server, and JSON bodies. Every timeout and limit
is on from the start, and the promises that matter are proven in
`net/LAWS.bend`. It does not do everything. What it does not do yet is listed
at the end.

Every snippet below is copied from a file in `net/examples/` that checks and
builds. Those files sit in `net/examples/`, so they import the library as
`../http.bend`. From your own file, import it by its path from there.

## Hello, Server!

```python
import Base
import ../http.bend as Http
import ../server.bend as Server

def hello(req: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "Hello, world!\n"))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    Server.serve(~hello, Server.args(xs, Server.config(8080)))
```

```bash
bend net/examples/hello.bend -o hello && ./hello --port 8080
curl -i http://127.0.0.1:8080/
```

A handler is a function from `Http.Request` to `IO(Http.Response)`.
`Server.serve(~app, cfg)` runs it for every request until SIGTERM. The `~`
passes it as a template, so it compiles into the connection loop as a direct
call. Each connection is its own computation, with its own socket and
deadlines, so one connection's failure is its own. The server listens on every
IPv4 interface (`0.0.0.0`) unless `Server.set.host` or `--host` names one, and
says where on stderr.

## Serving

### Requests and Responses

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

### Configuration

`Server.config(port)` is the defaults. `Server.set.host`, `idle`, `head`,
`body`, `send`, `max_head`, `max_body`, `conns`, `grace`, `tls(cert, key)` and
`shared` change one each:

```python
# 2 s of idle, bodies of at most 64 KiB, at most 256 connections
def config() -> Server.Cfg:
  Server.set.conns(Server.set.max_body(Server.set.idle(Server.config(8080), 2000), 65536), 256)
```

`Server.args(xs, cfg)` then reads the command line, `xs` as `IO.args()`
answers it, over it: `--host`, `--port`, `--idle-ms`, `--head-ms`,
`--body-ms`, `--max-head`, `--max-body`, `--max-conns`, `--grace-ms`,
`--tls-cert`, `--tls-key` and `--shared`. Anything else is left alone. A flag
given wins over `cfg`; a `Server.set` applied to what `args` answers wins over
the flag. `Server.flag(xs, "--root", "www")` reads a flag of your own. Each
reader takes the list whole, so ask `IO.args()` once for each. A `max_body`
past 1 MiB is cut to 1 MiB, the engine's cap. Larger bodies are streamed
(Uploads, below).

### The Router

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
that would work.

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

### Middleware

Middleware is a template from handler to handler, and they nest.
`~Server.logged(~app)` writes a line per request on stderr: the method, the
path, the status, the body's length and the time the handler took.
`~Server.secured(~app)` adds the headers a browser should see (nosniff, `DENY`
framing, no referrer, a CSP of `'self'`), each unless the handler set it:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    Server.serve(~Server.logged(~Server.secured(~app)), Server.args(xs, config()))
```

A handler that takes an environment (below) is no template argument, so each
also has an `.around` form over the IO a handler returns. `Server.logged.around`
reads the request twice, so the request is reusable (`+r`) there:

```python
# the routes, each request logged, the browser's headers added
def app.go(+db: Chan(Store), +r: Http.Request) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(Server.route(routes(db), r)))

def app(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  app.go(db, r)
```

A handler that can fail answers `Result<&2, &2, Bytes(), Http.Response>`.
`~Server.recovered(~h)`, or `Server.recovered.around`, turns a `Fail` into a
plain 500. The message goes to stderr, not to the client:

```python
# GET /add/:a/:b: a handler that answers Done{response} or Fail{why};
# Server.recovered.around turns a Fail into a plain 500
def sum(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Result<&2, &2, Bytes(), Http.Response>:
  match a b:
    case Some{x} Some{y}:
      Done{Http.text(200, Bytes.append(U32.show((x + y : U32)), "\n"))}
    case _ _:
      Fail{"/add wants two numbers"}

def add(+r: Http.Request) -> IO(Result<&2, &2, Bytes(), Http.Response>):
  IO.pure(Result<&2, &2, Bytes(), Http.Response>, sum(U32.read(Http.param(r, "a")), U32.read(Http.param(r, "b"))))

def routes() -> List<Server.Route>:
  [Server.get("/greet", greet), Server.get("/add/:a/:b", r => Server.recovered.around(add(r)))]
```

### Shared State

`Server.serve.with(~E, ~app, env, cfg)` hands `env` to every call of the
handler. `E` must be `Data`: a configuration, a client session, or a channel.
A channel of one is a lock. A handler takes the value out, changes it and puts
it back, so two requests never see half a change:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +db : Chan(Store) <- Chan.new(Store, 1)
    ok : Bool <- Chan.send(Store, db, Store{1, Map.new(&2, Bytes())})
    Server.serve.with(~Chan(Store), ~app, db, Server.args(xs, Server.config(8080)))
```

### Static Files

```python
def routes(+root: Bytes()) -> List<Server.Route>:
  [Server.get("/health", health), Server.static("", root)]
```

`Server.static(prefix, root)` serves the files under `root` at `prefix/...`.
The path is normalised, a climb out of the root or a dotfile is a 404, no link
is followed, and `/` is `index.html`. The kernel sends the file (sendfile), so
a file is not bound by `max_body`.

### TLS

```python
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
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
ALPN `http/1.1`. Every other default is the same. A certificate or key that
cannot be loaded ends the program before it listens, with `TLS setup failed`
and the file at fault.

### Uploads

A body too large to hold is read as a stream, on a stream route.
`Stream.serve.with(~E, ~app, ~uploads, env, cfg)` (`net/stream.bend`) serves
`app` as `Server.serve.with` does, and a table of stream routes beside it. A
stream route's handler gets the request's head and its body as a
`Stream.Body`, and hands the body back beside its response:

```python
def uploads(+dir: Bytes()) -> List<Stream.Route>:
  [Stream.on(["PUT", "POST"], "/upload/:name", r => b => upload(dir, r, b)),
   Stream.post("/count", count),
   Stream.post("/refuse", refuse)]
```

`Stream.to_file(b, path)` writes the rest of the body to a file, a read at a
time, and answers how many bytes, as `Stream.Out(Nat)`: the body beside a
`Result`, like a WebSocket's `Ws.Out`:

```python
# the file written: 201 with its size, or why the body stopped
def saved(+name: Bytes(), g: Stream.Out(Nat)) -> IO(Stream.Body & Http.Response):
  (b, r) = g
  match r:
    case Done{n}:
      IO.pure(Stream.Body & Http.Response, (b, Http.text(201, Bytes.concat(["saved ", name, ": ", Nat.show(n), " bytes\n"]))))
    case Fail{e}:
      IO.pure(Stream.Body & Http.Response, (b, Http.text(400, Bytes.append(Stream.err.show(e), "\n"))))
```

`Stream.read(b)` answers the next chunk (`Some`, never empty), `None` at the
end, or a `Stream.Err` (`ETime`, `EBad`, `ELarge`, `EClosed`, `EIo`). The socket
is read only when the handler asks, at most 64 KiB at a time, so a slow handler
slows the client down and the server holds one read. A 100 MB upload runs in
about 6 MB of memory.

`Stream.config(cfg)` wraps a server configuration. `Stream.set.max_stream`
(1 GiB) caps a body: a longer Content-Length is a 413 before a byte is read,
and a chunked body is cut there (a chunked body is at most 256 MiB).
`Stream.set.progress` (10 s) is the time each read has to bring a byte, or
408. `Stream.args` reads `--max-stream` and `--progress-ms`, and every
`Server.args` flag. An `Expect: 100-continue` is answered at the handler's
first read, so a handler that refuses without reading never asks for the body.
When the handler returns, the server drains up to 1 MiB of what is left and
the connection goes on. Past that, it answers and closes. A body that failed
(malformed, too large, too slow) is answered by the server itself, whatever
the handler said. The whole program is `net/examples/upload.bend`.

### Exports and Event Streams

A body too large to hold, or one that never ends, is written as it is made. A
`Stream.get(pat, h)` route (GET and HEAD, beside `Server.get` in
`Server.serve.routes`) answers `Stream.whole(resp)`, `Stream.pour(status,
fields, run)` (chunked) or `Stream.pour.len(status, fields, n, run)` (a
Content-Length). The producer `run` gets a `Stream.Sink` and hands it back:

```python
# GET /export.csv, /export.ndjson
def export(+json: Bool, r: Http.Request) -> IO(Stream.Reply):
  +n = arg(r, "rows", 100n)
  IO.pure(Stream.Reply, Stream.pour(200,
    [Http.Header{"content-type", Bool.pick(Bytes(), json, "application/x-ndjson", "text/csv")}],
    k => rows(n, json, 0n, n, k)))
```

`Stream.write(k, bytes)` returns once the bytes are on the socket, so a client
that stops reading stops the producer; it answers the Sink beside `Done` or a
`Stream.Err`: `EClosed` (the client left), `ETime` (a send stalled past 10 s),
`ELarge` (past the declared length: nothing of it sent, and the connection
closes), `ENone` (HEAD, 204, 304: the head goes alone). After a failure every
write answers it and sends nothing. A 1 GB export runs in about 5 MB.
`Stream.events(~S, ~next, s, every, fields)` is an event stream: `next(s,
every)` answers `Stream.event(name, data)`, `Stream.idle()` (a keepalive goes
out) or `Stream.over()`:

```python
def started(+keep: U32, +n: Nat, +ms: Nat, +now: Nat) -> IO(Stream.Reply):
  +left = Bool.pick(Nat, Nat.is_eq(n, 0n), U32.to_nat(4294967295), n)
  IO.pure(Stream.Reply, Stream.events(~Tk, ~next, Tk{0n, left, now, ms}, keep, []))
```

The whole programs are `net/examples/export.bend` and `net/examples/events.bend`.
`Client.stream(~K, ~give, ~fin, url, opts, k)` hands a GET's body to a
consumer as it comes; with a `Stream.Sink` as the consumer it relays a body
end to end (`net/examples/relay_stream.bend`).

## Fetching

### One Request

```python
def run(+base: Bytes()) -> IO(Unit):
  +note = Json.text(Json.obj([Json.kv("text", Json.str("written by notes_client"))]))
  do IO<Unit>:
    r : Client.Res() <- Client.post(Bytes.append(base, "/notes"), "application/json", note)
    created(base, r)
```

`Client.get(url)` and `Client.post(url, ctype, body)` answer
`IO(Client.Res())`, which is `Result<&2, &2, Client.NetError, Http.Response>`:
in `net/`, an error and a `Data` value are reusable (`&2`), and only a value
holding a handle, like a WebSocket connection, is affine.
Read a response with `Http.status(resp)`, `Http.resp.header(resp, "name")` and
`Http.resp.body(resp)`.

### Options

`Client.request(req, opts)` takes a request you build and options.
`Client.req(method, url)` is a request with no fields and no body;
`Client.req.header` sets a field and `Client.req.body` the body. `Client.opts()` is the
defaults, and `Client.with.connect`, `timeout`, `max_body`, `redirects` (each
a `U32`), `ca` and `gzip` change one each:

```python
        g : Client.Res() <- Client.get(url)
        shown("GET", g)
        d : Client.Res() <- Client.request(Client.req.header(Client.req("DELETE", url), "x-request-id", "notes-1"),
          Client.with.timeout(Client.opts(), 2000))
        shown("DELETE", d)
```

`Client.with.ca(o, file)` trusts only the CAs in that PEM file instead of the
system's store. TLS is always verified, and the name is checked against the
certificate. There is no option to turn that off.

### Errors

```python
type NetError is Data:
  Timeout{}
  Refused{}
  Dns{msg: Bytes()}
  Tls{msg: Bytes()}
  Protocol{msg: Bytes()}
  TooLarge{}
  Closed{}
  BadUrl{msg: Bytes()}
  TooManyRedirects{}
  Io{code: U32, msg: Bytes()}
```

`Client.error.show(e)` says one in words. Match on the kinds you handle and
let `_` catch the rest:

```python
# a NetError, by kind: the exit code says which
def failed(e: Client.NetError) -> IO(Unit):
  match e:
    case Client.Refused{}:
      IO.die(Unit, 3, "notes: nothing is listening there")
    case Client.Timeout{}:
      IO.die(Unit, 4, "notes: no answer in time")
    case _:
      IO.die(Unit, 1, "notes: " ++ Client.error.show(e))
```

A status like 404 or 500 is not an error: it is a `Done` with that status.

### Sessions

`Client.get`, `post` and `request` each open a session and close it after.
To keep connections between requests, make a session, `Client.fetch` on it,
and `Client.close` it at the end:

```python
def run(c: Cli) -> IO(Unit):
  match c:
    case Cli{u, m, b, hs, o, +sh, tw, prev}:
      +rq : Client.Req = Client.Req{m, u, hs, b}
      do IO<Unit>:
        +ss : Client.Session <- Client.session(o)
        r : Client.Res() <- Client.fetch(ss, rq)
        answered(sh, r)
        again(tw, ss, rq, sh)
        Client.close(ss)
```

A session is `Data`, so a server can hand one to every handler through
`serve.with`, and requests from all of them share its connections. A session
keeps at most 8 idle connections an origin and 32 origins. A connection is
checked before it is used again. The client sends a request again only when a
pooled connection turned out stale before anything came back, and only for an
idempotent method.

### Redirects

The client follows 301, 302, 303, 307 and 308, at most 10 by default. 303, and
301 or 302 after a POST, go on as GET without the body. 307 and 308 keep the
method and the body. Authorization, Cookie and Proxy-Authorization go only to
the first request's origin. Past the cap, the answer is `TooManyRedirects`.

## JSON

`net/json.bend` writes and reads JSON on `power/json_value.bend`. Build a value
with `Json.obj`, `Json.kv`, `Json.arr`, `Json.str`, `Json.num` (a `U32`),
`Json.i64` (an `I64`), `Json.f64` (an `F64`; NaN and infinities are `null`),
`Json.yes`, `Json.no` and `Json.null`, and answer it with
`Json.respond(status, j)`. `Json.text(j)` is its text, for a request body.

```python
def note(id: Bytes(), text: Bytes()) -> J.Json:
  Json.obj([Json.kv("id", Json.str(id)), Json.kv("text", Json.str(text))])
```

`Json.body(req, budget)` parses a request's body and `Json.of(resp, budget)` a
response's. Both answer `Result<&2, &2, J.Why, J.Json>`: the value, or why it
was refused (a syntax error, too deep, past the budget, not UTF-8, a lone
surrogate, each with its byte). `Json.get(j, key)` reads a field, and
`Json.get.str(j, key)` a string's bytes or a number's text. `Json.refused(why)`
is a 400 that says why, as JSON:

```python
def add.body(+db: Chan(Store), r: Result<&2, &2, J.Why, J.Json>) -> IO(Http.Response):
  match r:
    case Done{j}:
      add.text(db, Json.get.str(j, "text"))
    case Fail{w}:
      Http.reply(Json.refused(w))

def add(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  add.body(db, Json.body(r, 65536))
```

### Fetch, Parse, Serve

`net/examples/relay.bend` is a small API in front of another one. It gets the
upstream's JSON, keeps the fields it promises, and gives every failure its own
answer:

```python
# a timeout is the upstream being slow: 504; anything else, 502
def fetched(+id: Bytes(), +up: Bytes(), r: Client.Res()) -> IO(Http.Response):
  match r:
    case Done{resp}:
      Http.reply(answered(id, up, resp))
    case Fail{e}:
      match e:
        case Client.Timeout{}:
          Http.reply(failed(504, "the upstream did not answer in time"))
        case _:
          Http.reply(failed(502, Client.error.show(e)))

# GET /users/:id
def user(+env: Env, r: Http.Request) -> IO(Http.Response):
  +id = Http.param(r, "id")
  +up = env.up(env)
  +url = Bytes.concat([up, "/users/", Http.pct.encode(id)])
  do IO<Http.Response>:
    res : Client.Res() <- Client.fetch(env.s(env), Client.req("GET", url))
    fetched(id, up, res)
```

Its session is made once, in `main`, and handed to every handler:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    ys : List<String> <- IO.args()
    +s : Client.Session <- Client.session(Client.with.timeout(Client.opts(), 5000))
    +env : Env = Env{s, Server.flag(xs, "--upstream", "http://127.0.0.1:9000")}
    Server.serve.with(~Env, ~app, env, Server.args(ys, Server.config(8080)))
```

## WebSockets

`net/ws.bend` is a WebSocket client (RFC 6455), over TCP or TLS.
`Ws.connect(url, Ws.opts())` answers the connection or a `Ws.Err`, as
`Result<&2, &1, Ws.Err, Ws.Conn>`. A connection is affine: every call hands it back beside its result, and
`Ws.close` or `Ws.drop` lets it go.

```python
# each message, in order
def say(xs: List<&2, String>, +name: String, c: Ws.Conn) -> R():
  match xs:
    case Nil{}:
      IO.pure(Maybe<&1, Ws.Conn>, Some{c})
    case Con{x, t}:
      IO.bind(Maybe<&1, Ws.Conn>, Maybe<&1, Ws.Conn>,
        IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_text(c, name ++ ": " ++ x), said),
        m => then(m, cc => say(t, name, cc)))
```

`Ws.send_text(c, s)` and `Ws.send_bytes(c, b)` answer
`Ws.Out(Unit)`, the connection beside a `Result`. `Ws.recv(c)` and
`Ws.recv_for(c, ms)` answer `Ws.Out(F.Msg)`, where a message is `F.Text{t}`,
`F.Binary{b}` or `F.Closed{code, reason}` (`F` is `net/ws_frame.bend`). A recv
that times out answers `ETime` and leaves the connection as it was:

```python
# one message heard; a quiet --wait-ms (the recv's timeout) ends the
# listening with the connection as it was
def heard(g: Ws.Out(F.Msg), again: Ws.Conn -> R()) -> R():
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Text{t}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("< " ++ t)
            again(c)
        case F.Binary{b}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("< (" ++ Nat.show(Bytes.len(b)) ++ " bytes)")
            again(c)
        case F.Closed{code, reason}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("the server closed the room: " ++ U32.show(code) ++ " " ++ reason)
            Ws.drop(c)
            return None{}
    case Fail{e}:
      match e:
        case Ws.ETime{}:
          IO.pure(Maybe<&1, Ws.Conn>, Some{c})
        case _:
          lost(c, e)
```

`Ws.close(c, 1000, "bye")` runs the closing handshake and answers the server's
code. The library answers a ping as it comes, and every frame it sends is
masked. A frame the RFC forbids fails the connection with 1002, text that is
not UTF-8 with 1007, and a message past the cap with 1009. `WsNet.of(e)`
(`net/ws_net.bend`) turns a `Ws.Err` into a `NetError`, so a program that
speaks both keeps one error type:

```python
# an error, said as a NetError; the connection let go
def lost(c: Ws.Conn, e: Ws.Err) -> R():
  do IO<Maybe<&1, Ws.Conn>>:
    IO.print_err("chat: " ++ Client.error.show(WsNet.of(e)))
    Ws.drop(c)
    return None{}
```

`Ws.opts.protocols`, `Ws.opts.ca`, `Ws.opts.timeouts(o, connect, recv, close)`
and `Ws.opts.max_msg` change the options. The whole program is
`net/examples/ws_chat.bend`.

### A WebSocket Server

`net/ws_server.bend` adds WebSockets to the server: `WsServer.ws(pat, h)` is a
route like `Server.get`, and it sits in the same list. `h` gets the request
(its path and params, its query, its headers and cookies: authenticate there,
and pick a subprotocol) and answers `WsServer.accept(proto, run)` or
`WsServer.refuse(response)`. `run` gets a `Ws.Conn`, the client's own type:
the same `Ws.recv`, `Ws.recv_for`, `Ws.send_text`, `Ws.send_bytes`, `Ws.ping`
and `Ws.protocol`, the same messages. It hands the connection back when it is
done; one handed back open is closed with 1000, and `Ws.end(c, code, reason)`
closes it with a code of your own first. Serve the routes with
`WsServer.serve.with(~E, ~routes, env, cfg)`, which makes them from `env` for
each request:

```python
def routes(+hub: WsServer.Hub) -> List<&1, Server.Route>:
  [Server.get("/", page), WsServer.ws("/room", r => enter(hub, r))]

def main() -> IO(Unit):
  do IO<Unit>:
    +hub : WsServer.Hub <- WsServer.hub.new()
    xs : List<String> <- IO.args()
    WsServer.serve.with(~WsServer.Hub, ~routes, hub, Server.args(xs, Server.config(8765)))
```

`WsServer.choose(r, ["chat"])` is the first of your subprotocols the client
offered (`""` for none), and the answer never names one it did not offer. A
`Hub` is a room: `WsServer.join(hub)` makes a member with an inbox,
`WsServer.publish(hub, msg)` puts a message in every member's inbox, and
`WsServer.relay(me, c)` sends a member what came for it. A connection waits for
its client in slices (`Ws.recv_for(c, 50)`) and relays between them, so the
room reaches it within 50 ms:

```python
def talk(k: Nat, +hub: WsServer.Hub, +me: WsServer.Member, c: Ws.Conn) -> IO(Ws.Conn):
  match k:
    case 0n:
      IO.pure(Ws.Conn, c)
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Ws.Conn, Ws.recv_for(c, 50), g => heard(hub, me, g, cc => talk(j, hub, me, cc)))

# a client in the room: joined, talked with, and gone
def member(+hub: WsServer.Hub, c: Ws.Conn) -> IO(Ws.Conn):
  do IO<Ws.Conn>:
    +me : WsServer.Member <- WsServer.join(hub)
    c2 : Ws.Conn <- talk(Ws.big(), hub, me, c)
    WsServer.leave(hub, me)
    return c2
```

The server answers the opening handshake as RFC 6455 4.2.2 says: a GET that
asked to upgrade with a good key gets the 101 and the Accept its key earns; a
request that did not ask gets a 426 naming version 13 (a version other than 13
too), and one that asked broken (a key that is not sixteen bytes in base64) a
400. No extension is ever agreed: `permessage-deflate`, offered, is declined by
not naming it. Then every frame the client sends must be masked (1002), a
message is at most `max_msg` (1009), text must be UTF-8 (1007), a ping is
answered as it comes, and the client's close is answered once. A client quiet
for `ping` ms is pinged, and dropped with 1011 when `pong` ms more bring
nothing. On SIGTERM, a `recv` sends 1001 (going away) and hands over the
client's answer as `Closed`. `WsServer.ws.with(o, pat, h)` takes options:
`WsServer.opts()` changed by `opts.max_msg`, `opts.keepalive(o, ping, pong)`,
`opts.timeouts(o, recv, close, send)` and `opts.origins(o, [...])`, the
`Origin` values a browser's request may carry (none named: any; a request with
no `Origin` is not from a browser and passes; any other is a 403 before `h` is
asked). The whole program is `net/examples/chat_server.bend`, and
`net/examples/ws_echo.bend` is the echo the Autobahn suite runs against.

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
| a streamed response's writes | each send within 10 s (`send`) | `ETime`, closed | a client that stops reading cannot hold a producer |
| connections | 1024 | the next waits for a slot | each holds memory and a descriptor |
| SIGTERM | listener closed; idle connections let go within a second | the rest end, or grace (5 s) is up | a deploy does not cut requests in flight |
| client: connect (DNS aside) | 10 s | `Timeout` | a host that does not answer |
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
user or password in it is refused, and so is an IPv6 address. A JSON body is
parsed under the budget you pass, at most 64 containers deep.

## What the Laws Guarantee

`net/LAWS.bend` states them and `net/PROOF.bend` proves them. In plain words:

- `handler_framed`: a handler only sees requests the RFC 9112 spec frames,
  however TCP cut the bytes into reads.
- `respond_framed`: every response the server writes reads back as exactly one
  response, with the handler's status and body, or as the 500.
- `route_first`: the first matching route wins, and a 405's `Allow` lists
  exactly the methods that would have matched, once each.
- `pool_clean`: the client reuses a connection only when its response did not
  close it and nothing came after it.
- `redirect_cap`: a chain allowed k redirects sends at most k + 1 requests.
- `redirect_creds`: credentials never go to an origin other than the first
  request's.
- `stream_body`: the chunks a stream handler reads, joined, are the body RFC
  9112's framing finds, however TCP cut the stream.
- `stream_bounded`: between reads, a streamed body holds at most the last read.
- `stream_next`: after a streamed request the connection goes on only once
  the body has ended, with exactly the bytes after it. A body a handler did not
  read is never read as the next request.
- `pour_chunked`: a response written as it is made, its length unknown, reads
  back as exactly one response, its body the producer's writes joined, and
  nothing after it; `pour_length`: the same with a declared length the writes
  come to.
- `pour_capped`: a declared length is never written past.
- `pour_quiet`: after a failure nothing more is written.
- `pour_bounded`: a write goes out as itself and at most 120 bytes of framing,
  so a connection holds one write, however long the body.
- the vectors: percent-encoding round-trips every byte, and the query, URL,
  Location and route pattern readings match the tables listed there.

`net/ws_laws.bend` states the WebSocket client's and server's, and
`net/ws_proof.bend` proves them: every frame a client sends is masked and every
frame a server sends is not, forbidden frames are refused with their close
code (an unmasked one from a client with 1002), pings are answered, the
handshake is checked as RFC 6455 says on both ends (the server's 101 for every
request that asked well, a 400 or 426 for every other), the messages a server's
handler receives are the spec's reassembly of the input however TCP cut it
into reads, and a close is answered once. To run them:

```bash
bend net/PROOF.bend            # prints: All terms check.
bend net/ws_proof.bend
python3 net/mutants.py         # broken servers and clients; the proof must refuse each
python3 net/ws_mutants.py
python3 net/check.py           # the examples, checked from outside against every default
```

What is not proven: the IO loops themselves (they call the functions the laws
are about), the deadlines and limits, and a stream route's head, which
`net/stream.bend` reads line by line with the engine's spec views.
`net/check.py` checks those from outside.

## Speed

On one thread, with `wrk -t2 -c32`, `hello` answers about 40k requests a
second. The HTTP engine's literal `/health` answers 58k. The difference is the
checked response writer that `respond_framed` is about (`net/README.md`).

## Not Built Yet

- A streamed client response's head before its body: `Client.stream` tells the
  status once the body is through.
- A streamed response on a stream route (an upload's answer) or to a method
  but GET.
- A stream route's request pipelined behind another in one read is read whole,
  under `max_body`. Clients that do not pipeline are not affected.
- A chunked streamed body past 256 MiB. The reader's budget stays under 2^28,
  so a chunk's size never wraps. A Content-Length body can reach 4 GiB.
- WebSocket compression (`permessage-deflate`): offered, it is declined, on
  both ends.
- A deadline on the handler itself. A handler that never answers holds its
  connection.
- HTTP/2 in `net/`. `demos/io_http2` is an HTTP/2 server of its own, not
  behind `Server.serve`.
- IPv6. The server binds an IPv4 address, and the client refuses an IPv6 one.
