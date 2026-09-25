# Networking in Bend

Bend's networking library is `net/`. It is an HTTP/1.1 server, an HTTP/1.1
client, a WebSocket client and server, and JSON bodies. Every timeout and limit
is on from the start, and the promises that matter are proven in
`net/LAWS.bend`. This page is the tour; each part has a page of its own.

Every snippet in these pages is copied from a file in `net/examples/` that
checks and builds. Those files sit in `net/examples/`, so they import the
library as `../http.bend`. From your own file, import it by its path from there.

## Hello, Server!

```python
import Base
import ../http.bend as Http
import ../server.bend as Server

def hello(req: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "Hello, world!\n"))

def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv([])
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
deadlines, so one connection's failure is its own. `Server.argv([])` reads the
command line once and refuses a flag the server does not know, with a usage
line; `Server.args` reads the server's flags from it.

## The Tour

- **Serve**: routes (`Server.get("/notes/:id", h)`, `Server.static`), middleware
  (`Server.logged`, `secured`, `recovered`, and `Server.wrap(~mw, routes)` for a
  whole table, WebSocket routes and files included), a configuration and the
  command line (`Server.argv`, `Server.flag`), shared state, TLS, the handler's
  time. `bend guide net/serving`.
- **Stream**: uploads read a chunk at a time, exports and event streams written
  as they are made. `bend guide net/streams`.
- **Fetch**: `Client.get(url)`, `Client.request(req, opts)`, pooled sessions,
  per-request options (`Client.fetch.with`), `NetError` by kind, redirects,
  IPv6. `bend guide net/client`.
- **JSON**: build and answer values, parse bodies under a budget, and read
  fields typed (`Json.get.u32(j, "limits.max")`), every reason at once for a
  400. `bend guide net/json`.
- **WebSockets**: `Ws.connect` for a client, `WsServer.ws(pat, h)` for a route,
  a `Hub` for a room, `WsServer.broadcast` for a feed. `bend guide net/websockets`.
- **Defaults**: every one a bound (idle 5 s, a head 10 s and 16 KiB, a body
  1 MiB, a handler 30 s, 1024 connections; the client's connect 10 s, exchange
  30 s, body 10 MiB, 10 redirects). `bend guide net/limits`.
- **Laws**: a handler sees only what RFC 9112 frames, every response reads back
  as one, the first route wins, the pool keeps only clean connections, redirects
  are capped and keep credentials to their origin, streamed bodies are the RFC's
  both ways, a late handler's 503 is all that is written, and the WebSocket
  handshake and frames are RFC 6455's. `bend guide net/limits`.
