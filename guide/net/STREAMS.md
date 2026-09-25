# Streams

`net/stream.bend`: a request body too large to hold, read as it comes, and a
response body written as it is made. The tour is `bend guide networking`.

## Uploads

A body too large to hold is read as a stream, on a stream route.
`Stream.serve.with(~E, ~app, ~uploads, env, cfg)` serves `app` as
`Server.serve.with` does, and a table of stream routes beside it. A stream
route's handler gets the request's head and its body as a `Stream.Body`, and
hands the body back beside its response:

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

The head is read by the reader every request goes through, which stops at the
blank line of a head a stream route takes, wherever it comes on the connection:
first, or pipelined behind other requests in one read. The server's
`max_body` is not a stream's: `Stream.config(cfg)` wraps a server
configuration, and `Stream.set.max_stream` (1 GiB) caps a streamed body: a
longer Content-Length is a 413 before a byte is read, and a chunked body is
cut there (a chunked body is at most 256 MiB). `Stream.set.progress` (10 s) is
the time each read has to bring a byte, or 408. The command line goes through
`Stream.argv` and `Stream.args`, which know `--max-stream` and `--progress-ms`
beside the server's flags:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Stream.argv(["--dir DIR"])
    +dir : Bytes() = Server.flag(xs, "--dir", "uploads")
    Stream.serve.with(~Bytes(), ~app, ~uploads, dir, Stream.args(xs, Stream.config(Server.config(8080))))
```

An `Expect: 100-continue` is answered at the handler's first read, so a handler
that refuses without reading never asks for the body. When the handler returns,
the server drains up to 1 MiB of what is left and the connection goes on. Past
that, it answers and closes. A body that failed (malformed, too large, too
slow) is answered by the server itself, whatever the handler said. The whole
program is `net/examples/upload.bend`.

## Exports and Event Streams

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
end to end (`net/examples/relay_stream.bend`; `Stream.abort(k)` cuts the
response short when the upstream fails).
