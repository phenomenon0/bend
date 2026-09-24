# Exports of any size, in bounded memory: response bodies written as
# they are made.
#
#   bend net/examples/export.bend -o export && ./export --port 8080
#   curl 'http://127.0.0.1:8080/export.csv?rows=1000000' > rows.csv
#   curl -s 'http://127.0.0.1:8080/bytes?n=1000000000' | wc -c
#
# GET /export.csv?rows=N and /export.ndjson?rows=N write N rows, a
# thousand rows a write, chunked (the length is not known ahead); GET
# /bytes?n=N writes N bytes of a pattern, 16 KiB a write; GET
# /sized?n=N&give=M declares N bytes and writes M of them, ten a write
# (fewer and the connection closes after them; more and the write past
# N is refused, nothing of it sent). A producer that stops -- the
# client left, a send stalled -- says why on stderr. GET / is an
# ordinary handler, beside them.
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../stream.bend as Stream

# a number from the query, or d
def arg.of(m: Maybe<&2, Bytes()>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      Maybe.default(&2, Nat, Maybe.map(&2, U32, Nat, U32.to_nat, U32.read(v)), d)

def arg(r: Http.Request, +k: Bytes(), +d: Nat) -> Nat:
  arg.of(Http.query.get(r, k), d)

def csv.row(+i: Nat) -> Bytes():
  Bytes.concat([Nat.show(i), ",user", Nat.show(i), ",", Nat.show(Nat.add(i, i)), "\n"])

def json.row(+i: Nat) -> Bytes():
  Bytes.concat(["{\"id\":", Nat.show(i), ",\"name\":\"user", Nat.show(i), "\",\"score\":", Nat.show(Nat.add(i, i)), "}\n"])

def row(json: Bool, +i: Nat) -> Bytes():
  match json:
    case True{}:
      json.row(i)
    case False{}:
      csv.row(i)

# k rows from i, one block
def block(k: Nat, +json: Bool, +i: Nat, acc: Bytes()) -> Bytes():
  match k:
    case 0n:
      acc
    case 1n+j:
      block(j, json, 1n+i, Bytes.append(acc, row(json, i)))

def said(e: Stream.Err) -> Bool:
  match e:
    case Stream.ENone{}:
      False{}
    case _:
      True{}

def say(yes: Bool, +line: Bytes()) -> IO(Unit):
  match yes:
    case True{}:
      IO.print_err(line)
    case False{}:
      IO.pure(Unit, Unit{})

# a producer that could not go on says why (a HEAD, which has no body,
# not), and hands the Sink back
def stopped(+what: Bytes(), +n: Nat, +e: Stream.Err, k: Stream.Sink) -> IO(Stream.Sink):
  do IO<Stream.Sink>:
    say(said(e), Bytes.concat(["export: ", what, " stopped after ", Nat.show(n), ": ", Stream.err.show(e)]))
    return k

def wrote(+what: Bytes(), +n: Nat, w: Stream.Wrote(), go: Stream.Sink -> IO(Stream.Sink)) -> IO(Stream.Sink):
  (k, r) = w
  match r:
    case Done{u}:
      go(k)
    case Fail{e}:
      stopped(what, n, e, k)

def rows.at(done: Bool, +json: Bool, +i: Nat, +left: Nat, k: Stream.Sink, go: Nat -> Nat -> Stream.Sink -> IO(Stream.Sink)) ->
  IO(Stream.Sink):
  match done:
    case True{}:
      IO.pure(Stream.Sink, k)
    case False{}:
      +m = Nat.min(left, 1000n)
      IO.bind(Stream.Wrote(), Stream.Sink, Stream.write(k, block(m, json, i, "")),
        w => wrote("rows", i, w, k2 => go(Nat.add(i, m), Nat.sub(left, m), k2)))

# the rows from i, left of them, a block a write
def rows(f: Nat, +json: Bool, +i: Nat, +left: Nat, k: Stream.Sink) -> IO(Stream.Sink):
  match f:
    case 0n:
      IO.pure(Stream.Sink, k)
    case 1n+g:
      rows.at(Nat.is_eq(left, 0n), json, i, left, k, i2 => l2 => k2 => rows(g, json, i2, l2, k2))

# GET /export.csv, /export.ndjson
def export(+json: Bool, r: Http.Request) -> IO(Stream.Reply):
  +n = arg(r, "rows", 100n)
  IO.pure(Stream.Reply, Stream.pour(200,
    [Http.Header{"content-type", Bool.pick(Bytes(), json, "application/x-ndjson", "text/csv")}],
    k => rows(n, json, 0n, n, k)))

# a 16 KiB block of a pattern (check.py hashes the same)
def pattern.go(k: Nat, +i: U32, acc: Bytes()) -> Bytes():
  match k:
    case 0n:
      acc
    case 1n+j:
      pattern.go(j, (i + 1 : U32), Bytes.push(acc, ((i * 7 + 3) % 256 : U32)))

def pattern() -> Bytes():
  pattern.go(16384n, 0, "")

def bytes.at(done: Bool, +blk: Bytes(), +sent: Nat, +left: Nat, k: Stream.Sink,
  go: Nat -> Nat -> Stream.Sink -> IO(Stream.Sink)) -> IO(Stream.Sink):
  match done:
    case True{}:
      IO.pure(Stream.Sink, k)
    case False{}:
      +m = Nat.min(left, 16384n)
      IO.bind(Stream.Wrote(), Stream.Sink, Stream.write(k, String.take(blk, m)),
        w => wrote("bytes", sent, w, k2 => go(Nat.add(sent, m), Nat.sub(left, m), k2)))

def bytes.go(f: Nat, +blk: Bytes(), +sent: Nat, +left: Nat, k: Stream.Sink) -> IO(Stream.Sink):
  match f:
    case 0n:
      IO.pure(Stream.Sink, k)
    case 1n+g:
      bytes.at(Nat.is_eq(left, 0n), blk, sent, left, k, s2 => l2 => k2 => bytes.go(g, blk, s2, l2, k2))

# GET /bytes?n=N
def bytes(r: Http.Request) -> IO(Stream.Reply):
  +n = arg(r, "n", 1048576n)
  IO.pure(Stream.Reply, Stream.pour(200, [Http.Header{"content-type", "application/octet-stream"}],
    k => bytes.go(n, pattern(), 0n, n, k)))

def tens.at(done: Bool, +sent: Nat, +left: Nat, k: Stream.Sink, go: Nat -> Nat -> Stream.Sink -> IO(Stream.Sink)) ->
  IO(Stream.Sink):
  match done:
    case True{}:
      IO.pure(Stream.Sink, k)
    case False{}:
      +m = Nat.min(left, 10n)
      IO.bind(Stream.Wrote(), Stream.Sink, Stream.write(k, String.take("0123456789", m)),
        w => wrote("sized", sent, w, k2 => go(Nat.add(sent, m), Nat.sub(left, m), k2)))

def tens(f: Nat, +sent: Nat, +left: Nat, k: Stream.Sink) -> IO(Stream.Sink):
  match f:
    case 0n:
      IO.pure(Stream.Sink, k)
    case 1n+g:
      tens.at(Nat.is_eq(left, 0n), sent, left, k, s2 => l2 => k2 => tens(g, s2, l2, k2))

# GET /sized?n=N&give=M: N bytes declared, M written
def sized.go(+r: Http.Request) -> IO(Stream.Reply):
  +n = arg(r, "n", 100n)
  +give = arg(r, "give", n)
  IO.pure(Stream.Reply, Stream.pour.len(200, [Http.Header{"content-type", "text/plain"}], n, k => tens(give, 0n, give, k)))

def sized(r: Http.Request) -> IO(Stream.Reply):
  sized.go(r)

def index(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "GET /export.csv?rows=N, /export.ndjson?rows=N, /bytes?n=N, /sized?n=N&give=M\n"))

def routes(+u: Unit) -> List<Server.Route>:
  [Server.get("/", index),
   Stream.get("/export.csv", r => export(False{}, r)),
   Stream.get("/export.ndjson", r => export(True{}, r)),
   Stream.get("/bytes", bytes),
   Stream.get("/sized", sized)]

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    Server.serve.routes(~Unit, ~routes, Unit{}, Server.args(xs, Server.config(8080)))
