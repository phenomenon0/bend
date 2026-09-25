# Uploads of any size, in bounded memory: a body taken as a stream.
#
#   bend net/examples/upload.bend -o upload && ./upload --port 8080 --dir /tmp
#   curl -T big.iso http://127.0.0.1:8080/upload/big.iso
#   curl --data-binary @notes.txt http://127.0.0.1:8080/count
#
# PUT or POST /upload/NAME writes the body to DIR/NAME, a read at a
# time; POST /count counts a body's bytes and lines as it comes; POST
# /refuse answers 403 without reading the body (the server drains it,
# or closes); GET / is an ordinary handler, its body whole. --max-stream
# and --progress-ms bound the bodies, and every server flag works.
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../stream.bend as Stream

# GET /, and anything else not streamed (dir is the environment both
# tables are given)
def app(+dir: Bytes(), r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "PUT /upload/NAME, POST /count\n"))

# a file name as it may be: letters, digits, '.', '-', '_', not
# starting with '.'
def name.char(+c: U32) -> Bool:
  (U32.is_le(97, c) && U32.is_le(c, 122)) || (U32.is_le(65, c) && U32.is_le(c, 90)) ||
    (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 46) || U32.is_eq(c, 45) || U32.is_eq(c, 95)

def name.all(b: Bytes()) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      name.char(c) && name.all(t)

def name.ok(+n: Bytes()) -> Bool:
  Bool.not(String.is_empty(n)) && Bool.not(U32.is_eq(Bytes.get(n, 0n), 46)) && name.all(n)

# the file written: 201 with its size, or why the body stopped
def saved(+name: Bytes(), g: Stream.Out(Nat)) -> IO(Stream.Body & Http.Response):
  (b, r) = g
  match r:
    case Done{n}:
      IO.pure(Stream.Body & Http.Response, (b, Http.text(201, Bytes.concat(["saved ", name, ": ", Nat.show(n), " bytes\n"]))))
    case Fail{e}:
      IO.pure(Stream.Body & Http.Response, (b, Http.text(400, Bytes.append(Stream.err.show(e), "\n"))))

def upload.at(+dir: Bytes(), +name: Bytes(), ok: Bool, b: Stream.Body) -> IO(Stream.Body & Http.Response):
  match ok:
    case True{}:
      IO.bind(Stream.Out(Nat), Stream.Body & Http.Response, Stream.to_file(b, Bytes.concat([dir, "/", name])),
        g => saved(name, g))
    case False{}:
      IO.pure(Stream.Body & Http.Response, (b, Http.text(400, "a name of letters, digits, '.', '-' and '_'\n")))

# PUT or POST /upload/:name: the body to a file, never held whole
def upload(+dir: Bytes(), r: Http.Request, b: Stream.Body) -> IO(Stream.Body & Http.Response):
  +name = Http.param(r, "name")
  upload.at(dir, name, name.ok(name), b)

# the bytes and the lines of a body, a chunk at a time
def lines(b: Bytes()) -> Nat:
  match b:
    case SNil{}:
      0n
    case SCon{Chr{+c}, t}:
      Nat.add(Bool.pick(Nat, U32.is_eq(c, 10), 1n, 0n), lines(t))

def counted(+n: Nat, +ls: Nat, g: Stream.Out(Maybe<&2, Bytes()>), again: Stream.Body -> Nat -> Nat -> IO(Stream.Body & Http.Response)) ->
  IO(Stream.Body & Http.Response):
  (b, r) = g
  match r:
    case Done{m}:
      match m:
        case Some{+x}:
          again(b, Nat.add(n, Bytes.len(x)), Nat.add(ls, lines(x)))
        case None{}:
          IO.pure(Stream.Body & Http.Response,
            (b, Http.text(200, Bytes.concat([Nat.show(n), " bytes, ", Nat.show(ls), " lines\n"]))))
    case Fail{e}:
      IO.pure(Stream.Body & Http.Response, (b, Http.text(400, Bytes.append(Stream.err.show(e), "\n"))))

def count.go(k: Nat, b: Stream.Body, +n: Nat, +ls: Nat) -> IO(Stream.Body & Http.Response):
  match k:
    case 0n:
      IO.pure(Stream.Body & Http.Response, (b, Http.plain(413)))
    case 1n+j:
      IO.bind(Stream.Out(Maybe<&2, Bytes()>), Stream.Body & Http.Response, Stream.read(b),
        g => counted(n, ls, g, b2 => n2 => l2 => count.go(j, b2, n2, l2)))

# POST /count: read a chunk at a time until the end
def count(r: Http.Request, b: Stream.Body) -> IO(Stream.Body & Http.Response):
  count.go(Stream.fuel(), b, 0n, 0n)

# POST /refuse: answered without a byte of the body read
def refuse(r: Http.Request, b: Stream.Body) -> IO(Stream.Body & Http.Response):
  IO.pure(Stream.Body & Http.Response, (b, Http.text(403, "no uploads here\n")))

def uploads(+dir: Bytes()) -> List<Stream.Route>:
  [Stream.on(["PUT", "POST"], "/upload/:name", r => b => upload(dir, r, b)),
   Stream.post("/count", count),
   Stream.post("/refuse", refuse)]

def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Stream.argv(["--dir DIR"])
    +dir : Bytes() = Server.flag(xs, "--dir", "uploads")
    Stream.serve.with(~Bytes(), ~app, ~uploads, dir, Stream.args(xs, Stream.config(Server.config(8080))))
