# The wire bench, Bytes side: an HTTP-shaped server that reads a
# connection's bytes, cuts every whole head at CRLF CRLF, builds a reply
# for each out of pieces and sends the replies of one read in one send.
# list.bend is the same server over List<&2, U32>, one cell per byte;
# README.md has how to drive both with load.c and what they measured.
#
#   bend demos/io_wire_bench/buf.bend -o wbuf && ./wbuf --threads 1
import Base

def port() -> U32:
  18710

def body() -> Bytes():
  "{\"ok\":true}"

def missing() -> Bytes():
  "no route\n"

def reply.of(status: Bytes(), ctype: Bytes(), +b: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: ", ctype,
    "\r\ncontent-length: ", Nat.show(Bytes.len(b)),
    "\r\nconnection: keep-alive\r\n\r\n", b])

def reply(hit: Bool) -> Bytes():
  match hit:
    case True{}:
      reply.of("200 OK", "application/json", body())
    case False{}:
      reply.of("404 Not Found", "text/plain", missing())

# every whole head in buf answered (m is where the first one ends): the
# unread rest, the replies in order, and how many
def answer(fuel: Nat, +buf: Bytes(), out: Bytes(), n: Nat, m: Maybe<&2, Nat>)
  -> Bytes() & Bytes() & Nat:
  match fuel:
    case 0n:
      (buf, (out, n))
    case 1n+f:
      match m:
        case None{}:
          (buf, (out, n))
        case Some{+i}:
          +rest = Bytes.drop(buf, Nat.add(i, 4n))
          hit = Bytes.starts_with(Bytes.slice(buf, 0n, i), "GET /health ")
          answer(f, rest, Bytes.append(out, reply(hit)), 1n+n,
            Bytes.find(rest, "\r\n\r\n"))

# What a connection does next: read more after the unread rest, or stop.
type Step is Data:
  Go{left: Bytes()}
  Stop{}

def sent(rest: Bytes(), m: Socket & Result<&1, &1, U32 & String, Unit>) ->
  IO(Socket & Step):
  (s, r) = m
  match r:
    case Fail{e}:
      IO.pure(Socket & Step, (s, Stop{}))
    case Done{u}:
      IO.pure(Socket & Step, (s, Go{rest}))

def reply.all(s: Socket, a: Bytes() & Bytes() & Nat) -> IO(Socket & Step):
  (rest, (out, n)) = a
  IO.bind(Socket & Result<&1, &1, U32 & String, Unit>, Socket & Step,
    TCP.send_buf(s, out), sent(rest))

def data(s: Socket, left: Bytes(), +b: Bytes(), eof: Bool) -> IO(Socket & Step):
  match eof:
    case True{}:
      IO.pure(Socket & Step, (s, Stop{}))
    case False{}:
      +buf = Bytes.append(left, b)
      reply.all(s, answer(64n, buf, "", 0n, Bytes.find(buf, "\r\n\r\n")))

def got(left: Bytes(), m: Socket & Result<&1, &1, U32 & String, Bytes()>) ->
  IO(Socket & Step):
  (s, r) = m
  match r:
    case Fail{e}:
      IO.pure(Socket & Step, (s, Stop{}))
    case Done{+b}:
      data(s, left, b, String.is_empty(b))

# one connection: fuel reads at most
def serve(fuel: Nat, sp: Socket & Step) -> IO(Unit):
  match fuel:
    case 0n:
      (s, st) = sp
      Socket.close(s)
    case 1n+f:
      (s, st) = sp
      match st:
        case Stop{}:
          Socket.close(s)
        case Go{left}:
          do IO<Unit>:
            m : Socket & Result<&1, &1, U32 & String, Bytes()> <-
              TCP.recv_buf(s, 65536)
            sp2 : Socket & Step <- got(left, m)
            serve(f, sp2)

def accept.one(p: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Listener):
  (l, r) = p
  match r:
    case Fail{e}:
      IO.pure(Listener, l)
    case Done{s}:
      IO.bind(Unit, Listener, IO.spawn(Unit, serve(1000000000n, (s, Go{""}))),
        u => IO.pure(Listener, l))

def accept(fuel: Nat, l: Listener) -> IO(U32):
  match fuel:
    case 0n:
      IO.bind(Unit, U32, Listener.close(l), u => IO.pure(U32, 0))
    case 1n+f:
      do IO<U32>:
        p  : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        l2 : Listener <- accept.one(p)
        accept(f, l2)

def main() -> IO(U32):
  do IO<U32>:
    l : Listener <- IO.try(Listener, TCP.listen(port()))
    accept(1000000n, l)
