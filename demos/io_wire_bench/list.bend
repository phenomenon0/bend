# The wire bench, list side: buf.bend's server over List<&2, U32>, one
# cell per byte, through TCP.recv_bytes and TCP.send_bytes, written the
# way the engine writes it (a head cut by one walk, a reply out of
# ASCII pieces turned to bytes, the replies of one read in one send).
#
#   bend demos/io_wire_bench/list.bend -o wlist && ./wlist --threads 1
import Base

def port() -> U32:
  18711

def cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def rev(a: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, a)

def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, bytes(t)}

def bpre(a: List<&2, U32>, p: List<&2, U32>) -> Bool:
  match a p:
    case _ Nil{}:
      True{}
    case Nil{} Con{y, u}:
      False{}
    case Con{x, t} Con{y, u}:
      U32.is_eq(x, y) && bpre(t, u)

def body() -> List<&2, U32>:
  bytes("{\"ok\":true}")

def missing() -> List<&2, U32>:
  bytes("no route\n")

def reply.of(status: String, ctype: String, +b: List<&2, U32>) -> List<&2, U32>:
  cat(bytes("HTTP/1.1 "), cat(bytes(status),
  cat(bytes("\r\ncontent-type: "), cat(bytes(ctype),
  cat(bytes("\r\ncontent-length: "),
  cat(bytes(Nat.show(List.length(&2, U32, b))),
  cat(bytes("\r\nconnection: keep-alive\r\n\r\n"), b)))))))

def reply(hit: Bool) -> List<&2, U32>:
  match hit:
    case True{}:
      reply.of("200 OK", "application/json", body())
    case False{}:
      reply.of("404 Not Found", "text/plain", missing())

# The next CR LF CR LF state after c: k counts how much of it is seen.
def crlf(+k: U32, +c: U32) -> U32:
  +cr = U32.is_eq(c, 13)
  +odd = U32.is_eq(U32.and(k, 1), 1)
  up = cr && Bool.not(odd) || U32.is_eq(c, 10) && odd
  Bool.pick(U32, up, (k + 1 : U32), Bool.pick(U32, cr, 1, 0))

# One walk to the end of a head: Some{(head reversed, rest)}, or None
# when no head ends in xs (the caller keeps xs).
def cut(xs: List<&2, U32>, done: Bool, acc: List<&2, U32>, k: U32) ->
  Maybe<&1, List<&2, U32> & List<&2, U32>>:
  match xs:
    case Nil{}:
      match done:
        case True{}:
          Some{(acc, Nil{})}
        case False{}:
          None{}
    case Con{+c, t}:
      match done:
        case True{}:
          Some{(acc, Con{c, t})}
        case False{}:
          +k2 = crlf(k, c)
          cut(t, U32.is_eq(k2, 4), Con{c, acc}, k2)

def answer(fuel: Nat, +buf: List<&2, U32>, out: List<&2, List<&2, U32>>,
  m: Maybe<&1, List<&2, U32> & List<&2, U32>>)
  -> List<&2, U32> & List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      (buf, out)
    case 1n+f:
      match m:
        case None{}:
          (buf, out)
        case Some{(hd, +rest)}:
          hit = bpre(rev(hd), bytes("GET /health "))
          answer(f, rest, Con{reply(hit), out}, cut(rest, False{}, Nil{}, 0))

type Step is Data:
  Go{left: List<&2, U32>}
  Stop{}

def sent(rest: List<&2, U32>, m: Socket & Result<&1, &1, U32 & String, Unit>) ->
  IO(Socket & Step):
  (s, r) = m
  match r:
    case Fail{e}:
      IO.pure(Socket & Step, (s, Stop{}))
    case Done{u}:
      IO.pure(Socket & Step, (s, Go{rest}))

def reply.all(s: Socket, a: List<&2, U32> & List<&2, List<&2, U32>>) ->
  IO(Socket & Step):
  (rest, outs) = a
  out = List.concat(&2, U32, List.reverse(&2, List<&2, U32>, outs))
  IO.bind(Socket & Result<&1, &1, U32 & String, Unit>, Socket & Step,
    TCP.send_bytes(s, out), sent(rest))

def data(s: Socket, left: List<&2, U32>, b: List<&2, U32>) -> IO(Socket & Step):
  match b:
    case Nil{}:
      IO.pure(Socket & Step, (s, Stop{}))
    case Con{h, t}:
      +buf = cat(left, Con{h, t})
      reply.all(s, answer(64n, buf, Nil{}, cut(buf, False{}, Nil{}, 0)))

def got(left: List<&2, U32>, m: Socket & Result<&1, &1, U32 & String, List<&2, U32>>) ->
  IO(Socket & Step):
  (s, r) = m
  match r:
    case Fail{e}:
      IO.pure(Socket & Step, (s, Stop{}))
    case Done{b}:
      data(s, left, b)

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
            m : Socket & Result<&1, &1, U32 & String, List<&2, U32>> <-
              TCP.recv_bytes(s, 65536)
            sp2 : Socket & Step <- got(left, m)
            serve(f, sp2)

def accept.one(p: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Listener):
  (l, r) = p
  match r:
    case Fail{e}:
      IO.pure(Listener, l)
    case Done{s}:
      IO.bind(Unit, Listener, IO.spawn(Unit, serve(1000000000n, (s, Go{Nil{}}))),
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
