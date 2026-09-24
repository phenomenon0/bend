# io (io_tcp_buf): TCP.send_buf, TCP.recv_buf and TCP.poll_buf carry a
# Bytes, one packed block, where the byte pair carries a List cell per
# byte. All 256 byte values and a CRLF CRLF go out in one send and come
# back with the same count, the same sum and the head's end found where
# it was put; a poll with nothing waiting answers None at once, one
# after a send answers the bytes; and a Char past 255 is refused with
# EINVAL rather than encoded.
import Base

# the byte values below n, ascending; k is n as the fuel
def ramp(k: Nat, +n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+j:
      ramp(j, (n - 1 : U32), Con{(n - 1 : U32), acc})

def total(bs: List<&2, U32>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case Con{c, t}:
      total(t, (acc + c : U32))

def at(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "absent"
    case Some{n}:
      Nat.show(n)

def report(+b: Bytes()) -> String:
  Nat.show(Bytes.len(b)) ++ " " ++ U32.show(total(Bytes.to_list(b), 0))
    ++ " " ++ at(Bytes.find(b, "\r\n\r\n")) ++ " "
    ++ U32.show(Bytes.get(b, 255n)) ++ " " ++ Bytes.drop(b, 260n)

def polled(m: Maybe<&1, Bytes()>) -> String:
  match m:
    case None{}:
      "none"
    case Some{b}:
      "some " ++ b

def refused(r: Result<&1, &1, U32 & String, Unit>) -> String:
  match r:
    case Done{u}:
      "sent"
    case Fail{(code, msg)}:
      "refused " ++ U32.show(code)

law sent:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Socket)

def sent(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

law got:
  for m: Socket & Result<&1, &1, (U32 & String), Bytes()>
  IO(Socket)

def got(m):
  (s, r) = m
  do IO<Socket>:
    b : Bytes() <- IO.pass(Bytes(), r)
    p : Unit <- IO.print(report(b))
    return s

law poll:
  for m: Socket & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>
  IO(Socket)

def poll(m):
  (s, r) = m
  do IO<Socket>:
    b : Maybe<&1, Bytes()> <- IO.pass(Maybe<&1, Bytes()>, r)
    p : Unit <- IO.print(polled(b))
    return s

law bad:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Socket)

def bad(m):
  (s, r) = m
  do IO<Socket>:
    p : Unit <- IO.print(refused(r))
    return s

law talk:
  for c: Socket
  for a: Socket
  IO(Socket & Socket)

def talk(c, a):
  wire = Bytes.append(Bytes.from_list(ramp(256n, 256, Nil{})), "\r\n\r\ntail")
  do IO<Socket & Socket>:
    a1 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>,
      Socket, TCP.poll_buf(a, 64, 0), poll)
    c1 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Unit>, Socket,
      TCP.send_buf(c, wire), sent)
    a2 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Bytes()>, Socket,
      TCP.recv_buf(a1, 1024), got)
    c2 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Unit>, Socket,
      TCP.send_buf(c1, "€"), bad)
    c3 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Unit>, Socket,
      TCP.send_buf(c2, "ok"), sent)
    a3 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>,
      Socket, TCP.poll_buf(a2, 64, 1000), poll)
    return (c3, a3)

law finish:
  for l: Listener
  for p: Socket & Socket
  IO(U32)

def finish(l, p):
  (c, a) = p
  do IO<U32>:
    x : Unit <- Socket.close(a)
    y : Unit <- Socket.close(c)
    z : Unit <- Listener.close(l)
    return 0

law step_accept:
  for c: Socket
  for p: Listener & Result<&1, &1, (U32 & String), Socket>
  IO(U32)

def step_accept(c, p):
  (l, ar) = p
  do IO<U32>:
    a  : Socket <- IO.pass(Socket, ar)
    ca : Socket & Socket <- talk(c, a)
    finish(l, ca)

law main_go:
  for b: Listener & U32
  IO(U32)

def main_go(b):
  (l, port) = b
  do IO<U32>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    p : Listener & Result<&1, &1, (U32 & String), Socket> <- TCP.accept(l)
    step_accept(c, p)

law tcp_retry:
  for port : U32
  for r    : Result<&1, &1, (U32 & String), Listener>
  for rest : IO(Listener & U32)
  IO(Listener & U32)

def tcp_retry(port, r, rest):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

law tcp_listen_any:
  for tries : Nat
  for +port : U32
  IO(Listener & U32)

def tcp_listen_any(tries, port):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      rest = tcp_listen_any(t, (port + 1 : U32))
      do IO<Listener & U32>:
        r : Result<&1, &1, (U32 & String), Listener> <- TCP.listen(port)
        tcp_retry(port, r, rest)

law main:
  IO(U32)

def main():
  do IO<U32>:
    b : Listener & U32 <- tcp_listen_any(32n, 18700)
    main_go(b)

#|none
#|264 33112 256 255 tail
#|refused 22
#|some ok
