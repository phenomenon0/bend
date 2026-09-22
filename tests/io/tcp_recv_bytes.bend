# io (io_tcp_recv_bytes): TCP.send_bytes and TCP.recv_bytes carry bytes
# as they are, one List cell each. All 256 byte values go out on one
# socket and come back on the other with the same count and the same
# sum; through TCP.send and TCP.recv, which carry a String, the bytes
# that are not UTF-8 would come back as U+FFFD, longer and different.
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

# the count and the sum, from one walk each over a reusable list
def report(+bs: List<&2, U32>) -> String:
  String.append(Nat.show(List.length(&2, U32, bs)),
    String.append("\n", U32.show(total(bs, 0))))

law finish:
  for l: Listener
  for c: Socket
  for m: Socket & Result<&1, &1, (U32 & String), List<&2, U32>>
  IO(U32)

def finish(l, c, m):
  (a, r) = m
  do IO<U32>:
    got : List<&2, U32> <- IO.pass(List<&2, U32>, r)
    w   : Unit <- IO.print(report(got))
    x   : Unit <- Socket.close(a)
    y   : Unit <- Socket.close(c)
    z   : Unit <- Listener.close(l)
    return 0

law send_go:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Socket)

def send_go(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

law step_accept:
  for c: Socket
  for p: Listener & Result<&1, &1, (U32 & String), Socket>
  IO(U32)

def step_accept(c, p):
  (l, ar) = p
  do IO<U32>:
    a  : Socket <- IO.pass(Socket, ar)
    sm : Socket & Result<&1, &1, (U32 & String), Unit> <- TCP.send_bytes(c, ramp(256n, 256, Nil{}))
    c2 : Socket <- send_go(sm)
    m  : Socket & Result<&1, &1, (U32 & String), List<&2, U32>> <- TCP.recv_bytes(a, 512)
    finish(l, c2, m)

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
    b : Listener & U32 <- tcp_listen_any(32n, 19671)
    main_go(b)

#|256
#|32640
