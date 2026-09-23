# io (io_tcp_listen_backlog): a listener queues the connections it has
# not accepted yet up to the kernel's limit, not sixteen. 32 connects
# complete before any accept; under listen(fd, 16) the 18th found the
# queue full, its SYN was dropped, and it waited out retransmits that
# never succeed, so the run timed out.
import Base

law hold:
  for n: Nat
  for +port: U32
  IO(U32)

def hold(n, port):
  match n:
    case 0n:
      IO.pure(U32, 0)
    case 1n+k:
      do IO<U32>:
        c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
        m : U32 <- hold(k, port)
        x : Unit <- Socket.close(c)
        return (m + 1 : U32)

law main_go:
  for b: Listener & U32
  IO(U32)

def main_go(b):
  (l, port) = b
  do IO<U32>:
    n : U32 <- hold(32n, port)
    w : Unit <- IO.print(U32.show(n))
    z : Unit <- Listener.close(l)
    return 0

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
    b : Listener & U32 <- tcp_listen_any(32n, 21232)
    main_go(b)

#|32
