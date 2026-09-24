# io (io_tcp_send_buf_poll): TCP.send_buf_poll is TCP.send_buf with a
# deadline. To a peer that reads, 256 bytes go out and arrive.
# To a peer that never reads, 64 KiB sends go out until the sockets are
# full, and then the send that cannot move fails with ETIMEDOUT once
# 200 ms pass without progress, rather than parking for good; IO.now on
# both sides of that send shows it waited. The socket threads back
# OUTSIDE the Result each time.
import Base

def ramp(k: Nat, +n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+j:
      ramp(j, (n - 1 : U32), Con{(n - 1 : U32), acc})

# 64 bytes doubled k times
def fill(k: Nat, +b: Bytes()) -> Bytes():
  match k:
    case 0n:
      b
    case 1n+j:
      fill(j, Bytes.append(b, b))

def timed.go(ok: Bool, code: U32) -> String:
  match ok:
    case True{}:
      "timed out"
    case False{}:
      String.append("failed ", U32.show(code))

def timed(+code: U32) -> String:
  timed.go(U32.is_eq(code, 110) || U32.is_eq(code, 60), code)

def waited(ok: Bool) -> String:
  match ok:
    case True{}:
      "waited"
    case False{}:
      "early"

def flood.fail(t0: Nat, s: Socket, e: U32 & String) -> IO(Unit):
  (code, msg) = e
  do IO<Unit>:
    t1 : Nat <- IO.now()
    IO.print(timed(code))
    IO.print(waited(Nat.is_ge(Nat.sub(t1, t0), 150n)))
    Socket.close(s)

def flood.got(rest: Socket -> IO(Unit), t0: Nat, m: Socket & Result<&1, &1, (U32 & String), Unit>) -> IO(Unit):
  (s, r) = m
  match r:
    case Done{u}:
      rest(s)
    case Fail{e}:
      flood.fail(t0, s, e)

def flood(k: Nat, s: Socket) -> IO(Unit):
  match k:
    case 0n:
      do IO<Unit>:
        IO.print("never full")
        Socket.close(s)
    case 1n+j:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        m  : Socket & Result<&1, &1, (U32 & String), Unit> <-
          TCP.send_buf_poll(s, fill(10n, "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"), 200)
        flood.got(s2 => flood(j, s2), t0, m)

def sent(m: Socket & Result<&1, &1, (U32 & String), Unit>) -> IO(Socket):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

def got(m: Socket & Result<&1, &1, (U32 & String), List<&2, U32>>) -> IO(Socket):
  (s, r) = m
  do IO<Socket>:
    bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
    IO.print(Nat.show(List.length(&2, U32, bs)))
    return s

def step_accept(c: Socket, p: Listener & Result<&1, &1, (U32 & String), Socket>) -> IO(U32):
  (l2, ar) = p
  do IO<U32>:
    a  : Socket <- IO.pass(Socket, ar)
    sm : Socket & Result<&1, &1, (U32 & String), Unit> <-
      TCP.send_buf_poll(a, Bytes.from_list(ramp(256n, 256, Nil{})), 1000)
    a2 : Socket <- sent(sm)
    rm : Socket & Result<&1, &1, (U32 & String), List<&2, U32>> <- TCP.recv_bytes(c, 512)
    c2 : Socket <- got(rm)
    Unit <- flood(1024n, a2)
    Socket.close(c2)
    Listener.close(l2)
    return 0

def main_go(b: Listener & U32) -> IO(U32):
  (l, port) = b
  do IO<U32>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    p : Listener & Result<&1, &1, (U32 & String), Socket> <- TCP.accept(l)
    step_accept(c, p)

def tcp_retry(port: U32, r: Result<&1, &1, (U32 & String), Listener>, rest: IO(Listener & U32)) -> IO(Listener & U32):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

def tcp_listen_any(tries: Nat, +port: U32) -> IO(Listener & U32):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      rest = tcp_listen_any(t, (port + 1 : U32))
      do IO<Listener & U32>:
        r : Result<&1, &1, (U32 & String), Listener> <- TCP.listen(port)
        tcp_retry(port, r, rest)

def main() -> IO(U32):
  do IO<U32>:
    b : Listener & U32 <- tcp_listen_any(32n, 19911)
    main_go(b)

#|256
#|timed out
#|waited
