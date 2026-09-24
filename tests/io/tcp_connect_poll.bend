# io (io_tcp_connect_poll): TCP.connect with a deadline. A listener
# accepts (Done), a closed port refuses (ECONNREFUSED: 111 on Linux, 61
# on macOS), a malformed address is EINVAL at once, and an address that
# drops packets (TEST-NET-1) ends within the deadline's reach, as
# ETIMEDOUT, or at once when the network refuses (or a proxy takes) the
# route: never after the kernel's own connect timeout.
import Base

def named(+c: U32) -> String:
  Bool.pick(String, Bool.or(U32.is_eq(c, 111), U32.is_eq(c, 61)), "refused",
    Bool.pick(String, U32.is_eq(c, 22), "invalid", "failed"))

def said(r: Result<&1, &1, (U32 & String), Socket>) -> IO(Unit):
  match r:
    case Done{s}:
      do IO<Unit>:
        Unit <- IO.print("connected")
        Socket.close(s)
    case Fail{(c, m)}:
      IO.print(named(c))

def ended(r: Result<&1, &1, (U32 & String), Socket>, +t: Nat) -> IO(Unit):
  match r:
    case Done{s}:
      do IO<Unit>:
        Unit <- IO.print(Bool.pick(String, Nat.is_lt(t, 3000n), "ended in time",
          "ended late"))
        Socket.close(s)
    case Fail{e}:
      IO.print(Bool.pick(String, Nat.is_lt(t, 3000n), "ended in time",
        "ended late"))

def main() -> IO(U32):
  do IO<U32>:
    l  : Listener <- IO.try(Listener, TCP.listen(19251))
    r1 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("127.0.0.1", 19251, 1000)
    Unit <- said(r1)
    Unit <- Listener.close(l)
    r2 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("127.0.0.1", 19251, 1000)
    Unit <- said(r2)
    r3 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("1.2.3", 19251, 1000)
    Unit <- said(r3)
    t0 : Nat <- IO.now()
    r4 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("192.0.2.1", 80, 300)
    t1 : Nat <- IO.now()
    Unit <- ended(r4, Nat.sub(t1, t0))
    return 0

#|connected
#|refused
#|invalid
#|ended in time
