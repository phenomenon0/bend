# io (io_dns_resolve): DNS.resolve answers a dotted address as itself,
# "localhost" from the hosts file as 127.0.0.1, and refuses an empty
# name and one past 253 bytes with EINVAL before the resolver is asked.
# The answer connects: a listener on 127.0.0.1 is reached through it.
import Base

def said(r: Result<&1, &1, (U32 & String), String>) -> IO(Unit):
  match r:
    case Done{a}:
      IO.print(a)
    case Fail{(c, m)}:
      IO.print("refused " ++ U32.show(c))

def long(n: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      "a" ++ long(p)

def main() -> IO(U32):
  do IO<U32>:
    r1 : Result<&1, &1, (U32 & String), String> <- DNS.resolve("10.1.2.3")
    Unit <- said(r1)
    r2 : Result<&1, &1, (U32 & String), String> <- DNS.resolve("localhost")
    Unit <- said(r2)
    r3 : Result<&1, &1, (U32 & String), String> <- DNS.resolve("")
    Unit <- said(r3)
    r4 : Result<&1, &1, (U32 & String), String> <- DNS.resolve(long(254n))
    Unit <- said(r4)
    l  : Listener <- IO.try(Listener, TCP.listen(19252))
    a  : String <- IO.try(String, DNS.resolve("localhost"))
    s  : Socket <- IO.try(Socket, TCP.connect(a, 19252))
    Unit <- Socket.close(s)
    Unit <- Listener.close(l)
    Unit <- IO.print("connected")
    return 0

#|10.1.2.3
#|127.0.0.1
#|refused 22
#|refused 22
#|connected
