# io (io_tcp_listen_v6): TCP.listen_on binds an IPv6 address as it does
# a dotted one. On ::1 a connect to ::1 is accepted and carries bytes,
# and the peer reads back as ::1; on :: (IPV6_V6ONLY off) a connect to
# 127.0.0.1 is accepted too, its peer dotted. TCP.listen_shared_on takes
# ::1 as well. The text is inet_pton's: brackets, a zone and a second
# "::" are EINVAL. DNS.resolve_all answers a literal with itself, IPv6
# ones as RFC 5952 writes them.
import Base

def Peer.addr(s: Socket) -> IO(Socket & String):
  import "../../demos/io_proxy/peer.c"
  import "../../demos/io_proxy/peer.js"

def said(r: Result<&1, &1, (U32 & String), Listener>) -> IO(Unit):
  match r:
    case Done{l}:
      do IO<Unit>:
        p : Unit <- IO.print("bound")
        Listener.close(l)
    case Fail{(code, message)}:
      IO.print("refused " ++ U32.show(code))

def got(r: Result<&1, &1, (U32 & String), String>) -> IO(Unit):
  match r:
    case Done{a}:
      IO.print(a)
    case Fail{(code, message)}:
      IO.print("fail " ++ U32.show(code))

def peer(sa: Socket & String) -> IO(Unit):
  (s, a) = sa
  do IO<Unit>:
    p : Unit <- IO.print("peer " ++ a)
    Socket.close(s)

def read(m: Socket & Result<&1, &1, (U32 & String), String>) -> IO(Socket):
  (s, r) = m
  do IO<Socket>:
    data : String <- IO.pass(String, r)
    p : Unit <- IO.print(data)
    return s

def sent(m: Socket & Result<&1, &1, (U32 & String), Unit>) -> IO(Socket):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

def took(host: String, c: Socket, p: Listener & Result<&1, &1, (U32 & String), Socket>) -> IO(Unit):
  (l, r) = p
  do IO<Unit>:
    a : Socket <- IO.pass(Socket, r)
    c2 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), Unit>, Socket, TCP.send(c, "over " ++ host), sent)
    a2 : Socket <- IO.bind(Socket & Result<&1, &1, (U32 & String), String>, Socket, TCP.recv(a, 64), read)
    q : Unit <- IO.bind(Socket & String, Unit, Peer.addr(a2), peer)
    x : Unit <- Socket.close(c2)
    Listener.close(l)

# listen on host, connect from to, send a line one way, name the peer
def round(+host: String, to: String, +port: U32) -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen_on(host, port))
    c : Socket <- IO.try(Socket, TCP.connect(to, port))
    p : Listener & Result<&1, &1, (U32 & String), Socket> <- TCP.accept(l)
    took(host, c, p)

def main() -> IO(U32):
  do IO<U32>:
    a : Unit <- round("::1", "::1", 29380)
    b : Unit <- round("::", "127.0.0.1", 29381)
    r1 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_shared_on("::1", 29382)
    c : Unit <- said(r1)
    r2 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_on("[::1]", 29383)
    d : Unit <- said(r2)
    r3 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_on("::1%lo", 29383)
    e : Unit <- said(r3)
    r4 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_on("1::2::3", 29383)
    f : Unit <- said(r4)
    n1 : Result<&1, &1, (U32 & String), String> <- DNS.resolve_all("0:0:0:0:0:0:0:1")
    g : Unit <- got(n1)
    n2 : Result<&1, &1, (U32 & String), String> <- DNS.resolve_all("2001:DB8:0:0:1:0:0:1")
    h : Unit <- got(n2)
    n3 : Result<&1, &1, (U32 & String), String> <- DNS.resolve_all("127.0.0.1")
    i : Unit <- got(n3)
    return 0

#|over ::1
#|peer ::1
#|over ::
#|peer 127.0.0.1
#|bound
#|refused 22
#|refused 22
#|refused 22
#|::1
#|2001:db8::1:0:0:1
#|127.0.0.1
