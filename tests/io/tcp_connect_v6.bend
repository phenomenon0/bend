# io (io_tcp_connect_v6): TCP.connect_poll and TCP.connect dial an IPv6
# address as they do a dotted one: to a listener on ::1 they connect, to
# a port of ::1 nothing listens on they are refused (ECONNREFUSED: 111 on
# Linux, 61 on macOS), and a host in brackets or with a zone is EINVAL
# at once. The accepted socket's peer is ::1.
import Base

def Peer.addr(s: Socket) -> IO(Socket & String):
  import "../../demos/io_proxy/peer.c"
  import "../../demos/io_proxy/peer.js"

def said(r: Result<&1, &1, (U32 & String), Socket>) -> IO(Unit):
  match r:
    case Done{s}:
      do IO<Unit>:
        p : Unit <- IO.print("connected")
        Socket.close(s)
    case Fail{(+code, message)}:
      IO.print(Bool.pick(String, U32.is_eq(code, 111) || U32.is_eq(code, 61), "refused",
        "failed " ++ U32.show(code)))

def peer(sa: Socket & String) -> IO(Unit):
  (s, a) = sa
  do IO<Unit>:
    p : Unit <- IO.print("peer " ++ a)
    Socket.close(s)

def took(c: Socket, p: Listener & Result<&1, &1, (U32 & String), Socket>) -> IO(Unit):
  (l, r) = p
  do IO<Unit>:
    a : Socket <- IO.pass(Socket, r)
    q : Unit <- IO.bind(Socket & String, Unit, Peer.addr(a), peer)
    x : Unit <- Socket.close(c)
    Listener.close(l)

def main() -> IO(U32):
  do IO<U32>:
    l : Listener <- IO.try(Listener, TCP.listen_on("::1", 29384))
    c : Socket <- IO.try(Socket, TCP.connect_poll("::1", 29384, 2000))
    p : Unit <- IO.print("connected")
    m : Listener & Result<&1, &1, (U32 & String), Socket> <- TCP.accept(l)
    q : Unit <- took(c, m)
    r1 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("::1", 29385, 2000)
    a : Unit <- said(r1)
    r2 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect("::1", 29385)
    b : Unit <- said(r2)
    r3 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("[::1]", 29385, 2000)
    d : Unit <- said(r3)
    r4 : Result<&1, &1, (U32 & String), Socket> <- TCP.connect_poll("fe80::1%lo", 29385, 2000)
    e : Unit <- said(r4)
    return 0

#|connected
#|peer ::1
#|refused
#|refused
#|failed 22
#|failed 22
