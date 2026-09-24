# io (io_tcp_listen_on): TCP.listen_on and TCP.listen_shared_on bind the
# one address named (127.0.0.1 here, then a connect to it); anything but
# a dotted IPv4 address is EINVAL, never a bind to 0.0.0.0 in its place.
import Base

law said:
  for r: Result<&1, &1, (U32 & String), Listener>
  IO(Unit)

def said(r):
  match r:
    case Done{l}:
      do IO<Unit>:
        p : Unit <- IO.print("bound")
        Listener.close(l)
    case Fail{(code, message)}:
      IO.print("refused " ++ U32.show(code))

law main:
  IO(U32)

def main():
  do IO<U32>:
    l : Listener <- IO.try(Listener, TCP.listen_on("127.0.0.1", 19241))
    s : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", 19241))
    a : Unit <- Socket.close(s)
    b : Unit <- Listener.close(l)
    p : Unit <- IO.print("connected")
    r1 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_shared_on("127.0.0.1", 19242)
    c : Unit <- said(r1)
    r2 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_on("localhost", 19243)
    d : Unit <- said(r2)
    r3 : Result<&1, &1, (U32 & String), Listener> <- TCP.listen_on("1.2.3", 19243)
    e : Unit <- said(r3)
    return 0

#|connected
#|bound
#|refused 22
#|refused 22
