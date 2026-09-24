# U01, on a checkout that has the byte pair: the same echo over
# TCP.recv_bytes and TCP.send_bytes, which must give back 01 80 fe 02.
import Base

law echo_done:
  for l: Listener
  for m: Socket & Result<&1, &1, U32 & String, Unit>
  IO(Unit)

def echo_done(l, m):
  (s, r) = m
  do IO<Unit>:
    IO.pass(Unit, r)
    Socket.close(s)
    Listener.close(l)

law echo_got:
  for l: Listener
  for m: Socket & Result<&1, &1, U32 & String, List<&2, U32>>
  IO(Unit)

def echo_got(l, m):
  (s, r) = m
  do IO<Unit>:
    data : List<&2, U32> <- IO.pass(List<&2, U32>, r)
    sm : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_bytes(s, data)
    echo_done(l, sm)

law echo_one:
  for p: Listener & Result<&1, &1, U32 & String, Socket>
  IO(Unit)

def echo_one(p):
  (l, ar) = p
  do IO<Unit>:
    s : Socket <- IO.pass(Socket, ar)
    m : Socket & Result<&1, &1, U32 & String, List<&2, U32>> <- TCP.recv_bytes(s, 64)
    echo_got(l, m)

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(29601))
    p : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    echo_one(p)
