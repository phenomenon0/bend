# U01: TCP.recv decodes the bytes it reads as UTF-8 (and TCP.send
# re-encodes), so a byte that is not UTF-8 comes back as U+FFFD. The
# server accepts one peer on its port (29601), reads once and echoes
# what it read; peer.py echo sends 01 80 fe 02 and prints the echo.
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
  for m: Socket & Result<&1, &1, U32 & String, String>
  IO(Unit)

def echo_got(l, m):
  (s, r) = m
  do IO<Unit>:
    data : String <- IO.pass(String, r)
    sm : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(s, data)
    echo_done(l, sm)

law echo_one:
  for p: Listener & Result<&1, &1, U32 & String, Socket>
  IO(Unit)

def echo_one(p):
  (l, ar) = p
  do IO<Unit>:
    s : Socket <- IO.pass(Socket, ar)
    m : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 64)
    echo_got(l, m)

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(29601))
    p : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    echo_one(p)
