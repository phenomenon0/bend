# U02: TCP.listen asks the kernel for a backlog of 16. The server
# listens on 29602 and accepts nothing for 3 s; peer.py burst opens 64
# connections at once and counts the handshakes the kernel completed in
# 1 s: 17 (the backlog, plus one) where SOMAXCONN would take all 64.
import Base

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(29602))
    IO.sleep(3000)
    Listener.close(l)
