# U18: TCP.connect takes a dotted IPv4 address only; a host name, even
# "localhost", fails at once with EINVAL (22), and Base has no resolver.
# Nothing listens on 29605, so the right answer is ECONNREFUSED (111 on
# Linux, 61 on macOS).
import Base

law said:
  for r: Result<&1, &1, U32 & String, Socket>
  IO(Unit)

def said(r):
  match r:
    case Done{s}:
      do IO<Unit>:
        IO.print("connected")
        Socket.close(s)
    case Fail{e}:
      (code, message) = e
      IO.print("Fail " ++ U32.show(code) ++ ": " ++ message)

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Socket> <- TCP.connect("localhost", 29605)
    said(r)
