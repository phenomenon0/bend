# io (io_file_sendfile): File.sendfile puts a file's bytes on a socket
# from an offset, without moving the file's position. "0123456789" is
# written; from 2, five bytes arrive as "23456"; from 8, five are asked
# and the file has two: "89" arrives and the send fails with ENODATA;
# a File.read_buf after both still reads from the start.
import Base

def path() -> String:
  "/tmp/bend_io_file_sendfile"

def short(+code: U32) -> String:
  Bool.pick(String, U32.is_eq(code, 61) || U32.is_eq(code, 96), "short", "failed")

def shown(r: Result<&1, &1, (U32 & String), Unit>) -> String:
  match r:
    case Done{u}:
      "done"
    case Fail{e}:
      (code, msg) = e
      short(code)

law write_go:
  for w: File & Result<&1, &1, (U32 & String), Unit>
  IO(Unit)

def write_go(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

def heard(m: Socket & Result<&1, &1, (U32 & String), Bytes()>) -> IO(Socket):
  (s, r) = m
  do IO<Socket>:
    bs : Bytes() <- IO.pass(Bytes(), r)
    IO.print(bs)
    return s

def read(m: File & Result<&1, &1, (U32 & String), Bytes()>) -> IO(Unit):
  (f, r) = m
  do IO<Unit>:
    bs : Bytes() <- IO.pass(Bytes(), r)
    IO.print(bs)
    File.close(f)

def last(c: Socket, m: Socket & File & Result<&1, &1, (U32 & String), Unit>) -> IO(U32):
  (a, fr) = m
  (f, r) = fr
  do IO<U32>:
    IO.print(shown(r))
    r2 : Socket & Result<&1, &1, (U32 & String), Bytes()> <- TCP.recv_buf(c, 64)
    c2 : Socket <- heard(r2)
    g  : File & Result<&1, &1, (U32 & String), Bytes()> <- File.read_buf(f, 4)
    Unit <- read(g)
    Socket.close(a)
    Socket.close(c2)
    return 0

def first(c: Socket, m: Socket & File & Result<&1, &1, (U32 & String), Unit>) -> IO(U32):
  (a, fr) = m
  (f, r) = fr
  do IO<U32>:
    IO.print(shown(r))
    r1 : Socket & Result<&1, &1, (U32 & String), Bytes()> <- TCP.recv_buf(c, 64)
    c2 : Socket <- heard(r1)
    m2 : Socket & File & Result<&1, &1, (U32 & String), Unit> <- File.sendfile(a, f, 8, 5, 1000)
    last(c2, m2)

def pair(c: Socket, a: Socket, f: File) -> IO(U32):
  do IO<U32>:
    m1 : Socket & File & Result<&1, &1, (U32 & String), Unit> <- File.sendfile(a, f, 2, 5, 1000)
    first(c, m1)

def step_accept(c: Socket, p: Listener & Result<&1, &1, (U32 & String), Socket>) -> IO(U32):
  (l2, ar) = p
  do IO<U32>:
    a : Socket <- IO.pass(Socket, ar)
    f : File <- IO.try(File, File.open(path(), "r"))
    x : U32 <- pair(c, a, f)
    Listener.close(l2)
    return x

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
    f : File <- IO.try(File, File.open(path(), "w"))
    w : File & Result<&1, &1, (U32 & String), Unit> <- File.write(f, "0123456789")
    u : Unit <- write_go(w)
    b : Listener & U32 <- tcp_listen_any(32n, 19951)
    main_go(b)

#|done
#|23456
#|short
#|89
#|0123
