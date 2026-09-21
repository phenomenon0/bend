# cas (loopback): the daemon's reader against a real socket. The client sends
# the head and the body as two separate writes, because a recv is one recv(2)
# (bend2/effs/tcp_recv.c) and a reader that takes the first one for the whole
# request stores a truncated blob. read.go keeps asking until req.done says
# the Content-Length has arrived; what comes back here is the request whole,
# and serve answers it.
#
# Handles are affine, so every op threads its handle back outside the Result
# and each tuple destructures in a helper of its own -- a do line cannot take
# a pair apart. The listener walks up from a base port so a busy machine does
# not fail the lane.
import Base
import ../../demos/io_cas_store/cas.bend as Cas
import ../../demos/io_cas_store/serve.bend as Srv
import ../../demos/io_cas_store/main.bend as Daemon

def first(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      h

def payload() -> String:
  String.repeat("the quick brown fox ", 4n)

def head() -> String:
  String.concat(["PUT /blob HTTP/1.1\r\nHost: x\r\nContent-Length: ",
    U32.show(U32.from_nat(String.length(payload()))), "\r\n\r\n"])

def said(r: Cas.Store & String) -> String:
  (st, s) = r
  first(String.split_on(s, "\r\n"))

def report(+req: String) -> String:
  String.concat(["request ", Nat.show(String.length(req)), " chars -> ",
    said(Srv.serve(Cas.new(), req))])

def fin(l: Listener, c: Socket, p: Socket & String) -> IO(Unit):
  (a, req) = p
  do IO<Unit>:
    u : Unit <- IO.print(report(req))
    w : Unit <- Socket.close(a)
    x : Unit <- Socket.close(c)
    Listener.close(l)

def read_back(l: Listener, a: Socket, m: Socket & Result<&1, &1, U32 & String, Unit>)
    -> IO(Unit):
  (c, r) = m
  do IO<Unit>:
    p : Socket & String <- Daemon.read.go(16n, a, "")
    fin(l, c, p)

def send_body(l: Listener, a: Socket, m: Socket & Result<&1, &1, U32 & String, Unit>)
    -> IO(Unit):
  (c, r) = m
  do IO<Unit>:
    m2 : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(c, payload())
    read_back(l, a, m2)

def on_accept(c: Socket, p: Listener & Result<&1, &1, U32 & String, Socket>)
    -> IO(Unit):
  (l, r) = p
  do IO<Unit>:
    a : Socket <- IO.pass(Socket, r)
    m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(c, head())
    send_body(l, a, m)

def go(b: Listener & U32) -> IO(Unit):
  (l, port) = b
  do IO<Unit>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    p : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    on_accept(c, p)

def retry(+port: U32, r: Result<&1, &1, U32 & String, Listener>,
          rest: IO(Listener & U32)) -> IO(Listener & U32):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

def listen_any(tries: Nat, +port: U32) -> IO(Listener & U32):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      rest = listen_any(t, (port + 1 : U32))
      do IO<Listener & U32>:
        r : Result<&1, &1, U32 & String, Listener> <- TCP.listen(port)
        retry(port, r, rest)

def main() -> IO(Unit):
  do IO<Unit>:
    b : Listener & U32 <- listen_any(32n, 19631)
    go(b)
#|request 131 chars -> HTTP/1.1 201 Created
