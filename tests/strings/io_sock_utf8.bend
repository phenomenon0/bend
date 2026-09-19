# TCP.recv through a Utf8.Dec (effs/tcp_recv_text_go): a text received in
# chunks appends to its whole decode, wherever a recv cuts a scalar. TCP.recv
# decodes each chunk alone, so at max 1 every 2-, 3- and 4-byte scalar of this
# text would come back as replacement characters. Every max must answer the
# sent text's hash and length; max 1 also drives the recv that only feeds the
# carry (it parks again instead of answering ""). base.bend has no room for
# the wrapper under its cap (320 tok), so the effect is bound here.
import Base

def Sock.Raw() -> Type:
  Socket & Result<&1, &1, U32 & String, U32 & U32 & String>

def TCP.recv_text.go(sock: Socket, pend: U32, need: U32, max: U32) -> IO(Sock.Raw()):
  import "../../bend2/effs/tcp_recv_text_go.c"
  import "../../bend2/effs/tcp_recv_text_go.js"

def sent(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Socket):
  (s, r) = m
  IO.bind(Unit, Socket, IO.pass(Unit, r), u => IO.pure(Socket, s))

def more(eof: Bool, again: Unit -> IO(String), acc: String) -> IO(String):
  match eof:
    case True{}:
      IO.pure(String, acc)
    case False{}:
      again(Unit{})

def step(acc: String, again: Socket -> U32 -> U32 -> String -> IO(String), got: Sock.Raw()) -> IO(String):
  (a, r) = got
  match r:
    case Fail{(code, msg)}:
      IO.die(String, code, msg)
    case Done{(pend, (+need, text))}:
      +all = acc ++ text
      more(U32.is_eq(need, 4), u => again(a, pend, need, all), all)

def drain(fuel: Nat, a: Socket, pend: U32, need: U32, +max: U32, acc: String) -> IO(String):
  match fuel:
    case 0n:
      IO.die(String, 1, "out of fuel")
    case 1n+left:
      IO.bind(Sock.Raw(), String, TCP.recv_text.go(a, pend, need, max),
        step(acc, s => p => n => t => drain(left, s, p, n, max, t)))

def accepted(c: Socket, +max: U32, p: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  (l, ar) = p
  do IO<Unit>:
    a : Socket <- IO.pass(Socket, ar)
    sm : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(c, String.repeat("añ€😀 wörd\n", 3n))
    c2 : Socket <- sent(sm)
    Socket.close(c2)
    +text : String <- drain(4000n, a, 0, 0, max, "")
    Listener.close(l)
    IO.print(U32.show(max) ++ " " ++ U32.show(String.hash(text)) ++ " " ++ U32.show(U32.from_nat(String.length(text))))

def retry(+port: U32, r: Result<&1, &1, U32 & String, Listener>, rest: IO(Listener & U32)) -> IO(Listener & U32):
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
      IO.bind(Result<&1, &1, U32 & String, Listener>, Listener & U32, TCP.listen(port), r => retry(port, r, rest))

def round.go(+max: U32, b: Listener & U32) -> IO(Unit):
  (l, port) = b
  do IO<Unit>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    p : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    accepted(c, max, p)

def round(+max: U32) -> IO(Unit):
  IO.bind(Listener & U32, Unit, listen_any(32n, 19747), round.go(max))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(String.hash(String.repeat("añ€😀 wörd\n", 3n))))
    round(1)
    round(2)
    round(3)
    round(7)
    round(4096)

#|263802747
#|1 263802747 30
#|2 263802747 30
#|3 263802747 30
#|7 263802747 30
#|4096 263802747 30
