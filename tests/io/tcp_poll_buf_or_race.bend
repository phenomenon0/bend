# io (io_tcp_poll_buf_or_race): a wait on a socket and a channel loses
# nothing and takes nothing twice. Four computations send 500 numbered
# values each into a channel of room 4 (so senders park, too), while a
# fifth writes 200 chunks of 16 bytes to the socket and closes it. One
# consumer waits with TCP.poll_buf_or and, whenever the channel rings,
# takes one value; after the socket's close (which stays readable, so
# it is waited on no more) it takes the rest from the channel alone.
# It must count 2000 values summing to 1999000 and 3200 bytes.
import Base

type Tally is Data:
  Tally{n: U32, sum: U32, bytes: U32, eof: Bool}

def producer(k: Nat, +ch: Chan(U32), +i: U32) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+j:
      IO.bind(Bool, Unit, Chan.send(U32, ch, i), ok => producer(j, ch, U32.inc(i)))

law sent:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Socket)

def sent(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

law writer:
  for k: Nat
  for c: Socket
  IO(Unit)

def writer(k, c):
  match k:
    case 0n:
      Socket.close(c)
    case 1n+j:
      IO.bind(Socket, Unit, IO.bind(Socket & Result<&1, &1, (U32 & String), Unit>, Socket,
        TCP.send_buf(c, "0123456789abcdef"), sent), c1 => writer(j, c1))

def done(t: Tally) -> Bool:
  match t:
    case Tally{n, sum, bytes, eof}:
      U32.is_eq(n, 2000) && eof

def eof(t: Tally) -> Bool:
  match t:
    case Tally{n, sum, bytes, eof}:
      eof

def show(t: Tally) -> String:
  match t:
    case Tally{n, sum, bytes, eof}:
      U32.show(n) ++ " values, sum " ++ U32.show(sum) ++ ", " ++ U32.show(bytes) ++ " bytes"

def got.value(t: Tally, m: Maybe<&1, U32>) -> Tally:
  match t:
    case Tally{n, sum, bytes, eof}:
      match m:
        case Some{+v}:
          Tally{U32.inc(n), U32.add(sum, v), bytes, eof}
        case None{}:
          Tally{n, sum, bytes, eof}

def got.bytes(t: Tally, +b: Bytes()) -> Tally:
  match t:
    case Tally{n, sum, bytes, eof}:
      Tally{n, sum, U32.add(bytes, U32.from_nat(Bytes.len(b))), eof || String.is_empty(b)}

law consume:
  for hb: Maybe<&1, Bytes()>
  for rang: Bool
  for +ch: Chan(U32)
  for s: Socket
  for t: Tally
  for again: Socket -> Tally -> IO(Socket & Tally)
  IO(Socket & Tally)

def consume(hb, rang, ch, s, t, again):
  match hb rang:
    case Some{+b} _:
      again(s, got.bytes(t, b))
    case None{} True{}:
      IO.bind(Maybe<&1, U32>, Socket & Tally, Chan.recv(U32, ch), m => again(s, got.value(t, m)))
    case None{} False{}:
      again(s, t)

law heard:
  for +ch: Chan(U32)
  for t: Tally
  for m: Socket & Bool & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>
  for again: Socket -> Tally -> IO(Socket & Tally)
  IO(Socket & Tally)

def heard(ch, t, m, again):
  (s, rr) = m
  (rang, r) = rr
  do IO<Socket & Tally>:
    hb : Maybe<&1, Bytes()> <- IO.pass(Maybe<&1, Bytes()>, r)
    consume(hb, rang, ch, s, t, again)

def drain.at(+t: Tally, k: Tally -> IO(Tally)) -> IO(Tally):
  k(t)

# after the socket's close (which stays readable), the rest from the
# channel alone
def drain(k: Nat, fin: Bool, +ch: Chan(U32), t: Tally) -> IO(Tally):
  match k fin:
    case 0n _:
      IO.pure(Tally, t)
    case _ True{}:
      IO.pure(Tally, t)
    case 1n+j False{}:
      IO.bind(Maybe<&1, U32>, Tally, Chan.recv(U32, ch), m => drain.at(got.value(t, m), +t1 => drain(j, done(t1), ch, t1)))

law loop:
  for k: Nat
  for fin: Bool
  for +ch: Chan(U32)
  for s: Socket
  for +t: Tally
  IO(Socket & Tally)

def loop(k, fin, ch, s, t):
  match k fin:
    case 0n _:
      IO.pure(Socket & Tally, (s, t))
    case _ True{}:
      IO.bind(Tally, Socket & Tally, drain(2001n, done(t), ch, t), t2 => IO.pure(Socket & Tally, (s, t2)))
    case 1n+j False{}:
          IO.bind(Socket & Bool & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>, Socket & Tally,
            TCP.poll_buf_or(U32, s, 64, 1000, ch), m => heard(ch, t, m, s1 => +t1 => loop(j, eof(t1), ch, s1, t1)))

law report:
  for l: Listener
  for p: Socket & Tally
  IO(U32)

def report(l, p):
  (a, t) = p
  do IO<U32>:
    q : Unit <- IO.print(show(t))
    x : Unit <- Socket.close(a)
    z : Unit <- Listener.close(l)
    return 0

law step_accept:
  for c: Socket
  for p: Listener & Result<&1, &1, (U32 & String), Socket>
  IO(U32)

def step_accept(c, p):
  (l, ar) = p
  do IO<U32>:
    a  : Socket <- IO.pass(Socket, ar)
    +ch : Chan(U32) <- Chan.new(U32, 4)
    IO.spawn(Unit, producer(500n, ch, 0))
    IO.spawn(Unit, producer(500n, ch, 500))
    IO.spawn(Unit, producer(500n, ch, 1000))
    IO.spawn(Unit, producer(500n, ch, 1500))
    IO.spawn(Unit, writer(200n, c))
    p2 : Socket & Tally <- loop(100000n, False{}, ch, a, Tally{0, 0, 0, False{}})
    report(l, p2)

law main_go:
  for b: Listener & U32
  IO(U32)

def main_go(b):
  (l, port) = b
  do IO<U32>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    p : Listener & Result<&1, &1, (U32 & String), Socket> <- TCP.accept(l)
    step_accept(c, p)

law tcp_retry:
  for port : U32
  for r    : Result<&1, &1, (U32 & String), Listener>
  for rest : IO(Listener & U32)
  IO(Listener & U32)

def tcp_retry(port, r, rest):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

law tcp_listen_any:
  for tries : Nat
  for +port : U32
  IO(Listener & U32)

def tcp_listen_any(tries, port):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      rest = tcp_listen_any(t, (port + 1 : U32))
      do IO<Listener & U32>:
        r : Result<&1, &1, (U32 & String), Listener> <- TCP.listen(port)
        tcp_retry(port, r, rest)

law main:
  IO(U32)

def main():
  do IO<U32>:
    b : Listener & U32 <- tcp_listen_any(32n, 18800)
    main_go(b)

#|2000 values, sum 1999000, 3200 bytes
