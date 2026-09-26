# io (io_tcp_poll_buf_or): TCP.poll_buf_or waits on a socket and a
# channel at once and takes nothing from the channel. Nothing on either:
# quiet at the deadline. A value offered first: rang at once, and the
# value still there for Chan.recv. Bytes first: the bytes. Both: the
# bytes win, and the next wait rings. Then the waits that park: a value
# offered 50 ms into a 3 s wait rings it long before the deadline, as
# does a channel closed then (rang, and Chan.recv answers None), and
# bytes sent then end it. Chan.offer on a full channel answers False;
# Chan.take answers what is there now, or nothing.
import Base

def heard(rang: Bool, m: Maybe<&1, Bytes()>) -> String:
  match m:
    case Some{b}:
      "bytes " ++ b
    case None{}:
      Bool.pick(String, rang, "rang", "quiet")

def took(m: Maybe<&1, Unit>) -> String:
  match m:
    case Some{u}:
      "took"
    case None{}:
      "closed"

def early(+t0: Nat, +t1: Nat) -> String:
  Bool.pick(String, Nat.is_lt(Nat.sub(t1, t0), 1000n), "early", "late")

law waited:
  for m: Socket & Bool & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>
  IO(Socket)

def waited(m):
  (s, rr) = m
  (rang, r) = rr
  do IO<Socket>:
    b : Maybe<&1, Bytes()> <- IO.pass(Maybe<&1, Bytes()>, r)
    p : Unit <- IO.print(heard(rang, b))
    return s

law wait:
  for a: Socket
  for ms: U32
  for +bell: Chan(Unit)
  IO(Socket)

def wait(a, ms, bell):
  IO.bind(Socket & Bool & Result<&1, &1, (U32 & String), Maybe<&1, Bytes()>>, Socket,
    TCP.poll_buf_or(Unit, a, 64, ms, bell), waited)

# the same wait, timed: early when it ended well before its 3 s
law timed:
  for a: Socket
  for +bell: Chan(Unit)
  IO(Socket)

def timed(a, bell):
  do IO<Socket>:
    +t0 : Nat <- IO.now()
    a1 : Socket <- wait(a, 3000, bell)
    +t1 : Nat <- IO.now()
    p : Unit <- IO.print(early(t0, t1))
    return a1

law take:
  for +bell: Chan(Unit)
  IO(Unit)

def take(bell):
  IO.bind(Maybe<&1, Unit>, Unit, Chan.recv(Unit, bell), m => IO.print(took(m)))

# Chan.take: what is there now, or nothing, never a wait
law grab:
  for +bell: Chan(Unit)
  IO(Unit)

def grab(bell):
  IO.bind(Maybe<&1, Unit>, Unit, Chan.take(Unit, bell),
    m => IO.print(Bool.pick(String, Maybe.is_some(&1, Unit, m), "took now", "nothing")))

law offered:
  for ok: Bool
  IO(Unit)

def offered(ok):
  IO.print(Bool.pick(String, ok, "offered", "full"))

law sent:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Socket)

def sent(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

law send:
  for c: Socket
  for b: Bytes()
  IO(Socket)

def send(c, b):
  IO.bind(Socket & Result<&1, &1, (U32 & String), Unit>, Socket, TCP.send_buf(c, b), sent)

# 50 ms from now, a value offered to bell
law ring_later:
  for +bell: Chan(Unit)
  IO(Unit)

def ring_later(bell):
  IO.spawn(Unit, do IO<Unit>:
    z : Unit <- IO.sleep(50)
    ok : Bool <- Chan.offer(Unit, bell, Unit{})
    return Unit{})

# 50 ms from now, bytes on c (the computation closes c after)
law send_later:
  for c: Socket
  IO(Unit)

def send_later(c):
  IO.spawn(Unit, do IO<Unit>:
    z : Unit <- IO.sleep(50)
    c1 : Socket <- send(c, "late")
    Socket.close(c1))

law close_later:
  for +bell: Chan(Unit)
  IO(Unit)

def close_later(bell):
  IO.spawn(Unit, do IO<Unit>:
    z : Unit <- IO.sleep(50)
    Chan.close(Unit, bell))

law talk:
  for c: Socket
  for a: Socket
  IO(Socket)

def talk(c, a):
  do IO<Socket>:
    +bell : Chan(Unit) <- Chan.new(Unit, 1)
    a1 : Socket <- wait(a, 20, bell)
    grab(bell)
    ok : Bool <- Chan.offer(Unit, bell, Unit{})
    offered(ok)
    full : Bool <- Chan.offer(Unit, bell, Unit{})
    offered(full)
    a2 : Socket <- wait(a1, 3000, bell)
    take(bell)
    c1 : Socket <- send(c, "hi")
    a3 : Socket <- wait(a2, 3000, bell)
    ok2 : Bool <- Chan.offer(Unit, bell, Unit{})
    c2 : Socket <- send(c1, "both")
    a4 : Socket <- wait(a3, 3000, bell)
    a5 : Socket <- wait(a4, 3000, bell)
    grab(bell)
    ring_later(bell)
    a6 : Socket <- timed(a5, bell)
    take(bell)
    +shut : Chan(Unit) <- Chan.new(Unit, 1)
    close_later(shut)
    a7 : Socket <- timed(a6, shut)
    take(shut)
    send_later(c2)
    a8 : Socket <- timed(a7, bell)
    return a8

law finish:
  for l: Listener
  for a: Socket
  IO(U32)

def finish(l, a):
  do IO<U32>:
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
    a1 : Socket <- talk(c, a)
    finish(l, a1)

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
    b : Listener & U32 <- tcp_listen_any(32n, 18760)
    main_go(b)

#|quiet
#|nothing
#|offered
#|full
#|rang
#|took
#|bytes hi
#|bytes both
#|rang
#|took now
#|rang
#|early
#|took
#|rang
#|early
#|closed
#|bytes late
#|early
