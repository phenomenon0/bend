# io (io_tcp_accept_poll): TCP.accept_poll is TCP.accept with a
# deadline. With nothing connecting it answers None{} at once when ms
# is 0 and None{} after ms otherwise (IO.now on both sides shows the
# loop waited), and Some{socket} once a peer has connected. The
# listener threads back OUTSIDE the Result each time.
import Base

def waited(ok: Bool) -> String:
  match ok:
    case True{}:
      "waited"
    case False{}:
      "early"

law finish_go:
  for l: Listener
  for c: Socket
  for got: Maybe<&1, Socket>
  IO(U32)

def finish_go(l, c, got):
  match got:
    case None{}:
      do IO<U32>:
        w : Unit <- IO.print("none")
        x : Unit <- Socket.close(c)
        z : Unit <- Listener.close(l)
        return 1
    case Some{a}:
      do IO<U32>:
        w : Unit <- IO.print("accepted")
        x : Unit <- Socket.close(a)
        y : Unit <- Socket.close(c)
        z : Unit <- Listener.close(l)
        return 0

law finish:
  for c: Socket
  for m: Listener & Result<&1, &1, (U32 & String), Maybe<&1, Socket>>
  IO(U32)

def finish(c, m):
  (l, r) = m
  do IO<U32>:
    got : Maybe<&1, Socket> <- IO.pass(Maybe<&1, Socket>, r)
    finish_go(l, c, got)

# the third poll: a peer has connected, so a 1 s poll accepts it
law step_conn:
  for l: Listener
  for port: U32
  IO(U32)

def step_conn(l, port):
  do IO<U32>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    m : Listener & Result<&1, &1, (U32 & String), Maybe<&1, Socket>> <-
      TCP.accept_poll(l, 1000)
    finish(c, m)

# what a poll with nobody connecting answered: None{} is the point; a
# socket would be a surprise, closed and named
law saw:
  for got: Maybe<&1, Socket>
  IO(Unit)

def saw(got):
  match got:
    case None{}:
      IO.print("none")
    case Some{a}:
      do IO<Unit>:
        x : Unit <- Socket.close(a)
        IO.print("some")

# the second poll: 200 ms with nobody connecting answers None{}, and
# IO.now shows the loop waited for it
law step_timed_go:
  for port: U32
  for t0: Nat
  for m: Listener & Result<&1, &1, (U32 & String), Maybe<&1, Socket>>
  IO(U32)

def step_timed_go(port, t0, m):
  (l, r) = m
  do IO<U32>:
    got : Maybe<&1, Socket> <- IO.pass(Maybe<&1, Socket>, r)
    t1  : Nat <- IO.now()
    w   : Unit <- saw(got)
    v   : Unit <- IO.print(waited(Nat.is_ge(Nat.sub(t1, t0), 150n)))
    step_conn(l, port)

law step_timed:
  for l: Listener
  for port: U32
  IO(U32)

def step_timed(l, port):
  do IO<U32>:
    t0 : Nat <- IO.now()
    m  : Listener & Result<&1, &1, (U32 & String), Maybe<&1, Socket>> <-
      TCP.accept_poll(l, 200)
    step_timed_go(port, t0, m)

# the first poll: ms = 0 and nobody connecting answers None{} at once
law step_empty:
  for port: U32
  for m: Listener & Result<&1, &1, (U32 & String), Maybe<&1, Socket>>
  IO(U32)

def step_empty(port, m):
  (l, r) = m
  do IO<U32>:
    got : Maybe<&1, Socket> <- IO.pass(Maybe<&1, Socket>, r)
    w   : Unit <- saw(got)
    step_timed(l, port)

law main_go:
  for b: Listener & U32
  IO(U32)

def main_go(b):
  (l, port) = b
  do IO<U32>:
    m : Listener & Result<&1, &1, (U32 & String), Maybe<&1, Socket>> <-
      TCP.accept_poll(l, 0)
    step_empty(port, m)

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
    b : Listener & U32 <- tcp_listen_any(32n, 19689)
    main_go(b)

#|none
#|none
#|waited
#|accepted
