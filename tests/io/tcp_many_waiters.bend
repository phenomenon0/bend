# io (io_tcp_many_waiters): 64 clients fork at once, each connects,
# sends and waits on its reply, while the server's accept loop spawns an
# echo handler per connection: some 130 computations park on descriptors
# at the same time and each wakes on its own. The poller (epoll, kqueue)
# holds each waiter armed one-shot; a wake runs that waiter only.
import Base

law handle.sent:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Unit)

def handle.sent(m):
  (s, r) = m
  Socket.close(s)

law handle.read:
  for m: Socket & Result<&1, &1, (U32 & String), String>
  IO(Unit)

def handle.read(m):
  (s, r) = m
  do IO<Unit>:
    data : String <- IO.pass(String, r)
    sent : Socket & Result<&1, &1, (U32 & String), Unit> <-
      TCP.send(s, String.append("echo:", data))
    handle.sent(sent)

law handle:
  for s: Socket
  IO(Unit)

def handle(s):
  do IO<Unit>:
    m : Socket & Result<&1, &1, (U32 & String), String> <- TCP.recv(s, 8)
    handle.read(m)

law serve.got:
  for rest: Listener -> IO(Unit)
  for m: Listener & Result<&1, &1, (U32 & String), Socket>
  IO(Unit)

def serve.got(rest, m):
  (l, r) = m
  do IO<Unit>:
    s : Socket <- IO.pass(Socket, r)
    Unit <- IO.spawn(Unit, handle(s))
    rest(l)

law serve:
  for n: Nat
  for l: Listener
  IO(Unit)

def serve(n, l):
  match n:
    case 0n:
      Listener.close(l)
    case 1n+p:
      IO.bind(Listener & Result<&1, &1, (U32 & String), Socket>, Unit,
        TCP.accept(l), serve.got(l2 => serve(p, l2)))

law client.read:
  for m: Socket & Result<&1, &1, (U32 & String), String>
  IO(String)

def client.read(m):
  (s, r) = m
  do IO<String>:
    reply : String <- IO.pass(String, r)
    Unit <- Socket.close(s)
    return reply

law client.sent:
  for m: Socket & Result<&1, &1, (U32 & String), Unit>
  IO(String)

def client.sent(m):
  (s, r) = m
  do IO<String>:
    Unit <- IO.pass(Unit, r)
    got : Socket & Result<&1, &1, (U32 & String), String> <- TCP.recv(s, 64)
    client.read(got)

law client:
  for port: U32
  for tag: String
  IO(String)

def client(port, tag):
  do IO<String>:
    s : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    m : Socket & Result<&1, &1, (U32 & String), Unit> <- TCP.send(s, tag)
    client.sent(m)

law run:
  for n: Nat
  for +port: U32
  IO(Nat)

def run(n, port):
  match n:
    case 0n:
      IO.pure(Nat, 0n)
    case 1n+k:
      do IO<Nat>:
        a : Chan(String) <- IO.fork(String, client(port, "ab"))
        m : Nat <- run(k, port)
        x : String <- IO.join(String, a)
        return Nat.add(m, String.length(x))

law main.go:
  for b: Listener & U32
  IO(U32)

def main.go(b):
  (l, +port) = b
  do IO<U32>:
    Unit <- IO.spawn(Unit, serve(64n, l))
    n : Nat <- run(64n, port)
    Unit <- IO.print(Nat.show(n))
    return 0

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
    b : Listener & U32 <- tcp_listen_any(32n, 21264)
    main.go(b)

#|448
