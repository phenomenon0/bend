# The CAS store daemon: a content-addressed blob store over HTTP.
#
#   bend demos/io_cas_store/main.bend -o cas_store && ./cas_store
#   curl -X PUT --data-binary @file http://127.0.0.1:8089/blob
#   curl http://127.0.0.1:8089/blob/<address>/<off>/<len>
#
# The accept loop is serial, not one spawn per connection: the store is a
# value, and a value threaded through a loop is the only way two connections
# can agree on what is stored without a lock. One client at a time; the report
# says what that costs.
#
# A recv is one recv(2) (bend2/effs/tcp_recv.c), so the reader loops until
# Srv.req.done says the request is whole. Nothing else can be a loop here:
# a do line cannot destructure, and the checker allows neither forward
# references nor mutual recursion, so every step that has to both take a pair
# apart and come back gets the rest of the loop handed to it as a function.
import Base
import ./cas.bend as Cas
import ./serve.bend as Srv

def PORT() -> U32:
  8089

def RECV() -> U32:
  65536

# 64 MiB of request at most, and a dead peer ends the read on its own
def TRIES() -> Nat:
  1024n

# -- reading a whole request -------------------------------------------------

def read.pick(k: Socket -> String -> IO(Socket & String), s: Socket,
              acc: String, stop: Bool) -> IO(Socket & String):
  match stop:
    case True{}:
      IO.pure(Socket & String, (s, acc))
    case False{}:
      k(s)(acc)

def read.got(k: Socket -> String -> IO(Socket & String), s: Socket,
             +acc: String, +got: String) -> IO(Socket & String):
  read.pick(k, s, acc ++ got,
    Bool.or(String.is_empty(got), Srv.req.done(acc ++ got)))

def read.on(k: Socket -> String -> IO(Socket & String), acc: String,
            m: Socket & Result<&1, &1, U32 & String, String>)
    -> IO(Socket & String):
  (s, r) = m
  match r:
    case Done{got}:
      read.got(k, s, acc, got)
    case Fail{e}:
      IO.pure(Socket & String, (s, acc))

def read.go(fuel: Nat, s: Socket, acc: String) -> IO(Socket & String):
  match fuel:
    case 0n:
      IO.pure(Socket & String, (s, acc))
    case 1n++f:
      do IO<Socket & String>:
        m : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, RECV())
        read.on(s2 => a2 => read.go(f, s2, a2), acc, m)

# -- one connection ----------------------------------------------------------

def talk.close(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  Socket.close(s)

def talk.send(k: Cas.Store -> IO(Unit), s: Socket, r: Cas.Store & String)
    -> IO(Unit):
  (st, txt) = r
  do IO<Unit>:
    m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(s, txt)
    u : Unit <- talk.close(m)
    k(st)

def talk.req(k: Cas.Store -> IO(Unit), st: Cas.Store, p: Socket & String)
    -> IO(Unit):
  (s, req) = p
  talk.send(k, s, Srv.serve(st, req))

def conn.go(k: Cas.Store -> IO(Unit), st: Cas.Store, s: Socket) -> IO(Unit):
  do IO<Unit>:
    p : Socket & String <- read.go(TRIES(), s, "")
    talk.req(k, st, p)

def conn.on(k: Listener -> Cas.Store -> IO(Unit), st: Cas.Store,
            m: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  (l, r) = m
  match r:
    case Done{s}:
      conn.go(st2 => k(l)(st2), st, s)
    case Fail{e}:
      k(l)(st)

@unsafe
def serve.loop(l: Listener, st: Cas.Store) -> IO(Unit):
  do IO<Unit>:
    m : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    conn.on(l2 => st2 => serve.loop(l2, st2), st, m)

def main() -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(PORT()))
    u : Unit <- IO.print("cas store on http://127.0.0.1:8089")
    serve.loop(l, Cas.new())
