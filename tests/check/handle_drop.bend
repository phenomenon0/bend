# a handle that goes out of scope unused stays open until the process
# ends (UPSTREAM U19), so the check names it: a Socket a match arm binds
# and never uses, one inside a Result, one a let binds. Not named: a
# handle closed, one handed on, a scope that ends in IO.die (the process
# ends and its descriptors close with it), and a name that starts with _.
import Base

def arm(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Done{s}:
      IO.pure(Unit, Unit{})
    case Fail{e}:
      IO.pure(Unit, Unit{})

def held(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  IO.pure(Unit, Unit{})

def pair(p: Socket & Bool) -> Bool:
  (s, b) = p
  b

def closed(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Done{s}:
      Socket.close(s)
    case Fail{e}:
      IO.pure(Unit, Unit{})

def passed(s: Socket, k: Socket -> IO(Unit)) -> IO(Unit):
  k(s)

def dies(s: Socket) -> IO(Unit):
  IO.die(Unit, 1, "gone")

def named(_s: Socket) -> IO(Unit):
  IO.pure(Unit, Unit{})

#|warning: 3 handles are dropped unused (open until exit):
#|- arm: s (Socket) at line 10
#|- held: r (Socket) at line 15
#|- pair: s (Socket) at line 19
#|All terms check.
