# io (io_signal_self): a signal that lands while the program runs is
# noticed on every lane. The JS lane's io_run never returns to bun's
# event loop, so a process.on handler never ran there: SIGTERM was
# ignored by every net/ server on bun. The handler is now C on both
# lanes; sig.raise sends the signal to the process itself, mid-run.
import Base

law sig.raise:
  U32 -> IO(Unit)

def sig.raise(sig):
  import "./signal_self.c"
  import "./signal_self.js"

def flag(b: Bool) -> String:
  Bool.pick(String, b, "yes", "no")

def main() -> IO(Unit):
  do IO<Unit>:
    a : Bool <- IO.signal_pending(15)
    s : Bool <- IO.signal_seen(10)
    u : Unit <- sig.raise(15)
    b : Bool <- IO.signal_pending(15)
    c : Bool <- IO.signal_pending(15)
    d : Bool <- IO.signal_seen(15)
    v : Unit <- sig.raise(10)
    w : Unit <- sig.raise(15)
    e : Bool <- IO.signal_seen(10)
    f : Bool <- IO.signal_pending(15)
    IO.print(flag(a) ++ " " ++ flag(s) ++ " " ++ flag(b) ++ " " ++ flag(c) ++ " " ++ flag(d)
      ++ " " ++ flag(e) ++ " " ++ flag(f))

#|no no yes no yes yes yes
