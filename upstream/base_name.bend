# F08: a library cannot use a name Base has. base_name_lib.bend declares
# `type Event` with a constructor `Emit`, reached here only as E.Event and
# E.Emit; canon refuses the library ("a fresh name (duplicate declaration:
# Event)"), so a JSON tokenizer's Event, or a machine's Emit step, must be
# renamed before it ports (std/json.bend's Evt, its Yield).
import Base
import ./base_name_lib.bend as E

def main() -> U32:
  E.code(E.make(7))

#|7
