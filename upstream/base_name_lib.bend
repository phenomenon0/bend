# F08 (the library base_name.bend imports): a type named as one of Base's
# (Event) and a constructor named as one of Base's (Emit). On canon both
# are refused as duplicate declarations, though this file is only ever
# reached through an alias (E.Event, E.Emit) and cannot be confused with
# Base's.
import Base

type Event is Data:
  Emit{code: U32}

def code(e: Event) -> U32:
  match e:
    case Emit{c}:
      c

def make(c: U32) -> Event:
  Emit{c}
