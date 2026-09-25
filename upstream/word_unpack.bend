# U20: a U32 taken apart into its Word and walked to a default arm: the C
# emitter lays the WCon chain down to a WNil it never declared, and clang
# refuses the file ("use of undeclared identifier 'CID_WNIL'"). Every
# lane should print "0 32 16".
import Base

def ones(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          ones(p, t)
        case WCon{True{}, t}:
          1n+ones(p, t)
    case _:
      0n

def ones32(x: U32) -> Nat:
  match x:
    case U32{w}:
      ones(32n, w)

def main() -> String:
  Nat.show(ones32(0)) ++ " " ++ Nat.show(ones32(4294967295)) ++ " "
    ++ Nat.show(ones32(2863311530))
