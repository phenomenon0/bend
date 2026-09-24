# A U32 taken apart into its Word and walked bit by bit: the C lane
# lays the WCon chain itself, down to its WNil, so it must know WNil's id
# even when no source names WNil (only WCon is matched here, and the end
# of the word is a default arm). Found by tests/fuzz: the C build failed
# with "use of undeclared identifier 'CID_WNIL'".
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

#|"0 32 16"
