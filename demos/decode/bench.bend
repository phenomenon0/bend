# The decode step under load: 2^16 of the demo's rollouts (seed 35, K = 4, ids
# 0..65535) as a fork/join tree, each step decoded and its certificate checked.
# Prints the steps taken, the documents finished and the certificates that
# failed, which must be 0.
#   bend demos/decode/bench.bend -o db && time ./db --gpu off
import Base
import ../../power/grammar.bend as Gr
import ./main.bend as M

type T is Data:
  T{steps: U32, done: U32, bad: U32}

def one(t: Bool) -> U32:
  match t:
    case True{}:
      1
    case False{}:
      0

def t.of(r: M.Run) -> T:
  match r:
    case M.Run{s, pos, d, out, bad, stop}:
      T{pos, one(Gr.done(s)), bad}

def t.add(x: T, y: T) -> T:
  match x:
    case T{s, d, b}:
      match y:
        case T{s1, d1, b1}:
          T{U32.add(s, s1), U32.add(d, d1), U32.add(b, b1)}

def many(d: Nat, +i: U32) -> T:
  match d:
    case 0n:
      t.of(M.rollout(48n, 4, 35, i, False{}))
    case 1n++p:
      a b = many(p, i) many(p, U32.add(i, U32.shln(1, p)))
      t.add(a, b)

def show(t: T) -> String:
  match t:
    case T{s, d, b}:
      "rollouts 65536 steps " ++ U32.show(s) ++ " done " ++ U32.show(d) ++ " bad certs " ++ U32.show(b)

def main() -> IO(Unit):
  IO.print(show(many!(16n, 0)))
