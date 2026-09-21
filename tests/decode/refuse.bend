# Refusals and the one real bug. Where nothing legal has weight, the decoder
# returns a refusal value and never falls back to some other token. That
# includes a legal one it was given no weight for. The checker, handed a step
# forged at such a point, rejects it.
#
# The last rows are not forged. Sixty-four `[` put the grammar at its nesting
# ceiling, where the mask still offers `[` but the step kills the state:
# allows(s, c) == live(step(s, c)) fails on a reachable state, in
# power/grammar.bend. The decoder trusts the mask, so it emits the token, and
# the certificate is what catches it (split). A step there that picks the legal
# `]` splits too: the frontier pass tests the law on every token, not only on
# the one drawn. When grammar.bend is fixed, the `[` row refuses (empty), the
# `]` row passes (ok), and the mask loses 91 and 123.
import Base
import ../../power/grammar.bend as Gr
import ../../power/heap.bend as Heap
import ../../power/decode.bend as D
import ../../demos/decode/main.bend as M

# after `{"a"`: only ` ` (12) and `:` (5) are legal
def colon() -> Gr.St:
  D.st.of(D.walk(Gr.step(Gr.start(), 123), D.pack("\"a\"")))

def at() -> D.At:
  D.At{35, 0, 0}

# weight w at the ids in xs, zero elsewhere
def put.if(+w: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      w
    case False{}:
      0

def has(xs: List<&2, U32>, +i: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Bool.or(U32.is_eq(x, i), has(rest, i))

def put(f: Nat, +xs: List<&2, U32>, +w: U32, +i: U32) -> List<&2, U32>:
  match f:
    case 0n:
      []
    case 1n++p:
      Con{put.if(w, has(xs, i)), put(p, xs, w, U32.inc(i))}

def ls(xs: List<&2, U32>, w: U32) -> List<&2, U32>:
  put(18n, xs, w, 0)

def add(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{x, xr}:
      match ys:
        case Nil{}:
          []
        case Con{y, yr}:
          Con{U32.add(x, y), add(xr, yr)}

def say(+st: D.Step) -> String:
  match st:
    case D.Step{t, n, c}:
      "`" ++ M.text(M.vocab(), t) ++ "` -> " ++ Gr.show(n)

def res(r: Result<&2, &2, D.Bad, D.Step>) -> String:
  match r:
    case Fail{e}:
      "refused " ++ D.show(e)
    case Done{st}:
      say(st)

def step(s: Gr.St, logits: List<&2, U32>) -> String:
  res(D.decode_step(M.vocab(), s, logits, 4, at()))

def verdict(s: Gr.St, logits: List<&2, U32>, st: D.Step) -> String:
  D.show.vd(D.check(M.vocab(), s, logits, 4, at(), st))

def checked(+s: Gr.St, +logits: List<&2, U32>, r: Result<&2, &2, D.Bad, D.Step>) -> String:
  match r:
    case Fail{e}:
      "refused " ++ D.show(e)
    case Done{+st}:
      say(st) ++ " " ++ verdict(s, logits, st)

def deep.go(f: Nat, s: Gr.St) -> Gr.St:
  match f:
    case 0n:
      s
    case 1n++p:
      deep.go(p, Gr.step(s, 91))

def main() -> IO(Unit):
  do IO<Unit>:
    # `}` and `[` weighted, both illegal after a key; the legal ` ` and `:` are unweighted
    IO.print("illegal only " ++ step(colon(), ls([1, 2], 1000)))
    IO.print("dead state " ++ step(Gr.dead(), ls([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], 1000)))
    IO.print("no weight " ++ step(colon(), ls([], 0)))
    IO.print("k = 0 " ++ res(D.decode_step(M.vocab(), colon(), ls([5, 12], 1000), 0, at())))
    IO.print("short logits " ++ step(colon(), put(17n, [5], 1000, 0)))
    # the kept mass must fit a U32: 2^32 - 1 fits, 2^32 is refused
    IO.print("mass 2^32-1 " ++ checked(colon(), add(ls([12], 4294967294), ls([5], 1)), D.decode_step(M.vocab(), colon(), add(ls([12], 4294967294), ls([5], 1)), 4, at())))
    IO.print("mass 2^32 " ++ step(colon(), add(ls([12], 4294967295), ls([5], 1))))
    # forged steps where the decoder refused: nothing kept, or a legal token it gave no weight
    IO.print("forged at refusal, empty cert " ++ verdict(colon(), ls([1, 2], 1000), D.Step{5, Gr.step(colon(), 58), D.Cert{[], 0}}))
    IO.print("forged at refusal, weightless legal " ++ verdict(colon(), ls([1, 2], 1000), D.Step{5, Gr.step(colon(), 58), D.Cert{[Heap.Entry{0, 5}], 0}}))
    # the nesting ceiling: 64 open arrays
    IO.print("depth 64 " ++ Gr.show(deep.go(64n, Gr.start())) ++ " mask " ++ Gr.Mask.show(Gr.mask(deep.go(64n, Gr.start()))))
    IO.print("depth 64, `[` weighted " ++ checked(deep.go(64n, Gr.start()), ls([2], 1000), D.decode_step(M.vocab(), deep.go(64n, Gr.start()), ls([2], 1000), 4, at())))
    IO.print("depth 64, `]` weighted " ++ checked(deep.go(64n, Gr.start()), ls([3], 1000), D.decode_step(M.vocab(), deep.go(64n, Gr.start()), ls([3], 1000), 4, at())))
#|illegal only refused empty
#|dead state refused empty
#|no weight refused empty
#|k = 0 refused empty
#|short logits refused shape
#|mass 2^32-1 ` ` -> colon/1 ok
#|mass 2^32 refused heavy
#|forged at refusal, empty cert draw
#|forged at refusal, weightless legal illegal
#|depth 64 vale/64 mask  9-10 13 32 34 45 48-57 91 93 102 110 116 123
#|depth 64, `[` weighted `[` -> dead/0 split
#|depth 64, `]` weighted `]` -> sep/63 split
