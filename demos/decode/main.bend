# Decode: a JSON document grown one token at a time from noise, where every
# token comes with a certificate that is checked before the next token is drawn.
#
# The model is Threefry noise: logits[id] is a fresh draw for each (rollout,
# position, id). That makes the grammar the only thing that shapes the output.
# A document is JSON because the mask never offers anything else. It stops at
# the first accepting state, or after N steps.
#
# Every step prints the token, the kept list the certificate carries (weight @
# id, best first), the draw out of the kept mass, the new state, and the
# checker's verdict on the step. Every lane prints the same bytes.
import Base
import ../../power/grammar.bend as Gr
import ../../power/heap.bend as Heap
import ../../power/decode.bend as D
import ../../power/rng.bend as Rng

def vocab() -> List<&2, U32>:
  [D.pack("{"), D.pack("}"), D.pack("["), D.pack("]"), D.pack(","), D.pack(":"),
   D.pack("\"a\""), D.pack("\"b\""), D.pack("1"), D.pack("23"), D.pack("true"),
   D.pack("null"), D.pack(" "), D.pack("\"a\":"), D.pack("-"), D.pack("0.5"),
   D.pack("\""), D.pack("x")]

# the toy model: one draw per (rollout, position, id), under a key of its own
def model(vs: List<&2, U32>, +seed: U32, +roll: U32, +pos: U32, +id: U32) -> List<&2, U32>:
  match vs:
    case Nil{}:
      []
    case Con{v, rest}:
      Con{U32.shrn(Rng.u32(U32.xor(seed, 2654435769), roll, U32.add(U32.mul(pos, 64), id)), 8n),
        model(rest, seed, roll, pos, U32.inc(id))}

def text.of(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "?"
    case Some{t}:
      D.text(t)

def text(vs: List<&2, U32>, id: U32) -> String:
  text.of(D.nth(vs, id))

type Run is Data:
  Run{s: Gr.St, pos: U32, doc: String, out: String, bad: U32, stop: Bool}

def sum.of(m: D.Ms) -> U32:
  match m:
    case D.Ms{sum, whole}:
      sum

def mass(kept: List<&2, Heap.Entry>) -> U32:
  sum.of(D.mass(kept, D.Ms{0, True{}}))

def line(vs: List<&2, U32>, +pos: U32, +tok: U32, next: Gr.St, cert: D.Cert, v: D.Vd) -> String:
  match cert:
    case D.Cert{+kept, draw}:
      U32.show(pos) ++ " `" ++ text(vs, tok) ++ "` kept " ++ D.show.kept(kept) ++ " draw " ++
        U32.show(draw) ++ "/" ++ U32.show(mass(kept)) ++ " -> " ++ Gr.show(next) ++ " " ++ D.show.vd(v) ++ "\n"

def say(+vs: List<&2, U32>, +pos: U32, +tok: U32, +next: Gr.St, cert: D.Cert, v: D.Vd, talk: Bool) -> String:
  match talk:
    case True{}:
      line(vs, pos, tok, next, cert, v)
    case False{}:
      ""

def bad.of(v: D.Vd) -> U32:
  match v:
    case D.Ok{}:
      0
    case D.No{b}:
      1

def run.ok(+vs: List<&2, U32>, talk: Bool, +pos: U32, doc: String, out: String, bad: U32, st: D.Step, +v: D.Vd) -> Run:
  match st:
    case D.Step{+tok, +next, cert}:
      Run{next, U32.inc(pos), doc ++ text(vs, tok), out ++ say(vs, pos, tok, next, cert, v, talk),
        U32.add(bad, bad.of(v)), Gr.done(next)}

def run.res(+vs: List<&2, U32>, +s: Gr.St, +ls: List<&2, U32>, +k: U32, +at: D.At, talk: Bool, pos: U32, doc: String, out: String, bad: U32, r: Result<&2, &2, D.Bad, D.Step>) -> Run:
  match r:
    case Fail{e}:
      Run{s, pos, doc, out ++ "refused " ++ D.show(e) ++ "\n", bad, True{}}
    case Done{+st}:
      run.ok(vs, talk, pos, doc, out, bad, st, D.check(vs, s, ls, k, at, st))

def run.step(+vs: List<&2, U32>, +k: U32, +seed: U32, +roll: U32, talk: Bool, +s: Gr.St, +pos: U32, doc: String, out: String, bad: U32, +ls: List<&2, U32>) -> Run:
  run.res(vs, s, ls, k, D.At{seed, roll, pos}, talk, pos, doc, out, bad, D.decode_step(vs, s, ls, k, D.At{seed, roll, pos}))

def run.one(+vs: List<&2, U32>, +k: U32, +seed: U32, +roll: U32, talk: Bool, r: Run) -> Run:
  match r:
    case Run{+s, +pos, doc, out, bad, stop}:
      match stop:
        case True{}:
          Run{s, pos, doc, out, bad, True{}}
        case False{}:
          run.step(vs, k, seed, roll, talk, s, pos, doc, out, bad, model(vs, seed, roll, pos, 0))

def run.go(f: Nat, +vs: List<&2, U32>, +k: U32, +seed: U32, +roll: U32, +talk: Bool, r: Run) -> Run:
  match f:
    case 0n:
      r
    case 1n++p:
      run.go(p, vs, k, seed, roll, talk, run.one(vs, k, seed, roll, talk, r))

# one rollout from the prompt `{`: at most n steps of width k
def rollout(n: Nat, k: U32, seed: U32, roll: U32, talk: Bool) -> Run:
  run.go(n, vocab(), k, seed, roll, talk, Run{Gr.step(Gr.start(), 123), 0, "{", "", 0, False{}})

def yn(t: Bool) -> String:
  match t:
    case True{}:
      "Y"
    case False{}:
      "n"

def report(r: Run) -> String:
  match r:
    case Run{s, pos, doc, out, bad, stop}:
      out ++ "doc " ++ doc ++ "\nsteps " ++ U32.show(pos) ++ " done " ++ yn(Gr.done(s)) ++
        " bad certs " ++ U32.show(bad)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report(rollout(48n, 4, 35, 0, True{})))
