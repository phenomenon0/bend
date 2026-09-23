# The proofs of the HTTP engine laws.
#
# feed_split and bad_feeds are inductions on the chunk: feed walks the
# string structurally and ++ builds it the same way, so in the cons
# case both sides step the reader once and the induction hypothesis is
# already the goal. bad_absorbs and the five reply laws compute: the
# machine's last row sends Bad{} to Bad{} whatever the byte class is,
# and each written-out reply normalises to the same string the builder
# does.
import Base
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./ws.bend as Ws
import ./spec.bend as Spec
import ./world.bend as W
import ./LAWS.bend as Laws

def Laws.feed_split(a, b, p):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.feed_split(t, b, Eng.step(p, c))

def Laws.bad_absorbs(c, pd, out):
  {==}

def Laws.bad_feeds(s, pd, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.bad_feeds(t, pd, out)

# Framing
# =======
#
# cls_is_spec, lower_is_spec and the vectors compute. field_by_bytes is
# an induction over the table: at each entry both lookups test the same
# name, the engine with bytes.eq and the reference with Spec.eq, and
# eq_is_spec says those two are one function. The laws with a class in
# their premise go through one lemma each over the ten classes: where
# the premise says the class is allowed, it reads True == False and the
# case is refuted through BD; everywhere else the step computes to Bad.

# a type chosen by a Bool, for refuting True == False
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

# the step a run takes on one of its bytes: the state it was in, with
# the byte added (a skipped value adds nothing)
def SG(-sel: Eng.Run, -k: Eng.Cls, -c: U32, -acc: Bytes(), -pd: Eng.Pend,
  -out: List<&2, Eng.Req>) -> Type:
  {Eng.step.at(Eng.st.put(sel, acc), k, c, pd, out) ==
    Eng.P{Eng.st.put(sel, Eng.push(acc, c)), pd, out} : Eng.P}

# anything, from False == True
def no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : BD(_, g, Unit)
  Unit{}

# a byte a run carries is one step keeps it on: checked for every run
# and every class, and refuted where the run does not carry the class
def lem.stay(sel: Eng.Run, k: Eng.Cls, -c: U32, -acc: Bytes(), -pd: Eng.Pend,
  -out: List<&2, Eng.Req>) ->
  {Eng.run.stay(sel, k) == True{} : Bool} -> SG(sel, k, c, acc, pd, out):
  match sel k:
    case Eng.RM{} Eng.KSp{}:
      e => no(SG(Eng.RM{}, Eng.KSp{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KHt{}:
      e => no(SG(Eng.RM{}, Eng.KHt{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KCr{}:
      e => no(SG(Eng.RM{}, Eng.KCr{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KLf{}:
      e => no(SG(Eng.RM{}, Eng.KLf{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KCo{}:
      e => no(SG(Eng.RM{}, Eng.KCo{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KCm{}:
      e => no(SG(Eng.RM{}, Eng.KCm{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KDg{}:
      e => {==}
    case Eng.RM{} Eng.KTk{}:
      e => {==}
    case Eng.RM{} Eng.KVc{}:
      e => no(SG(Eng.RM{}, Eng.KVc{}, c, acc, pd, out), e)
    case Eng.RM{} Eng.KCt{}:
      e => no(SG(Eng.RM{}, Eng.KCt{}, c, acc, pd, out), e)
    case Eng.RT{} Eng.KSp{}:
      e => no(SG(Eng.RT{}, Eng.KSp{}, c, acc, pd, out), e)
    case Eng.RT{} Eng.KHt{}:
      e => no(SG(Eng.RT{}, Eng.KHt{}, c, acc, pd, out), e)
    case Eng.RT{} Eng.KCr{}:
      e => no(SG(Eng.RT{}, Eng.KCr{}, c, acc, pd, out), e)
    case Eng.RT{} Eng.KLf{}:
      e => no(SG(Eng.RT{}, Eng.KLf{}, c, acc, pd, out), e)
    case Eng.RT{} Eng.KCo{}:
      e => {==}
    case Eng.RT{} Eng.KCm{}:
      e => {==}
    case Eng.RT{} Eng.KDg{}:
      e => {==}
    case Eng.RT{} Eng.KTk{}:
      e => {==}
    case Eng.RT{} Eng.KVc{}:
      e => {==}
    case Eng.RT{} Eng.KCt{}:
      e => no(SG(Eng.RT{}, Eng.KCt{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KSp{}:
      e => no(SG(Eng.RV{}, Eng.KSp{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KHt{}:
      e => no(SG(Eng.RV{}, Eng.KHt{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KCr{}:
      e => no(SG(Eng.RV{}, Eng.KCr{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KLf{}:
      e => no(SG(Eng.RV{}, Eng.KLf{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KCo{}:
      e => no(SG(Eng.RV{}, Eng.KCo{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KCm{}:
      e => no(SG(Eng.RV{}, Eng.KCm{}, c, acc, pd, out), e)
    case Eng.RV{} Eng.KDg{}:
      e => {==}
    case Eng.RV{} Eng.KTk{}:
      e => {==}
    case Eng.RV{} Eng.KVc{}:
      e => {==}
    case Eng.RV{} Eng.KCt{}:
      e => no(SG(Eng.RV{}, Eng.KCt{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KSp{}:
      e => no(SG(Eng.RN{}, Eng.KSp{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KHt{}:
      e => no(SG(Eng.RN{}, Eng.KHt{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KCr{}:
      e => no(SG(Eng.RN{}, Eng.KCr{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KLf{}:
      e => no(SG(Eng.RN{}, Eng.KLf{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KCo{}:
      e => no(SG(Eng.RN{}, Eng.KCo{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KCm{}:
      e => no(SG(Eng.RN{}, Eng.KCm{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KDg{}:
      e => {==}
    case Eng.RN{} Eng.KTk{}:
      e => {==}
    case Eng.RN{} Eng.KVc{}:
      e => no(SG(Eng.RN{}, Eng.KVc{}, c, acc, pd, out), e)
    case Eng.RN{} Eng.KCt{}:
      e => no(SG(Eng.RN{}, Eng.KCt{}, c, acc, pd, out), e)
    case Eng.RK{} Eng.KSp{}:
      e => {==}
    case Eng.RK{} Eng.KHt{}:
      e => {==}
    case Eng.RK{} Eng.KCr{}:
      e => no(SG(Eng.RK{}, Eng.KCr{}, c, acc, pd, out), e)
    case Eng.RK{} Eng.KLf{}:
      e => no(SG(Eng.RK{}, Eng.KLf{}, c, acc, pd, out), e)
    case Eng.RK{} Eng.KCo{}:
      e => {==}
    case Eng.RK{} Eng.KCm{}:
      e => {==}
    case Eng.RK{} Eng.KDg{}:
      e => {==}
    case Eng.RK{} Eng.KTk{}:
      e => {==}
    case Eng.RK{} Eng.KVc{}:
      e => {==}
    case Eng.RK{} Eng.KCt{}:
      e => no(SG(Eng.RK{}, Eng.KCt{}, c, acc, pd, out), e)
    case Eng.RX{} Eng.KSp{}:
      e => {==}
    case Eng.RX{} Eng.KHt{}:
      e => {==}
    case Eng.RX{} Eng.KCr{}:
      e => no(SG(Eng.RX{}, Eng.KCr{}, c, acc, pd, out), e)
    case Eng.RX{} Eng.KLf{}:
      e => no(SG(Eng.RX{}, Eng.KLf{}, c, acc, pd, out), e)
    case Eng.RX{} Eng.KCo{}:
      e => {==}
    case Eng.RX{} Eng.KCm{}:
      e => {==}
    case Eng.RX{} Eng.KDg{}:
      e => {==}
    case Eng.RX{} Eng.KTk{}:
      e => {==}
    case Eng.RX{} Eng.KVc{}:
      e => {==}
    case Eng.RX{} Eng.KCt{}:
      e => no(SG(Eng.RX{}, Eng.KCt{}, c, acc, pd, out), e)

# The walk
# ========
#
# feed_buf is feed. The byte-at-a-time walk over a block is feed on the
# block's bytes by one induction. The engine's walk moves by adv, and
# every move lands where the byte-at-a-time walk over the bytes it took
# would have: one byte is one step; a run is its bytes stepped one by
# one (each keeps the state and adds itself, lem.stay), and the run
# stops where it says it does (run.len); a body is r + 1 bytes counted
# down; after an upgrade and after a refusal every byte is kept or
# ignored. Then the fuel never matters: however many moves are left,
# the walk ends where the byte-at-a-time walk does.

def slow_is_feed(s: Bytes(), p: Eng.P) ->
  {Eng.feed_buf.slow(s, p) == Eng.feed(Bytes.to_list(s), p) : Eng.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      slow_is_feed(t, Eng.step(p, c))

# Bytes joined
def app_nil(a: Bytes()) -> {Bytes.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %app_nil(t) : {SCon{h, Bytes.append(t, "")} == SCon{h, _} : Bytes()}
      {==}

def app_assoc(a: Bytes(), -b: Bytes(), -c: Bytes()) ->
  {Bytes.append(Bytes.append(a, b), c) == Bytes.append(a, Bytes.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %app_assoc(t, b, c) : {SCon{h, Bytes.append(Bytes.append(t, b), c)} == SCon{h, _} : Bytes()}
      {==}

# a token grown by one byte, then by more, is the token grown by all of them
def push_app(acc: Bytes(), -c: U32, -x: Bytes()) ->
  {Bytes.append(Eng.push(acc, c), x) == Bytes.append(acc, SCon{Chr{c}, x}) : Bytes()}:
  app_assoc(acc, Eng.one(c), x)

def take0(t: Bytes()) -> {String.take(t, 0n) == "" : Bytes()}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

def drop0(t: Bytes()) -> {String.drop(t, 0n) == t : Bytes()}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

# the length of a byte after the first
def len_shift(t: Bytes()) -> {String.length.go(t, 1n) == 1n+String.length.go(t, 0n) : Nat}:
  Bytes.len.shift(t, 0n)

# One byte
def lem.one(p: Eng.P, s: Bytes()) ->
  {Eng.feed_buf.last(Eng.one.step(p, s)) == Eng.feed_buf.slow(s, p) : Eng.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      {==}

# A run
def lem.len0(t: Bytes(), -sel: Eng.Run) -> {Eng.run.len(t, False{}, sel, 0n) == 0n : Nat}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{x}, u}:
      {==}

def lem.shift.at(
  -u: Bytes(), -sel: Eng.Run, -k: Nat, ok: Bool,
  ht: {Eng.run.len(u, True{}, sel, 1n+1n+k) == 1n+Eng.run.len(u, True{}, sel, 1n+k) : Nat},
  hf: {Eng.run.len(u, False{}, sel, 1n+k) == 1n+Eng.run.len(u, False{}, sel, k) : Nat}
) -> {Eng.run.len(u, ok, sel, Eng.run.inc(ok, 1n+k)) ==
  1n+Eng.run.len(u, ok, sel, Eng.run.inc(ok, k)) : Nat}:
  match ok:
    case True{}:
      ht
    case False{}:
      hf

# counting from k + 1 is counting from k, plus one
def lem.shift(+t: Bytes(), go: Bool, +sel: Eng.Run, +k: Nat) ->
  {Eng.run.len(t, go, sel, 1n+k) == 1n+Eng.run.len(t, go, sel, k) : Nat}:
  match t go:
    case SNil{} _:
      {==}
    case SCon{Chr{c}, u} False{}:
      {==}
    case SCon{Chr{c}, u} True{}:
      lem.shift.at(u, sel, k, Eng.run.stay(sel, Eng.cls(c)),
        lem.shift(u, True{}, sel, 1n+k), lem.shift(u, False{}, sel, k))

# what a run takes of s, stepped a byte at a time, is the run's state
# with those bytes added, and what follows is walked from there
def RG(-sel: Eng.Run, -s: Bytes(), -acc: Bytes(), -pd: Eng.Pend,
  -out: List<&2, Eng.Req>) -> Type:
  {Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) ==
    Eng.feed_buf.slow(String.drop(s, Eng.run.len(s, True{}, sel, 0n)),
      Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, Eng.run.len(s, True{}, sel, 0n)))),
        pd, out}) : Eng.P}

def lem.run.at(
  +sel: Eng.Run, +c: U32, +t: Bytes(), +acc: Bytes(), +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, ok: Bool, ih: RG(sel, t, Eng.push(acc, c), pd, out)
) -> {Eng.run.stay(sel, Eng.cls(c)) == ok : Bool} -> RG(sel, SCon{Chr{c}, t}, acc, pd, out):
  match ok:
    case True{}:
      +e =>
        %Equal.sym(Bool, Eng.run.stay(sel, Eng.cls(c)), True{}, e) :
          {Eng.feed_buf.slow(t, Eng.step.at(Eng.st.put(sel, acc), Eng.cls(c), c, pd, out)) ==
            Eng.feed_buf.slow(String.drop(SCon{Chr{c}, t}, Eng.run.len(t, _, sel, Eng.run.inc(_, 0n))),
              Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(SCon{Chr{c}, t},
                Eng.run.len(t, _, sel, Eng.run.inc(_, 0n))))), pd, out}) : Eng.P}
        %Equal.sym(Nat, Eng.run.len(t, True{}, sel, 1n), 1n+Eng.run.len(t, True{}, sel, 0n),
          lem.shift(t, True{}, sel, 0n)) :
          {Eng.feed_buf.slow(t, Eng.step.at(Eng.st.put(sel, acc), Eng.cls(c), c, pd, out)) ==
            Eng.feed_buf.slow(String.drop(SCon{Chr{c}, t}, _),
              Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(SCon{Chr{c}, t}, _))), pd, out}) :
            Eng.P}
        %Equal.sym(Eng.P, Eng.step.at(Eng.st.put(sel, acc), Eng.cls(c), c, pd, out),
          Eng.P{Eng.st.put(sel, Eng.push(acc, c)), pd, out},
          lem.stay(sel, Eng.cls(c), c, acc, pd, out)(e)) :
          {Eng.feed_buf.slow(t, _) ==
            Eng.feed_buf.slow(String.drop(t, Eng.run.len(t, True{}, sel, 0n)),
              Eng.P{Eng.st.put(sel, Bytes.append(acc, SCon{Chr{c}, String.take(t,
                Eng.run.len(t, True{}, sel, 0n))})), pd, out}) : Eng.P}
        %push_app(acc, c, String.take(t, Eng.run.len(t, True{}, sel, 0n))) :
          {Eng.feed_buf.slow(t, Eng.P{Eng.st.put(sel, Eng.push(acc, c)), pd, out}) ==
            Eng.feed_buf.slow(String.drop(t, Eng.run.len(t, True{}, sel, 0n)),
              Eng.P{Eng.st.put(sel, _), pd, out}) : Eng.P}
        ih
    case False{}:
      e =>
        %Equal.sym(Bool, Eng.run.stay(sel, Eng.cls(c)), False{}, e) :
          {Eng.feed_buf.slow(t, Eng.step.at(Eng.st.put(sel, acc), Eng.cls(c), c, pd, out)) ==
            Eng.feed_buf.slow(String.drop(SCon{Chr{c}, t}, Eng.run.len(t, _, sel, Eng.run.inc(_, 0n))),
              Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(SCon{Chr{c}, t},
                Eng.run.len(t, _, sel, Eng.run.inc(_, 0n))))), pd, out}) : Eng.P}
        %Equal.sym(Nat, Eng.run.len(t, False{}, sel, 0n), 0n, lem.len0(t, sel)) :
          {Eng.feed_buf.slow(t, Eng.step.at(Eng.st.put(sel, acc), Eng.cls(c), c, pd, out)) ==
            Eng.feed_buf.slow(String.drop(SCon{Chr{c}, t}, _),
              Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(SCon{Chr{c}, t}, _))), pd, out}) :
            Eng.P}
        %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
          {Eng.feed_buf.slow(t, Eng.step.at(Eng.st.put(sel, acc), Eng.cls(c), c, pd, out)) ==
            Eng.feed_buf.slow(t, Eng.step.at(Eng.st.put(sel, _), Eng.cls(c), c, pd, out)) : Eng.P}
        {==}

def lem.run(+sel: Eng.Run, +s: Bytes(), +acc: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  RG(sel, s, acc, pd, out):
  match s:
    case SNil{}:
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
        {Eng.P{Eng.st.put(sel, acc), pd, out} == Eng.P{Eng.st.put(sel, _), pd, out} : Eng.P}
      {==}
    case SCon{Chr{c}, t}:
      lem.run.at(sel, c, t, acc, pd, out, Eng.run.stay(sel, Eng.cls(c)),
        lem.run(sel, t, Eng.push(acc, c), pd, out))({==})

# a run cut where run.len says: the cut's two halves are what RG names
def lem.cut.took(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, j: Nat, e: {Eng.run.len(s, True{}, sel, 0n) == 1n+j : Nat}) ->
  {Eng.feed_buf.slow(String.drop(s, 1n+j),
    Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, 1n+j))), pd, out}) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  %e : {Eng.feed_buf.slow(String.drop(s, _),
    Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, _))), pd, out}) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}
  Equal.sym(Eng.P, Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}),
    Eng.feed_buf.slow(String.drop(s, Eng.run.len(s, True{}, sel, 0n)),
      Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, Eng.run.len(s, True{}, sel, 0n)))),
        pd, out}),
    lem.run(sel, s, acc, pd, out))

def lem.cut(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +k: Nat) ->
  {Eng.run.len(s, True{}, sel, 0n) == k : Nat} ->
  {Eng.feed_buf.last(Eng.run.cut(sel, acc, s, pd, out, k)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  match k:
    case 0n:
      e => lem.one(Eng.P{Eng.st.put(sel, acc), pd, out}, s)
    case 1n+j:
      e => Equal.trans(Eng.P,
        Eng.feed_buf.last(Eng.one.step(
          Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, 1n+j))), pd, out},
          String.drop(s, 1n+j))),
        Eng.feed_buf.slow(String.drop(s, 1n+j),
          Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, 1n+j))), pd, out}),
        Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}),
        lem.one(Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, 1n+j))), pd, out},
          String.drop(s, 1n+j)),
        lem.cut.took(sel, acc, s, pd, out, j, e))

# Visible ASCII in a run
# ----------------------

# The runs run.fast starts with a span of visible ASCII (33 up to 127):
# a target's and a key's. Every such byte is a token, a digit, a colon, a
# comma or vchar, which both stay on; lem.fast is run.fast counting what
# run.len does.
type Vis is Data:
  VT{}
  VK{}

def vis.sel(v: Vis) -> Eng.Run:
  match v:
    case VT{}:
      Eng.RT{}
    case VK{}:
      Eng.RK{}

# what a Bool that is False rules out
def BT(b: Bool, g: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      g

def lem.vis.sym(v: Vis, co: Bool, cm: Bool, tk: Bool) ->
  {Eng.run.stay(vis.sel(v), Eng.cls.sym(co, cm, tk)) == True{} : Bool}:
  match v co cm tk:
    case VT{} True{} True{} True{}:
      {==}
    case VT{} True{} True{} False{}:
      {==}
    case VT{} True{} False{} True{}:
      {==}
    case VT{} True{} False{} False{}:
      {==}
    case VT{} False{} True{} True{}:
      {==}
    case VT{} False{} True{} False{}:
      {==}
    case VT{} False{} False{} True{}:
      {==}
    case VT{} False{} False{} False{}:
      {==}
    case VK{} True{} True{} True{}:
      {==}
    case VK{} True{} True{} False{}:
      {==}
    case VK{} True{} False{} True{}:
      {==}
    case VK{} True{} False{} False{}:
      {==}
    case VK{} False{} True{} True{}:
      {==}
    case VK{} False{} True{} False{}:
      {==}
    case VK{} False{} False{} True{}:
      {==}
    case VK{} False{} False{} False{}:
      {==}

def lem.vis.vis(v: Vis, +c: U32, al: Bool, dg: Bool) ->
  {Eng.run.stay(vis.sel(v), Eng.cls.vis(c, al, dg)) == True{} : Bool}:
  match v al dg:
    case VT{} True{} True{}:
      {==}
    case VT{} True{} False{}:
      {==}
    case VT{} False{} True{}:
      {==}
    case VT{} False{} False{}:
      lem.vis.sym(VT{}, U32.is_eq(c, 58), U32.is_eq(c, 44), Eng.tsym(c))
    case VK{} True{} True{}:
      {==}
    case VK{} True{} False{}:
      {==}
    case VK{} False{} True{}:
      {==}
    case VK{} False{} False{}:
      lem.vis.sym(VK{}, U32.is_eq(c, 58), U32.is_eq(c, 44), Eng.tsym(c))

def lem.vis.go(v: Vis, +c: U32, x: Bool, y: Bool) ->
  {Bool.and(Bool.not(x), Bool.not(y)) == True{} : Bool} ->
  {Eng.run.stay(vis.sel(v), Eng.cls.go(c, x, y)) == True{} : Bool}:
  match x y:
    case True{} True{}:
      e =>
        %e : BT(_, {Eng.run.stay(vis.sel(v), Eng.cls.go(c, True{}, True{})) == True{} : Bool})
        Unit{}
    case True{} False{}:
      e =>
        %e : BT(_, {Eng.run.stay(vis.sel(v), Eng.cls.go(c, True{}, False{})) == True{} : Bool})
        Unit{}
    case False{} True{}:
      e =>
        %e : BT(_, {Eng.run.stay(vis.sel(v), Eng.cls.go(c, False{}, True{})) == True{} : Bool})
        Unit{}
    case False{} False{}:
      e => lem.vis.vis(v, c, Eng.alpha(c), Eng.digit(c))

# a byte in [33, 127) is one the run stays on
def lem.vis.in(v: Vis, +c: U32) ->
  {Bytes.span.in(c, 33, 127) == True{} : Bool} ->
  {Eng.run.stay(vis.sel(v), Eng.cls(c)) == True{} : Bool}:
  e => lem.vis.go(v, c, U32.is_lt(c, 33), U32.is_le(127, c))(e)

# the run after the span, counted on from it
def VR(-sel: Eng.Run, -s: Bytes()) -> Type:
  {Eng.run.len(s, True{}, sel, 0n) ==
    Nat.add(Bytes.span.go(s, 33, 127),
      Eng.run.len(String.drop(s, Bytes.span.go(s, 33, 127)), True{}, sel, 0n)) : Nat}

def lem.vis.at(+v: Vis, +c: U32, +t: Bytes(), b: Bool, ih: VR(vis.sel(v), t)) ->
  {Bytes.span.in(c, 33, 127) == b : Bool} ->
  {Eng.run.len(SCon{Chr{c}, t}, True{}, vis.sel(v), 0n) ==
    Nat.add(Bytes.span.at(b, t, 33, 127),
      Eng.run.len(String.drop(SCon{Chr{c}, t}, Bytes.span.at(b, t, 33, 127)), True{},
        vis.sel(v), 0n)) : Nat}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        %Equal.sym(Bool, Eng.run.stay(vis.sel(v), Eng.cls(c)), True{}, lem.vis.in(v, c)(e)) :
          {Eng.run.len(t, _, vis.sel(v), Eng.run.inc(_, 0n)) ==
            1n+Nat.add(Bytes.span.go(t, 33, 127),
              Eng.run.len(String.drop(t, Bytes.span.go(t, 33, 127)), True{}, vis.sel(v), 0n)) : Nat}
        Equal.trans(Nat, Eng.run.len(t, True{}, vis.sel(v), 1n),
          1n+Eng.run.len(t, True{}, vis.sel(v), 0n),
          1n+Nat.add(Bytes.span.go(t, 33, 127),
            Eng.run.len(String.drop(t, Bytes.span.go(t, 33, 127)), True{}, vis.sel(v), 0n)),
          lem.shift(t, True{}, vis.sel(v), 0n),
          Equal.cong(Nat, Nat, y => 1n+y, Eng.run.len(t, True{}, vis.sel(v), 0n),
            Nat.add(Bytes.span.go(t, 33, 127),
              Eng.run.len(String.drop(t, Bytes.span.go(t, 33, 127)), True{}, vis.sel(v), 0n)), ih))

def lem.vis.run(+s: Bytes(), +v: Vis) -> VR(vis.sel(v), s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      lem.vis.at(v, c, t, Bytes.span.in(c, 33, 127), lem.vis.run(t, v))({==})

# run.fast counts what run.len does
def lem.fast(+s: Bytes(), +sel: Eng.Run) ->
  {Eng.run.len(s, True{}, sel, 0n) == Eng.run.fast(s, sel) : Nat}:
  match s sel:
    case SNil{} Eng.RT{}:
      {==}
    case SNil{} Eng.RK{}:
      {==}
    case SCon{h, t} Eng.RT{}:
      lem.vis.run(SCon{h, t}, VT{})
    case SCon{h, t} Eng.RK{}:
      lem.vis.run(SCon{h, t}, VK{})
    case _ Eng.RM{}:
      {==}
    case _ Eng.RV{}:
      {==}
    case _ Eng.RN{}:
      {==}
    case _ Eng.RX{}:
      {==}

def lem.go.run(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.run.go(sel, acc, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  lem.cut(sel, acc, s, pd, out, Eng.run.fast(s, sel))(lem.fast(s, sel))

# A value skipped: what the walk is to answer, by whether the byte
# before s was part of the value
def skip.want(go: Bool, c: U32, s: Bytes(), pd: Eng.Pend, out: List<&2, Eng.Req>) -> Eng.P:
  match go:
    case True{}:
      Eng.feed_buf.slow(s, Eng.P{Eng.InLx{}, pd, out})
    case False{}:
      Eng.feed_buf.slow(s, Eng.step(Eng.P{Eng.InLx{}, pd, out}, c))

def lem.skip.at(+x: U32, +t: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>, ok: Bool) ->
  {Eng.run.stay(Eng.RX{}, Eng.cls(x)) == ok : Bool} ->
  {skip.want(ok, x, t, pd, out) ==
    Eng.feed_buf.slow(t, Eng.step(Eng.P{Eng.InLx{}, pd, out}, x)) : Eng.P}:
  match ok:
    case True{}:
      e =>
        %Equal.sym(Eng.P, Eng.step.at(Eng.InLx{}, Eng.cls(x), x, pd, out),
          Eng.P{Eng.InLx{}, pd, out}, lem.stay(Eng.RX{}, Eng.cls(x), x, "", pd, out)(e)) :
          {Eng.feed_buf.slow(t, Eng.P{Eng.InLx{}, pd, out}) == Eng.feed_buf.slow(t, _) : Eng.P}
        {==}
    case False{}:
      e => {==}

def lem.skip(+s: Bytes(), go: Bool, +c: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.skip(s, go, c, pd, out)) == skip.want(go, c, s, pd, out) : Eng.P}:
  match s go:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{Chr{x}, t} False{}:
      {==}
    case SCon{Chr{+x}, t} True{}:
      Equal.trans(Eng.P, Eng.feed_buf.last(Eng.skip(t, Eng.run.stay(Eng.RX{}, Eng.cls(x)), x, pd, out)),
        skip.want(Eng.run.stay(Eng.RX{}, Eng.cls(x)), x, t, pd, out),
        Eng.feed_buf.slow(t, Eng.step(Eng.P{Eng.InLx{}, pd, out}, x)),
        lem.skip(t, Eng.run.stay(Eng.RX{}, Eng.cls(x)), x, pd, out),
        lem.skip.at(x, t, pd, out, Eng.run.stay(Eng.RX{}, Eng.cls(x)))({==}))

# A method or a name, from its first byte: the state before it steps
# each byte the run carries as the run's empty state does
def lem.ent.step(e: Eng.Ent, k: Eng.Cls, -c: U32, -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.run.stay(Eng.ent.sel(e), k) == True{} : Bool} ->
  {Eng.step.at(Eng.ent.st(e), k, c, pd, out) ==
    Eng.step.at(Eng.st.put(Eng.ent.sel(e), ""), k, c, pd, out) : Eng.P}:
  match e k:
    case Eng.EMeth{} Eng.KSp{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KSp{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KSp{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KHt{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KHt{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KHt{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KCr{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KCr{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KCr{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KLf{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KLf{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KLf{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KCo{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KCo{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KCo{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KCm{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KCm{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KCm{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KDg{}:
      e => {==}
    case Eng.EMeth{} Eng.KTk{}:
      e => {==}
    case Eng.EMeth{} Eng.KVc{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KVc{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KVc{}, c, pd, out) : Eng.P}, e)
    case Eng.EMeth{} Eng.KCt{}:
      e => no({Eng.step.at(Eng.Pre{}, Eng.KCt{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RM{}, ""), Eng.KCt{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KSp{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KSp{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KSp{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KHt{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KHt{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KHt{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KCr{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KCr{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KCr{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KLf{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KLf{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KLf{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KCo{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KCo{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KCo{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KCm{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KCm{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KCm{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KDg{}:
      e => {==}
    case Eng.EName{} Eng.KTk{}:
      e => {==}
    case Eng.EName{} Eng.KVc{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KVc{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KVc{}, c, pd, out) : Eng.P}, e)
    case Eng.EName{} Eng.KCt{}:
      e => no({Eng.step.at(Eng.Lin{}, Eng.KCt{}, c, pd, out) ==
        Eng.step.at(Eng.st.put(Eng.RN{}, ""), Eng.KCt{}, c, pd, out) : Eng.P}, e)

# a Nat that is one more than something is not zero
def ZN(n: Nat, g: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      g

def EG(-e: Eng.Ent, -s: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) -> Type:
  {Eng.feed_buf.slow(s, Eng.P{Eng.st.put(Eng.ent.sel(e), ""), pd, out}) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.ent.st(e), pd, out}) : Eng.P}

def lem.ent.at(+e: Eng.Ent, +c: U32, +t: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  j: Nat, ok: Bool) ->
  {Eng.run.stay(Eng.ent.sel(e), Eng.cls(c)) == ok : Bool} ->
  {Eng.run.len(t, ok, Eng.ent.sel(e), Eng.run.inc(ok, 0n)) == 1n+j : Nat} ->
  EG(e, SCon{Chr{c}, t}, pd, out):
  match ok:
    case True{}:
      st => eq =>
        %lem.ent.step(e, Eng.cls(c), c, pd, out)(st) :
          {Eng.feed_buf.slow(t, _) ==
            Eng.feed_buf.slow(t, Eng.step.at(Eng.ent.st(e), Eng.cls(c), c, pd, out)) : Eng.P}
        {==}
    case False{}:
      st => eq =>
        %Equal.trans(Nat, 0n, Eng.run.len(t, False{}, Eng.ent.sel(e), 0n), 1n+j,
          Equal.sym(Nat, Eng.run.len(t, False{}, Eng.ent.sel(e), 0n), 0n,
            lem.len0(t, Eng.ent.sel(e))), eq) :
          ZN(_, EG(e, SCon{Chr{c}, t}, pd, out))
        Unit{}

def lem.ent.first(+e: Eng.Ent, s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>, j: Nat) ->
  {Eng.run.len(s, True{}, Eng.ent.sel(e), 0n) == 1n+j : Nat} -> EG(e, s, pd, out):
  match s:
    case SNil{}:
      eq =>
        %eq : ZN(_, EG(e, SNil{}, pd, out))
        Unit{}
    case SCon{Chr{+c}, t}:
      eq => lem.ent.at(e, c, t, pd, out, j, Eng.run.stay(Eng.ent.sel(e), Eng.cls(c)))({==}, eq)

def lem.ent.cut(+e: Eng.Ent, +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>, +k: Nat) ->
  {Eng.run.len(s, True{}, Eng.ent.sel(e), 0n) == k : Nat} ->
  {Eng.feed_buf.last(Eng.ent.cut(e, s, pd, out, k)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.ent.st(e), pd, out}) : Eng.P}:
  match k:
    case 0n:
      eq => lem.one(Eng.P{Eng.ent.st(e), pd, out}, s)
    case 1n+j:
      +eq => Equal.trans(Eng.P, Eng.feed_buf.last(Eng.run.cut(Eng.ent.sel(e), "", s, pd, out, 1n+j)),
        Eng.feed_buf.slow(s, Eng.P{Eng.st.put(Eng.ent.sel(e), ""), pd, out}),
        Eng.feed_buf.slow(s, Eng.P{Eng.ent.st(e), pd, out}),
        lem.cut(Eng.ent.sel(e), "", s, pd, out, 1n+j)(eq),
        lem.ent.first(e, s, pd, out, j)(eq))

def lem.ent(+e: Eng.Ent, +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.ent.go(e, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.ent.st(e), pd, out}) : Eng.P}:
  lem.ent.cut(e, s, pd, out, Eng.run.len(s, True{}, Eng.ent.sel(e), 0n))({==})

# A body
def lem.bod.at(+q: Nat, +b: Bytes(), +c: U32, +t: Bytes(), +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, d: Bool) ->
  {Eng.feed_buf.last(Eng.bod.at(1n+q, b, SCon{Chr{c}, t}, pd, out, d)) ==
    Eng.feed_buf.last(Eng.bod.at(q, Eng.push(b, c), t, pd, out, d)) : Eng.P}:
  match d:
    case False{}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Eng.P{Eng.Bod{Nat.sub(1n+q, _), Bytes.append(b, SCon{Chr{c}, t})}, pd, out} ==
          Eng.P{Eng.Bod{Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Eng.push(b, c), t)},
            pd, out} : Eng.P}
      %push_app(b, c, t) :
        {Eng.P{Eng.Bod{Nat.sub(q, String.length.go(t, 0n)), _}, pd, out} ==
          Eng.P{Eng.Bod{Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Eng.push(b, c), t)},
            pd, out} : Eng.P}
      {==}
    case True{}:
      %push_app(b, c, String.take(t, 1n+q)) :
        {Eng.feed_buf.slow(String.drop(t, 1n+q), Eng.emit(pd, _, out)) ==
          Eng.feed_buf.slow(String.drop(t, 1n+q),
            Eng.emit(pd, Bytes.append(Eng.push(b, c), String.take(t, 1n+q)), out)) : Eng.P}
      {==}

def lem.bod(+s: Bytes(), +r: Nat, +b: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.bod.go(r, b, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.Bod{r, b}, pd, out}) : Eng.P}:
  match s r:
    case SNil{} 0n:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_nil(b)) :
        {Eng.P{Eng.Bod{0n, _}, pd, out} == Eng.P{Eng.Bod{0n, b}, pd, out} : Eng.P}
      {==}
    case SNil{} 1n+q:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_nil(b)) :
        {Eng.P{Eng.Bod{1n+q, _}, pd, out} == Eng.P{Eng.Bod{1n+q, b}, pd, out} : Eng.P}
      {==}
    case SCon{Chr{c}, t} 0n:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Eng.feed_buf.last(Eng.bod.at(0n, b, SCon{Chr{c}, t}, pd, out, Nat.is_lt(0n, _))) ==
          Eng.feed_buf.slow(t, Eng.emit(pd, Eng.push(b, c), out)) : Eng.P}
      %Equal.sym(Bytes(), String.take(t, 0n), "", take0(t)) :
        {Eng.feed_buf.slow(String.drop(t, 0n), Eng.emit(pd, Bytes.append(b, SCon{Chr{c}, _}), out)) ==
          Eng.feed_buf.slow(t, Eng.emit(pd, Eng.push(b, c), out)) : Eng.P}
      %Equal.sym(Bytes(), String.drop(t, 0n), t, drop0(t)) :
        {Eng.feed_buf.slow(_, Eng.emit(pd, Eng.push(b, c), out)) ==
          Eng.feed_buf.slow(t, Eng.emit(pd, Eng.push(b, c), out)) : Eng.P}
      {==}
    case SCon{Chr{c}, t} 1n+q:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Eng.feed_buf.last(Eng.bod.at(1n+q, b, SCon{Chr{c}, t}, pd, out, Nat.is_lt(1n+q, _))) ==
          Eng.feed_buf.slow(t, Eng.P{Eng.Bod{q, Eng.push(b, c)}, pd, out}) : Eng.P}
      Equal.trans(Eng.P,
        Eng.feed_buf.last(Eng.bod.at(1n+q, b, SCon{Chr{c}, t}, pd, out,
          Nat.is_lt(q, String.length.go(t, 0n)))),
        Eng.feed_buf.last(Eng.bod.at(q, Eng.push(b, c), t, pd, out,
          Nat.is_lt(q, String.length.go(t, 0n)))),
        Eng.feed_buf.slow(t, Eng.P{Eng.Bod{q, Eng.push(b, c)}, pd, out}),
        lem.bod.at(q, b, c, t, pd, out, Nat.is_lt(q, String.length.go(t, 0n))),
        lem.bod(t, q, Eng.push(b, c), pd, out))

# A chunk's data, the same way
def lem.chd.at(+q: Nat, +b: Bytes(), +c: U32, +t: Bytes(), +left: U32, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, d: Bool) ->
  {Eng.feed_buf.last(Eng.chd.at(1n+q, b, SCon{Chr{c}, t}, left, pd, out, d)) ==
    Eng.feed_buf.last(Eng.chd.at(q, Eng.push(b, c), t, left, pd, out, d)) : Eng.P}:
  match d:
    case False{}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Eng.P{Eng.Chd{Nat.sub(1n+q, _), Bytes.append(b, SCon{Chr{c}, t}), left}, pd, out} ==
          Eng.P{Eng.Chd{Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Eng.push(b, c), t), left},
            pd, out} : Eng.P}
      %push_app(b, c, t) :
        {Eng.P{Eng.Chd{Nat.sub(q, String.length.go(t, 0n)), _, left}, pd, out} ==
          Eng.P{Eng.Chd{Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Eng.push(b, c), t), left},
            pd, out} : Eng.P}
      {==}
    case True{}:
      %push_app(b, c, String.take(t, 1n+q)) :
        {Eng.feed_buf.slow(String.drop(t, 1n+q), Eng.P{Eng.Chk{Eng.CDataCr{}, 0, _, left}, pd, out}) ==
          Eng.feed_buf.slow(String.drop(t, 1n+q),
            Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Bytes.append(Eng.push(b, c), String.take(t, 1n+q)), left},
              pd, out}) : Eng.P}
      {==}

def lem.chd(+s: Bytes(), +r: Nat, +b: Bytes(), +left: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.chd.go(r, b, s, left, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.Chd{r, b, left}, pd, out}) : Eng.P}:
  match s r:
    case SNil{} 0n:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_nil(b)) :
        {Eng.P{Eng.Chd{0n, _, left}, pd, out} == Eng.P{Eng.Chd{0n, b, left}, pd, out} : Eng.P}
      {==}
    case SNil{} 1n+q:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_nil(b)) :
        {Eng.P{Eng.Chd{1n+q, _, left}, pd, out} == Eng.P{Eng.Chd{1n+q, b, left}, pd, out} : Eng.P}
      {==}
    case SCon{Chr{c}, t} 0n:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Eng.feed_buf.last(Eng.chd.at(0n, b, SCon{Chr{c}, t}, left, pd, out, Nat.is_lt(0n, _))) ==
          Eng.feed_buf.slow(t, Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Eng.push(b, c), left}, pd, out}) : Eng.P}
      %Equal.sym(Bytes(), String.take(t, 0n), "", take0(t)) :
        {Eng.feed_buf.slow(String.drop(t, 0n),
          Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Bytes.append(b, SCon{Chr{c}, _}), left}, pd, out}) ==
          Eng.feed_buf.slow(t, Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Eng.push(b, c), left}, pd, out}) : Eng.P}
      %Equal.sym(Bytes(), String.drop(t, 0n), t, drop0(t)) :
        {Eng.feed_buf.slow(_, Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Eng.push(b, c), left}, pd, out}) ==
          Eng.feed_buf.slow(t, Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Eng.push(b, c), left}, pd, out}) : Eng.P}
      {==}
    case SCon{Chr{c}, t} 1n+q:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Eng.feed_buf.last(Eng.chd.at(1n+q, b, SCon{Chr{c}, t}, left, pd, out, Nat.is_lt(1n+q, _))) ==
          Eng.feed_buf.slow(t, Eng.P{Eng.Chd{q, Eng.push(b, c), left}, pd, out}) : Eng.P}
      Equal.trans(Eng.P,
        Eng.feed_buf.last(Eng.chd.at(1n+q, b, SCon{Chr{c}, t}, left, pd, out,
          Nat.is_lt(q, String.length.go(t, 0n)))),
        Eng.feed_buf.last(Eng.chd.at(q, Eng.push(b, c), t, left, pd, out,
          Nat.is_lt(q, String.length.go(t, 0n)))),
        Eng.feed_buf.slow(t, Eng.P{Eng.Chd{q, Eng.push(b, c), left}, pd, out}),
        lem.chd.at(q, b, c, t, left, pd, out, Nat.is_lt(q, String.length.go(t, 0n))),
        lem.chd(t, q, Eng.push(b, c), left, pd, out))

# After an upgrade, and after a refusal
def lem.rest(+s: Bytes(), +bs: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.slow(s, Eng.P{Eng.Rest{bs}, pd, out}) ==
    Eng.P{Eng.Rest{Bytes.append(bs, s)}, pd, out} : Eng.P}:
  match s:
    case SNil{}:
      %Equal.sym(Bytes(), Bytes.append(bs, ""), bs, app_nil(bs)) :
        {Eng.P{Eng.Rest{bs}, pd, out} == Eng.P{Eng.Rest{_}, pd, out} : Eng.P}
      {==}
    case SCon{Chr{c}, t}:
      %push_app(bs, c, t) :
        {Eng.feed_buf.slow(t, Eng.P{Eng.Rest{Eng.push(bs, c)}, pd, out}) ==
          Eng.P{Eng.Rest{_}, pd, out} : Eng.P}
      lem.rest(t, Eng.push(bs, c), pd, out)

def lem.bad(s: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.slow(s, Eng.P{Eng.Bad{}, pd, out}) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      lem.bad(t, pd, out)

# Every move
def lem.adv.at(st: Eng.St, +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.adv.at(st, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{st, pd, out}) : Eng.P}:
  match st:
    case Eng.InM{m}:
      lem.go.run(Eng.RM{}, m, s, pd, out)
    case Eng.InT{p}:
      lem.go.run(Eng.RT{}, p, s, pd, out)
    case Eng.InV{v}:
      lem.go.run(Eng.RV{}, v, s, pd, out)
    case Eng.InN{n}:
      lem.go.run(Eng.RN{}, n, s, pd, out)
    case Eng.InLk{k}:
      lem.go.run(Eng.RK{}, k, s, pd, out)
    case Eng.InLx{}:
      lem.skip(s, True{}, 0, pd, out)
    case Eng.Bod{r, b}:
      lem.bod(s, r, b, pd, out)
    case Eng.Rest{bs}:
      Equal.sym(Eng.P, Eng.feed_buf.slow(s, Eng.P{Eng.Rest{bs}, pd, out}),
        Eng.P{Eng.Rest{Bytes.append(bs, s)}, pd, out}, lem.rest(s, bs, pd, out))
    case Eng.Bad{}:
      Equal.sym(Eng.P, Eng.feed_buf.slow(s, Eng.P{Eng.Bad{}, pd, out}),
        Eng.P{Eng.Bad{}, pd, out}, lem.bad(s, pd, out))
    case Eng.Pre{}:
      lem.ent(Eng.EMeth{}, s, pd, out)
    case Eng.PreLf{}:
      lem.one(Eng.P{Eng.PreLf{}, pd, out}, s)
    case Eng.CrM{}:
      lem.one(Eng.P{Eng.CrM{}, pd, out}, s)
    case Eng.Lin{}:
      lem.ent(Eng.EName{}, s, pd, out)
    case Eng.InL0{}:
      lem.one(Eng.P{Eng.InL0{}, pd, out}, s)
    case Eng.InL{v}:
      lem.one(Eng.P{Eng.InL{v}, pd, out}, s)
    case Eng.InLt{v}:
      lem.one(Eng.P{Eng.InLt{v}, pd, out}, s)
    case Eng.InLc{t, a, b, x}:
      lem.one(Eng.P{Eng.InLc{t, a, b, x}, pd, out}, s)
    case Eng.InLe0{}:
      lem.one(Eng.P{Eng.InLe0{}, pd, out}, s)
    case Eng.InLe{v}:
      lem.one(Eng.P{Eng.InLe{v}, pd, out}, s)
    case Eng.Chk{pos, n, b, left}:
      lem.one(Eng.P{Eng.Chk{pos, n, b, left}, pd, out}, s)
    case Eng.Chd{r, b, left}:
      lem.chd(s, r, b, left, pd, out)
    case Eng.InLu{t, w}:
      lem.one(Eng.P{Eng.InLu{t, w}, pd, out}, s)
    case Eng.InLk0{}:
      lem.one(Eng.P{Eng.InLk0{}, pd, out}, s)
    case Eng.InLv{v}:
      lem.one(Eng.P{Eng.InLv{v}, pd, out}, s)
    case Eng.CrL{}:
      lem.one(Eng.P{Eng.CrL{}, pd, out}, s)

def lem.adv(+s: Bytes(), p: Eng.P) ->
  {Eng.feed_buf.last(Eng.adv(s, p)) == Eng.feed_buf.slow(s, p) : Eng.P}:
  match p:
    case Eng.P{st, pd, out}:
      lem.adv.at(st, s, pd, out)

# the fuel never matters
def lem.go(n: Nat, q: Eng.P & Bytes()) ->
  {Eng.feed_buf.go(n, q) == Eng.feed_buf.last(q) : Eng.P}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match q:
        case (p, SNil{}):
          {==}
        case (+p, SCon{+h, +t}):
          Equal.trans(Eng.P, Eng.feed_buf.go(m, Eng.adv(SCon{h, t}, p)),
            Eng.feed_buf.last(Eng.adv(SCon{h, t}, p)), Eng.feed_buf.slow(SCon{h, t}, p),
            lem.go(m, Eng.adv(SCon{h, t}, p)), lem.adv(SCon{h, t}, p))

def Laws.feed_buf_is_feed(b, p):
  Equal.trans(Eng.P, Eng.feed_buf(b, p), Eng.feed_buf.slow(b, p), Eng.feed(Bytes.to_list(b), p),
    lem.go(Bytes.len(b), (p, b)), slow_is_feed(b, p))

def Laws.feed_buf_split(a, b, p):
  %Equal.sym(Eng.P, Eng.feed_buf(Bytes.append(a, b), p),
    Eng.feed(Bytes.to_list(Bytes.append(a, b)), p), Laws.feed_buf_is_feed(Bytes.append(a, b), p)) :
    {_ == Eng.feed_buf(b, Eng.feed_buf(a, p)) : Eng.P}
  %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(a, b)),
    List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), Bytes.to_list_append(a, b)) :
    {Eng.feed(_, p) == Eng.feed_buf(b, Eng.feed_buf(a, p)) : Eng.P}
  %Equal.sym(Eng.P, Eng.feed(List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), p),
    Eng.feed(Bytes.to_list(b), Eng.feed(Bytes.to_list(a), p)),
    Laws.feed_split(Bytes.to_list(a), Bytes.to_list(b), p)) :
    {_ == Eng.feed_buf(b, Eng.feed_buf(a, p)) : Eng.P}
  %Laws.feed_buf_is_feed(a, p) :
    {Eng.feed(Bytes.to_list(b), _) == Eng.feed_buf(b, Eng.feed_buf(a, p)) : Eng.P}
  Equal.sym(Eng.P, Eng.feed_buf(b, Eng.feed_buf(a, p)),
    Eng.feed(Bytes.to_list(b), Eng.feed_buf(a, p)), Laws.feed_buf_is_feed(b, Eng.feed_buf(a, p)))

def Laws.bad_feeds_buf(s, pd, out):
  %Equal.sym(Eng.P, Eng.feed_buf(s, Eng.P{Eng.Bad{}, pd, out}),
    Eng.feed(Bytes.to_list(s), Eng.P{Eng.Bad{}, pd, out}),
    Laws.feed_buf_is_feed(s, Eng.P{Eng.Bad{}, pd, out})) :
    {_ == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  Laws.bad_feeds(Bytes.to_list(s), pd, out)

# the runtime compares two blocks by their order; at the first pair of
# bytes it says LT or GT and stops, or EQ and goes on, which is the
# walk's answer whatever the pair is
def eq_is_spec.step(-xt: Bytes(), -yt: Bytes(), c: Cmp,
  ih: {Cmp.is_eq(String.order(xt, yt)) == Spec.eq(xt, yt) : Bool}) ->
  {Cmp.is_eq(String.order.step(xt, yt, c)) == Bool.and(Cmp.is_eq(c), Spec.eq(xt, yt)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      ih
    case GT{}:
      {==}

def eq_is_spec(+a: Bytes(), +b: Bytes()) ->
  {Eng.bytes.eq(a, b) == Spec.eq(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{y}, u}:
      {==}
    case SCon{Chr{x}, t} SNil{}:
      {==}
    case SCon{Chr{x}, t} SCon{Chr{y}, u}:
      eq_is_spec.step(t, u, U32.cmp(x, y), eq_is_spec(t, u))

# The lookup's walk: what it has found so far, else the reference's
# answer for the rest of the table
def alt(acc: Maybe<&2, Eng.Fld>, r: Eng.Fld) -> Eng.Fld:
  match acc:
    case None{}:
      r
    case Some{g}:
      g

def alt_hit(b: Bool, -f: Eng.Fld, -r: Eng.Fld) ->
  {alt(Eng.fld.hit.at(b, f), r) == Eng.fld.pick(b, f, r) : Eng.Fld}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def scan_step(acc: Maybe<&2, Eng.Fld>, +k: Bytes(), +n: Bytes(), +f: Eng.Fld, +r: Eng.Fld) ->
  {alt(Eng.fld.hit(acc, String.order(k, n), f), r) == alt(acc, Eng.fld.pick(Spec.eq(k, n), f, r)) :
    Eng.Fld}:
  match acc:
    case None{}:
      %eq_is_spec(k, n) : {alt(Eng.fld.hit.at(Eng.bytes.eq(k, n), f), r) ==
        alt(None{}, Eng.fld.pick(_, f, r)) : Eng.Fld}
      alt_hit(Eng.bytes.eq(k, n), f, r)
    case Some{g}:
      {==}

def scan_is(+tbl: List<&2, Eng.Known>, +k: Bytes(), +acc: Maybe<&2, Eng.Fld>) ->
  {Eng.fld.scan(tbl, (k, acc)) == alt(acc, Spec.find(k, tbl)) : Eng.Fld}:
  match tbl:
    case Nil{}:
      match acc:
        case None{}:
          {==}
        case Some{g}:
          {==}
    case Con{h, t}:
      match h:
        case Eng.Known{+n, +f}:
          Equal.trans(Eng.Fld, Eng.fld.scan(t, (k, Eng.fld.hit(acc, String.order(k, n), f))),
            alt(Eng.fld.hit(acc, String.order(k, n), f), Spec.find(k, t)),
            alt(acc, Eng.fld.pick(Spec.eq(k, n), f, Spec.find(k, t))),
            scan_is(t, k, Eng.fld.hit(acc, String.order(k, n), f)),
            scan_step(acc, k, n, f, Spec.find(k, t)))

def Laws.cls_is_spec():
  {==}

def Laws.lower_is_spec():
  {==}

def Laws.lows_is_spec():
  {==}

def Laws.field_by_bytes(k):
  scan_is(Eng.fld.table(), k, None{})

# a Transfer-Encoding's line refused: whatever the message held, a
# refusal keeps it
def te.no(pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.te.at(False{}, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match fx:
        case Eng.Fx{a, b, c}:
          {==}

def Laws.te_chunked_only(v, pd, out, e):
  %Equal.sym(Bool, Eng.bytes.eq(Eng.lows(v), Eng.te.lit()), Spec.eq(Eng.lows(v), Eng.te.lit()),
    eq_is_spec(Eng.lows(v), Eng.te.lit())) : {Eng.step.te.at(_, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Bool, Spec.eq(Eng.lows(v), "chunked"), False{}, e) :
    {Eng.step.te.at(_, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  te.no(pd, out)

def te.twice(ok: Bool, -m: Eng.Meth, -path: Bytes(), -l: Eng.Cl, -cl: Bool, -h: Eng.Hosts, -ws: Eng.Up,
  -v10: Bool, -ka: Bool, -out: List<&2, Eng.Req>) ->
  {Eng.step.te.at(ok, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, True{}}}, out) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, True{}}}, out} : Eng.P}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.te_once(v, m, path, l, cl, h, ws, v10, ka, out):
  te.twice(Eng.bytes.eq(Eng.lows(v), Eng.te.lit()), m, path, l, cl, h, ws, v10, ka, out)

def Laws.te_cl_refused(m, path, v, cl, h, ws, v10, ka, out):
  match h v10:
    case Eng.H0{} True{}:
      {==}
    case Eng.H1{} True{}:
      {==}
    case Eng.H2{} True{}:
      {==}
    case Eng.H0{} False{}:
      {==}
    case Eng.H1{} False{}:
      {==}
    case Eng.H2{} False{}:
      {==}

def Laws.te_10_refused(m, path, l, cl, h, ws, ka, out):
  match h:
    case Eng.H0{}:
      {==}
    case Eng.H1{}:
      {==}
    case Eng.H2{}:
      {==}

def Laws.chunk_bare_lf(pos, n, b, left, pd, out, e):
  match pos:
    case Eng.CSize0{}:
      {==}
    case Eng.CSize{}:
      {==}
    case Eng.CBws{}:
      {==}
    case Eng.CName0{}:
      {==}
    case Eng.CName{}:
      {==}
    case Eng.CNameWs{}:
      {==}
    case Eng.CVal0{}:
      {==}
    case Eng.CToken{}:
      {==}
    case Eng.CQuoted{}:
      {==}
    case Eng.CEscape{}:
      {==}
    case Eng.CClosed{}:
      {==}
    case Eng.CLf{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.Chk{Eng.CLf{}, n, b, left}, pd, out}, 10) ==
        Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.CDataCr{}:
      {==}
    case Eng.CDataLf{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.Chk{Eng.CDataLf{}, n, b, left}, pd, out}, 10) ==
        Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.CTrail{}:
      {==}
    case Eng.CTName{}:
      {==}
    case Eng.CTVal{}:
      {==}
    case Eng.CTLf{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.Chk{Eng.CTLf{}, n, b, left}, pd, out}, 10) ==
        Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.CEnd{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.Chk{Eng.CEnd{}, n, b, left}, pd, out}, 10) ==
        Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}

def Laws.clen_disagree(v, w, m, path, cl, h, ws, fx, out, e):
  %Equal.sym(Bool, U32.is_eq(w, v), False{}, e) :
    {Eng.step.clen.dup(Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, fx}, out, _) ==
      Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, fx}, out} : Eng.P}
  {==}

def Laws.host_once(m, path, l, cl, h, ws, v10, ka, te, out, e):
  match h v10:
    case Eng.H0{} True{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, Eng.H0{}, ws, Eng.Fx{True{}, ka, te}}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, Eng.H0{}, ws, Eng.Fx{True{}, ka, te}}, out} : Eng.P})
      Unit{}
    case Eng.H1{} True{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{True{}, ka, te}}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{True{}, ka, te}}, out} : Eng.P})
      Unit{}
    case Eng.H2{} True{}:
      {==}
    case Eng.H0{} False{}:
      {==}
    case Eng.H1{} False{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{False{}, ka, te}}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{False{}, ka, te}}, out} : Eng.P})
      Unit{}
    case Eng.H2{} False{}:
      {==}

def Laws.rest_feeds(s, bs, pd, out):
  Equal.trans(Eng.P, Eng.feed_buf(s, Eng.P{Eng.Rest{bs}, pd, out}),
    Eng.feed_buf.slow(s, Eng.P{Eng.Rest{bs}, pd, out}),
    Eng.P{Eng.Rest{Bytes.append(bs, s)}, pd, out},
    lem.go(Bytes.len(s), (Eng.P{Eng.Rest{bs}, pd, out}, s)), lem.rest(s, bs, pd, out))

def name_bad(
  k: Eng.Cls, c: U32, n: Bytes(), pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.name(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InN{n}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InN{n}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InN{n}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InN{n}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def Laws.name_refuses(c, n, pd, out, e):
  name_bad(Eng.cls(c), c, n, pd, out, e)

def line_bad(
  k: Eng.Cls, c: U32, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.line(k) == False{} : Bool}
) -> {Eng.step.at(Eng.Lin{}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.Lin{}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.Lin{}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.Lin{}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def Laws.line_refuses(c, pd, out, e):
  line_bad(Eng.cls(c), c, pd, out, e)

def clen_bad(
  k: Eng.Cls, c: U32, v: U32, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.clen(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InL{v}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def Laws.clen_refuses(c, v, pd, out, e):
  clen_bad(Eng.cls(c), c, v, pd, out, e)

def target_bad(
  k: Eng.Cls, c: U32, p: Bytes(), pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.target(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InT{p}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.target_refuses(c, p, pd, out, e):
  target_bad(Eng.cls(c), c, p, pd, out, e)

def value_bad(
  k: Eng.Cls, c: U32, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLx{}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.value_refuses(c, pd, out, e):
  value_bad(Eng.cls(c), c, pd, out, e)

def conn_bad(
  k: Eng.Cls, c: U32, t: Bytes(), a: Bool, b: Bool, x: Bool, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLc{t, a, b, x}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.conn_refuses(c, t, a, b, x, pd, out, e):
  conn_bad(Eng.cls(c), c, t, a, b, x, pd, out, e)

def Laws.parse_get():
  {==}

def Laws.parse_body():
  {==}

def Laws.parse_hash_twin():
  {==}

def Laws.parse_agree():
  {==}

def Laws.parse_upgrade():
  {==}

def Laws.rest_upgrade():
  {==}

def Laws.refuse_space_colon():
  {==}

def Laws.refuse_te_space_colon():
  {==}

def Laws.refuse_te():
  {==}

def Laws.refuse_two_lengths():
  {==}

def Laws.refuse_wrap():
  {==}

def Laws.refuse_past_cap():
  {==}

def Laws.refuse_not_digits():
  {==}

def Laws.refuse_list():
  {==}

def Laws.refuse_fold():
  {==}

def Laws.refuse_bare_lf():
  {==}

def Laws.refuse_no_colon():
  {==}

def Laws.refuse_target_cr():
  {==}

def Laws.refuse_no_host():
  {==}

def Laws.refuse_two_hosts():
  {==}

def Laws.refuse_version():
  {==}

def Laws.refuse_after_one():
  {==}

def Laws.path_query():
  {==}

def Laws.health_closing():
  {==}

def Laws.health_is_built():
  {==}

def Laws.root_is_built():
  {==}

def Laws.missing_is_built():
  {==}

def Laws.method_is_built():
  {==}

def Laws.bad_is_built():
  {==}

def Laws.head_of_health():
  {==}

def Laws.head_of_missing():
  {==}

def Laws.route_health():
  {==}

def Laws.route_root():
  {==}

def Laws.route_echo():
  {==}

def Laws.route_events():
  {==}

def Laws.route_missing():
  {==}

def Laws.route_files():
  {==}

def Laws.route_files_index():
  {==}

def Laws.route_files_fixed():
  {==}

def Laws.routes_distinct():
  {==}

def Laws.routes_distinct_root():
  {==}

def Laws.route_empty(path):
  {==}

def Laws.norm_climb():
  {==}

def Laws.norm_deep_climb():
  {==}

def Laws.norm_dots():
  {==}

def Laws.norm_flat():
  {==}

# Once the normaliser has refused, nothing after revives the path.
def lem.norm_none(ss: List<&2, List<&2, U32>>) ->
  {None{} == Eng.norm.go(ss, None{}) : Maybe<&2, List<&2, List<&2, U32>>>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      lem.norm_none(t)

def Laws.norm_climb_refused(ss):
  %lem.norm_none(ss) : {Eng.norm.rev(_) == None{} : Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

def Laws.norm_climb_cancels(s, ss, e):
  %Equal.sym(Eng.Piece, Eng.piece(s), Eng.Name{}, e) :
    {Eng.norm.rev(Eng.norm.go(Con{[46, 46], ss}, Eng.norm.step(_, s, Nil{}))) ==
      Eng.norm(ss) : Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

# path_safe: the rule LAWS.bend states is, segment by segment, the rule
# the guard in fnames.of checks, so whatever the guard lets through
# keeps it; the clean gate only ever refuses more.
def lem.bytes(bs: List<&2, U32>) -> {Laws.seg_bytes(bs) == Eng.fname.bytes(bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      %lem.bytes(t) : {Bool.and(Laws.seg_byte(c), Laws.seg_bytes(t)) ==
        Bool.and(Eng.fname.byte(c), _) : Bool}
      {==}

def lem.seg(dot: Bool, s: List<&2, U32>) -> {Laws.seg_ok(dot, s) == Eng.fname.ok(dot, s) : Bool}:
  match dot:
    case True{}:
      match s:
        case Nil{}:
          {==}
        case Con{c, t}:
          %lem.bytes(Con{c, t}) : {Bool.and(Laws.seg_lead(True{}, c, Con{c, t}),
            Laws.seg_bytes(Con{c, t})) == Bool.and(Eng.fname.lead(True{}, c, Con{c, t}), _) : Bool}
          {==}
    case False{}:
      match s:
        case Nil{}:
          {==}
        case Con{c, t}:
          %lem.bytes(Con{c, t}) : {Bool.and(Laws.seg_lead(False{}, c, Con{c, t}),
            Laws.seg_bytes(Con{c, t})) == Bool.and(Eng.fname.lead(False{}, c, Con{c, t}), _) : Bool}
          {==}

def lem.segs(+dot: Bool, ss: List<&2, List<&2, U32>>) ->
  {Laws.segs_ok(dot, ss) == Eng.fnames.ok(dot, ss) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      %lem.segs(dot, t) : {Bool.and(Laws.seg_ok(dot, s), Laws.segs_ok(dot, t)) ==
        Bool.and(Eng.fname.ok(dot, s), _) : Bool}
      %lem.seg(dot, s) : {Bool.and(Laws.seg_ok(dot, s), Laws.segs_ok(dot, t)) ==
        Bool.and(_, Laws.segs_ok(dot, t)) : Bool}
      {==}

def lem.keep(+dot: Bool, +ss: List<&2, List<&2, U32>>, b: Bool) ->
  {Eng.fnames.ok(dot, ss) == b : Bool} ->
  {Laws.safe(dot, Eng.fnames.keep(ss, b)) == True{} : Bool}:
  match b:
    case True{}:
      e => Equal.trans(Bool, Laws.segs_ok(dot, ss), Eng.fnames.ok(dot, ss), True{},
        lem.segs(dot, ss), e)
    case False{}:
      e => {==}

def lem.guard(+dot: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) ->
  {Laws.safe(dot, Eng.fnames.guard(dot, may)) == True{} : Bool}:
  match may:
    case None{}:
      {==}
    case Some{+ss}:
      lem.keep(dot, ss, Eng.fnames.ok(dot, ss))({==})

def lem.gate(+dot: Bool, ok: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) ->
  {Laws.safe(dot, may) == True{} : Bool} ->
  {Laws.safe(dot, Eng.fnames.gate(ok, may)) == True{} : Bool}:
  match ok:
    case True{}:
      h => h
    case False{}:
      h => {==}

def Laws.path_safe(dot, t):
  lem.gate(dot, Eng.clean(t), Eng.fnames.guard(dot, Eng.norm(Eng.segs(t))))(
    lem.guard(dot, Eng.norm(Eng.segs(t))))

# clean_refuses_control: a refused byte makes the running verdict False,
# and False stays False to the end of the target.
def lem.clean_false(bs: List<&2, U32>) -> {Eng.clean.go(bs, False{}) == False{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      lem.clean_false(t)

def lem.clean(
  a: List<&2, U32>, +b: List<&2, U32>, +c: U32,
  e: {(U32.is_lt(c, 32) || U32.is_eq(c, 127)) == True{} : Bool}, ok: Bool
) -> {Eng.clean.go(List.append(&2, U32, a, Con{c, b}), ok) == False{} : Bool}:
  match a:
    case Nil{}:
      match ok:
        case False{}:
          lem.clean_false(b)
        case True{}:
          %Equal.sym(Bool, (U32.is_lt(c, 32) || U32.is_eq(c, 127)), True{}, e) :
            {Eng.clean.go(b, Eng.clean.pick(_, c)) == False{} : Bool}
          lem.clean_false(b)
    case Con{+h, t}:
      lem.clean(t, b, c, e, Bool.and(ok, Eng.clean.pick(Eng.ctl(h), h)))

def Laws.clean_refuses_control(a, b, c, e):
  lem.clean(a, b, c, e, True{})

def Laws.unclean_names_nothing(dot, t, e):
  %Equal.sym(Bool, Eng.clean(t), False{}, e) :
    {Eng.fnames.gate(_, Eng.fnames.guard(dot, Eng.norm(Eng.segs(t)))) == None{} :
      Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

def Laws.fnames_dotfile():
  {==}

def Laws.fnames_dotdir():
  {==}

def Laws.fnames_backslash():
  {==}

def Laws.fnames_nul():
  {==}

def Laws.fnames_dots():
  {==}

def Laws.fnames_plain():
  {==}

def Laws.sha1_empty():
  {==}

def Laws.sha1_abc():
  {==}

def Laws.sha1_two_blocks():
  {==}

def Laws.b64_empty():
  {==}

def Laws.b64_f():
  {==}

def Laws.b64_fo():
  {==}

def Laws.b64_foo():
  {==}

def Laws.b64_foob():
  {==}

def Laws.b64_fooba():
  {==}

def Laws.b64_foobar():
  {==}

def Laws.ws_accept():
  {==}

def Laws.ws_feed_split(a, b, w):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.ws_feed_split(t, b, Ws.step(w, c))

def Laws.ws_bad_absorbs(c, out):
  {==}

def Laws.ws_bad_feeds(s, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.ws_bad_feeds(t, out)

# ws_feed_buf: the two walks step the same machine on the same byte, so
# the cons case is the hypothesis on the stepped state.
def Laws.ws_feed_buf(b, w):
  match b:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Laws.ws_feed_buf(t, Ws.step(w, c))

# ws_feed_buf_split: through the lists. Each buffer walk is the list
# walk of its bytes, the bytes of a join are the join of the bytes, and
# the list reader splits.
def Laws.ws_feed_buf_split(a, b, w):
  Equal.trans(Ws.W, Ws.feed_buf(Bytes.append(a, b), w),
    Ws.feed(Bytes.to_list(Bytes.append(a, b)), w),
    Ws.feed_buf(b, Ws.feed_buf(a, w)),
    Laws.ws_feed_buf(Bytes.append(a, b), w),
    Equal.trans(Ws.W, Ws.feed(Bytes.to_list(Bytes.append(a, b)), w),
      Ws.feed(List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), w),
      Ws.feed_buf(b, Ws.feed_buf(a, w)),
      Equal.cong(List<&2, U32>, Ws.W, xs => Ws.feed(xs, w),
        Bytes.to_list(Bytes.append(a, b)),
        List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)),
        Bytes.to_list_append(a, b)),
      Equal.trans(Ws.W,
        Ws.feed(List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), w),
        Ws.feed(Bytes.to_list(b), Ws.feed(Bytes.to_list(a), w)),
        Ws.feed_buf(b, Ws.feed_buf(a, w)),
        Laws.ws_feed_split(Bytes.to_list(a), Bytes.to_list(b), w),
        Equal.trans(Ws.W,
          Ws.feed(Bytes.to_list(b), Ws.feed(Bytes.to_list(a), w)),
          Ws.feed(Bytes.to_list(b), Ws.feed_buf(a, w)),
          Ws.feed_buf(b, Ws.feed_buf(a, w)),
          Equal.cong(Ws.W, Ws.W, v => Ws.feed(Bytes.to_list(b), v),
            Ws.feed(Bytes.to_list(a), w), Ws.feed_buf(a, w),
            Equal.sym(Ws.W, Ws.feed_buf(a, w), Ws.feed(Bytes.to_list(a), w),
              Laws.ws_feed_buf(a, w))),
          Equal.sym(Ws.W, Ws.feed_buf(b, Ws.feed_buf(a, w)),
            Ws.feed(Bytes.to_list(b), Ws.feed_buf(a, w)),
            Laws.ws_feed_buf(b, Ws.feed_buf(a, w)))))))

def Laws.ws_bad_feeds_buf(s, out):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Laws.ws_bad_feeds_buf(t, out)

def Laws.ws_read_text():
  {==}

def Laws.ws_read_ping():
  {==}

def Laws.ws_read_text_buf():
  {==}

def Laws.ws_read_text_buf_cut():
  {==}

def Laws.ws_read_ping_buf():
  {==}

def Laws.ws_unmasked_is_bad():
  {==}

def Laws.ws_fragment_is_bad():
  {==}

def Laws.ws_reserved_is_bad():
  {==}

def Laws.ws_unmasked_is_bad_buf():
  {==}

def Laws.ws_fragment_is_bad_buf():
  {==}

def Laws.ws_reserved_is_bad_buf():
  {==}

def Laws.ws_control_long_is_bad():
  {==}

def Laws.ws_short_126_is_bad():
  {==}

def Laws.ws_short_127_is_bad():
  {==}

def Laws.ws_len_126_least():
  {==}

def Laws.ws_len_127_least():
  {==}

def Laws.ws_frame_short():
  {==}

def Laws.ws_len_two_bytes():
  {==}

def Laws.ws_close_code():
  {==}

def Laws.ws_close_codes_rule():
  {==}

def Laws.ws_close_codes():
  {==}

def Laws.ws_close_echo():
  {==}

def Laws.ws_close_reserved():
  {==}

def Laws.ws_close_one_byte():
  {==}

def Laws.ws_close_bad_reason():
  {==}

def Laws.ws_text_bad():
  {==}

def Laws.ws_binary_any():
  {==}

def Laws.ws_utf8_reference():
  {==}

def Laws.ws_utf8_vectors():
  {==}

# batch_under: the comparison is generalised with its equation. Below
# the cap what stays is k, and the equation says k is below it; at or
# past it what stays is 0, which the checker compares with the cap.
law batch_under.go:
  for +k: U32
  for +c: Cmp
  for e: {c == U32.cmp(k, Eng.send.cap()) : Cmp}
  {U32.is_lt(Eng.batch.keep(c, k), Eng.send.cap()) == True{} : Bool}

def batch_under.go(k, c, e):
  match c:
    case LT{}:
      %e : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.batch_under(k):
  batch_under.go(k, U32.cmp(k, Eng.send.cap()), {==})

# long_at and long_past: long compares the count with the length, and a
# byte in front is one more
def lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

def lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ(p)

def Laws.long_at(bs):
  lt_irrefl(Bytes.len(bs))

def Laws.long_past(bs, c):
  %Equal.sym(Nat, String.length.go(bs, 1n), 1n+String.length.go(bs, 0n), len_shift(bs)) :
    {Nat.is_lt(String.length.go(bs, 0n), _) == True{} : Bool}
  lt_succ(Bytes.len(bs))

def Laws.hw_rest(hw):
  {==}

def Laws.hw_keeps(t0, n):
  {==}

def Laws.key_rfc():
  {==}

def Laws.key_short():
  {==}

def Laws.key_alphabet():
  {==}

def Laws.key_padding():
  {==}

def Laws.parse_version_13():
  {==}

def Laws.parse_version_other():
  {==}

def Laws.parse_ows_trimmed():
  {==}

def Laws.parse_version_inner():
  {==}

# The world
# =========
#
# The loops in world.bend's model are pure functions, so most of these
# compute once the right thing is generalised. A value the proof cannot
# see (a send's answer, a comparison with the cap, a Bool the premise
# pins) is made a variable by a lemma quantified over it, with the
# equation that says what it was. end_is_last, stop_is_last and
# go_order compute; fail_* take the send's answer apart; the buffering
# laws walk the writer (send.hold, send.raw, and a file through
# fopen, fsize, page.start and the pump) with the comparison with the
# cap generalised; refuse_* walk answer.go one request at a time, and
# plan.ans through the owed replies; segs_wire walks send.go with the
# held batch, and the peer's appends reassociated; stall_ends shows
# that a turn at the mute peer always plans Stop (or, for a stream,
# plans one event whose send must fail), so that fuel past three turns
# is never used; accept_* walk accept.run one event at a time.

def Laws.end_is_last(srv, w, out, hw, g, v):
  {==}

def Laws.stop_is_last(srv, w, hw, g, v):
  {==}

def Laws.go_order(srv, w, out, p2, hw, g, v):
  {==}

def Laws.fail_go(srv, g, v, m, p, hw, e):
  match g:
    case 0n:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({W.sim.conn(0n, srv, W.sim.turn(srv, (s, Done{u}), p, hw), v) == s : W.World},
            Equal.sym(Bool, True{}, False{}, e))
    case 1n+h:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({W.sim.conn(1n+h, srv, W.sim.turn(srv, (s, Done{u}), p, hw), v) == s : W.World},
            Equal.sym(Bool, True{}, False{}, e))

def Laws.fail_ws(srv, g, v, m, wr, e):
  match g:
    case 0n:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({W.sim.conn(0n, srv, (W.sim.turn.ws(srv, (s, Done{u}), wr), Eng.NoHead{}), v) == s :
            W.World}, Equal.sym(Bool, True{}, False{}, e))
    case 1n+h:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({W.sim.conn(1n+h, srv, (W.sim.turn.ws(srv, (s, Done{u}), wr), Eng.NoHead{}), v) ==
            s : W.World}, Equal.sym(Bool, True{}, False{}, e))

def Laws.fail_feed(srv, g, v, m, n, e):
  match g:
    case 0n:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({W.sim.conn(0n, srv, (W.sim.tick((s, Done{u}), n), Eng.NoHead{}), v) ==
            W.w.nap(s, Eng.sse.gap()) : W.World}, Equal.sym(Bool, True{}, False{}, e))
    case 1n+h:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({W.sim.conn(1n+h, srv, (W.sim.tick((s, Done{u}), n), Eng.NoHead{}), v) ==
            W.w.nap(s, Eng.sse.gap()) : W.World}, Equal.sym(Bool, True{}, False{}, e))

def Laws.head_expires(srv, w, p, t0, n, e):
  %Equal.sym(Bool, Nat.is_lt(Nat.sub(W.w.now(w), t0), U32.to_nat(Eng.srv.head(srv))), False{}, e) :
    {W.sim.left(srv, w, p, t0, n, Nat.sub(W.w.now(w), t0), _) == ((w, Eng.Stop{}), Eng.NoHead{}) :
      (W.World & Eng.Plan) & Eng.Hw}
  {==}

law wl.head_sized:
  for +srv: Eng.Srv
  for w: W.World
  for buf: Bytes()
  for p: Eng.P
  for t0: Nat
  for +k: U32
  for big: Bool
  for e: {big == U32.is_lt(Eng.head.cap(), k) : Bool}
  {W.hw.fine(W.hw.of(Eng.plan.sized(W.World, srv, w, buf, p, t0, k, big))) == True{} : Bool}

def wl.head_sized(srv, w, buf, p, t0, k, big, e):
  match big:
    case True{}:
      {==}
    case False{}:
      %e : {Bool.not(_) == True{} : Bool}
      {==}

def Laws.head_capped(srv, w, may, p, t0, n):
  match may:
    case None{}:
      {==}
    case Some{+buf}:
      wl.head_sized(srv, w, buf, p, t0, (n + U32.from_nat(Bytes.len(buf)) : U32),
        U32.is_lt(Eng.head.cap(), (n + U32.from_nat(Bytes.len(buf)) : U32)), {==})

law wl.flushed_fine:
  for m: Eng.Put(W.World)
  {W.em.fine(W.sim.flushed(m)) == True{} : Bool}

def wl.flushed_fine(m):
  (s, r) = m
  match r:
    case Done{u}:
      {==}
    case Fail{e}:
      {==}

law wl.held_fine:
  for +ms: U32
  for s: W.World
  for +acc: Bytes()
  for c: Cmp
  for e: {c == U32.cmp(U32.from_nat(Bytes.len(acc)), Eng.send.cap()) : Cmp}
  {W.em.fine(W.sim.held(ms, s, acc, c)) == True{} : Bool}

def wl.held_fine(ms, s, acc, c, e):
  match c:
    case LT{}:
      %e : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      wl.flushed_fine(W.w.tx(s, acc, ms))
    case GT{}:
      wl.flushed_fine(W.w.tx(s, acc, ms))

def Laws.hold_fine(ms, s, acc):
  wl.held_fine(ms, s, acc, U32.cmp(U32.from_nat(Bytes.len(acc)), Eng.send.cap()), {==})

def Laws.raw_fine(ms, may, bs, st):
  match st:
    case Eng.Em{s, acc, ok}:
      match ok:
        case False{}:
          {==}
        case True{}:
          Laws.hold_fine(ms, s, Bytes.append(acc, W.sim.note(may, bs)))

law wl.pleft_fine:
  for +ms: U32
  for f: Bytes()
  for left: U32
  for s: W.World
  for pre: Bytes()
  for done: Bool
  {W.pump.fine(W.sim.pleft(ms, f, left, s, pre, done)) == True{} : Bool}

def wl.pleft_fine(ms, f, left, s, pre, done):
  match done:
    case True{}:
      Laws.hold_fine(ms, s, pre)
    case False{}:
      {==}

law wl.psent_fine:
  for +ms: U32
  for m: Eng.Put(W.World)
  for f: Bytes()
  for +left: U32
  {W.pump.fine(W.sim.psent(ms, m, f, left)) == True{} : Bool}

def wl.psent_fine(ms, m, f, left):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.pleft_fine(ms, f, left, s, "", U32.is_zero(left))

law wl.pblock_fine:
  for +ms: U32
  for f: Bytes()
  for +left: U32
  for s: W.World
  for pre: Bytes()
  for bs: Bytes()
  for +n: U32
  for empty: Bool
  {W.pump.fine(W.sim.pblock(ms, f, left, s, pre, bs, n, empty)) == True{} : Bool}

def wl.pblock_fine(ms, f, left, s, pre, bs, n, empty):
  match empty:
    case True{}:
      {==}
    case False{}:
      wl.psent_fine(ms, W.w.tx(s, Bytes.append(pre, bs), ms), f, (left - n : U32))

law wl.pgot_fine:
  for +ms: U32
  for got: Bytes() & Result<&1, &1, U32 & String, Bytes()>
  for left: U32
  for s: W.World
  for pre: Bytes()
  {W.pump.fine(W.sim.pgot(ms, got, left, s, pre)) == True{} : Bool}

def wl.pgot_fine(ms, got, left, s, pre):
  (f, r) = got
  match r:
    case Fail{e}:
      {==}
    case Done{+bs}:
      wl.pblock_fine(ms, f, left, s, pre, bs, U32.from_nat(Bytes.len(bs)),
        U32.is_zero(U32.from_nat(Bytes.len(bs))))

law wl.pump_fine:
  for k: Nat
  for +ms: U32
  for p: Eng.Pump<W.World, Bytes()>
  for e: {W.pump.fine(p) == True{} : Bool}
  {W.em.fine(W.sim.pump(k, ms, p)) == True{} : Bool}

def wl.pump_fine(k, ms, p, e):
  match k:
    case 0n:
      match p:
        case Eng.Going{f, left, s, pre}:
          {==}
        case Eng.Over{em}:
          e
    case 1n+j:
      match p:
        case Eng.Over{em}:
          e
        case Eng.Going{+f, +left, +s, +pre}:
          wl.pump_fine(j, ms, W.sim.pgot(ms, W.w.fread(f, U32.min(Eng.page.chunk(), left)), left, s, pre),
            wl.pgot_fine(ms, W.w.fread(f, U32.min(Eng.page.chunk(), left)), left, s, pre))

law wl.miss_fine:
  for +ms: U32
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for s: W.World
  for acc: Bytes()
  {W.em.fine(W.sim.miss(ms, head, may, sh, s, acc)) == True{} : Bool}

def wl.miss_fine(ms, head, may, sh, s, acc):
  Laws.hold_fine(ms, s, Bytes.append(acc, W.sim.note(may, Eng.flat.shut(sh, Eng.miss(head)))))

law wl.pstart_fine:
  for +ms: U32
  for +f: Bytes()
  for +n: U32
  for +hd: Bytes()
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for +s: W.World
  for +acc: Bytes()
  {W.em.fine(W.sim.pstart(ms, f, n, hd, head, may, s, acc)) == True{} : Bool}

def wl.pstart_fine(ms, f, n, hd, head, may, s, acc):
  match head:
    case True{}:
      Laws.hold_fine(ms, s, Bytes.append(acc, hd))
    case False{}:
      wl.pump_fine(U32.to_nat((n / Eng.page.chunk() + 64 : U32)), ms,
        W.sim.pleft(ms, f, n, s, Bytes.append(acc, hd), U32.is_zero(n)),
        wl.pleft_fine(ms, f, n, s, Bytes.append(acc, hd), U32.is_zero(n)))

law wl.psized_fine:
  for +ms: U32
  for got: Bytes() & Result<&1, &1, U32 & String, U32>
  for ct: List<&2, U32>
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for s: W.World
  for acc: Bytes()
  {W.em.fine(W.sim.psized(ms, got, ct, head, may, sh, s, acc)) == True{} : Bool}

def wl.psized_fine(ms, got, ct, head, may, sh, s, acc):
  (f, r) = got
  match r:
    case Fail{e}:
      wl.miss_fine(ms, head, may, sh, s, acc)
    case Done{+n}:
      wl.pstart_fine(ms, f, n, Eng.flat.shut(sh, Eng.reply.n.head("200 OK", ct, n)), head, may, s,
        acc)

law wl.opened_fine:
  for +ms: U32
  for m: W.World & Result<&1, &1, U32 & String, Bytes()>
  for ct: List<&2, U32>
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for acc: Bytes()
  {W.em.fine(W.sim.opened(ms, m, ct, head, may, sh, acc)) == True{} : Bool}

def wl.opened_fine(ms, m, ct, head, may, sh, acc):
  (s, r) = m
  match r:
    case Fail{e}:
      wl.miss_fine(ms, head, may, sh, s, acc)
    case Done{f}:
      wl.psized_fine(ms, W.w.fsize(f), ct, head, may, sh, s, acc)

def Laws.page_fine(ms, root, path, ct, head, may, sh, st):
  match st:
    case Eng.Em{s, acc, ok}:
      match ok:
        case False{}:
          {==}
        case True{}:
          wl.opened_fine(ms, W.w.fopen(s, Eng.text(root), Eng.text(path)), ct, head, may, sh, acc)

def wl.and_l(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      no({False{} == True{} : Bool}, e)

def wl.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      no({b == True{} : Bool}, e)

def Laws.accept_calm(k, evs, served, e):
  match k:
    case 0n:
      {==}
    case 1n+j:
      match evs:
        case Nil{}:
          Laws.accept_calm(j, Nil{}, served, {==})
        case Con{ev, t}:
          match ev:
            case W.Come{}:
              Laws.accept_calm(j, t, 1n+served, e)
            case W.Idle{}:
              Laws.accept_calm(j, t, served, e)
            case W.Term{}:
              no({W.why.of(W.sim.accept(1n+j, W.Lw{Con{W.Term{}, t}, False{}, served})) ==
                Eng.Spent{} : Eng.Why}, e)
            case W.Err{+code}:
              %Equal.sym(Bool, Eng.accept.soft(code), True{},
                wl.and_l(Eng.accept.soft(code), W.calm(t), e)) :
                {W.why.of(W.sim.acc.dead(j, W.Lw{t, False{}, served}, code, _)) == Eng.Spent{} :
                  Eng.Why}
              Laws.accept_calm(j, t, served, wl.and_r(Eng.accept.soft(code), W.calm(t), e))

# a loop told why it ended answers that, whatever turns it had left
law wl.some_ends:
  for j: Nat
  for l: W.Lw
  for +why: Eng.Why
  for e: {W.ok.end(why) == True{} : Bool}
  {W.ok.end(W.why.of(W.sim.acc.run(j, (l, Some{why})))) == True{} : Bool}

def wl.some_ends(j, l, why, e):
  match j:
    case 0n:
      e
    case 1n+i:
      e

law wl.err_stopped:
  for j: Nat
  for +t: List<&2, W.Ac>
  for +served: Nat
  for +code: U32
  for sb: Bool
  for e: {sb == Eng.accept.soft(code) : Bool}
  {W.ok.end(W.why.of(W.sim.acc.dead(j, W.Lw{t, True{}, served}, code, sb))) == True{} : Bool}

def wl.err_stopped(j, t, served, code, sb, e):
  match sb:
    case True{}:
      wl.some_ends(j, W.Lw{t, True{}, served}, Eng.Asked{}, {==})
    case False{}:
      wl.some_ends(j, W.Lw{t, True{}, served}, Eng.Dead{code},
        (%e : {Bool.not(_) == True{} : Bool}
         {==}))

law wl.err_going:
  for j: Nat
  for +t: List<&2, W.Ac>
  for +served: Nat
  for +code: U32
  for sb: Bool
  for e: {sb == Eng.accept.soft(code) : Bool}
  for ih: {W.ok.end(W.why.of(W.sim.accept(j, W.Lw{t, False{}, served}))) == True{} : Bool}
  {W.ok.end(W.why.of(W.sim.acc.dead(j, W.Lw{t, False{}, served}, code, sb))) == True{} : Bool}

def wl.err_going(j, t, served, code, sb, e, ih):
  match sb:
    case True{}:
      ih
    case False{}:
      wl.some_ends(j, W.Lw{t, False{}, served}, Eng.Dead{code},
        (%e : {Bool.not(_) == True{} : Bool}
         {==}))

def Laws.accept_ends(k, sp, evs, served):
  match k:
    case 0n:
      {==}
    case 1n+j:
      match sp evs:
        case True{} Nil{}:
          wl.some_ends(j, W.Lw{Nil{}, True{}, served}, Eng.Asked{}, {==})
        case True{} Con{W.Come{}, t}:
          wl.some_ends(j, W.Lw{t, True{}, 1n+served}, Eng.Asked{}, {==})
        case True{} Con{W.Idle{}, t}:
          wl.some_ends(j, W.Lw{t, True{}, served}, Eng.Asked{}, {==})
        case True{} Con{W.Term{}, t}:
          wl.some_ends(j, W.Lw{t, True{}, served}, Eng.Asked{}, {==})
        case True{} Con{W.Err{+code}, t}:
          wl.err_stopped(j, t, served, code, Eng.accept.soft(code), {==})
        case False{} Nil{}:
          Laws.accept_ends(j, False{}, Nil{}, served)
        case False{} Con{W.Come{}, t}:
          Laws.accept_ends(j, False{}, t, 1n+served)
        case False{} Con{W.Idle{}, t}:
          Laws.accept_ends(j, False{}, t, served)
        case False{} Con{W.Term{}, t}:
          wl.some_ends(j, W.Lw{t, True{}, served}, Eng.Asked{}, {==})
        case False{} Con{W.Err{+code}, t}:
          wl.err_going(j, t, served, code, Eng.accept.soft(code), {==},
            Laws.accept_ends(j, False{}, t, served))

# one request's step through answer.go, when its reply keeps the
# connection: the reply joins the batch as it was, and the walk goes on
law wl.ag_step:
  for +srv: Eng.Srv
  for +t: List<&2, Eng.Req>
  for c: Bool
  for +s: U32
  for k: Bool
  for +o: List<&2, Eng.Seg>
  for +acc: List<&2, List<&2, Eng.Seg>>
  for e: {Bool.not(c || k || Bool.not(U32.is_zero(s))) == True{} : Bool}
  for ih: {Eng.answer.go(srv, t, True{}, True{}, c, s, k, Con{o, acc}) ==
    Eng.Ans{Eng.answer.flat(Con{o, acc}, W.owed(srv, t, W.bad.reply())), True{}, 0, False{}} : Eng.Ans}
  {Eng.answer.go(srv, t, True{}, Bool.not(c || k || Bool.not(U32.is_zero(s))), c, s, k,
    Con{Eng.answer.shut(o, c && U32.is_zero(s) && Bool.not(k)), acc}) ==
    Eng.Ans{Eng.answer.flat(Con{o, acc}, W.owed(srv, t, W.bad.reply())), True{}, 0, False{}} : Eng.Ans}

def wl.ag_step(srv, t, c, s, k, o, acc, e, ih):
  match c:
    case True{}:
      no({Eng.answer.go(srv, t, True{}, False{}, True{}, s, k,
        Con{Eng.answer.shut(o, U32.is_zero(s) && Bool.not(k)), acc}) ==
        Eng.Ans{Eng.answer.flat(Con{o, acc}, W.owed(srv, t, W.bad.reply())), True{}, 0, False{}} :
        Eng.Ans}, e)
    case False{}:
      match k:
        case True{}:
          no({Eng.answer.go(srv, t, True{}, False{}, False{}, s, True{}, Con{o, acc}) ==
            Eng.Ans{Eng.answer.flat(Con{o, acc}, W.owed(srv, t, W.bad.reply())), True{}, 0, False{}} :
            Eng.Ans}, e)
        case False{}:
          %Equal.sym(Bool, Bool.not(Bool.not(U32.is_zero(s))), True{}, e) :
            {Eng.answer.go(srv, t, True{}, _, False{}, s, False{}, Con{o, acc}) ==
              Eng.Ans{Eng.answer.flat(Con{o, acc}, W.owed(srv, t, W.bad.reply())), True{}, 0, False{}} :
              Eng.Ans}
          ih

# a read whose requests all keep the connection, and whose grammar then
# broke, is answered with every reply they are owed, in order, then the
# 400, and nothing else; the answer closes
law wl.ag_owed:
  for +srv: Eng.Srv
  for +rs: List<&2, Eng.Req>
  for c: Bool
  for +s: U32
  for k: Bool
  for +acc: List<&2, List<&2, Eng.Seg>>
  for +e: {W.all.keep(srv, rs) == True{} : Bool}
  {Eng.answer.go(srv, rs, True{}, True{}, c, s, k, acc) ==
    Eng.Ans{Eng.answer.flat(acc, W.owed(srv, rs, W.bad.reply())), True{}, 0, False{}} : Eng.Ans}

def wl.ag_owed(srv, rs, c, s, k, acc, e):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      wl.ag_step(srv, t, W.ag.c(srv, r), W.ag.s(srv, r), W.ag.k(srv, r), W.ag.o(srv, r), acc,
        wl.and_l(W.keeps(srv, r), W.all.keep(srv, t), e),
        wl.ag_owed(srv, t, W.ag.c(srv, r), W.ag.s(srv, r), W.ag.k(srv, r), Con{W.ag.o(srv, r), acc},
          wl.and_r(W.keeps(srv, r), W.all.keep(srv, t), e)))

law wl.ans_end_app:
  for xs: List<&2, Eng.Seg>
  for +ys: List<&2, Eng.Seg>
  for +q: Eng.P
  for e: {Eng.plan.ans(Eng.Ans{ys, True{}, 0, False{}}, q) == Eng.End{ys} : Eng.Plan}
  {Eng.plan.ans(Eng.Ans{List.append(&2, Eng.Seg, xs, ys), True{}, 0, False{}}, q) ==
    Eng.End{List.append(&2, Eng.Seg, xs, ys)} : Eng.Plan}

def wl.ans_end_app(xs, ys, q, e):
  match xs:
    case Nil{}:
      e
    case Con{h, t}:
      {==}

law wl.ans_end_owed:
  for +srv: Eng.Srv
  for +rs: List<&2, Eng.Req>
  for +q: Eng.P
  {Eng.plan.ans(Eng.Ans{W.owed(srv, rs, W.bad.reply()), True{}, 0, False{}}, q) ==
    Eng.End{W.owed(srv, rs, W.bad.reply())} : Eng.Plan}

def wl.ans_end_owed(srv, rs, q):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      wl.ans_end_app(W.ag.o(srv, r), W.owed(srv, t, W.bad.reply()), q, wl.ans_end_owed(srv, t, q))

def Laws.refuse_plan(srv, rs, q, e):
  %Equal.sym(Eng.Ans, Eng.answer.go(srv, rs, True{}, True{}, False{}, 0, False{}, Nil{}),
    Eng.Ans{Eng.answer.flat(Nil{}, W.owed(srv, rs, W.bad.reply())), True{}, 0, False{}},
    wl.ag_owed(srv, rs, False{}, 0, False{}, Nil{}, e)) :
    {Eng.plan.ans(_, q) == Eng.End{W.owed(srv, rs, W.bad.reply())} : Eng.Plan}
  wl.ans_end_owed(srv, rs, q)

def Laws.refuse_conn(srv, w, q, rs, hw, g, v, e):
  %Equal.sym(Eng.Plan, Eng.plan.take(srv, (q, rs), True{}), Eng.End{W.owed(srv, rs, W.bad.reply())},
    Laws.refuse_plan(srv, rs, q, e)) :
    {W.sim.conn(1n+g, srv, ((w, _), hw), v) ==
      Eng.put.s(W.World, W.sim.segs(w, W.owed(srv, rs, W.bad.reply()), Eng.srv.idle(srv))) : W.World}
  {==}

def wl.app_nil(+a: Bytes()) -> {Bytes.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(t, ""), t, wl.app_nil(t))

def wl.app_assoc(+a: Bytes(), +b: Bytes(), +c: Bytes()) ->
  {Bytes.append(Bytes.append(a, b), c) == Bytes.append(a, Bytes.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(Bytes.append(t, b), c),
        Bytes.append(t, Bytes.append(b, c)), wl.app_assoc(t, b, c))

# a send to a peer that takes everything puts the whole buffer on the
# wire after what was there, and succeeds
law wl.tx_eager:
  for +rd: List<&2, W.Rd>
  for +now: Nat
  for +fs: List<&2, W.Fil>
  for +out: Bytes()
  for +a: Bytes()
  for +ms: U32
  {W.w.tx(W.eager(rd, now, fs, out), a, ms) == W.sent(rd, now, fs, Bytes.append(out, a)) :
    Eng.Put(W.World)}

def wl.tx_eager(rd, now, fs, out, a, ms):
  match a:
    case SNil{}:
      %Equal.sym(Bytes(), Bytes.append(out, ""), out, wl.app_nil(out)) :
        {W.sent(rd, now, fs, out) == W.sent(rd, now, fs, _) : Eng.Put(W.World)}
      {==}
    case SCon{h, t}:
      {==}

def wl.note_is(may: Maybe<&2, Bytes()>, +x: Bytes()) -> {W.sim.note(may, x) == x : Bytes()}:
  match may:
    case None{}:
      {==}
    case Some{n}:
      {==}

law wl.held_eager:
  for +t: List<&2, Eng.Seg>
  for +ms: U32
  for +rd: List<&2, W.Rd>
  for +now: Nat
  for +fs: List<&2, W.Fil>
  for +out: Bytes()
  for +a: Bytes()
  for c: Cmp
  for ih1: {W.sim.go(t, ms, None{}, False{}, Eng.Em{W.eager(rd, now, fs, out), a, True{}}) ==
    W.sent(rd, now, fs, Bytes.append(out, Bytes.append(a, W.wire(t, False{})))) :
    Eng.Put(W.World)}
  for ih2: {W.sim.go(t, ms, None{}, False{},
    Eng.Em{W.eager(rd, now, fs, Bytes.append(out, a)), "", True{}}) ==
    W.sent(rd, now, fs, Bytes.append(Bytes.append(out, a), W.wire(t, False{}))) :
    Eng.Put(W.World)}
  {W.sim.go(t, ms, None{}, False{}, W.sim.held(ms, W.eager(rd, now, fs, out), a, c)) ==
    W.sent(rd, now, fs, Bytes.append(out, Bytes.append(a, W.wire(t, False{})))) :
    Eng.Put(W.World)}

def wl.held_eager(t, ms, rd, now, fs, out, a, c, ih1, ih2):
  match c:
    case LT{}:
      ih1
    case EQ{}:
      %Equal.sym(Eng.Put(W.World), W.w.tx(W.eager(rd, now, fs, out), a, ms),
        W.sent(rd, now, fs, Bytes.append(out, a)), wl.tx_eager(rd, now, fs, out, a, ms)) :
        {W.sim.go(t, ms, None{}, False{}, W.sim.flushed(_)) ==
          W.sent(rd, now, fs, Bytes.append(out, Bytes.append(a, W.wire(t, False{})))) :
          Eng.Put(W.World)}
      Equal.trans(Eng.Put(W.World),
        W.sim.go(t, ms, None{}, False{}, Eng.Em{W.eager(rd, now, fs, Bytes.append(out, a)), "", True{}}),
        W.sent(rd, now, fs, Bytes.append(Bytes.append(out, a), W.wire(t, False{}))),
        W.sent(rd, now, fs, Bytes.append(out, Bytes.append(a, W.wire(t, False{})))),
        ih2,
        Equal.cong(Bytes(), Eng.Put(W.World), o => W.sent(rd, now, fs, o),
          Bytes.append(Bytes.append(out, a), W.wire(t, False{})),
          Bytes.append(out, Bytes.append(a, W.wire(t, False{}))),
          wl.app_assoc(out, a, W.wire(t, False{}))))
    case GT{}:
      %Equal.sym(Eng.Put(W.World), W.w.tx(W.eager(rd, now, fs, out), a, ms),
        W.sent(rd, now, fs, Bytes.append(out, a)), wl.tx_eager(rd, now, fs, out, a, ms)) :
        {W.sim.go(t, ms, None{}, False{}, W.sim.flushed(_)) ==
          W.sent(rd, now, fs, Bytes.append(out, Bytes.append(a, W.wire(t, False{})))) :
          Eng.Put(W.World)}
      Equal.trans(Eng.Put(W.World),
        W.sim.go(t, ms, None{}, False{}, Eng.Em{W.eager(rd, now, fs, Bytes.append(out, a)), "", True{}}),
        W.sent(rd, now, fs, Bytes.append(Bytes.append(out, a), W.wire(t, False{}))),
        W.sent(rd, now, fs, Bytes.append(out, Bytes.append(a, W.wire(t, False{})))),
        ih2,
        Equal.cong(Bytes(), Eng.Put(W.World), o => W.sent(rd, now, fs, o),
          Bytes.append(Bytes.append(out, a), W.wire(t, False{})),
          Bytes.append(out, Bytes.append(a, W.wire(t, False{}))),
          wl.app_assoc(out, a, W.wire(t, False{}))))

law wl.go_wire:
  for +xs: List<&2, Eng.Seg>
  for +ms: U32
  for may: Maybe<&2, Bytes()>
  for +sh: Bool
  for +rd: List<&2, W.Rd>
  for +now: Nat
  for +fs: List<&2, W.Fil>
  for +out: Bytes()
  for +acc: Bytes()
  for +e: {W.raws(xs) == True{} : Bool}
  {W.sim.go(xs, ms, may, sh, Eng.Em{W.eager(rd, now, fs, out), acc, True{}}) ==
    W.sent(rd, now, fs, Bytes.append(out, Bytes.append(acc, W.wire(xs, sh)))) :
    Eng.Put(W.World)}

def wl.go_wire(xs, ms, may, sh, rd, now, fs, out, acc, e):
  match xs:
    case Nil{}:
      %Equal.sym(Eng.Put(W.World), W.w.tx(W.eager(rd, now, fs, out), acc, ms),
        W.sent(rd, now, fs, Bytes.append(out, acc)), wl.tx_eager(rd, now, fs, out, acc, ms)) :
        {Eng.send.fin(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, _, True{}) ==
          W.sent(rd, now, fs, Bytes.append(out, Bytes.append(acc, ""))) : Eng.Put(W.World)}
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, wl.app_nil(acc)) :
        {W.sent(rd, now, fs, Bytes.append(out, acc)) ==
          W.sent(rd, now, fs, Bytes.append(out, _)) : Eng.Put(W.World)}
      {==}
    case Con{+g, +t}:
      match g:
        case Eng.Raw{+bs}:
          %Equal.sym(Bytes(), W.sim.note(may, Eng.flat.shut(sh, bs)), Eng.flat.shut(sh, bs),
            wl.note_is(may, Eng.flat.shut(sh, bs))) :
            {W.sim.go(t, ms, None{}, False{},
              W.sim.hold(ms, W.eager(rd, now, fs, out), Bytes.append(acc, _))) ==
              W.sent(rd, now, fs, Bytes.append(out, Bytes.append(acc,
                Bytes.append(Eng.flat.shut(sh, bs), W.wire(t, False{}))))) : Eng.Put(W.World)}
          Equal.trans(Eng.Put(W.World),
            W.sim.go(t, ms, None{}, False{},
              W.sim.hold(ms, W.eager(rd, now, fs, out), Bytes.append(acc, Eng.flat.shut(sh, bs)))),
            W.sent(rd, now, fs, Bytes.append(out, Bytes.append(Bytes.append(acc, Eng.flat.shut(sh, bs)),
              W.wire(t, False{})))),
            W.sent(rd, now, fs, Bytes.append(out, Bytes.append(acc,
              Bytes.append(Eng.flat.shut(sh, bs), W.wire(t, False{}))))),
            wl.held_eager(t, ms, rd, now, fs, out, Bytes.append(acc, Eng.flat.shut(sh, bs)),
              U32.cmp(U32.from_nat(Bytes.len(Bytes.append(acc, Eng.flat.shut(sh, bs)))),
                Eng.send.cap()),
              wl.go_wire(t, ms, None{}, False{}, rd, now, fs, out,
                Bytes.append(acc, Eng.flat.shut(sh, bs)), e),
              wl.go_wire(t, ms, None{}, False{}, rd, now, fs,
                Bytes.append(out, Bytes.append(acc, Eng.flat.shut(sh, bs))), "", e)),
            Equal.cong(Bytes(), Eng.Put(W.World), o => W.sent(rd, now, fs, Bytes.append(out, o)),
              Bytes.append(Bytes.append(acc, Eng.flat.shut(sh, bs)), W.wire(t, False{})),
              Bytes.append(acc, Bytes.append(Eng.flat.shut(sh, bs), W.wire(t, False{}))),
              wl.app_assoc(acc, Eng.flat.shut(sh, bs), W.wire(t, False{}))))
        case Eng.Note{bs}:
          wl.go_wire(t, ms, Some{bs}, sh, rd, now, fs, out, acc, e)
        case Eng.Shut{}:
          wl.go_wire(t, ms, may, True{}, rd, now, fs, out, acc, e)
        case Eng.Page{root, path, ct, head}:
          no({W.sim.go(Con{Eng.Page{root, path, ct, head}, t}, ms, may, sh,
            Eng.Em{W.eager(rd, now, fs, out), acc, True{}}) ==
            W.sent(rd, now, fs, Bytes.append(out, Bytes.append(acc,
              W.wire(Con{Eng.Page{root, path, ct, head}, t}, sh)))) : Eng.Put(W.World)}, e)

def Laws.segs_wire(xs, ms, rd, now, fs, out, e):
  wl.go_wire(xs, ms, None{}, False{}, rd, now, fs, out, "", e)

# a turn at a stopped peer ends the connection: one more turn of fuel
# does nothing more
law wl.mute_left:
  for +srv: Eng.Srv
  for s: W.World
  for p: Eng.P
  for t0: Nat
  for n: U32
  for +el: Nat
  for ok: Bool
  for g: Nat
  for v: Nat
  {W.mute.conn(1n+g, srv, W.mute.left(srv, s, p, t0, n, el, ok), v) ==
    W.mute.conn(1n, srv, W.mute.left(srv, s, p, t0, n, el, ok), v) : W.World}

def wl.mute_left(srv, s, p, t0, n, el, ok, g, v):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

law wl.mute_turn_h:
  for +srv: Eng.Srv
  for +s: W.World
  for p: Eng.P
  for hw: Eng.Hw
  for g: Nat
  for v: Nat
  {W.mute.conn(1n+g, srv, W.mute.turn.h(srv, s, p, hw), v) ==
    W.mute.conn(1n, srv, W.mute.turn.h(srv, s, p, hw), v) : W.World}

def wl.mute_turn_h(srv, s, p, hw, g, v):
  match hw:
    case Eng.NoHead{}:
      {==}
    case Eng.Begun{}:
      wl.mute_left(srv, s, p, W.w.now(s), 0, Nat.sub(W.w.now(s), W.w.now(s)),
        Nat.is_lt(Nat.sub(W.w.now(s), W.w.now(s)), U32.to_nat(Eng.srv.head(srv))), g, v)
    case Eng.Since{+t0, n}:
      wl.mute_left(srv, s, p, t0, n, Nat.sub(W.w.now(s), t0),
        Nat.is_lt(Nat.sub(W.w.now(s), t0), U32.to_nat(Eng.srv.head(srv))), g, v)

law wl.mute_turn:
  for +srv: Eng.Srv
  for m: Eng.Put(W.World)
  for p: Eng.P
  for hw: Eng.Hw
  for g: Nat
  for v: Nat
  {W.mute.conn(1n+g, srv, W.mute.turn(srv, m, p, hw), v) ==
    W.mute.conn(1n, srv, W.mute.turn(srv, m, p, hw), v) : W.World}

def wl.mute_turn(srv, m, p, hw, g, v):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.mute_turn_h(srv, s, p, hw, g, v)

law wl.mute_ws:
  for +srv: Eng.Srv
  for m: Eng.Put(W.World)
  for wr: Ws.W
  for g: Nat
  for v: Nat
  {W.mute.conn(1n+g, srv, (W.mute.turn.ws(srv, m, wr), Eng.NoHead{}), v) ==
    W.mute.conn(1n, srv, (W.mute.turn.ws(srv, m, wr), Eng.NoHead{}), v) : W.World}

def wl.mute_ws(srv, m, wr, g, v):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      {==}

# a send of bytes to a stopped peer fails; of none, succeeds
law wl.mute_held:
  for +ms: U32
  for s: W.World
  for h: Char
  for t: Bytes()
  for c: Cmp
  {W.put.done(W.mute.go(Nil{}, ms, None{}, False{}, W.mute.held(ms, s, SCon{h, t}, c))) ==
    False{} : Bool}

def wl.mute_held(ms, s, h, t, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law wl.mute_raw:
  for +ms: U32
  for s: W.World
  for +bs: Bytes()
  {W.put.done(W.mute.segs(s, [Eng.Raw{bs}], ms)) == W.empty(bs) : Bool}

def wl.mute_raw(ms, s, bs):
  match bs:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      wl.mute_held(ms, s, h, t, U32.cmp(U32.from_nat(Bytes.len(SCon{h, t})), Eng.send.cap()))

law wl.mute_tick_failed:
  for +srv: Eng.Srv
  for m: Eng.Put(W.World)
  for n: U32
  for g: Nat
  for v: Nat
  for e: {W.put.done(m) == False{} : Bool}
  {W.mute.conn(1n+g, srv, (W.mute.tick(m, n), Eng.NoHead{}), v) ==
    W.mute.conn(1n, srv, (W.mute.tick(m, n), Eng.NoHead{}), v) : W.World}

def wl.mute_tick_failed(srv, m, n, g, v, e):
  (s, r) = m
  match r:
    case Fail{x}:
      {==}
    case Done{u}:
      no({W.mute.conn(1n+g, srv, (W.mute.tick((s, Done{u}), n), Eng.NoHead{}), v) ==
        W.mute.conn(1n, srv, (W.mute.tick((s, Done{u}), n), Eng.NoHead{}), v) : W.World},
        Equal.sym(Bool, True{}, False{}, e))

law wl.mute_more:
  for +srv: Eng.Srv
  for +s: W.World
  for +n: U32
  for z: Bool
  for g: Nat
  for v: Nat
  {W.mute.conn(1n+1n+g, srv, (Eng.plan.more(W.World, s, n, z), Eng.NoHead{}), v) ==
    W.mute.conn(1n+1n, srv, (Eng.plan.more(W.World, s, n, z), Eng.NoHead{}), v) : W.World}

def wl.mute_more(srv, s, n, z, g, v):
  match z:
    case True{}:
      {==}
    case False{}:
      wl.mute_tick_failed(srv, W.mute.segs(s, [Eng.Raw{Eng.sse.event(n)}], Eng.srv.idle(srv)),
        (n - 1 : U32), g, Eng.conn.waits(),
        wl.mute_raw(Eng.srv.idle(srv), s, Eng.sse.event(n)))

law wl.mute_tick:
  for +srv: Eng.Srv
  for m: Eng.Put(W.World)
  for +n: U32
  for g: Nat
  for v: Nat
  {W.mute.conn(1n+1n+g, srv, (W.mute.tick(m, n), Eng.NoHead{}), v) ==
    W.mute.conn(1n+1n, srv, (W.mute.tick(m, n), Eng.NoHead{}), v) : W.World}

def wl.mute_tick(srv, m, n, g, v):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.mute_more(srv, s, n, U32.is_zero(n), g, v)

def Laws.stall_ends(srv, w, pl, hw, g, v):
  match pl:
    case Eng.Stop{}:
      {==}
    case Eng.End{out}:
      {==}
    case Eng.Go{+out, +p2}:
      Equal.trans(W.World,
        W.mute.conn(1n+1n+g, srv, W.mute.turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
          Eng.hw.next(Eng.p.head(p2), Eng.NoHead{})), Eng.conn.waits()),
        W.mute.conn(1n, srv, W.mute.turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
          Eng.hw.next(Eng.p.head(p2), Eng.NoHead{})), Eng.conn.waits()),
        W.mute.conn(1n+1n, srv, W.mute.turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
          Eng.hw.next(Eng.p.head(p2), Eng.NoHead{})), Eng.conn.waits()),
        wl.mute_turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
          Eng.hw.next(Eng.p.head(p2), Eng.NoHead{}), 1n+g, Eng.conn.waits()),
        Equal.sym(W.World,
          W.mute.conn(1n+1n, srv, W.mute.turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
            Eng.hw.next(Eng.p.head(p2), Eng.NoHead{})), Eng.conn.waits()),
          W.mute.conn(1n, srv, W.mute.turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
            Eng.hw.next(Eng.p.head(p2), Eng.NoHead{})), Eng.conn.waits()),
          wl.mute_turn(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), p2,
            Eng.hw.next(Eng.p.head(p2), Eng.NoHead{}), 1n, Eng.conn.waits())))
    case Eng.Wait{+p2}:
      match v:
        case 0n:
          {==}
        case 1n+u:
          Equal.trans(W.World,
            W.mute.conn(1n+1n+g, srv, W.mute.turn.h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw)), u),
            W.mute.conn(1n, srv, W.mute.turn.h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw)), u),
            W.mute.conn(1n+1n, srv, W.mute.turn.h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw)), u),
            wl.mute_turn_h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw), 1n+g, u),
            Equal.sym(W.World,
              W.mute.conn(1n+1n, srv, W.mute.turn.h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw)), u),
              W.mute.conn(1n, srv, W.mute.turn.h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw)), u),
              wl.mute_turn_h(srv, w, p2, Eng.hw.next(Eng.p.head(p2), hw), 1n, u)))
    case Eng.Feed{+out, +n}:
      wl.mute_tick(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), n, g, Eng.conn.waits())
    case Eng.Sock{+out, +wr}:
      Equal.trans(W.World,
        W.mute.conn(1n+1n+g, srv, (W.mute.turn.ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr),
          Eng.NoHead{}), Eng.conn.waits()),
        W.mute.conn(1n, srv, (W.mute.turn.ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr),
          Eng.NoHead{}), Eng.conn.waits()),
        W.mute.conn(1n+1n, srv, (W.mute.turn.ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr),
          Eng.NoHead{}), Eng.conn.waits()),
        wl.mute_ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr, 1n+g, Eng.conn.waits()),
        Equal.sym(W.World,
          W.mute.conn(1n+1n, srv, (W.mute.turn.ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr),
            Eng.NoHead{}), Eng.conn.waits()),
          W.mute.conn(1n, srv, (W.mute.turn.ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr),
            Eng.NoHead{}), Eng.conn.waits()),
          wl.mute_ws(srv, W.mute.segs(w, out, Eng.srv.idle(srv)), wr, 1n, Eng.conn.waits())))
    case Eng.Hold{wr}:
      match v:
        case 0n:
          {==}
        case 1n+u:
          {==}

def wl.sub_add(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      wl.sub_add(p, b)

def wl.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wl.le_refl(p)

def wl.lt_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      no({True{} == True{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      no({False{} == True{} : Bool}, e)
    case 1n+p 1n+q:
      wl.lt_le(p, q, e)

# a read that waited out its time: took exactly ms
def wl.waited(+now: Nat, +ms: U32) ->
  {Nat.is_le(U32.to_nat(ms), Nat.sub(Nat.add(now, U32.to_nat(ms)), now)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(Nat.add(now, U32.to_nat(ms)), now), U32.to_nat(ms),
    wl.sub_add(now, U32.to_nat(ms))) :
    {Nat.is_le(U32.to_nat(ms), _) == True{} : Bool}
  wl.le_refl(U32.to_nat(ms))

law wl.give_model:
  for +t: List<&2, W.Rd>
  for +wait: Nat
  for +bs: Bytes()
  for +ms: U32
  for +wr: List<&2, W.Wr>
  for +eager: Bool
  for +now: Nat
  for +fs: List<&2, W.Fil>
  for +out: Bytes()
  for +max: U32
  for soon: Bool
  for es: {soon == Nat.is_lt(wait, U32.to_nat(ms)) : Bool}
  for ef: {U32.is_le(U32.from_nat(Bytes.len(bs)), max) == True{} : Bool}
  {W.rx.seen(max, ms, now, W.w.rx.give(t, wait, bs, ms, wr, eager, now, fs, out, soon)) ==
    True{} : Bool}

def wl.give_model(t, wait, bs, ms, wr, eager, now, fs, out, max, soon, es, ef):
  match soon:
    case True{}:
      %Equal.sym(Bool, U32.is_le(U32.from_nat(Bytes.len(bs)), max), True{}, ef) :
        {_ && Nat.is_le(Nat.sub(Nat.add(now, wait), now), U32.to_nat(ms)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(Nat.add(now, wait), now), wait, wl.sub_add(now, wait)) :
        {Nat.is_le(_, U32.to_nat(ms)) == True{} : Bool}
      wl.lt_le(wait, U32.to_nat(ms), Equal.sym(Bool, True{}, Nat.is_lt(wait, U32.to_nat(ms)), es))
    case False{}:
      wl.waited(now, ms)

def Laws.rx_model(rd, wr, eager, now, fs, out, max, ms, e):
  match rd:
    case Nil{}:
      wl.waited(now, ms)
    case Con{ev, t}:
      match ev:
        case W.Hush{}:
          wl.waited(now, ms)
        case W.Cut{code}:
          {==}
        case W.Give{+wait, +bs}:
          wl.give_model(t, wait, bs, ms, wr, eager, now, fs, out, max,
            Nat.is_lt(wait, U32.to_nat(ms)), {==}, e)

def Laws.tx_stalled(rd, now, fs, out, h, t, ms):
  wl.waited(now, ms)

def Laws.tx_served(rd, now, fs, out, a, ms):
  %Equal.sym(Eng.Put(W.World), W.w.tx(W.eager(rd, now, fs, out), a, ms),
    W.sent(rd, now, fs, Bytes.append(out, a)), wl.tx_eager(rd, now, fs, out, a, ms)) :
    {W.tx.seen(ms, W.Reads{}, now, _) == True{} : Bool}
  {==}

def Laws.fread_model(f, n):
  match f n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+q:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      %Equal.sym(Nat, String.length.go(String.take(t, p), 1n),
        1n+String.length.go(String.take(t, p), 0n), Bytes.len.shift(String.take(t, p), 0n)) :
        {Nat.is_le(_, 1n+p) == True{} : Bool}
      Laws.fread_model(t, p)

# Bytes, bridged
# --------------
#
# The reader classes and lowercases every U32 as the reference does,
# not only the 256 bytes cls_is_spec runs: a U32 is its 32 bits, and one
# with a bit set past the low eight compares GT with every byte, so both
# sides call it a visible byte and leave its case alone -- the reader by
# adding a zero (add0). The low eight bits are 256 closed cases.
# Generated; every leaf is a computation.

# a word plus zero is the word
def add0(n: Nat, w: Word(n)) -> {Word.adc(n, w, Word.zero(n), False{}, False{}) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x},
                Word.adc(p, t, Word.zero(p), False{}, False{}), t, add0(p, t))
            case False{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x},
                Word.adc(p, t, Word.zero(p), False{}, False{}), t, add0(p, t))

# lowercasing a U32 past the bytes adds zero to it
def low.hi(w: Word(32n)) ->
  {Chr{U32{w}} == Chr{U32{Word.adc(32n, w, Word.zero(32n), False{}, False{})}} : Char}:
  Equal.sym(Char, Chr{U32{Word.adc(32n, w, Word.zero(32n), False{}, False{})}}, Chr{U32{w}},
    Equal.cong(Word(32n), Char, x => Chr{U32{x}},
      Word.adc(32n, w, Word.zero(32n), False{}, False{}), w, add0(32n, w)))

def br.cls.lo(b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b7 b6 b5 b4 b3 b2 b1 b0:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

def br.cls.hi8(b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool,
    b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b8:
    case True{}:
      {==}
    case False{}:
      br.cls.lo(b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi9(b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
    b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b9:
    case True{}:
      {==}
    case False{}:
      br.cls.hi8(b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi10(b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool,
    b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b10:
    case True{}:
      {==}
    case False{}:
      br.cls.hi9(b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi11(b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool,
    b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b11:
    case True{}:
      {==}
    case False{}:
      br.cls.hi10(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi12(b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool,
    b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b12:
    case True{}:
      {==}
    case False{}:
      br.cls.hi11(b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi13(b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool,
    b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b13:
    case True{}:
      {==}
    case False{}:
      br.cls.hi12(b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi14(b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool,
    b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b14:
    case True{}:
      {==}
    case False{}:
      br.cls.hi13(b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi15(b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool,
    b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b15:
    case True{}:
      {==}
    case False{}:
      br.cls.hi14(b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi16(b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool,
    b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool,
    b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0,
      WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b16:
    case True{}:
      {==}
    case False{}:
      br.cls.hi15(b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi17(b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool,
    b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
    b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0,
      WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b17:
    case True{}:
      {==}
    case False{}:
      br.cls.hi16(b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi18(b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool,
    b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool,
    b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1,
      WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
      WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b18:
    case True{}:
      {==}
    case False{}:
      br.cls.hi17(b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi19(b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool,
    b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool,
    b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1,
      WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
      WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b19:
    case True{}:
      {==}
    case False{}:
      br.cls.hi18(b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1,
          b0)

def br.cls.hi20(b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool,
    b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool,
    b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1,
      WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
      WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b20:
    case True{}:
      {==}
    case False{}:
      br.cls.hi19(b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2,
          b1, b0)

def br.cls.hi21(b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool,
    b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool,
    b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1,
      WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
      WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20,
      WCon{b21, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b21:
    case True{}:
      {==}
    case False{}:
      br.cls.hi20(b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4,
          b3, b2, b1, b0)

def br.cls.hi22(b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool,
    b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool,
    b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b22:
    case True{}:
      {==}
    case False{}:
      br.cls.hi21(b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5,
          b4, b3, b2, b1, b0)

def br.cls.hi23(b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool,
    b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool,
    b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b23:
    case True{}:
      {==}
    case False{}:
      br.cls.hi22(b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
          b5, b4, b3, b2, b1, b0)

def br.cls.hi24(b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool,
    b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool,
    b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool,
    b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b24:
    case True{}:
      {==}
    case False{}:
      br.cls.hi23(b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7,
          b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi25(b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool,
    b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool,
    b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
    b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b25:
    case True{}:
      {==}
    case False{}:
      br.cls.hi24(b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9,
          b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi26(b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool,
    b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool,
    b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool,
    b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b26:
    case True{}:
      {==}
    case False{}:
      br.cls.hi25(b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10,
          b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi27(b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool,
    b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool,
    b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool,
    b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
      WCon{b27, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b27:
    case True{}:
      {==}
    case False{}:
      br.cls.hi26(b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11,
          b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi28(b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool,
    b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool,
    b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool,
    b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
      WCon{b27, WCon{b28, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b28:
    case True{}:
      {==}
    case False{}:
      br.cls.hi27(b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12,
          b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi29(b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool,
    b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool,
    b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool,
    b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
      WCon{b27, WCon{b28, WCon{b29, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b29:
    case True{}:
      {==}
    case False{}:
      br.cls.hi28(b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13,
          b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi30(b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool,
    b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool,
    b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool,
    b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
      WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b30:
    case True{}:
      {==}
    case False{}:
      br.cls.hi29(b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14,
          b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.hi31(b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool,
    b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool,
    b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool,
    b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
      WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match b31:
    case True{}:
      {==}
    case False{}:
      br.cls.hi30(b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15,
          b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.p3(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool,
    b8: Bool, b9: Bool, b10: Bool, b11: Bool, b12: Bool, b13: Bool, b14: Bool, b15: Bool,
    b16: Bool, b17: Bool, b18: Bool, b19: Bool, b20: Bool, b21: Bool, b22: Bool, b23: Bool,
    w24: Word(8n)) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
      WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23,
      w24}}}}}}}}}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
      WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, w24}}}}}}}}}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match w24:
    case WCon{b24, w25}:
      match w25:
        case WCon{b25, w26}:
          match w26:
            case WCon{b26, w27}:
              match w27:
                case WCon{b27, w28}:
                  match w28:
                    case WCon{b28, w29}:
                      match w29:
                        case WCon{b29, w30}:
                          match w30:
                            case WCon{b30, w31}:
                              match w31:
                                case WCon{b31, w32}:
                                  match w32:
                                    case WNil{}:
                                      br.cls.hi31(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22,
                                          b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11,
                                          b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.cls.p2(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool,
    b8: Bool, b9: Bool, b10: Bool, b11: Bool, b12: Bool, b13: Bool, b14: Bool, b15: Bool,
    w16: Word(16n)) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
      WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15,
      w16}}}}}}}}}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5,
      WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14,
      WCon{b15, w16}}}}}}}}}}}}}}}}}) : Eng.Cls}:
  match w16:
    case WCon{b16, w17}:
      match w17:
        case WCon{b17, w18}:
          match w18:
            case WCon{b18, w19}:
              match w19:
                case WCon{b19, w20}:
                  match w20:
                    case WCon{b20, w21}:
                      match w21:
                        case WCon{b21, w22}:
                          match w22:
                            case WCon{b22, w23}:
                              match w23:
                                case WCon{b23, w24}:
                                  br.cls.p3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
                                      b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, w24)

def br.cls.p1(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool,
    w8: Word(24n)) ->
  {Spec.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      w8}}}}}}}}}) == Eng.cls(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6,
      WCon{b7, w8}}}}}}}}}) : Eng.Cls}:
  match w8:
    case WCon{b8, w9}:
      match w9:
        case WCon{b9, w10}:
          match w10:
            case WCon{b10, w11}:
              match w11:
                case WCon{b11, w12}:
                  match w12:
                    case WCon{b12, w13}:
                      match w13:
                        case WCon{b13, w14}:
                          match w14:
                            case WCon{b14, w15}:
                              match w15:
                                case WCon{b15, w16}:
                                  br.cls.p2(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
                                      b13, b14, b15, w16)

def br.cls(c: U32) -> {Spec.cls(c) == Eng.cls(c) : Eng.Cls}:
  match c:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          match w5:
                            case WCon{b5, w6}:
                              match w6:
                                case WCon{b6, w7}:
                                  match w7:
                                    case WCon{b7, w8}:
                                      br.cls.p1(b0, b1, b2, b3, b4, b5, b6, b7, w8)

def br.low.lo(b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b7 b6 b5 b4 b3 b2 b1 b0:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

def br.low.hi8(b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool,
    b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b8:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{True{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.lo(b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi9(b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
    b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b9:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi8(b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi10(b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool,
    b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b10:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi9(b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi11(b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool,
    b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b11:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi10(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi12(b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool,
    b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b12:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi11(b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi13(b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool,
    b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b13:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{True{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi12(b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi14(b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool,
    b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b14:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{True{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi13(b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi15(b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool,
    b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b15:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{True{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi14(b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi16(b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool,
    b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool,
    b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b16:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{True{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi15(b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi17(b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool,
    b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
    b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b17:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
          WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi16(b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi18(b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool,
    b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool,
    b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b18:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi17(b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi19(b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool,
    b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool,
    b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b19:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi18(b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1,
          b0)

def br.low.hi20(b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool,
    b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool,
    b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b20:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi19(b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2,
          b1, b0)

def br.low.hi21(b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool,
    b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool,
    b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0,
      WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19,
      WCon{b20, WCon{b21, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b21:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi20(b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4,
          b3, b2, b1, b0)

def br.low.hi22(b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool,
    b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool,
    b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0,
      WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19,
      WCon{b20, WCon{b21, WCon{b22, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b22:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{True{}, WCon{False{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi21(b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5,
          b4, b3, b2, b1, b0)

def br.low.hi23(b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool,
    b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool,
    b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0,
      WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19,
      WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b23:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{True{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi22(b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
          b5, b4, b3, b2, b1, b0)

def br.low.hi24(b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool,
    b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool,
    b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool,
    b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b24:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{True{}, WCon{False{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi23(b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7,
          b6, b5, b4, b3, b2, b1, b0)

def br.low.hi25(b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool,
    b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool,
    b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
    b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b25:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{True{},
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi24(b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9,
          b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi26(b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool,
    b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool,
    b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool,
    b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{b26, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{False{}, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b26:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
          WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi25(b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10,
          b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi27(b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool,
    b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool,
    b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool,
    b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{b26, WCon{b27, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{False{}, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b27:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
          WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi26(b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11,
          b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi28(b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool,
    b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool,
    b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool,
    b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{b26, WCon{b27, WCon{b28, WCon{False{}, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{False{},
      WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b28:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
          WCon{b27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi27(b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12,
          b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi29(b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool,
    b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool,
    b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool,
    b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{False{}, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{False{},
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b29:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
          WCon{b27, WCon{b28, WCon{True{}, WCon{False{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi28(b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13,
          b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi30(b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool,
    b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool,
    b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool,
    b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{False{},
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30,
      WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b30:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
          WCon{b27, WCon{b28, WCon{b29, WCon{True{}, WCon{False{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi29(b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14,
          b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.hi31(b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool,
    b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool,
    b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool,
    b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25,
      WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2,
      WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
      WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30,
      WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match b31:
    case True{}:
      low.hi(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8,
          WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17,
          WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26,
          WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{True{},
          WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
    case False{}:
      br.low.hi30(b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15,
          b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.p3(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool,
    b8: Bool, b9: Bool, b10: Bool, b11: Bool, b12: Bool, b13: Bool, b14: Bool, b15: Bool,
    b16: Bool, b17: Bool, b18: Bool, b19: Bool, b20: Bool, b21: Bool, b22: Bool, b23: Bool,
    w24: Word(8n)) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16,
      WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23,
      w24}}}}}}}}}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
      WCon{b23, w24}}}}}}}}}}}}}}}}}}}}}}}}}}) : Char}:
  match w24:
    case WCon{b24, w25}:
      match w25:
        case WCon{b25, w26}:
          match w26:
            case WCon{b26, w27}:
              match w27:
                case WCon{b27, w28}:
                  match w28:
                    case WCon{b28, w29}:
                      match w29:
                        case WCon{b29, w30}:
                          match w30:
                            case WCon{b30, w31}:
                              match w31:
                                case WCon{b31, w32}:
                                  match w32:
                                    case WNil{}:
                                      br.low.hi31(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22,
                                          b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11,
                                          b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def br.low.p2(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool,
    b8: Bool, b9: Bool, b10: Bool, b11: Bool, b12: Bool, b13: Bool, b14: Bool, b15: Bool,
    w16: Word(16n)) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15,
      w16}}}}}}}}}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
      WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13,
      WCon{b14, WCon{b15, w16}}}}}}}}}}}}}}}}}}) : Char}:
  match w16:
    case WCon{b16, w17}:
      match w17:
        case WCon{b17, w18}:
          match w18:
            case WCon{b18, w19}:
              match w19:
                case WCon{b19, w20}:
                  match w20:
                    case WCon{b20, w21}:
                      match w21:
                        case WCon{b21, w22}:
                          match w22:
                            case WCon{b22, w23}:
                              match w23:
                                case WCon{b23, w24}:
                                  br.low.p3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
                                      b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, w24)

def br.low.p1(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool,
    w8: Word(24n)) ->
  {Chr{Spec.lower(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      w8}}}}}}}}})} == Char.to_lower(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5,
      WCon{b6, WCon{b7, w8}}}}}}}}}}) : Char}:
  match w8:
    case WCon{b8, w9}:
      match w9:
        case WCon{b9, w10}:
          match w10:
            case WCon{b10, w11}:
              match w11:
                case WCon{b11, w12}:
                  match w12:
                    case WCon{b12, w13}:
                      match w13:
                        case WCon{b13, w14}:
                          match w14:
                            case WCon{b14, w15}:
                              match w15:
                                case WCon{b15, w16}:
                                  br.low.p2(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
                                      b13, b14, b15, w16)

def br.low(c: U32) -> {Chr{Spec.lower(c)} == Char.to_lower(Chr{c}) : Char}:
  match c:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          match w5:
                            case WCon{b5, w6}:
                              match w6:
                                case WCon{b6, w7}:
                                  match w7:
                                    case WCon{b7, w8}:
                                      br.low.p1(b0, b1, b2, b3, b4, b5, b6, b7, w8)

def br.lower(c: U32) -> {Spec.lower(c) == Eng.lower(c) : U32}:
  Equal.cong(Char, U32, x => Char.to_u32(x), Chr{Spec.lower(c)}, Char.to_lower(Chr{c}), br.low(c))

def Laws.cls_every(c):
  Equal.sym(Eng.Cls, Spec.cls(c), Eng.cls(c), br.cls(c))

def Laws.lower_every(c):
  Equal.sym(U32, Spec.lower(c), Eng.lower(c), br.lower(c))

# The reader is the framing
# =========================
#
# frame_sim: for every input, the reader fed it agrees with spec.bend's
# frame() of it. The proof is a simulation. frame() is a walk that
# gathers a line's bytes and reads the line whole at its CR; the reader
# steps each byte. REL (below) says where the reader is, given where
# the walk is, and a byte moves both so that REL holds after it (STEP);
# at the input's end REL gives the agreement (END); induction on the
# input does the rest (walk.lem).
#
# Inside a line, REL says only that the reader is a line-start reader
# fed the line so far. What that reader is, the spec's view of the same
# bytes says: line.req and line.field prove, for every line, that the
# reader's state is the one the view names -- a method, target or
# version being read; a name; a value in the state its field reads it
# in -- or refused. They go token by token: a span of bytes a token may
# hold is one the reader stays on (RS), and the byte that stops the span
# is stepped as the spec reads it. At the CR, the view says what the
# line means and the reader's pending fields change the same way; the
# two sides are compared through PV, which forgets only how the reader
# stores "no upgrade field seen".
#
# A chunked body's framing is regular, and both sides read it as a table
# of where a byte arrives and where it goes: at.eng and go.eng name the
# reader's place and move for each of the spec's, tbl says the tables
# agree row by row, and xk.is that the two sides tell the same bytes
# apart (a class, then a HEXDIG's value, then ";", "=", DQUOTE and "\").
# REL holds the reader at the spec's place with the same size, body so
# far and budget; the budget's arithmetic is the same U32 terms on both
# sides, so a case on each comparison is all the proof needs of it.
#
# Every byte is classified twice, once by each side; br.cls and br.low
# (generated: a set bit past the low eight makes every comparison with a
# byte GT, and the low eight are 256 closed cases) say the two agree on
# every U32.

# The engine seen through the spec
# --------------------------------

def br.lows(s: Bytes()) -> {Spec.lows(s) == Eng.lows(s) : Bytes()}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      %br.low(c) : {SCon{Chr{Spec.lower(c)}, Spec.lows(t)} == SCon{_, String.to_lower(t)} : Bytes()}
      %br.lows(t) : {SCon{Chr{Spec.lower(c)}, Spec.lows(t)} == SCon{Chr{Spec.lower(c)}, _} : Bytes()}
      {==}

# the step of a reader, with the class of its byte given
def SK(p: Eng.P, k: Eng.Cls, c: U32) -> Eng.P:
  match p:
    case Eng.P{st, pd, out}:
      Eng.step.at(st, k, c, pd, out)

def stepc(p: Eng.P, +c: U32) -> {SK(p, Spec.cls(c), c) == Eng.step(p, c) : Eng.P}:
  match p:
    case Eng.P{st, pd, out}:
      %br.cls(c) : {Eng.step.at(st, Spec.cls(c), c, pd, out) == Eng.step.at(st, _, c, pd, out) : Eng.P}
      {==}

def feedc(+c: U32, -t: List<&2, U32>, p: Eng.P) ->
  {Eng.feed(t, SK(p, Spec.cls(c), c)) == Eng.feed(Con{c, t}, p) : Eng.P}:
  Equal.cong(Eng.P, Eng.P, x => Eng.feed(t, x), SK(p, Spec.cls(c), c), Eng.step(p, c), stepc(p, c))

def eqs(+a: Bytes(), +b: Bytes()) -> {Spec.eq(a, b) == Eng.bytes.eq(a, b) : Bool}:
  Equal.sym(Bool, Eng.bytes.eq(a, b), Spec.eq(a, b), eq_is_spec(a, b))

# a refused reader: whatever it held pending, it is Bad with its
# requests
def kill(p: Eng.P) -> Eng.P:
  match p:
    case Eng.P{st, pd, out}:
      Eng.P{st, Eng.pend.new(), out}

def Dead(-p: Eng.P, -out: List<&2, Eng.Req>) -> Data:
  {kill(p) == Eng.P{Eng.Bad{}, Eng.pend.new(), out} : Eng.P}

def st.of(p: Eng.P) -> Eng.St:
  match p:
    case Eng.P{st, pd, out}:
      st

def out.of(p: Eng.P) -> List<&2, Eng.Req>:
  match p:
    case Eng.P{st, pd, out}:
      out

def dead.step(p: Eng.P, -k: Eng.Cls, -c: U32, -out: List<&2, Eng.Req>) ->
  Dead(p, out) -> Dead(SK(p, k, c), out):
  match p:
    case Eng.P{st, pd, o}:
      +d =>
        %Equal.sym(Eng.St, st, Eng.Bad{},
          Equal.cong(Eng.P, Eng.St, x => st.of(x), Eng.P{st, Eng.pend.new(), o},
            Eng.P{Eng.Bad{}, Eng.pend.new(), out}, d)) :
          {kill(Eng.step.at(_, k, c, pd, o)) == Eng.P{Eng.Bad{}, Eng.pend.new(), out} : Eng.P}
        %Equal.sym(List<&2, Eng.Req>, o, out,
          Equal.cong(Eng.P, List<&2, Eng.Req>, x => out.of(x), Eng.P{st, Eng.pend.new(), o},
            Eng.P{Eng.Bad{}, Eng.pend.new(), out}, d)) :
          {kill(Eng.step.at(Eng.Bad{}, k, c, pd, _)) == Eng.P{Eng.Bad{}, Eng.pend.new(), out} : Eng.P}
        {==}

def dead.byte(p: Eng.P, -c: U32, -out: List<&2, Eng.Req>) -> Dead(p, out) -> Dead(Eng.step(p, c), out):
  match p:
    case Eng.P{st, pd, o}:
      dead.step(Eng.P{st, pd, o}, Eng.cls(c), c, out)

def dead.feed(xs: List<&2, U32>, +p: Eng.P, -out: List<&2, Eng.Req>) ->
  Dead(p, out) -> Dead(Eng.feed(xs, p), out):
  match xs:
    case Nil{}:
      d => d
    case Con{c, t}:
      d => dead.feed(t, Eng.step(p, c), out)(dead.byte(p, c, out)(d))

def dead.bad(xs: List<&2, U32>, pd: Eng.Pend, out: List<&2, Eng.Req>) ->
  Dead(Eng.feed(xs, Eng.P{Eng.Bad{}, pd, out}), out):
  dead.feed(xs, Eng.P{Eng.Bad{}, pd, out}, out)({==})

# a line holds no CR and no LF: they end it
def notcrlf(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KCr{}:
      False{}
    case Eng.KLf{}:
      False{}
    case _:
      True{}

def Plain(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{c, t}:
      {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(t)

def plain.snoc.con(-x: U32, -t: List<&2, U32>, -c: U32,
  pl: {notcrlf(Spec.cls(x)) == True{} : Bool} & Plain(t), ih: Plain(t) -> Plain(Spec.snoc(t, c))) ->
  {notcrlf(Spec.cls(x)) == True{} : Bool} & Plain(Spec.snoc(t, c)):
  (a, b) = pl
  (a, ih(b))

def plain.snoc(xs: List<&2, U32>, -c: U32, nc: {notcrlf(Spec.cls(c)) == True{} : Bool}) ->
  Plain(xs) -> Plain(Spec.snoc(xs, c)):
  match xs:
    case Nil{}:
      pl => (nc, Unit{})
    case Con{x, t}:
      pl => plain.snoc.con(x, t, c, pl, plain.snoc(t, c, nc))

# a list read as bytes, grown by one
def fl.snoc(xs: List<&2, U32>, -c: U32) ->
  {Bytes.from_list(Spec.snoc(xs, c)) == Eng.push(Bytes.from_list(xs), c) : Bytes()}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{Chr{x}, y}, Bytes.from_list(Spec.snoc(t, c)),
        Eng.push(Bytes.from_list(t), c), fl.snoc(t, c))

def lb.snoc(xs: List<&2, U32>, -c: U32) ->
  {Spec.lows(Bytes.from_list(Spec.snoc(xs, c))) ==
    Eng.push(Spec.lows(Bytes.from_list(xs)), Spec.lower(c)) : Bytes()}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{Chr{Spec.lower(x)}, y},
        Spec.lows(Bytes.from_list(Spec.snoc(t, c))),
        Eng.push(Spec.lows(Bytes.from_list(t)), Spec.lower(c)), lb.snoc(t, c))

# a run of a token, stepped: where the reader is while it reads one
type Sel is Data:
  SelR{sel: Eng.Run}
  SelL0{}
  SelLt{v: U32}
  SelK0{}
  SelLv{}
  SelE0{}
  SelE{}

def put(s: Sel, acc: Bytes()) -> Eng.St:
  match s:
    case SelR{sel}:
      Eng.st.put(sel, acc)
    case SelL0{}:
      Eng.InL0{}
    case SelLt{v}:
      Eng.InLt{v}
    case SelK0{}:
      Eng.InLk0{}
    case SelLv{}:
      Eng.InLv{acc}
    case SelE0{}:
      Eng.InLe0{}
    case SelE{}:
      Eng.InLe{acc}

def tokof(s: Sel) -> Spec.Tok:
  match s:
    case SelR{Eng.RM{}}:
      Spec.TMeth{}
    case SelR{Eng.RT{}}:
      Spec.TTarget{}
    case SelR{Eng.RV{}}:
      Spec.TVer{}
    case SelR{Eng.RN{}}:
      Spec.TName{}
    case SelR{Eng.RK{}}:
      Spec.TVal{}
    case SelR{Eng.RX{}}:
      Spec.TVal{}
    case SelL0{}:
      Spec.TOws{}
    case SelLt{v}:
      Spec.TOws{}
    case SelK0{}:
      Spec.TOws{}
    case SelLv{}:
      Spec.TVal{}
    case SelE0{}:
      Spec.TOws{}
    case SelE{}:
      Spec.TVal{}

# a byte a token holds is one the reader stays on, adding it
def SS(-s: Sel, -k: Eng.Cls, -c: U32, -acc: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) -> Type:
  {Eng.P{put(s, Eng.push(acc, c)), pd, out} == Eng.step.at(put(s, acc), k, c, pd, out) : Eng.P}

def stay(s: Sel, k: Eng.Cls, -c: U32, -acc: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Spec.allows(tokof(s), k) == True{} : Bool} -> SS(s, k, c, acc, pd, out):
  match s k:
    case SelR{Eng.RM{}} Eng.KSp{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KSp{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KHt{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KHt{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KCr{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KCr{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KLf{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KLf{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KCo{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KCo{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KCm{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KCm{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KDg{}:
      e => {==}
    case SelR{Eng.RM{}} Eng.KTk{}:
      e => {==}
    case SelR{Eng.RM{}} Eng.KVc{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KVc{}, c, acc, pd, out), e)
    case SelR{Eng.RM{}} Eng.KCt{}:
      e => no(SS(SelR{Eng.RM{}}, Eng.KCt{}, c, acc, pd, out), e)
    case SelR{Eng.RT{}} Eng.KSp{}:
      e => no(SS(SelR{Eng.RT{}}, Eng.KSp{}, c, acc, pd, out), e)
    case SelR{Eng.RT{}} Eng.KHt{}:
      e => no(SS(SelR{Eng.RT{}}, Eng.KHt{}, c, acc, pd, out), e)
    case SelR{Eng.RT{}} Eng.KCr{}:
      e => no(SS(SelR{Eng.RT{}}, Eng.KCr{}, c, acc, pd, out), e)
    case SelR{Eng.RT{}} Eng.KLf{}:
      e => no(SS(SelR{Eng.RT{}}, Eng.KLf{}, c, acc, pd, out), e)
    case SelR{Eng.RT{}} Eng.KCo{}:
      e => {==}
    case SelR{Eng.RT{}} Eng.KCm{}:
      e => {==}
    case SelR{Eng.RT{}} Eng.KDg{}:
      e => {==}
    case SelR{Eng.RT{}} Eng.KTk{}:
      e => {==}
    case SelR{Eng.RT{}} Eng.KVc{}:
      e => {==}
    case SelR{Eng.RT{}} Eng.KCt{}:
      e => no(SS(SelR{Eng.RT{}}, Eng.KCt{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KSp{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KSp{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KHt{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KHt{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KCr{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KCr{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KLf{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KLf{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KCo{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KCo{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KCm{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KCm{}, c, acc, pd, out), e)
    case SelR{Eng.RV{}} Eng.KDg{}:
      e => {==}
    case SelR{Eng.RV{}} Eng.KTk{}:
      e => {==}
    case SelR{Eng.RV{}} Eng.KVc{}:
      e => {==}
    case SelR{Eng.RV{}} Eng.KCt{}:
      e => no(SS(SelR{Eng.RV{}}, Eng.KCt{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KSp{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KSp{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KHt{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KHt{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KCr{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KCr{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KLf{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KLf{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KCo{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KCo{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KCm{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KCm{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KDg{}:
      e => {==}
    case SelR{Eng.RN{}} Eng.KTk{}:
      e => {==}
    case SelR{Eng.RN{}} Eng.KVc{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KVc{}, c, acc, pd, out), e)
    case SelR{Eng.RN{}} Eng.KCt{}:
      e => no(SS(SelR{Eng.RN{}}, Eng.KCt{}, c, acc, pd, out), e)
    case SelR{Eng.RK{}} Eng.KSp{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KHt{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KCr{}:
      e => no(SS(SelR{Eng.RK{}}, Eng.KCr{}, c, acc, pd, out), e)
    case SelR{Eng.RK{}} Eng.KLf{}:
      e => no(SS(SelR{Eng.RK{}}, Eng.KLf{}, c, acc, pd, out), e)
    case SelR{Eng.RK{}} Eng.KCo{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KCm{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KDg{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KTk{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KVc{}:
      e => {==}
    case SelR{Eng.RK{}} Eng.KCt{}:
      e => no(SS(SelR{Eng.RK{}}, Eng.KCt{}, c, acc, pd, out), e)
    case SelR{Eng.RX{}} Eng.KSp{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KHt{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KCr{}:
      e => no(SS(SelR{Eng.RX{}}, Eng.KCr{}, c, acc, pd, out), e)
    case SelR{Eng.RX{}} Eng.KLf{}:
      e => no(SS(SelR{Eng.RX{}}, Eng.KLf{}, c, acc, pd, out), e)
    case SelR{Eng.RX{}} Eng.KCo{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KCm{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KDg{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KTk{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KVc{}:
      e => {==}
    case SelR{Eng.RX{}} Eng.KCt{}:
      e => no(SS(SelR{Eng.RX{}}, Eng.KCt{}, c, acc, pd, out), e)
    case SelL0{} Eng.KSp{}:
      e => {==}
    case SelL0{} Eng.KHt{}:
      e => {==}
    case SelL0{} Eng.KCr{}:
      e => no(SS(SelL0{}, Eng.KCr{}, c, acc, pd, out), e)
    case SelL0{} Eng.KLf{}:
      e => no(SS(SelL0{}, Eng.KLf{}, c, acc, pd, out), e)
    case SelL0{} Eng.KCo{}:
      e => no(SS(SelL0{}, Eng.KCo{}, c, acc, pd, out), e)
    case SelL0{} Eng.KCm{}:
      e => no(SS(SelL0{}, Eng.KCm{}, c, acc, pd, out), e)
    case SelL0{} Eng.KDg{}:
      e => no(SS(SelL0{}, Eng.KDg{}, c, acc, pd, out), e)
    case SelL0{} Eng.KTk{}:
      e => no(SS(SelL0{}, Eng.KTk{}, c, acc, pd, out), e)
    case SelL0{} Eng.KVc{}:
      e => no(SS(SelL0{}, Eng.KVc{}, c, acc, pd, out), e)
    case SelL0{} Eng.KCt{}:
      e => no(SS(SelL0{}, Eng.KCt{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KSp{}:
      e => {==}
    case SelLt{v} Eng.KHt{}:
      e => {==}
    case SelLt{v} Eng.KCr{}:
      e => no(SS(SelLt{v}, Eng.KCr{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KLf{}:
      e => no(SS(SelLt{v}, Eng.KLf{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KCo{}:
      e => no(SS(SelLt{v}, Eng.KCo{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KCm{}:
      e => no(SS(SelLt{v}, Eng.KCm{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KDg{}:
      e => no(SS(SelLt{v}, Eng.KDg{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KTk{}:
      e => no(SS(SelLt{v}, Eng.KTk{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KVc{}:
      e => no(SS(SelLt{v}, Eng.KVc{}, c, acc, pd, out), e)
    case SelLt{v} Eng.KCt{}:
      e => no(SS(SelLt{v}, Eng.KCt{}, c, acc, pd, out), e)
    case SelK0{} Eng.KSp{}:
      e => {==}
    case SelK0{} Eng.KHt{}:
      e => {==}
    case SelK0{} Eng.KCr{}:
      e => no(SS(SelK0{}, Eng.KCr{}, c, acc, pd, out), e)
    case SelK0{} Eng.KLf{}:
      e => no(SS(SelK0{}, Eng.KLf{}, c, acc, pd, out), e)
    case SelK0{} Eng.KCo{}:
      e => no(SS(SelK0{}, Eng.KCo{}, c, acc, pd, out), e)
    case SelK0{} Eng.KCm{}:
      e => no(SS(SelK0{}, Eng.KCm{}, c, acc, pd, out), e)
    case SelK0{} Eng.KDg{}:
      e => no(SS(SelK0{}, Eng.KDg{}, c, acc, pd, out), e)
    case SelK0{} Eng.KTk{}:
      e => no(SS(SelK0{}, Eng.KTk{}, c, acc, pd, out), e)
    case SelK0{} Eng.KVc{}:
      e => no(SS(SelK0{}, Eng.KVc{}, c, acc, pd, out), e)
    case SelK0{} Eng.KCt{}:
      e => no(SS(SelK0{}, Eng.KCt{}, c, acc, pd, out), e)
    case SelLv{} Eng.KSp{}:
      e => {==}
    case SelLv{} Eng.KHt{}:
      e => {==}
    case SelLv{} Eng.KCr{}:
      e => no(SS(SelLv{}, Eng.KCr{}, c, acc, pd, out), e)
    case SelLv{} Eng.KLf{}:
      e => no(SS(SelLv{}, Eng.KLf{}, c, acc, pd, out), e)
    case SelLv{} Eng.KCo{}:
      e => {==}
    case SelLv{} Eng.KCm{}:
      e => {==}
    case SelLv{} Eng.KDg{}:
      e => {==}
    case SelLv{} Eng.KTk{}:
      e => {==}
    case SelLv{} Eng.KVc{}:
      e => {==}
    case SelLv{} Eng.KCt{}:
      e => no(SS(SelLv{}, Eng.KCt{}, c, acc, pd, out), e)
    case SelE0{} Eng.KSp{}:
      e => {==}
    case SelE0{} Eng.KHt{}:
      e => {==}
    case SelE0{} Eng.KCr{}:
      e => no(SS(SelE0{}, Eng.KCr{}, c, acc, pd, out), e)
    case SelE0{} Eng.KLf{}:
      e => no(SS(SelE0{}, Eng.KLf{}, c, acc, pd, out), e)
    case SelE0{} Eng.KCo{}:
      e => no(SS(SelE0{}, Eng.KCo{}, c, acc, pd, out), e)
    case SelE0{} Eng.KCm{}:
      e => no(SS(SelE0{}, Eng.KCm{}, c, acc, pd, out), e)
    case SelE0{} Eng.KDg{}:
      e => no(SS(SelE0{}, Eng.KDg{}, c, acc, pd, out), e)
    case SelE0{} Eng.KTk{}:
      e => no(SS(SelE0{}, Eng.KTk{}, c, acc, pd, out), e)
    case SelE0{} Eng.KVc{}:
      e => no(SS(SelE0{}, Eng.KVc{}, c, acc, pd, out), e)
    case SelE0{} Eng.KCt{}:
      e => no(SS(SelE0{}, Eng.KCt{}, c, acc, pd, out), e)
    case SelE{} Eng.KSp{}:
      e => {==}
    case SelE{} Eng.KHt{}:
      e => {==}
    case SelE{} Eng.KCr{}:
      e => no(SS(SelE{}, Eng.KCr{}, c, acc, pd, out), e)
    case SelE{} Eng.KLf{}:
      e => no(SS(SelE{}, Eng.KLf{}, c, acc, pd, out), e)
    case SelE{} Eng.KCo{}:
      e => {==}
    case SelE{} Eng.KCm{}:
      e => {==}
    case SelE{} Eng.KDg{}:
      e => {==}
    case SelE{} Eng.KTk{}:
      e => {==}
    case SelE{} Eng.KVc{}:
      e => {==}
    case SelE{} Eng.KCt{}:
      e => no(SS(SelE{}, Eng.KCt{}, c, acc, pd, out), e)

# where the reader is after the run a span took: the run's state with
# the run added, and, when a byte stopped it, that byte stepped and what
# follows it walked
def RES.at(stop: Spec.Stop, s: Sel, acc: Bytes(), pd: Eng.Pend, out: List<&2, Eng.Req>) -> Eng.P:
  match stop:
    case Spec.SEnd{}:
      Eng.P{put(s, acc), pd, out}
    case Spec.SAt{k, c, rest}:
      Eng.feed(rest, Eng.step.at(put(s, acc), k, c, pd, out))

def RES(sp: Spec.Span, s: Sel, acc: Bytes(), pd: Eng.Pend, out: List<&2, Eng.Req>) -> Eng.P:
  match sp:
    case Spec.Span{run, stop}:
      RES.at(stop, s, Bytes.append(acc, Bytes.from_list(run)), pd, out)

def respush(-c: U32, sp: Spec.Span, -s: Sel, acc: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {RES(sp, s, Eng.push(acc, c), pd, out) == RES(Spec.span.push(c, sp), s, acc, pd, out) : Eng.P}:
  match sp:
    case Spec.Span{r, st}:
      %push_app(acc, c, Bytes.from_list(r)) :
        {RES.at(st, s, Bytes.append(Eng.push(acc, c), Bytes.from_list(r)), pd, out) ==
          RES.at(st, s, _, pd, out) : Eng.P}
      {==}

def RSG(-x: List<&2, U32>, -s: Sel, -acc: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) -> Type:
  {RES(Spec.span(tokof(s), x), s, acc, pd, out) == Eng.feed(x, Eng.P{put(s, acc), pd, out}) : Eng.P}

def RS.ok(+s: Sel, +k: Eng.Cls, +c: U32, +t: List<&2, U32>, +acc: Bytes(), +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, ok: Bool, ih: RSG(t, s, Eng.push(acc, c), pd, out)) ->
  {Spec.allows(tokof(s), k) == ok : Bool} ->
  {RES(Spec.span.pick(ok, k, c, t, Spec.span(tokof(s), t)), s, acc, pd, out) ==
    Eng.feed(t, Eng.step.at(put(s, acc), k, c, pd, out)) : Eng.P}:
  match ok:
    case True{}:
      e =>
        %stay(s, k, c, acc, pd, out)(e) :
          {RES(Spec.span.push(c, Spec.span(tokof(s), t)), s, acc, pd, out) == Eng.feed(t, _) : Eng.P}
        %respush(c, Spec.span(tokof(s), t), s, acc, pd, out) :
          {_ == Eng.feed(t, Eng.P{put(s, Eng.push(acc, c)), pd, out}) : Eng.P}
        ih
    case False{}:
      e =>
        %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
          {Eng.feed(t, Eng.step.at(put(s, _), k, c, pd, out)) ==
            Eng.feed(t, Eng.step.at(put(s, acc), k, c, pd, out)) : Eng.P}
        {==}

# a span, stepped: the reader walks the run a byte at a time, staying
# on it, and steps the byte that stopped it
def RS(x: List<&2, U32>, +s: Sel, +acc: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  RSG(x, s, acc, pd, out):
  match x:
    case Nil{}:
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
        {Eng.P{put(s, _), pd, out} == Eng.P{put(s, acc), pd, out} : Eng.P}
      {==}
    case Con{+c, +t}:
      %feedc(c, t, Eng.P{put(s, acc), pd, out}) :
        {RES(Spec.span(tokof(s), Con{c, t}), s, acc, pd, out) == _ : Eng.P}
      RS.ok(s, Spec.cls(c), c, t, acc, pd, out, Spec.allows(tokof(s), Spec.cls(c)),
        RS(t, s, Eng.push(acc, c), pd, out))({==})

# anything, from True == False
def no2(-g: Type, e: {True{} == False{} : Bool}) -> g:
  %e : BD(_, Unit, g)
  Unit{}

# what a span stopped at: a byte its token does not hold, and, in a
# line, no CR or LF, with the rest of the line after it
def SW.at(-t: Spec.Tok, stop: Spec.Stop) -> Type:
  match stop:
    case Spec.SEnd{}:
      Unit
    case Spec.SAt{+k, c, rest}:
      {Spec.allows(t, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))

def SW(-t: Spec.Tok, sp: Spec.Span) -> Type:
  match sp:
    case Spec.Span{r, stop}:
      SW.at(t, stop)

def sw.push(-t: Spec.Tok, -c: U32, sp: Spec.Span) -> SW(t, sp) -> SW(t, Spec.span.push(c, sp)):
  match sp:
    case Spec.Span{r, stop}:
      h => h

def span.sw.ok(+t: Spec.Tok, +c: U32, +u: List<&2, U32>, ok: Bool,
  ih: Plain(u) -> SW(t, Spec.span(t, u))) ->
  {Spec.allows(t, Spec.cls(c)) == ok : Bool} -> {notcrlf(Spec.cls(c)) == True{} : Bool} -> Plain(u) ->
  SW(t, Spec.span.pick(ok, Spec.cls(c), c, u, Spec.span(t, u))):
  match ok:
    case True{}:
      e => nc => pu => sw.push(t, c, Spec.span(t, u))(ih(pu))
    case False{}:
      e => nc => pu => (e, (nc, pu))

def span.sw.con(+t: Spec.Tok, +c: U32, +u: List<&2, U32>,
  pl: {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(u), ih: Plain(u) -> SW(t, Spec.span(t, u))) ->
  SW(t, Spec.span(t, Con{c, u})):
  (nc, pu) = pl
  span.sw.ok(t, c, u, Spec.allows(t, Spec.cls(c)), ih)({==})(nc)(pu)

def span.sw(+t: Spec.Tok, x: List<&2, U32>) -> Plain(x) -> SW(t, Spec.span(t, x)):
  match x:
    case Nil{}:
      pl => Unit{}
    case Con{+c, +u}:
      pl => span.sw.con(t, c, u, pl, span.sw(t, u))

# The request line, seen
# ----------------------
#
# The reader's state after as much of a request line as has come, from
# a reader between requests, is fixed by the spec's view of that much:
# a method, a target or a version being read, with the method and the
# target, once closed, in the pending message -- or refused.

def pd1(m: List<&2, U32>) -> Eng.Pend:
  Eng.pend.meth(Eng.pend.new(), Eng.meth.of(Bytes.from_list(m)))

def pd2(m: List<&2, U32>, t: List<&2, U32>) -> Eng.Pend:
  Eng.pend.path(pd1(m), Bytes.from_list(t))

def LR.req(-p: Eng.P, v: Spec.RLine, -out: List<&2, Eng.Req>) -> Type:
  match v:
    case Spec.RNone{}:
      {p == Eng.P{Eng.Pre{}, Eng.pend.new(), out} : Eng.P}
    case Spec.RMeth{m}:
      {p == Eng.P{Eng.InM{Bytes.from_list(m)}, Eng.pend.new(), out} : Eng.P}
    case Spec.RTarget{m, t}:
      {p == Eng.P{Eng.InT{Bytes.from_list(t)}, pd1(m), out} : Eng.P}
    case Spec.RVer{m, t, v}:
      {p == Eng.P{Eng.InV{Bytes.from_list(v)}, pd2(m, t), out} : Eng.P}
    case Spec.RBad{}:
      Dead(p, out)

# the version
def G.ver(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +m: List<&2, U32>, +t: List<&2, U32>,
  +v: List<&2, U32>, +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InV{Bytes.from_list(v)}, k, c, pd2(m, t), out)), out)

def K.ver.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +m: List<&2, U32>, +t: List<&2, U32>,
  +v: List<&2, U32>, +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TVer{}, k) == False{} : Bool},
  nc: {notcrlf(k) == True{} : Bool}) -> G.ver(k, c, rest, m, t, v, out):
  match k:
    case Eng.KSp{}:
      dead.bad(rest, pd2(m, t), out)
    case Eng.KHt{}:
      dead.bad(rest, pd2(m, t), out)
    case Eng.KCr{}:
      no(G.ver(Eng.KCr{}, c, rest, m, t, v, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd2(m, t), out)
    case Eng.KCo{}:
      dead.bad(rest, pd2(m, t), out)
    case Eng.KCm{}:
      dead.bad(rest, pd2(m, t), out)
    case Eng.KDg{}:
      no2(G.ver(Eng.KDg{}, c, rest, m, t, v, out), mx)
    case Eng.KTk{}:
      no2(G.ver(Eng.KTk{}, c, rest, m, t, v, out), mx)
    case Eng.KVc{}:
      no2(G.ver(Eng.KVc{}, c, rest, m, t, v, out), mx)
    case Eng.KCt{}:
      dead.bad(rest, pd2(m, t), out)

def K.ver.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +m: List<&2, U32>, +t: List<&2, U32>,
  +v: List<&2, U32>, +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVer{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.ver(k, c, rest, m, t, v, out):
  (mx, np) = sw
  (nc, pr) = np
  K.ver.at(k, c, rest, m, t, v, out, mx, nc)

def K.ver.stop(+m: List<&2, U32>, +t: List<&2, U32>, +v: List<&2, U32>, stop: Spec.Stop,
  +out: List<&2, Eng.Req>) -> SW.at(Spec.TVer{}, stop) ->
  LR.req(RES.at(stop, SelR{Eng.RV{}}, Bytes.from_list(v), pd2(m, t), out),
    Spec.req.ver(m, t, Spec.Span{v, stop}), out):
  match stop:
    case Spec.SEnd{}:
      sw => {==}
    case Spec.SAt{k, c, rest}:
      sw => K.ver.sat(k, c, rest, m, t, v, out, sw)

def K.ver(+m: List<&2, U32>, +t: List<&2, U32>, sp: Spec.Span, +out: List<&2, Eng.Req>) ->
  SW(Spec.TVer{}, sp) -> LR.req(RES(sp, SelR{Eng.RV{}}, "", pd2(m, t), out), Spec.req.ver(m, t, sp), out):
  match sp:
    case Spec.Span{v, stop}:
      K.ver.stop(m, t, v, stop, out)

# the target
def K.target.sp(+m: List<&2, U32>, t: List<&2, U32>, +rest: List<&2, U32>, +out: List<&2, Eng.Req>) ->
  Plain(rest) -> LR.req(Eng.feed(rest, Eng.step.target(Bytes.from_list(t), pd1(m), out)),
    Spec.req.target.sp(m, t, rest), out):
  match t:
    case Nil{}:
      pl => dead.bad(rest, pd1(m), out)
    case Con{+h, +r}:
      pl =>
        %RS(rest, SelR{Eng.RV{}}, "", pd2(m, Con{h, r}), out) :
          LR.req(_, Spec.req.ver(m, Con{h, r}, Spec.span(Spec.TVer{}, rest)), out)
        K.ver(m, Con{h, r}, Spec.span(Spec.TVer{}, rest), out)(span.sw(Spec.TVer{}, rest)(pl))

def G.tgt(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +m: List<&2, U32>, +t: List<&2, U32>,
  +out: List<&2, Eng.Req>) -> Type:
  LR.req(Eng.feed(rest, Eng.step.at(Eng.InT{Bytes.from_list(t)}, k, c, pd1(m), out)),
    Spec.req.target(m, Spec.Span{t, Spec.SAt{k, c, rest}}), out)

def K.target.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +m: List<&2, U32>, +t: List<&2, U32>,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TTarget{}, k) == False{} : Bool},
  pr: Plain(rest)) -> G.tgt(k, c, rest, m, t, out):
  match k:
    case Eng.KSp{}:
      K.target.sp(m, t, rest, out)(pr)
    case Eng.KHt{}:
      dead.bad(rest, pd1(m), out)
    case Eng.KCr{}:
      dead.bad(rest, pd1(m), out)
    case Eng.KLf{}:
      dead.bad(rest, pd1(m), out)
    case Eng.KCo{}:
      no2(G.tgt(Eng.KCo{}, c, rest, m, t, out), mx)
    case Eng.KCm{}:
      no2(G.tgt(Eng.KCm{}, c, rest, m, t, out), mx)
    case Eng.KDg{}:
      no2(G.tgt(Eng.KDg{}, c, rest, m, t, out), mx)
    case Eng.KTk{}:
      no2(G.tgt(Eng.KTk{}, c, rest, m, t, out), mx)
    case Eng.KVc{}:
      no2(G.tgt(Eng.KVc{}, c, rest, m, t, out), mx)
    case Eng.KCt{}:
      dead.bad(rest, pd1(m), out)

def K.target.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +m: List<&2, U32>, +t: List<&2, U32>,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TTarget{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.tgt(k, c, rest, m, t, out):
  (mx, np) = sw
  (nc, pr) = np
  K.target.at(k, c, rest, m, t, out, mx, pr)

def K.target.stop(+m: List<&2, U32>, +t: List<&2, U32>, stop: Spec.Stop, +out: List<&2, Eng.Req>) ->
  SW.at(Spec.TTarget{}, stop) ->
  LR.req(RES.at(stop, SelR{Eng.RT{}}, Bytes.from_list(t), pd1(m), out),
    Spec.req.target(m, Spec.Span{t, stop}), out):
  match stop:
    case Spec.SEnd{}:
      sw => {==}
    case Spec.SAt{k, c, rest}:
      sw => K.target.sat(k, c, rest, m, t, out, sw)

def K.target(+m: List<&2, U32>, sp: Spec.Span, +out: List<&2, Eng.Req>) ->
  SW(Spec.TTarget{}, sp) -> LR.req(RES(sp, SelR{Eng.RT{}}, "", pd1(m), out), Spec.req.target(m, sp), out):
  match sp:
    case Spec.Span{t, stop}:
      K.target.stop(m, t, stop, out)

# the method
def G.meth(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>,
  +out: List<&2, Eng.Req>) -> Type:
  LR.req(Eng.feed(rest, Eng.step.at(Eng.InM{Bytes.from_list(Con{c, r})}, k, d, Eng.pend.new(), out)),
    Spec.req.meth(Spec.Span{Con{c, r}, Spec.SAt{k, d, rest}}), out)

def K.meth.at(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TMeth{}, k) == False{} : Bool},
  pr: Plain(rest)) -> G.meth(k, d, rest, c, r, out):
  match k:
    case Eng.KSp{}:
      %RS(rest, SelR{Eng.RT{}}, "", pd1(Con{c, r}), out) :
        LR.req(_, Spec.req.target(Con{c, r}, Spec.span(Spec.TTarget{}, rest)), out)
      K.target(Con{c, r}, Spec.span(Spec.TTarget{}, rest), out)(span.sw(Spec.TTarget{}, rest)(pr))
    case Eng.KHt{}:
      dead.bad(rest, Eng.pend.new(), out)
    case Eng.KCr{}:
      dead.bad(rest, Eng.pend.new(), out)
    case Eng.KLf{}:
      dead.bad(rest, Eng.pend.new(), out)
    case Eng.KCo{}:
      dead.bad(rest, Eng.pend.new(), out)
    case Eng.KCm{}:
      dead.bad(rest, Eng.pend.new(), out)
    case Eng.KDg{}:
      no2(G.meth(Eng.KDg{}, d, rest, c, r, out), mx)
    case Eng.KTk{}:
      no2(G.meth(Eng.KTk{}, d, rest, c, r, out), mx)
    case Eng.KVc{}:
      dead.bad(rest, Eng.pend.new(), out)
    case Eng.KCt{}:
      dead.bad(rest, Eng.pend.new(), out)

def K.meth.sat(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TMeth{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.meth(k, d, rest, c, r, out):
  (mx, np) = sw
  (nc, pr) = np
  K.meth.at(k, d, rest, c, r, out, mx, pr)

def K.meth.stop(+c: U32, +r: List<&2, U32>, stop: Spec.Stop, +out: List<&2, Eng.Req>) ->
  SW.at(Spec.TMeth{}, stop) ->
  LR.req(RES.at(stop, SelR{Eng.RM{}}, Bytes.from_list(Con{c, r}), Eng.pend.new(), out),
    Spec.req.meth(Spec.Span{Con{c, r}, stop}), out):
  match stop:
    case Spec.SEnd{}:
      sw => {==}
    case Spec.SAt{k, d, rest}:
      sw => K.meth.sat(k, d, rest, c, r, out, sw)

def K.meth(+c: U32, sp: Spec.Span, +out: List<&2, Eng.Req>) ->
  SW(Spec.TMeth{}, sp) ->
  LR.req(RES(sp, SelR{Eng.RM{}}, Eng.one(c), Eng.pend.new(), out), Spec.req.meth(Spec.span.push(c, sp)), out):
  match sp:
    case Spec.Span{r, stop}:
      K.meth.stop(c, r, stop, out)

# the first byte of a request line
def G.req1(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +out: List<&2, Eng.Req>) -> Type:
  LR.req(Eng.feed(t, Eng.step.at(Eng.Pre{}, k, c, Eng.pend.new(), out)),
    Spec.req.meth(Spec.span.pick(Spec.allows(Spec.TMeth{}, k), k, c, t, Spec.span(Spec.TMeth{}, t))), out)

def line.req.first(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +out: List<&2, Eng.Req>,
  nc: {notcrlf(k) == True{} : Bool}, pt: Plain(t)) -> G.req1(k, c, t, out):
  match k:
    case Eng.KTk{}:
      %RS(t, SelR{Eng.RM{}}, Eng.one(c), Eng.pend.new(), out) :
        LR.req(_, Spec.req.meth(Spec.span.push(c, Spec.span(Spec.TMeth{}, t))), out)
      K.meth(c, Spec.span(Spec.TMeth{}, t), out)(span.sw(Spec.TMeth{}, t)(pt))
    case Eng.KDg{}:
      %RS(t, SelR{Eng.RM{}}, Eng.one(c), Eng.pend.new(), out) :
        LR.req(_, Spec.req.meth(Spec.span.push(c, Spec.span(Spec.TMeth{}, t))), out)
      K.meth(c, Spec.span(Spec.TMeth{}, t), out)(span.sw(Spec.TMeth{}, t)(pt))
    case Eng.KCr{}:
      no(G.req1(Eng.KCr{}, c, t, out), nc)
    case Eng.KSp{}:
      dead.bad(t, Eng.pend.new(), out)
    case Eng.KHt{}:
      dead.bad(t, Eng.pend.new(), out)
    case Eng.KLf{}:
      dead.bad(t, Eng.pend.new(), out)
    case Eng.KCo{}:
      dead.bad(t, Eng.pend.new(), out)
    case Eng.KCm{}:
      dead.bad(t, Eng.pend.new(), out)
    case Eng.KVc{}:
      dead.bad(t, Eng.pend.new(), out)
    case Eng.KCt{}:
      dead.bad(t, Eng.pend.new(), out)

def line.req.con(+c: U32, +t: List<&2, U32>, +out: List<&2, Eng.Req>,
  pl: {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(t)) ->
  LR.req(Eng.feed(Con{c, t}, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), Spec.req.view(Con{c, t}), out):
  (nc, pt) = pl
  %feedc(c, t, Eng.P{Eng.Pre{}, Eng.pend.new(), out}) : LR.req(_, Spec.req.view(Con{c, t}), out)
  line.req.first(Spec.cls(c), c, t, out, nc, pt)

# LEMMA: a request line, read as far as it has come
def line.req(cur: List<&2, U32>, +out: List<&2, Eng.Req>) -> Plain(cur) ->
  LR.req(Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), Spec.req.view(cur), out):
  match cur:
    case Nil{}:
      pl => {==}
    case Con{+c, +t}:
      pl => line.req.con(c, t, out, pl)

# The field lines, seen
# ---------------------
#
# The same for a field line, from a reader at the start of one with the
# fields pd pending: a name being read, or a value, in the state its
# field is read in -- the digits of a length read so far, a list's
# member being read and whether a member so far said close, upgrade or
# websocket, a key, a version -- or refused.

def lowb(cur: List<&2, U32>) -> Bytes():
  Spec.lows(Bytes.from_list(cur))

def LR.len(-p: Eng.P, -n: U32, ws: Bool, -pd: Eng.Pend, -out: List<&2, Eng.Req>) -> Type:
  match ws:
    case True{}:
      {p == Eng.P{Eng.InLt{n}, pd, out} : Eng.P}
    case False{}:
      {p == Eng.P{Eng.InL{n}, pd, out} : Eng.P}

def LR.val(-p: Eng.P, val: Spec.Val, -pd: Eng.Pend, -out: List<&2, Eng.Req>) -> Type:
  match val:
    case Spec.VLen0{}:
      {p == Eng.P{Eng.InL0{}, pd, out} : Eng.P}
    case Spec.VLen{n, ws}:
      LR.len(p, n, ws, pd, out)
    case Spec.VConn{d, c}:
      {p == Eng.P{Eng.InLc{lowb(c), Spec.named("close", d), Spec.named("upgrade", d),
        Spec.named("keep-alive", d)}, pd, out} : Eng.P}
    case Spec.VUp{d, c}:
      {p == Eng.P{Eng.InLu{lowb(c), Spec.named("websocket", d)}, pd, out} : Eng.P}
    case Spec.VKey0{}:
      {p == Eng.P{Eng.InLk0{}, pd, out} : Eng.P}
    case Spec.VKey{k}:
      {p == Eng.P{Eng.InLk{Bytes.from_list(k)}, pd, out} : Eng.P}
    case Spec.VVer{v}:
      {p == Eng.P{Eng.InLv{Bytes.from_list(v)}, pd, out} : Eng.P}
    case Spec.VTe0{}:
      {p == Eng.P{Eng.InLe0{}, pd, out} : Eng.P}
    case Spec.VTe{t}:
      {p == Eng.P{Eng.InLe{Bytes.from_list(t)}, pd, out} : Eng.P}
    case Spec.VHost{}:
      {p == Eng.P{Eng.InLx{}, Eng.pend.host(pd), out} : Eng.P}
    case Spec.VSkip{}:
      {p == Eng.P{Eng.InLx{}, pd, out} : Eng.P}

def LR.field(-p: Eng.P, v: Spec.FLine, -pd: Eng.Pend, -out: List<&2, Eng.Req>) -> Type:
  match v:
    case Spec.FEmpty{}:
      {p == Eng.P{Eng.Lin{}, pd, out} : Eng.P}
    case Spec.FName{n}:
      {p == Eng.P{Eng.InN{Bytes.from_list(n)}, pd, out} : Eng.P}
    case Spec.FVal{val}:
      LR.val(p, val, pd, out)
    case Spec.FBad{}:
      Dead(p, out)

# a value only checked: Host, or any field this engine does not act on
def G.host(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLx{}, k, c, Eng.pend.host(pd), out)), out)

def K.host.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  mx: {Spec.allows(Spec.TVal{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}) ->
  G.host(k, c, rest, pd, out):
  match k:
    case Eng.KCr{}:
      no(G.host(Eng.KCr{}, c, rest, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, Eng.pend.host(pd), out)
    case Eng.KCt{}:
      dead.bad(rest, Eng.pend.host(pd), out)
    case Eng.KSp{}:
      no2(G.host(Eng.KSp{}, c, rest, pd, out), mx)
    case Eng.KHt{}:
      no2(G.host(Eng.KHt{}, c, rest, pd, out), mx)
    case Eng.KCo{}:
      no2(G.host(Eng.KCo{}, c, rest, pd, out), mx)
    case Eng.KCm{}:
      no2(G.host(Eng.KCm{}, c, rest, pd, out), mx)
    case Eng.KDg{}:
      no2(G.host(Eng.KDg{}, c, rest, pd, out), mx)
    case Eng.KTk{}:
      no2(G.host(Eng.KTk{}, c, rest, pd, out), mx)
    case Eng.KVc{}:
      no2(G.host(Eng.KVc{}, c, rest, pd, out), mx)

def K.host.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.host(k, c, rest, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.host.at(k, c, rest, pd, out, mx, nc)

def K.host(sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelR{Eng.RX{}}, "", Eng.pend.host(pd), out), Spec.skip.view(Spec.VHost{}, sp), pd, out):
  match sp:
    case Spec.Span{r, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{r, Spec.SAt{k, c, rest}}:
      sw => K.host.sat(k, c, rest, pd, out, sw)

def G.other(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLx{}, k, c, pd, out)), out)

def K.other.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  mx: {Spec.allows(Spec.TVal{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}) ->
  G.other(k, c, rest, pd, out):
  match k:
    case Eng.KCr{}:
      no(G.other(Eng.KCr{}, c, rest, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KSp{}:
      no2(G.other(Eng.KSp{}, c, rest, pd, out), mx)
    case Eng.KHt{}:
      no2(G.other(Eng.KHt{}, c, rest, pd, out), mx)
    case Eng.KCo{}:
      no2(G.other(Eng.KCo{}, c, rest, pd, out), mx)
    case Eng.KCm{}:
      no2(G.other(Eng.KCm{}, c, rest, pd, out), mx)
    case Eng.KDg{}:
      no2(G.other(Eng.KDg{}, c, rest, pd, out), mx)
    case Eng.KTk{}:
      no2(G.other(Eng.KTk{}, c, rest, pd, out), mx)
    case Eng.KVc{}:
      no2(G.other(Eng.KVc{}, c, rest, pd, out), mx)

def K.other.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.other(k, c, rest, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.other.at(k, c, rest, pd, out, mx, nc)

def K.other(sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelR{Eng.RX{}}, "", pd, out), Spec.skip.view(Spec.VSkip{}, sp), pd, out):
  match sp:
    case Spec.Span{r, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{r, Spec.SAt{k, c, rest}}:
      sw => K.other.sat(k, c, rest, pd, out, sw)

# a version
def G.vv(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLv{Bytes.from_list(v)}, k, c, pd, out)), out)

def K.vv.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TVal{}, k) == False{} : Bool},
  nc: {notcrlf(k) == True{} : Bool}) -> G.vv(k, c, rest, v, pd, out):
  match k:
    case Eng.KCr{}:
      no(G.vv(Eng.KCr{}, c, rest, v, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KSp{}:
      no2(G.vv(Eng.KSp{}, c, rest, v, pd, out), mx)
    case Eng.KHt{}:
      no2(G.vv(Eng.KHt{}, c, rest, v, pd, out), mx)
    case Eng.KCo{}:
      no2(G.vv(Eng.KCo{}, c, rest, v, pd, out), mx)
    case Eng.KCm{}:
      no2(G.vv(Eng.KCm{}, c, rest, v, pd, out), mx)
    case Eng.KDg{}:
      no2(G.vv(Eng.KDg{}, c, rest, v, pd, out), mx)
    case Eng.KTk{}:
      no2(G.vv(Eng.KTk{}, c, rest, v, pd, out), mx)
    case Eng.KVc{}:
      no2(G.vv(Eng.KVc{}, c, rest, v, pd, out), mx)

def K.vv.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.vv(k, c, rest, v, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.vv.at(k, c, rest, v, pd, out, mx, nc)

def K.vv(sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelLv{}, "", pd, out), Spec.ver.view(sp), pd, out):
  match sp:
    case Spec.Span{v, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{v, Spec.SAt{k, c, rest}}:
      sw => K.vv.sat(k, c, rest, v, pd, out, sw)

# a key: the rest of it, from its first byte
def G.keym(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLk{Bytes.from_list(Con{c, r})}, k, d, pd, out)), out)

def K.keym.at(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TVal{}, k) == False{} : Bool},
  nc: {notcrlf(k) == True{} : Bool}) -> G.keym(k, d, rest, c, r, pd, out):
  match k:
    case Eng.KCr{}:
      no(G.keym(Eng.KCr{}, d, rest, c, r, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KSp{}:
      no2(G.keym(Eng.KSp{}, d, rest, c, r, pd, out), mx)
    case Eng.KHt{}:
      no2(G.keym(Eng.KHt{}, d, rest, c, r, pd, out), mx)
    case Eng.KCo{}:
      no2(G.keym(Eng.KCo{}, d, rest, c, r, pd, out), mx)
    case Eng.KCm{}:
      no2(G.keym(Eng.KCm{}, d, rest, c, r, pd, out), mx)
    case Eng.KDg{}:
      no2(G.keym(Eng.KDg{}, d, rest, c, r, pd, out), mx)
    case Eng.KTk{}:
      no2(G.keym(Eng.KTk{}, d, rest, c, r, pd, out), mx)
    case Eng.KVc{}:
      no2(G.keym(Eng.KVc{}, d, rest, c, r, pd, out), mx)

def K.keym.sat(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.keym(k, d, rest, c, r, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.keym.at(k, d, rest, c, r, pd, out, mx, nc)

def K.keym(+c: U32, sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelR{Eng.RK{}}, Eng.one(c), pd, out), Spec.key.more(c, sp), pd, out):
  match sp:
    case Spec.Span{r, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{r, Spec.SAt{k, d, rest}}:
      sw => K.keym.sat(k, d, rest, c, r, pd, out, sw)

# a key: whitespace, then its first byte
def G.key(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(rest, Eng.step.at(Eng.InLk0{}, k, c, pd, out)),
    Spec.key.first(Spec.allows(Spec.TVal{}, k), c, rest), pd, out)

def K.key.in(+c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>, pr: Plain(rest)) ->
  LR.field(Eng.feed(rest, Eng.P{Eng.InLk{Eng.one(c)}, pd, out}),
    Spec.key.more(c, Spec.span(Spec.TVal{}, rest)), pd, out):
  %RS(rest, SelR{Eng.RK{}}, Eng.one(c), pd, out) :
    LR.field(_, Spec.key.more(c, Spec.span(Spec.TVal{}, rest)), pd, out)
  K.keym(c, Spec.span(Spec.TVal{}, rest), pd, out)(span.sw(Spec.TVal{}, rest)(pr))

def K.key.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  mx: {Spec.allows(Spec.TOws{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool},
  pr: Plain(rest)) -> G.key(k, c, rest, pd, out):
  match k:
    case Eng.KSp{}:
      no2(G.key(Eng.KSp{}, c, rest, pd, out), mx)
    case Eng.KHt{}:
      no2(G.key(Eng.KHt{}, c, rest, pd, out), mx)
    case Eng.KCr{}:
      no(G.key(Eng.KCr{}, c, rest, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KCo{}:
      K.key.in(c, rest, pd, out, pr)
    case Eng.KCm{}:
      K.key.in(c, rest, pd, out, pr)
    case Eng.KDg{}:
      K.key.in(c, rest, pd, out, pr)
    case Eng.KTk{}:
      K.key.in(c, rest, pd, out, pr)
    case Eng.KVc{}:
      K.key.in(c, rest, pd, out, pr)

def K.key.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.key(k, c, rest, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.key.at(k, c, rest, pd, out, mx, nc, pr)

def K.key(sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TOws{}, sp) ->
  LR.field(RES(sp, SelK0{}, "", pd, out), Spec.key.view(sp), pd, out):
  match sp:
    case Spec.Span{w, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{w, Spec.SAt{k, c, rest}}:
      sw => K.key.sat(k, c, rest, pd, out, sw)

# a transfer coding: the rest of it, from its first byte
def G.tem(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLe{Bytes.from_list(Con{c, r})}, k, d, pd, out)), out)

def K.tem.at(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TVal{}, k) == False{} : Bool},
  nc: {notcrlf(k) == True{} : Bool}) -> G.tem(k, d, rest, c, r, pd, out):
  match k:
    case Eng.KCr{}:
      no(G.tem(Eng.KCr{}, d, rest, c, r, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KSp{}:
      no2(G.tem(Eng.KSp{}, d, rest, c, r, pd, out), mx)
    case Eng.KHt{}:
      no2(G.tem(Eng.KHt{}, d, rest, c, r, pd, out), mx)
    case Eng.KCo{}:
      no2(G.tem(Eng.KCo{}, d, rest, c, r, pd, out), mx)
    case Eng.KCm{}:
      no2(G.tem(Eng.KCm{}, d, rest, c, r, pd, out), mx)
    case Eng.KDg{}:
      no2(G.tem(Eng.KDg{}, d, rest, c, r, pd, out), mx)
    case Eng.KTk{}:
      no2(G.tem(Eng.KTk{}, d, rest, c, r, pd, out), mx)
    case Eng.KVc{}:
      no2(G.tem(Eng.KVc{}, d, rest, c, r, pd, out), mx)

def K.tem.sat(+k: Eng.Cls, +d: U32, +rest: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.tem(k, d, rest, c, r, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.tem.at(k, d, rest, c, r, pd, out, mx, nc)

def K.tem(+c: U32, sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelE{}, Eng.one(c), pd, out), Spec.te.more(c, sp), pd, out):
  match sp:
    case Spec.Span{r, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{r, Spec.SAt{k, d, rest}}:
      sw => K.tem.sat(k, d, rest, c, r, pd, out, sw)

# a transfer coding: whitespace, then its first byte
def G.te(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(rest, Eng.step.at(Eng.InLe0{}, k, c, pd, out)),
    Spec.te.first(Spec.allows(Spec.TVal{}, k), c, rest), pd, out)

def K.te.in(+c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>, pr: Plain(rest)) ->
  LR.field(Eng.feed(rest, Eng.P{Eng.InLe{Eng.one(c)}, pd, out}),
    Spec.te.more(c, Spec.span(Spec.TVal{}, rest)), pd, out):
  %RS(rest, SelE{}, Eng.one(c), pd, out) :
    LR.field(_, Spec.te.more(c, Spec.span(Spec.TVal{}, rest)), pd, out)
  K.tem(c, Spec.span(Spec.TVal{}, rest), pd, out)(span.sw(Spec.TVal{}, rest)(pr))

def K.te.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  mx: {Spec.allows(Spec.TOws{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool},
  pr: Plain(rest)) -> G.te(k, c, rest, pd, out):
  match k:
    case Eng.KSp{}:
      no2(G.te(Eng.KSp{}, c, rest, pd, out), mx)
    case Eng.KHt{}:
      no2(G.te(Eng.KHt{}, c, rest, pd, out), mx)
    case Eng.KCr{}:
      no(G.te(Eng.KCr{}, c, rest, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KCo{}:
      K.te.in(c, rest, pd, out, pr)
    case Eng.KCm{}:
      K.te.in(c, rest, pd, out, pr)
    case Eng.KDg{}:
      K.te.in(c, rest, pd, out, pr)
    case Eng.KTk{}:
      K.te.in(c, rest, pd, out, pr)
    case Eng.KVc{}:
      K.te.in(c, rest, pd, out, pr)

def K.te.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.te(k, c, rest, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.te.at(k, c, rest, pd, out, mx, nc, pr)

def K.te(sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TOws{}, sp) ->
  LR.field(RES(sp, SelE0{}, "", pd, out), Spec.te.view(sp), pd, out):
  match sp:
    case Spec.Span{w, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{w, Spec.SAt{k, c, rest}}:
      sw => K.te.sat(k, c, rest, pd, out, sw)

# a length: whitespace after its digits
def G.lws(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: U32, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLt{v}, k, c, pd, out)), out)

def K.lws.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: U32, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TOws{}, k) == False{} : Bool},
  nc: {notcrlf(k) == True{} : Bool}) -> G.lws(k, c, rest, v, pd, out):
  match k:
    case Eng.KSp{}:
      no2(G.lws(Eng.KSp{}, c, rest, v, pd, out), mx)
    case Eng.KHt{}:
      no2(G.lws(Eng.KHt{}, c, rest, v, pd, out), mx)
    case Eng.KCr{}:
      no(G.lws(Eng.KCr{}, c, rest, v, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCo{}:
      dead.bad(rest, pd, out)
    case Eng.KCm{}:
      dead.bad(rest, pd, out)
    case Eng.KDg{}:
      dead.bad(rest, pd, out)
    case Eng.KTk{}:
      dead.bad(rest, pd, out)
    case Eng.KVc{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)

def K.lws.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: U32, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.lws(k, c, rest, v, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.lws.at(k, c, rest, v, pd, out, mx, nc)

def K.lws(+v: U32, sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TOws{}, sp) ->
  LR.field(RES(sp, SelLt{v}, "", pd, out), Spec.len.ws(v, sp), pd, out):
  match sp:
    case Spec.Span{w, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{w, Spec.SAt{k, c, rest}}:
      sw => K.lws.sat(k, c, rest, v, pd, out, sw)

# a length: its digits
def DG(+x: List<&2, U32>, +v: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(x, Eng.P{Eng.InL{v}, pd, out}), Spec.len.num(Spec.dec(x, v)), pd, out)

def K.dig1(b: Bool, +n: U32, +t: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  ih: DG(t, n, pd, out)) ->
  LR.field(Eng.feed(t, Eng.step.digit.go(n, pd, out, b)), Spec.len.num(Spec.dec.big(b, Spec.dec(t, n))), pd, out):
  match b:
    case True{}:
      dead.bad(t, pd, out)
    case False{}:
      ih

def G.dig(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +v: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(t, Eng.step.at(Eng.InL{v}, k, c, pd, out)),
    Spec.len.num(Spec.dec.pick(Spec.is.digit(k), k, c, t, v, Spec.dec(t, Spec.len.digit(v, c)))), pd, out)

def DIG.k(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +v: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  nc: {notcrlf(k) == True{} : Bool}, pt: Plain(t), ih: Plain(t) -> DG(t, Spec.len.digit(v, c), pd, out)) ->
  G.dig(k, c, t, v, pd, out):
  match k:
    case Eng.KDg{}:
      K.dig1(U32.is_lt(1048576, Spec.len.digit(v, c)), Spec.len.digit(v, c), t, pd, out, ih(pt))
    case Eng.KSp{}:
      %RS(t, SelLt{v}, "", pd, out) : LR.field(_, Spec.len.ws(v, Spec.span(Spec.TOws{}, t)), pd, out)
      K.lws(v, Spec.span(Spec.TOws{}, t), pd, out)(span.sw(Spec.TOws{}, t)(pt))
    case Eng.KHt{}:
      %RS(t, SelLt{v}, "", pd, out) : LR.field(_, Spec.len.ws(v, Spec.span(Spec.TOws{}, t)), pd, out)
      K.lws(v, Spec.span(Spec.TOws{}, t), pd, out)(span.sw(Spec.TOws{}, t)(pt))
    case Eng.KCr{}:
      no(G.dig(Eng.KCr{}, c, t, v, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(t, pd, out)
    case Eng.KCo{}:
      dead.bad(t, pd, out)
    case Eng.KCm{}:
      dead.bad(t, pd, out)
    case Eng.KTk{}:
      dead.bad(t, pd, out)
    case Eng.KVc{}:
      dead.bad(t, pd, out)
    case Eng.KCt{}:
      dead.bad(t, pd, out)

def DIG.con(+c: U32, +t: List<&2, U32>, +v: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  pl: {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(t), ih: Plain(t) -> DG(t, Spec.len.digit(v, c), pd, out)) ->
  DG(Con{c, t}, v, pd, out):
  (nc, pt) = pl
  %feedc(c, t, Eng.P{Eng.InL{v}, pd, out}) : LR.field(_, Spec.len.num(Spec.dec(Con{c, t}, v)), pd, out)
  DIG.k(Spec.cls(c), c, t, v, pd, out, nc, pt, ih)

def DIG(x: List<&2, U32>, +v: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Plain(x) -> DG(x, v, pd, out):
  match x:
    case Nil{}:
      pl => {==}
    case Con{+c, +t}:
      pl => DIG.con(c, t, v, pd, out, pl, DIG(t, Spec.len.digit(v, c), pd, out))

# a length: whitespace, then its first digit
def G.len(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +w: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(rest, Eng.step.at(Eng.InL0{}, k, c, pd, out)),
    Spec.len.view(Spec.Span{w, Spec.SAt{k, c, rest}}), pd, out)

def K.len.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +w: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TOws{}, k) == False{} : Bool},
  pr: Plain(rest)) -> G.len(k, c, rest, w, pd, out):
  match k:
    case Eng.KDg{}:
      K.dig1(U32.is_lt(1048576, Spec.len.digit(0, c)), Spec.len.digit(0, c), rest, pd, out,
        DIG(rest, Spec.len.digit(0, c), pd, out)(pr))
    case Eng.KSp{}:
      no2(G.len(Eng.KSp{}, c, rest, w, pd, out), mx)
    case Eng.KHt{}:
      no2(G.len(Eng.KHt{}, c, rest, w, pd, out), mx)
    case Eng.KCr{}:
      dead.bad(rest, pd, out)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCo{}:
      dead.bad(rest, pd, out)
    case Eng.KCm{}:
      dead.bad(rest, pd, out)
    case Eng.KTk{}:
      dead.bad(rest, pd, out)
    case Eng.KVc{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)

def K.len.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +w: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.len(k, c, rest, w, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.len.at(k, c, rest, w, pd, out, mx, pr)

def K.len(sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TOws{}, sp) ->
  LR.field(RES(sp, SelL0{}, "", pd, out), Spec.len.view(sp), pd, out):
  match sp:
    case Spec.Span{w, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{w, Spec.SAt{k, c, rest}}:
      sw => K.len.sat(k, c, rest, w, pd, out, sw)

# a list: a byte no value holds spoils it for good
def membad(x: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>) ->
  {Spec.LBad{} == Spec.members(x, False{}, done, cur) : Spec.Mem}:
  match x:
    case Nil{}:
      {==}
    case Con{+c, t}:
      membad(t, Spec.mem.done(Spec.mem.sep(Spec.cls(c)), done, cur),
        Spec.mem.cur(Spec.mem.sep(Spec.cls(c)), cur, c))

# a Connection list
def MC(+x: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(x, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done)}, pd, out}),
    Spec.list.view(True{}, Spec.members(x, True{}, done, cur)), pd, out)

def G.memc(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>,
  +cur: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(t, Eng.step.at(Eng.InLc{lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done)},
      k, c, pd, out)),
    Spec.list.view(True{}, Spec.members(t, Spec.allows(Spec.TVal{}, k), Spec.mem.done(Spec.mem.sep(k), done, cur),
      Spec.mem.cur(Spec.mem.sep(k), cur, c))), pd, out)

def MEMc.sep(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pt: Plain(t), ih: Plain(t) -> MC(t, Con{cur, done}, Nil{}, pd, out)) ->
  LR.field(Eng.feed(t, Eng.P{Eng.tok.conn(lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done)), pd, out}),
    Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out):
  %eqs(lowb(cur), "close") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{"", Spec.named("close", done) || _,
      Spec.named("upgrade", done) || Eng.bytes.eq(lowb(cur), "upgrade"),
      Spec.named("keep-alive", done) || Eng.bytes.eq(lowb(cur), "keep-alive")}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  %eqs(lowb(cur), "upgrade") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{"", Spec.named("close", done) || Spec.eq(lowb(cur), "close"),
      Spec.named("upgrade", done) || _,
      Spec.named("keep-alive", done) || Eng.bytes.eq(lowb(cur), "keep-alive")}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  %eqs(lowb(cur), "keep-alive") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{"", Spec.named("close", done) || Spec.eq(lowb(cur), "close"),
      Spec.named("upgrade", done) || Spec.eq(lowb(cur), "upgrade"),
      Spec.named("keep-alive", done) || _}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  ih(pt)

def MEMc.in(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pt: Plain(t), ih: Plain(t) -> MC(t, done, Spec.snoc(cur, c), pd, out)) ->
  LR.field(Eng.feed(t, Eng.P{Eng.InLc{Eng.push(lowb(cur), Eng.lower(c)), Spec.named("close", done),
      Spec.named("upgrade", done), Spec.named("keep-alive", done)}, pd, out}),
    Spec.list.view(True{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out):
  %br.lower(c) :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{Eng.push(lowb(cur), _), Spec.named("close", done),
      Spec.named("upgrade", done), Spec.named("keep-alive", done)}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out)
  %lb.snoc(cur, c) :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{_, Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done)}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out)
  ih(pt)

def MEMc.k(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>,
  +cur: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>, nc: {notcrlf(k) == True{} : Bool},
  pt: Plain(t),
  ih: Plain(t) -> MC(t, Spec.mem.done(Spec.mem.sep(k), done, cur), Spec.mem.cur(Spec.mem.sep(k), cur, c), pd, out)) ->
  G.memc(k, c, t, done, cur, pd, out):
  match k:
    case Eng.KSp{}:
      MEMc.sep(c, t, done, cur, pd, out, pt, ih)
    case Eng.KHt{}:
      MEMc.sep(c, t, done, cur, pd, out, pt, ih)
    case Eng.KCm{}:
      MEMc.sep(c, t, done, cur, pd, out, pt, ih)
    case Eng.KCr{}:
      no(G.memc(Eng.KCr{}, c, t, done, cur, pd, out), nc)
    case Eng.KLf{}:
      no(G.memc(Eng.KLf{}, c, t, done, cur, pd, out), nc)
    case Eng.KCt{}:
      %membad(t, done, Spec.snoc(cur, c)) :
        LR.field(Eng.feed(t, Eng.P{Eng.Bad{}, pd, out}), Spec.list.view(True{}, _), pd, out)
      dead.bad(t, pd, out)
    case Eng.KCo{}:
      MEMc.in(c, t, done, cur, pd, out, pt, ih)
    case Eng.KDg{}:
      MEMc.in(c, t, done, cur, pd, out, pt, ih)
    case Eng.KTk{}:
      MEMc.in(c, t, done, cur, pd, out, pt, ih)
    case Eng.KVc{}:
      MEMc.in(c, t, done, cur, pd, out, pt, ih)

def MEMc.con(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pl: {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(t),
  ih: Plain(t) -> MC(t, Spec.mem.done(Spec.mem.sep(Spec.cls(c)), done, cur),
    Spec.mem.cur(Spec.mem.sep(Spec.cls(c)), cur, c), pd, out)) ->
  MC(Con{c, t}, done, cur, pd, out):
  (nc, pt) = pl
  %feedc(c, t, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done)}, pd, out}) :
    LR.field(_, Spec.list.view(True{}, Spec.members(Con{c, t}, True{}, done, cur)), pd, out)
  MEMc.k(Spec.cls(c), c, t, done, cur, pd, out, nc, pt, ih)

def MEMc(x: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Plain(x) -> MC(x, done, cur, pd, out):
  match x:
    case Nil{}:
      pl => {==}
    case Con{+c, +t}:
      pl => MEMc.con(c, t, done, cur, pd, out, pl,
        MEMc(t, Spec.mem.done(Spec.mem.sep(Spec.cls(c)), done, cur),
          Spec.mem.cur(Spec.mem.sep(Spec.cls(c)), cur, c), pd, out))

# an Upgrade list
def MU(+x: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(x, Eng.P{Eng.InLu{lowb(cur), Spec.named("websocket", done)}, pd, out}),
    Spec.list.view(False{}, Spec.members(x, True{}, done, cur)), pd, out)

def G.memu(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>,
  +cur: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(t, Eng.step.at(Eng.InLu{lowb(cur), Spec.named("websocket", done)}, k, c, pd, out)),
    Spec.list.view(False{}, Spec.members(t, Spec.allows(Spec.TVal{}, k), Spec.mem.done(Spec.mem.sep(k), done, cur),
      Spec.mem.cur(Spec.mem.sep(k), cur, c))), pd, out)

def MEMu.sep(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pt: Plain(t), ih: Plain(t) -> MU(t, Con{cur, done}, Nil{}, pd, out)) ->
  LR.field(Eng.feed(t, Eng.P{Eng.tok.up(lowb(cur), Spec.named("websocket", done)), pd, out}),
    Spec.list.view(False{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out):
  %eqs(lowb(cur), "websocket") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLu{"", Spec.named("websocket", done) || _}, pd, out}),
      Spec.list.view(False{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  ih(pt)

def MEMu.in(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pt: Plain(t), ih: Plain(t) -> MU(t, done, Spec.snoc(cur, c), pd, out)) ->
  LR.field(Eng.feed(t, Eng.P{Eng.InLu{Eng.push(lowb(cur), Eng.lower(c)), Spec.named("websocket", done)}, pd, out}),
    Spec.list.view(False{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out):
  %br.lower(c) :
    LR.field(Eng.feed(t, Eng.P{Eng.InLu{Eng.push(lowb(cur), _), Spec.named("websocket", done)}, pd, out}),
      Spec.list.view(False{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out)
  %lb.snoc(cur, c) :
    LR.field(Eng.feed(t, Eng.P{Eng.InLu{_, Spec.named("websocket", done)}, pd, out}),
      Spec.list.view(False{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out)
  ih(pt)

def MEMu.k(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>,
  +cur: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>, nc: {notcrlf(k) == True{} : Bool},
  pt: Plain(t),
  ih: Plain(t) -> MU(t, Spec.mem.done(Spec.mem.sep(k), done, cur), Spec.mem.cur(Spec.mem.sep(k), cur, c), pd, out)) ->
  G.memu(k, c, t, done, cur, pd, out):
  match k:
    case Eng.KSp{}:
      MEMu.sep(c, t, done, cur, pd, out, pt, ih)
    case Eng.KHt{}:
      MEMu.sep(c, t, done, cur, pd, out, pt, ih)
    case Eng.KCm{}:
      MEMu.sep(c, t, done, cur, pd, out, pt, ih)
    case Eng.KCr{}:
      no(G.memu(Eng.KCr{}, c, t, done, cur, pd, out), nc)
    case Eng.KLf{}:
      no(G.memu(Eng.KLf{}, c, t, done, cur, pd, out), nc)
    case Eng.KCt{}:
      %membad(t, done, Spec.snoc(cur, c)) :
        LR.field(Eng.feed(t, Eng.P{Eng.Bad{}, pd, out}), Spec.list.view(False{}, _), pd, out)
      dead.bad(t, pd, out)
    case Eng.KCo{}:
      MEMu.in(c, t, done, cur, pd, out, pt, ih)
    case Eng.KDg{}:
      MEMu.in(c, t, done, cur, pd, out, pt, ih)
    case Eng.KTk{}:
      MEMu.in(c, t, done, cur, pd, out, pt, ih)
    case Eng.KVc{}:
      MEMu.in(c, t, done, cur, pd, out, pt, ih)

def MEMu.con(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pl: {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(t),
  ih: Plain(t) -> MU(t, Spec.mem.done(Spec.mem.sep(Spec.cls(c)), done, cur),
    Spec.mem.cur(Spec.mem.sep(Spec.cls(c)), cur, c), pd, out)) ->
  MU(Con{c, t}, done, cur, pd, out):
  (nc, pt) = pl
  %feedc(c, t, Eng.P{Eng.InLu{lowb(cur), Spec.named("websocket", done)}, pd, out}) :
    LR.field(_, Spec.list.view(False{}, Spec.members(Con{c, t}, True{}, done, cur)), pd, out)
  MEMu.k(Spec.cls(c), c, t, done, cur, pd, out, nc, pt, ih)

def MEMu(x: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Plain(x) -> MU(x, done, cur, pd, out):
  match x:
    case Nil{}:
      pl => {==}
    case Con{+c, +t}:
      pl => MEMu.con(c, t, done, cur, pd, out, pl,
        MEMu(t, Spec.mem.done(Spec.mem.sep(Spec.cls(c)), done, cur),
          Spec.mem.cur(Spec.mem.sep(Spec.cls(c)), cur, c), pd, out))

# a field, by its name: the value read the way the name says
def fbb(+k: Bytes()) -> {Spec.field(k) == Eng.fld.of(k) : Eng.Fld}:
  Equal.sym(Eng.Fld, Eng.fld.of(k), Spec.field(k), scan_is(Eng.fld.table(), k, None{}))

def K.of(f: Eng.Fld, +v: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Plain(v) ->
  LR.field(Eng.feed(v, Eng.step.name(f, pd, out)), Spec.field.of(f, v), pd, out):
  match f:
    case Eng.FTe{}:
      pl =>
        %RS(v, SelE0{}, "", pd, out) : LR.field(_, Spec.te.view(Spec.span(Spec.TOws{}, v)), pd, out)
        K.te(Spec.span(Spec.TOws{}, v), pd, out)(span.sw(Spec.TOws{}, v)(pl))
    case Eng.FCl{}:
      pl =>
        %RS(v, SelL0{}, "", pd, out) : LR.field(_, Spec.len.view(Spec.span(Spec.TOws{}, v)), pd, out)
        K.len(Spec.span(Spec.TOws{}, v), pd, out)(span.sw(Spec.TOws{}, v)(pl))
    case Eng.FConn{}:
      pl => MEMc(v, Nil{}, Nil{}, pd, out)(pl)
    case Eng.FUp{}:
      pl => MEMu(v, Nil{}, Nil{}, pd, out)(pl)
    case Eng.FKey{}:
      pl =>
        %RS(v, SelK0{}, "", pd, out) : LR.field(_, Spec.key.view(Spec.span(Spec.TOws{}, v)), pd, out)
        K.key(Spec.span(Spec.TOws{}, v), pd, out)(span.sw(Spec.TOws{}, v)(pl))
    case Eng.FHost{}:
      pl =>
        %RS(v, SelR{Eng.RX{}}, "", Eng.pend.host(pd), out) :
          LR.field(_, Spec.skip.view(Spec.VHost{}, Spec.span(Spec.TVal{}, v)), pd, out)
        K.host(Spec.span(Spec.TVal{}, v), pd, out)(span.sw(Spec.TVal{}, v)(pl))
    case Eng.FVer{}:
      pl =>
        %RS(v, SelLv{}, "", pd, out) : LR.field(_, Spec.ver.view(Spec.span(Spec.TVal{}, v)), pd, out)
        K.vv(Spec.span(Spec.TVal{}, v), pd, out)(span.sw(Spec.TVal{}, v)(pl))
    case Eng.FOther{}:
      pl =>
        %RS(v, SelR{Eng.RX{}}, "", pd, out) :
          LR.field(_, Spec.skip.view(Spec.VSkip{}, Spec.span(Spec.TVal{}, v)), pd, out)
        K.other(Spec.span(Spec.TVal{}, v), pd, out)(span.sw(Spec.TVal{}, v)(pl))

# a name
def G.name(+k: Eng.Cls, +d: U32, +v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(v, Eng.step.at(Eng.InN{Bytes.from_list(Con{c, r})}, k, d, pd, out)),
    Spec.field.name(Spec.Span{Con{c, r}, Spec.SAt{k, d, v}}), pd, out)

def K.name.colon(+v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  pr: Plain(v)) ->
  LR.field(Eng.feed(v, Eng.step.name(Eng.fld.of(Eng.lows(Bytes.from_list(Con{c, r}))), pd, out)),
    Spec.field.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), v), pd, out):
  %br.lows(Bytes.from_list(Con{c, r})) :
    LR.field(Eng.feed(v, Eng.step.name(Eng.fld.of(_), pd, out)),
      Spec.field.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), v), pd, out)
  %fbb(Spec.lows(Bytes.from_list(Con{c, r}))) :
    LR.field(Eng.feed(v, Eng.step.name(_, pd, out)),
      Spec.field.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), v), pd, out)
  K.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), v, pd, out)(pr)

def K.name.at(+k: Eng.Cls, +d: U32, +v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TName{}, k) == False{} : Bool}, pr: Plain(v)) ->
  G.name(k, d, v, c, r, pd, out):
  match k:
    case Eng.KCo{}:
      K.name.colon(v, c, r, pd, out, pr)
    case Eng.KDg{}:
      no2(G.name(Eng.KDg{}, d, v, c, r, pd, out), mx)
    case Eng.KTk{}:
      no2(G.name(Eng.KTk{}, d, v, c, r, pd, out), mx)
    case Eng.KSp{}:
      dead.bad(v, pd, out)
    case Eng.KHt{}:
      dead.bad(v, pd, out)
    case Eng.KCr{}:
      dead.bad(v, pd, out)
    case Eng.KLf{}:
      dead.bad(v, pd, out)
    case Eng.KCm{}:
      dead.bad(v, pd, out)
    case Eng.KVc{}:
      dead.bad(v, pd, out)
    case Eng.KCt{}:
      dead.bad(v, pd, out)

def K.name.sat(+k: Eng.Cls, +d: U32, +v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TName{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(v))) ->
  G.name(k, d, v, c, r, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.name.at(k, d, v, c, r, pd, out, mx, pr)

def K.name.stop(+c: U32, +r: List<&2, U32>, stop: Spec.Stop, +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  SW.at(Spec.TName{}, stop) ->
  LR.field(RES.at(stop, SelR{Eng.RN{}}, Bytes.from_list(Con{c, r}), pd, out),
    Spec.field.name(Spec.Span{Con{c, r}, stop}), pd, out):
  match stop:
    case Spec.SEnd{}:
      sw => {==}
    case Spec.SAt{k, d, v}:
      sw => K.name.sat(k, d, v, c, r, pd, out, sw)

def K.name(+c: U32, sp: Spec.Span, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TName{}, sp) ->
  LR.field(RES(sp, SelR{Eng.RN{}}, Eng.one(c), pd, out), Spec.field.name(Spec.span.push(c, sp)), pd, out):
  match sp:
    case Spec.Span{r, stop}:
      K.name.stop(c, r, stop, pd, out)

# the first byte of a field line
def G.fl1(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(t, Eng.step.at(Eng.Lin{}, k, c, pd, out)),
    Spec.field.name(Spec.span.pick(Spec.allows(Spec.TName{}, k), k, c, t, Spec.span(Spec.TName{}, t))), pd, out)

def line.field.first(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  nc: {notcrlf(k) == True{} : Bool}, pt: Plain(t)) -> G.fl1(k, c, t, pd, out):
  match k:
    case Eng.KTk{}:
      %RS(t, SelR{Eng.RN{}}, Eng.one(c), pd, out) :
        LR.field(_, Spec.field.name(Spec.span.push(c, Spec.span(Spec.TName{}, t))), pd, out)
      K.name(c, Spec.span(Spec.TName{}, t), pd, out)(span.sw(Spec.TName{}, t)(pt))
    case Eng.KDg{}:
      %RS(t, SelR{Eng.RN{}}, Eng.one(c), pd, out) :
        LR.field(_, Spec.field.name(Spec.span.push(c, Spec.span(Spec.TName{}, t))), pd, out)
      K.name(c, Spec.span(Spec.TName{}, t), pd, out)(span.sw(Spec.TName{}, t)(pt))
    case Eng.KCr{}:
      no(G.fl1(Eng.KCr{}, c, t, pd, out), nc)
    case Eng.KSp{}:
      dead.bad(t, pd, out)
    case Eng.KHt{}:
      dead.bad(t, pd, out)
    case Eng.KLf{}:
      dead.bad(t, pd, out)
    case Eng.KCo{}:
      dead.bad(t, pd, out)
    case Eng.KCm{}:
      dead.bad(t, pd, out)
    case Eng.KVc{}:
      dead.bad(t, pd, out)
    case Eng.KCt{}:
      dead.bad(t, pd, out)

def line.field.con(+c: U32, +t: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  pl: {notcrlf(Spec.cls(c)) == True{} : Bool} & Plain(t)) ->
  LR.field(Eng.feed(Con{c, t}, Eng.P{Eng.Lin{}, pd, out}), Spec.field.view(Con{c, t}), pd, out):
  (nc, pt) = pl
  %feedc(c, t, Eng.P{Eng.Lin{}, pd, out}) : LR.field(_, Spec.field.view(Con{c, t}), pd, out)
  line.field.first(Spec.cls(c), c, t, pd, out, nc, pt)

# LEMMA: a field line, read as far as it has come
def line.field(cur: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Plain(cur) ->
  LR.field(Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), Spec.field.view(cur), pd, out):
  match cur:
    case Nil{}:
      pl => {==}
    case Con{+c, +t}:
      pl => line.field.con(c, t, pd, out, pl)

# The head, seen
# --------------
#
# What the reader holds pending and what the spec's head has said are
# the same message when they look the same through PV: the method, the
# target, the length, close, the Host count (none, one, more), the four
# things an upgrade needs, and what the request line and the framing
# fields said (Fx: HTTP/1.0, keep-alive, chunked). A reader that never
# saw an upgrade field holds none of them, which looks like an empty key
# and three falses.

type UV is Data:
  UV{key: Bytes(), up: Bool, cu: Bool, vb: Bool}

type PV is Data:
  PV{meth: Eng.Meth, path: Bytes(), cl: Eng.Cl, close: Bool, host: Eng.Hosts, u: UV, fx: Eng.Fx}

def uv(ws: Eng.Up) -> UV:
  match ws:
    case Eng.Plain{}:
      UV{"", False{}, False{}, False{}}
    case Eng.Asks{k, u, c, v}:
      UV{k, u, c, v}

def pv(pd: Eng.Pend) -> PV:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      PV{m, p, cl, close, host, uv(ws), fx}

def hsat(n: Nat) -> Eng.Hosts:
  match n:
    case 0n:
      Eng.H0{}
    case 1n+p:
      match p:
        case 0n:
          Eng.H1{}
        case 1n+q:
          Eng.H2{}

def clv(l: Maybe<&2, U32>) -> Eng.Cl:
  match l:
    case None{}:
      Eng.NoCl{}
    case Some{n}:
      Eng.Has{n}

def hv(h: Spec.Head) -> PV:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      PV{m, Bytes.from_list(t), clv(l), cl, hsat(hs), UV{Bytes.from_list(k), u, c, v}, f}

def PR(-pd: Eng.Pend, -h: Spec.Head) -> Data:
  {pv(pd) == hv(h) : PV}

# a change seen the same on both sides is the same change
def pr.by(-f: PV -> PV, -pd: Eng.Pend, -pd2: Eng.Pend, -h: Spec.Head, -h2: Spec.Head,
  e1: {pv(pd2) == f(pv(pd)) : PV}, e2: {f(hv(h)) == hv(h2) : PV}, pr: PR(pd, h)) -> PR(pd2, h2):
  Equal.trans(PV, pv(pd2), f(pv(pd)), hv(h2), e1,
    Equal.trans(PV, f(pv(pd)), f(hv(h)), hv(h2), Equal.cong(PV, PV, f, pv(pd), hv(h), pr), e2))

def pv.conn(x: PV, a: Bool, b: Bool, k: Bool) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close || a, host, UV{kk, uu, c || b, v}, Eng.fx.ka(fx, k)}

def pv.up(x: PV, w: Bool) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close, host, UV{kk, uu || w, c, v}, fx}

def pv.key(x: PV, kb: Bytes()) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close, host, UV{kb, uu, c, v}, fx}

def pv.ver(x: PV, ok: Bool) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close, host, UV{kk, uu, c, v || Bool.not(ok)}, fx}

def pv.host(x: PV) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      PV{m, p, cl, close, Eng.hosts.more(host), u, fx}

def pv.cl(x: PV, l: Eng.Cl) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      PV{m, p, l, close, host, u, fx}

def pv.te(x: PV) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match fx:
        case Eng.Fx{a, b, c}:
          PV{m, p, cl, close, host, u, Eng.Fx{a, b, True{}}}

# the engine's side of each change
def e.conn(pd: Eng.Pend, +a: Bool, +b: Bool, +k: Bool) ->
  {pv(Eng.pend.conn(pd, a, b, k)) == pv.conn(pv(pd), a, b, k) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match ws b:
        case Eng.Plain{} False{}:
          {==}
        case Eng.Plain{} True{}:
          {==}
        case Eng.Asks{kk, u, c, v} w:
          {==}

def e.up(pd: Eng.Pend, +w: Bool) -> {pv(Eng.pend.up(pd, w)) == pv.up(pv(pd), w) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match ws w:
        case Eng.Plain{} False{}:
          {==}
        case Eng.Plain{} True{}:
          {==}
        case Eng.Asks{k, u, c, v} x:
          {==}

def e.key(pd: Eng.Pend, +kb: Bytes()) -> {pv(Eng.pend.key(pd, kb)) == pv.key(pv(pd), kb) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match ws:
        case Eng.Plain{}:
          {==}
        case Eng.Asks{k, u, c, v}:
          {==}

def e.ver(pd: Eng.Pend, +ok: Bool) -> {pv(Eng.pend.ver(pd, ok)) == pv.ver(pv(pd), ok) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match ws ok:
        case Eng.Plain{} True{}:
          {==}
        case Eng.Plain{} False{}:
          {==}
        case Eng.Asks{k, u, c, v} x:
          {==}

def e.host(pd: Eng.Pend) -> {pv(Eng.pend.host(pd)) == pv.host(pv(pd)) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      {==}

# and the spec's
def s.conn(h: Spec.Head, -a: Bool, -b: Bool, -k: Bool) ->
  {pv.conn(hv(h), a, b, k) == hv(Spec.head.conn(h, a, b, k)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, kk, u, c, v, f}:
      match f:
        case Eng.Fx{v10, ka, te}:
          {==}

def s.up(h: Spec.Head, -w: Bool) -> {pv.up(hv(h), w) == hv(Spec.head.up(h, w)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      {==}

def s.key(h: Spec.Head, -kl: List<&2, U32>) ->
  {pv.key(hv(h), Bytes.from_list(kl)) == hv(Spec.head.key(h, kl)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      {==}

def s.ver(h: Spec.Head, -ok: Bool) -> {pv.ver(hv(h), ok) == hv(Spec.head.ver(h, ok)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      {==}

def s.host(h: Spec.Head) -> {pv.host(hv(h)) == hv(Spec.head.host(h)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      match hs:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              {==}
            case 1n+q:
              {==}

def pr.conn(+pd: Eng.Pend, +h: Spec.Head, +a: Bool, +b: Bool, +k: Bool, pr: PR(pd, h)) ->
  PR(Eng.pend.conn(pd, a, b, k), Spec.head.conn(h, a, b, k)):
  pr.by(x => pv.conn(x, a, b, k), pd, Eng.pend.conn(pd, a, b, k), h, Spec.head.conn(h, a, b, k),
    e.conn(pd, a, b, k), s.conn(h, a, b, k), pr)

def pr.up(+pd: Eng.Pend, +h: Spec.Head, +w: Bool, pr: PR(pd, h)) ->
  PR(Eng.pend.up(pd, w), Spec.head.up(h, w)):
  pr.by(x => pv.up(x, w), pd, Eng.pend.up(pd, w), h, Spec.head.up(h, w), e.up(pd, w), s.up(h, w), pr)

def pr.key(+pd: Eng.Pend, +h: Spec.Head, +kl: List<&2, U32>, pr: PR(pd, h)) ->
  PR(Eng.pend.key(pd, Bytes.from_list(kl)), Spec.head.key(h, kl)):
  pr.by(x => pv.key(x, Bytes.from_list(kl)), pd, Eng.pend.key(pd, Bytes.from_list(kl)), h,
    Spec.head.key(h, kl), e.key(pd, Bytes.from_list(kl)), s.key(h, kl), pr)

def pr.ver(+pd: Eng.Pend, +h: Spec.Head, +ok: Bool, pr: PR(pd, h)) ->
  PR(Eng.pend.ver(pd, ok), Spec.head.ver(h, ok)):
  pr.by(x => pv.ver(x, ok), pd, Eng.pend.ver(pd, ok), h, Spec.head.ver(h, ok), e.ver(pd, ok), s.ver(h, ok), pr)

def pr.host(+pd: Eng.Pend, +h: Spec.Head, pr: PR(pd, h)) -> PR(Eng.pend.host(pd), Spec.head.host(h)):
  pr.by(x => pv.host(x), pd, Eng.pend.host(pd), h, Spec.head.host(h), e.host(pd), s.host(h), pr)

# A Transfer-Encoding at its line's end, on both sides: taken when it
# says chunked and none came before it, refused otherwise. Each side's
# decision is read off what it holds (pv.teok), so the two are one
# decision.
def pv.teok(x: PV, ok: Bool) -> Bool:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match fx:
        case Eng.Fx{a, b, t}:
          ok && Bool.not(t)

def pend.teset(pd: Eng.Pend) -> Eng.Pend:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match fx:
        case Eng.Fx{a, b, t}:
          Eng.Pend{m, p, cl, close, host, ws, Eng.Fx{a, b, True{}}}

def head.teset(h: Spec.Head) -> Spec.Head:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{a, b, x}:
          Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{a, b, True{}}}

def te.pick(b: Bool, pd: Eng.Pend, out: List<&2, Eng.Req>) -> Eng.P:
  match b:
    case True{}:
      Eng.P{Eng.CrM{}, pend.teset(pd), out}
    case False{}:
      Eng.P{Eng.Bad{}, pd, out}

def hte.pick(b: Bool, h: Spec.Head) -> Maybe<&2, Spec.Head>:
  match b:
    case True{}:
      Some{head.teset(h)}
    case False{}:
      None{}

def e.te.go(b: Bool, -m: Eng.Meth, -p: Bytes(), -cl: Eng.Cl, -close: Bool, -host: Eng.Hosts, -ws: Eng.Up,
  -v10: Bool, -ka: Bool, -out: List<&2, Eng.Req>, -t: Bool) ->
  {Eng.step.te.go(b, m, p, cl, close, host, ws, v10, ka, out, t) ==
    te.pick(b, Eng.Pend{m, p, cl, close, host, ws, Eng.Fx{v10, ka, t}}, out) : Eng.P}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def e.te(pd: Eng.Pend, +ok: Bool, -out: List<&2, Eng.Req>) ->
  {Eng.step.te.at(ok, pd, out) == te.pick(pv.teok(pv(pd), ok), pd, out) : Eng.P}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match fx:
        case Eng.Fx{a, b, +t}:
          e.te.go(ok && Bool.not(t), m, p, cl, close, host, ws, a, b, out, t)

def s.te.go(b: Bool, -m: Eng.Meth, -t: List<&2, U32>, -l: Maybe<&2, U32>, -cl: Bool, -hs: Nat,
  -k: List<&2, U32>, -u: Bool, -c: Bool, -v: Bool, -v10: Bool, -ka: Bool, -x: Bool) ->
  {hte.pick(b, Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, x}}) ==
    Spec.head.te.at(b, m, t, l, cl, hs, k, u, c, v, v10, ka) : Maybe<&2, Spec.Head>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def s.te(h: Spec.Head, +ok: Bool) ->
  {hte.pick(pv.teok(hv(h), ok), h) == Spec.head.te(h, ok) : Maybe<&2, Spec.Head>}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{a, b, +x}:
          s.te.go(ok && Bool.not(x), m, t, l, cl, hs, k, u, c, v, a, b, x)

def e.teset(pd: Eng.Pend) -> {pv(pend.teset(pd)) == pv.te(pv(pd)) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match fx:
        case Eng.Fx{a, b, t}:
          {==}

def s.teset(h: Spec.Head) -> {pv.te(hv(h)) == hv(head.teset(h)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{a, b, x}:
          {==}

def pr.te(+pd: Eng.Pend, +h: Spec.Head, pr: PR(pd, h)) -> PR(pend.teset(pd), head.teset(h)):
  pr.by(x => pv.te(x), pd, pend.teset(pd), h, head.teset(h), e.teset(pd), s.teset(h), pr)

# the method, by its bytes, on both sides
def meth.pick.is(a: Bool, b: Bool) -> {Spec.meth.pick(a, b) == Eng.meth.pick(a, b) : Eng.Meth}:
  match a b:
    case True{} x:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def meth.is(+m: Bytes()) -> {Spec.method(m) == Eng.meth.of(m) : Eng.Meth}:
  %eqs(m, "GET") : {Spec.method(m) == Eng.meth.pick(_, Eng.bytes.eq(m, "HEAD")) : Eng.Meth}
  %eqs(m, "HEAD") : {Spec.method(m) == Eng.meth.pick(Spec.eq(m, "GET"), _) : Eng.Meth}
  meth.pick.is(Spec.eq(m, "GET"), Spec.eq(m, "HEAD"))

# a request line's head, on both sides: HTTP/1.1, and HTTP/1.0
def pr.new(+m: List<&2, U32>, +t: List<&2, U32>) -> PR(pd2(m, t), Spec.head.new(m, t, False{})):
  %meth.is(Bytes.from_list(m)) :
    {PV{_, Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{}, UV{"", False{}, False{}, False{}},
      Eng.Fx{False{}, False{}, False{}}} ==
      PV{Spec.method(Bytes.from_list(m)), Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{},
        UV{"", False{}, False{}, False{}}, Eng.Fx{False{}, False{}, False{}}} : PV}
  {==}

def pr.new10(+m: List<&2, U32>, +t: List<&2, U32>) ->
  PR(Eng.pend.v10(pd2(m, t)), Spec.head.new(m, t, True{})):
  %meth.is(Bytes.from_list(m)) :
    {PV{_, Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{}, UV{"", False{}, False{}, False{}},
      Eng.Fx{True{}, False{}, False{}}} ==
      PV{Spec.method(Bytes.from_list(m)), Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{},
        UV{"", False{}, False{}, False{}}, Eng.Fx{True{}, False{}, False{}}} : PV}
  {==}

# whitespace cut from either end, on both sides
def tl.pick(w: Bool, +c: U32, +t: List<&2, U32>, -rl: List<&2, U32>, -rb: Bytes(),
  ih: {Bytes.from_list(rl) == rb : Bytes()}) ->
  {Bytes.from_list(Spec.trim.lead.pick(w, c, t, rl)) == Eng.trim.lead.pick(w, c, Bytes.from_list(t), rb) : Bytes()}:
  match w:
    case True{}:
      ih
    case False{}:
      {==}

def ows.is(k: Eng.Cls) -> {Spec.ows(k) == Eng.ows(k) : Bool}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def tl(x: List<&2, U32>) -> {Bytes.from_list(Spec.trim.lead(x)) == Eng.trim.lead(Bytes.from_list(x)) : Bytes()}:
  match x:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %br.cls(c) :
        {Bytes.from_list(Spec.trim.lead(Con{c, t})) ==
          Eng.trim.lead.pick(Eng.ows(_), c, Bytes.from_list(t), Eng.trim.lead(Bytes.from_list(t))) : Bytes()}
      %ows.is(Spec.cls(c)) :
        {Bytes.from_list(Spec.trim.lead(Con{c, t})) ==
          Eng.trim.lead.pick(_, c, Bytes.from_list(t), Eng.trim.lead(Bytes.from_list(t))) : Bytes()}
      tl.pick(Spec.ows(Spec.cls(c)), c, t, Spec.trim.lead(t), Eng.trim.lead(Bytes.from_list(t)), tl(t))

def te.pick.is(w: Bool, +c: U32, r: List<&2, U32>) ->
  {Bytes.from_list(Spec.trim.end.pick(w, c, r)) == Eng.trim.end.pick(w, c, Bytes.from_list(r)) : Bytes()}:
  match w r:
    case True{} Nil{}:
      {==}
    case True{} Con{h, t}:
      {==}
    case False{} Nil{}:
      {==}
    case False{} Con{h, t}:
      {==}

def te(x: List<&2, U32>) -> {Bytes.from_list(Spec.trim.end(x)) == Eng.trim.end(Bytes.from_list(x)) : Bytes()}:
  match x:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %br.cls(c) :
        {Bytes.from_list(Spec.trim.end(Con{c, t})) ==
          Eng.trim.end.pick(Eng.ows(_), c, Eng.trim.end(Bytes.from_list(t))) : Bytes()}
      %ows.is(Spec.cls(c)) :
        {Bytes.from_list(Spec.trim.end(Con{c, t})) ==
          Eng.trim.end.pick(_, c, Eng.trim.end(Bytes.from_list(t))) : Bytes()}
      %te(t) :
        {Bytes.from_list(Spec.trim.end(Con{c, t})) ==
          Eng.trim.end.pick(Spec.ows(Spec.cls(c)), c, _) : Bytes()}
      te.pick.is(Spec.ows(Spec.cls(c)), c, Spec.trim.end(t))

def trim.is(+x: List<&2, U32>) ->
  {Bytes.from_list(Spec.trim(x)) == Eng.trim(Bytes.from_list(x)) : Bytes()}:
  %tl(x) : {Bytes.from_list(Spec.trim(x)) == Eng.trim.end(_) : Bytes()}
  te(Spec.trim.lead(x))

# The chunked body, seen
# ----------------------
#
# Where the spec's grammar is, the reader is: at.eng names the reader's
# place for each of the spec's, go.eng its move for each of the spec's,
# and tbl says the two tables are one table, row by row. A byte's kind
# is the same on both sides (xk.is: each side's class of it, then its
# hex value by each side's own walk of the digits, and ";", "=", DQUOTE
# and "\\" by each side's own test).

def at.eng(at: Spec.At) -> Eng.ChPos:
  match at:
    case Spec.ASize0{}:
      Eng.CSize0{}
    case Spec.ASize{}:
      Eng.CSize{}
    case Spec.ABws{}:
      Eng.CBws{}
    case Spec.AName0{}:
      Eng.CName0{}
    case Spec.AName{}:
      Eng.CName{}
    case Spec.ANameWs{}:
      Eng.CNameWs{}
    case Spec.AVal0{}:
      Eng.CVal0{}
    case Spec.AToken{}:
      Eng.CToken{}
    case Spec.AQuoted{}:
      Eng.CQuoted{}
    case Spec.AEscape{}:
      Eng.CEscape{}
    case Spec.AClosed{}:
      Eng.CClosed{}
    case Spec.ALf{}:
      Eng.CLf{}
    case Spec.ADataCr{}:
      Eng.CDataCr{}
    case Spec.ADataLf{}:
      Eng.CDataLf{}
    case Spec.ATrail{}:
      Eng.CTrail{}
    case Spec.ATName{}:
      Eng.CTName{}
    case Spec.ATVal{}:
      Eng.CTVal{}
    case Spec.ATLf{}:
      Eng.CTLf{}
    case Spec.AEnd{}:
      Eng.CEnd{}

def go.eng(g: Spec.Go) -> Eng.Mv:
  match g:
    case Spec.GBad{}:
      Eng.MvBad{}
    case Spec.GTo{at, paid}:
      Eng.MvTo{at.eng(at), paid}
    case Spec.GDigit{d}:
      Eng.MvDigit{d}
    case Spec.GLine{}:
      Eng.MvLine{}
    case Spec.GDone{}:
      Eng.MvDone{}

def tbl(at: Spec.At, x: Eng.XK) -> {Eng.chk.next(at.eng(at), x) == go.eng(Spec.chunk.step(at, x)) : Eng.Mv}:
  match at x:
    case Spec.ASize0{} Eng.XHex{d}:
      {==}
    case Spec.ASize0{} Eng.XTok{}:
      {==}
    case Spec.ASize0{} Eng.XWs{}:
      {==}
    case Spec.ASize0{} Eng.XSemi{}:
      {==}
    case Spec.ASize0{} Eng.XEq{}:
      {==}
    case Spec.ASize0{} Eng.XQuote{}:
      {==}
    case Spec.ASize0{} Eng.XBack{}:
      {==}
    case Spec.ASize0{} Eng.XColon{}:
      {==}
    case Spec.ASize0{} Eng.XCr{}:
      {==}
    case Spec.ASize0{} Eng.XLf{}:
      {==}
    case Spec.ASize0{} Eng.XVis{}:
      {==}
    case Spec.ASize0{} Eng.XCtl{}:
      {==}
    case Spec.ASize{} Eng.XHex{d}:
      {==}
    case Spec.ASize{} Eng.XTok{}:
      {==}
    case Spec.ASize{} Eng.XWs{}:
      {==}
    case Spec.ASize{} Eng.XSemi{}:
      {==}
    case Spec.ASize{} Eng.XEq{}:
      {==}
    case Spec.ASize{} Eng.XQuote{}:
      {==}
    case Spec.ASize{} Eng.XBack{}:
      {==}
    case Spec.ASize{} Eng.XColon{}:
      {==}
    case Spec.ASize{} Eng.XCr{}:
      {==}
    case Spec.ASize{} Eng.XLf{}:
      {==}
    case Spec.ASize{} Eng.XVis{}:
      {==}
    case Spec.ASize{} Eng.XCtl{}:
      {==}
    case Spec.ABws{} Eng.XHex{d}:
      {==}
    case Spec.ABws{} Eng.XTok{}:
      {==}
    case Spec.ABws{} Eng.XWs{}:
      {==}
    case Spec.ABws{} Eng.XSemi{}:
      {==}
    case Spec.ABws{} Eng.XEq{}:
      {==}
    case Spec.ABws{} Eng.XQuote{}:
      {==}
    case Spec.ABws{} Eng.XBack{}:
      {==}
    case Spec.ABws{} Eng.XColon{}:
      {==}
    case Spec.ABws{} Eng.XCr{}:
      {==}
    case Spec.ABws{} Eng.XLf{}:
      {==}
    case Spec.ABws{} Eng.XVis{}:
      {==}
    case Spec.ABws{} Eng.XCtl{}:
      {==}
    case Spec.AName0{} Eng.XHex{d}:
      {==}
    case Spec.AName0{} Eng.XTok{}:
      {==}
    case Spec.AName0{} Eng.XWs{}:
      {==}
    case Spec.AName0{} Eng.XSemi{}:
      {==}
    case Spec.AName0{} Eng.XEq{}:
      {==}
    case Spec.AName0{} Eng.XQuote{}:
      {==}
    case Spec.AName0{} Eng.XBack{}:
      {==}
    case Spec.AName0{} Eng.XColon{}:
      {==}
    case Spec.AName0{} Eng.XCr{}:
      {==}
    case Spec.AName0{} Eng.XLf{}:
      {==}
    case Spec.AName0{} Eng.XVis{}:
      {==}
    case Spec.AName0{} Eng.XCtl{}:
      {==}
    case Spec.AName{} Eng.XHex{d}:
      {==}
    case Spec.AName{} Eng.XTok{}:
      {==}
    case Spec.AName{} Eng.XWs{}:
      {==}
    case Spec.AName{} Eng.XSemi{}:
      {==}
    case Spec.AName{} Eng.XEq{}:
      {==}
    case Spec.AName{} Eng.XQuote{}:
      {==}
    case Spec.AName{} Eng.XBack{}:
      {==}
    case Spec.AName{} Eng.XColon{}:
      {==}
    case Spec.AName{} Eng.XCr{}:
      {==}
    case Spec.AName{} Eng.XLf{}:
      {==}
    case Spec.AName{} Eng.XVis{}:
      {==}
    case Spec.AName{} Eng.XCtl{}:
      {==}
    case Spec.ANameWs{} Eng.XHex{d}:
      {==}
    case Spec.ANameWs{} Eng.XTok{}:
      {==}
    case Spec.ANameWs{} Eng.XWs{}:
      {==}
    case Spec.ANameWs{} Eng.XSemi{}:
      {==}
    case Spec.ANameWs{} Eng.XEq{}:
      {==}
    case Spec.ANameWs{} Eng.XQuote{}:
      {==}
    case Spec.ANameWs{} Eng.XBack{}:
      {==}
    case Spec.ANameWs{} Eng.XColon{}:
      {==}
    case Spec.ANameWs{} Eng.XCr{}:
      {==}
    case Spec.ANameWs{} Eng.XLf{}:
      {==}
    case Spec.ANameWs{} Eng.XVis{}:
      {==}
    case Spec.ANameWs{} Eng.XCtl{}:
      {==}
    case Spec.AVal0{} Eng.XHex{d}:
      {==}
    case Spec.AVal0{} Eng.XTok{}:
      {==}
    case Spec.AVal0{} Eng.XWs{}:
      {==}
    case Spec.AVal0{} Eng.XSemi{}:
      {==}
    case Spec.AVal0{} Eng.XEq{}:
      {==}
    case Spec.AVal0{} Eng.XQuote{}:
      {==}
    case Spec.AVal0{} Eng.XBack{}:
      {==}
    case Spec.AVal0{} Eng.XColon{}:
      {==}
    case Spec.AVal0{} Eng.XCr{}:
      {==}
    case Spec.AVal0{} Eng.XLf{}:
      {==}
    case Spec.AVal0{} Eng.XVis{}:
      {==}
    case Spec.AVal0{} Eng.XCtl{}:
      {==}
    case Spec.AToken{} Eng.XHex{d}:
      {==}
    case Spec.AToken{} Eng.XTok{}:
      {==}
    case Spec.AToken{} Eng.XWs{}:
      {==}
    case Spec.AToken{} Eng.XSemi{}:
      {==}
    case Spec.AToken{} Eng.XEq{}:
      {==}
    case Spec.AToken{} Eng.XQuote{}:
      {==}
    case Spec.AToken{} Eng.XBack{}:
      {==}
    case Spec.AToken{} Eng.XColon{}:
      {==}
    case Spec.AToken{} Eng.XCr{}:
      {==}
    case Spec.AToken{} Eng.XLf{}:
      {==}
    case Spec.AToken{} Eng.XVis{}:
      {==}
    case Spec.AToken{} Eng.XCtl{}:
      {==}
    case Spec.AQuoted{} Eng.XHex{d}:
      {==}
    case Spec.AQuoted{} Eng.XTok{}:
      {==}
    case Spec.AQuoted{} Eng.XWs{}:
      {==}
    case Spec.AQuoted{} Eng.XSemi{}:
      {==}
    case Spec.AQuoted{} Eng.XEq{}:
      {==}
    case Spec.AQuoted{} Eng.XQuote{}:
      {==}
    case Spec.AQuoted{} Eng.XBack{}:
      {==}
    case Spec.AQuoted{} Eng.XColon{}:
      {==}
    case Spec.AQuoted{} Eng.XCr{}:
      {==}
    case Spec.AQuoted{} Eng.XLf{}:
      {==}
    case Spec.AQuoted{} Eng.XVis{}:
      {==}
    case Spec.AQuoted{} Eng.XCtl{}:
      {==}
    case Spec.AEscape{} Eng.XHex{d}:
      {==}
    case Spec.AEscape{} Eng.XTok{}:
      {==}
    case Spec.AEscape{} Eng.XWs{}:
      {==}
    case Spec.AEscape{} Eng.XSemi{}:
      {==}
    case Spec.AEscape{} Eng.XEq{}:
      {==}
    case Spec.AEscape{} Eng.XQuote{}:
      {==}
    case Spec.AEscape{} Eng.XBack{}:
      {==}
    case Spec.AEscape{} Eng.XColon{}:
      {==}
    case Spec.AEscape{} Eng.XCr{}:
      {==}
    case Spec.AEscape{} Eng.XLf{}:
      {==}
    case Spec.AEscape{} Eng.XVis{}:
      {==}
    case Spec.AEscape{} Eng.XCtl{}:
      {==}
    case Spec.AClosed{} Eng.XHex{d}:
      {==}
    case Spec.AClosed{} Eng.XTok{}:
      {==}
    case Spec.AClosed{} Eng.XWs{}:
      {==}
    case Spec.AClosed{} Eng.XSemi{}:
      {==}
    case Spec.AClosed{} Eng.XEq{}:
      {==}
    case Spec.AClosed{} Eng.XQuote{}:
      {==}
    case Spec.AClosed{} Eng.XBack{}:
      {==}
    case Spec.AClosed{} Eng.XColon{}:
      {==}
    case Spec.AClosed{} Eng.XCr{}:
      {==}
    case Spec.AClosed{} Eng.XLf{}:
      {==}
    case Spec.AClosed{} Eng.XVis{}:
      {==}
    case Spec.AClosed{} Eng.XCtl{}:
      {==}
    case Spec.ALf{} Eng.XHex{d}:
      {==}
    case Spec.ALf{} Eng.XTok{}:
      {==}
    case Spec.ALf{} Eng.XWs{}:
      {==}
    case Spec.ALf{} Eng.XSemi{}:
      {==}
    case Spec.ALf{} Eng.XEq{}:
      {==}
    case Spec.ALf{} Eng.XQuote{}:
      {==}
    case Spec.ALf{} Eng.XBack{}:
      {==}
    case Spec.ALf{} Eng.XColon{}:
      {==}
    case Spec.ALf{} Eng.XCr{}:
      {==}
    case Spec.ALf{} Eng.XLf{}:
      {==}
    case Spec.ALf{} Eng.XVis{}:
      {==}
    case Spec.ALf{} Eng.XCtl{}:
      {==}
    case Spec.ADataCr{} Eng.XHex{d}:
      {==}
    case Spec.ADataCr{} Eng.XTok{}:
      {==}
    case Spec.ADataCr{} Eng.XWs{}:
      {==}
    case Spec.ADataCr{} Eng.XSemi{}:
      {==}
    case Spec.ADataCr{} Eng.XEq{}:
      {==}
    case Spec.ADataCr{} Eng.XQuote{}:
      {==}
    case Spec.ADataCr{} Eng.XBack{}:
      {==}
    case Spec.ADataCr{} Eng.XColon{}:
      {==}
    case Spec.ADataCr{} Eng.XCr{}:
      {==}
    case Spec.ADataCr{} Eng.XLf{}:
      {==}
    case Spec.ADataCr{} Eng.XVis{}:
      {==}
    case Spec.ADataCr{} Eng.XCtl{}:
      {==}
    case Spec.ADataLf{} Eng.XHex{d}:
      {==}
    case Spec.ADataLf{} Eng.XTok{}:
      {==}
    case Spec.ADataLf{} Eng.XWs{}:
      {==}
    case Spec.ADataLf{} Eng.XSemi{}:
      {==}
    case Spec.ADataLf{} Eng.XEq{}:
      {==}
    case Spec.ADataLf{} Eng.XQuote{}:
      {==}
    case Spec.ADataLf{} Eng.XBack{}:
      {==}
    case Spec.ADataLf{} Eng.XColon{}:
      {==}
    case Spec.ADataLf{} Eng.XCr{}:
      {==}
    case Spec.ADataLf{} Eng.XLf{}:
      {==}
    case Spec.ADataLf{} Eng.XVis{}:
      {==}
    case Spec.ADataLf{} Eng.XCtl{}:
      {==}
    case Spec.ATrail{} Eng.XHex{d}:
      {==}
    case Spec.ATrail{} Eng.XTok{}:
      {==}
    case Spec.ATrail{} Eng.XWs{}:
      {==}
    case Spec.ATrail{} Eng.XSemi{}:
      {==}
    case Spec.ATrail{} Eng.XEq{}:
      {==}
    case Spec.ATrail{} Eng.XQuote{}:
      {==}
    case Spec.ATrail{} Eng.XBack{}:
      {==}
    case Spec.ATrail{} Eng.XColon{}:
      {==}
    case Spec.ATrail{} Eng.XCr{}:
      {==}
    case Spec.ATrail{} Eng.XLf{}:
      {==}
    case Spec.ATrail{} Eng.XVis{}:
      {==}
    case Spec.ATrail{} Eng.XCtl{}:
      {==}
    case Spec.ATName{} Eng.XHex{d}:
      {==}
    case Spec.ATName{} Eng.XTok{}:
      {==}
    case Spec.ATName{} Eng.XWs{}:
      {==}
    case Spec.ATName{} Eng.XSemi{}:
      {==}
    case Spec.ATName{} Eng.XEq{}:
      {==}
    case Spec.ATName{} Eng.XQuote{}:
      {==}
    case Spec.ATName{} Eng.XBack{}:
      {==}
    case Spec.ATName{} Eng.XColon{}:
      {==}
    case Spec.ATName{} Eng.XCr{}:
      {==}
    case Spec.ATName{} Eng.XLf{}:
      {==}
    case Spec.ATName{} Eng.XVis{}:
      {==}
    case Spec.ATName{} Eng.XCtl{}:
      {==}
    case Spec.ATVal{} Eng.XHex{d}:
      {==}
    case Spec.ATVal{} Eng.XTok{}:
      {==}
    case Spec.ATVal{} Eng.XWs{}:
      {==}
    case Spec.ATVal{} Eng.XSemi{}:
      {==}
    case Spec.ATVal{} Eng.XEq{}:
      {==}
    case Spec.ATVal{} Eng.XQuote{}:
      {==}
    case Spec.ATVal{} Eng.XBack{}:
      {==}
    case Spec.ATVal{} Eng.XColon{}:
      {==}
    case Spec.ATVal{} Eng.XCr{}:
      {==}
    case Spec.ATVal{} Eng.XLf{}:
      {==}
    case Spec.ATVal{} Eng.XVis{}:
      {==}
    case Spec.ATVal{} Eng.XCtl{}:
      {==}
    case Spec.ATLf{} Eng.XHex{d}:
      {==}
    case Spec.ATLf{} Eng.XTok{}:
      {==}
    case Spec.ATLf{} Eng.XWs{}:
      {==}
    case Spec.ATLf{} Eng.XSemi{}:
      {==}
    case Spec.ATLf{} Eng.XEq{}:
      {==}
    case Spec.ATLf{} Eng.XQuote{}:
      {==}
    case Spec.ATLf{} Eng.XBack{}:
      {==}
    case Spec.ATLf{} Eng.XColon{}:
      {==}
    case Spec.ATLf{} Eng.XCr{}:
      {==}
    case Spec.ATLf{} Eng.XLf{}:
      {==}
    case Spec.ATLf{} Eng.XVis{}:
      {==}
    case Spec.ATLf{} Eng.XCtl{}:
      {==}
    case Spec.AEnd{} Eng.XHex{d}:
      {==}
    case Spec.AEnd{} Eng.XTok{}:
      {==}
    case Spec.AEnd{} Eng.XWs{}:
      {==}
    case Spec.AEnd{} Eng.XSemi{}:
      {==}
    case Spec.AEnd{} Eng.XEq{}:
      {==}
    case Spec.AEnd{} Eng.XQuote{}:
      {==}
    case Spec.AEnd{} Eng.XBack{}:
      {==}
    case Spec.AEnd{} Eng.XColon{}:
      {==}
    case Spec.AEnd{} Eng.XCr{}:
      {==}
    case Spec.AEnd{} Eng.XLf{}:
      {==}
    case Spec.AEnd{} Eng.XVis{}:
      {==}
    case Spec.AEnd{} Eng.XCtl{}:
      {==}

def or_f(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def vc.is(a: Bool, b: Bool, q: Bool, t: Bool) -> {Spec.xk.vc(a, b, q, t) == Eng.xk.vc(a, b, q, t) : Eng.XK}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match q:
            case True{}:
              {==}
            case False{}:
              match t:
                case True{}:
                  {==}
                case False{}:
                  {==}

def hexat.pick(b: Bool, -i: U32, -r1: Maybe<&2, U32>, -r2: Maybe<&2, U32>, ih: {r1 == r2 : Maybe<&2, U32>}) ->
  {Spec.u32.may(b, i, r1) == Eng.hex.pick(b, i, r2) : Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def hexat.is(+x: U32, xs: List<&2, U32>, +i: U32) ->
  {Spec.hexdig.at(x, xs, i) == Eng.hex.in(x, xs, i) : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      hexat.pick(U32.is_eq(x, h), i, Spec.hexdig.at(x, t, (i + 1 : U32)), Eng.hex.in(x, t, (i + 1 : U32)),
        hexat.is(x, t, (i + 1 : U32)))

def hex.is(+c: U32) -> {Spec.hexdig(c) == Eng.hex(c) : Maybe<&2, U32>}:
  %br.lower(c) :
    {Spec.hexdig.at(Spec.lower(c), Eng.bytes("0123456789abcdef"), 0) ==
      Eng.hex.in(_, Eng.bytes("0123456789abcdef"), 0) : Maybe<&2, U32>}
  hexat.is(Spec.lower(c), Eng.bytes("0123456789abcdef"), 0)

def xk.hex.is(m: Maybe<&2, U32>) -> {Spec.xk.hex(m) == Eng.xk.hex(m) : Eng.XK}:
  match m:
    case Some{d}:
      {==}
    case None{}:
      {==}

def xk.hexc(+c: U32) -> {Spec.xk.hex(Spec.hexdig(c)) == Eng.xk.hex(Eng.hex(c)) : Eng.XK}:
  Equal.trans(Eng.XK, Spec.xk.hex(Spec.hexdig(c)), Spec.xk.hex(Eng.hex(c)), Eng.xk.hex(Eng.hex(c)),
    Equal.cong(Maybe<&2, U32>, Eng.XK, m => Spec.xk.hex(m), Spec.hexdig(c), Eng.hex(c), hex.is(c)),
    xk.hex.is(Eng.hex(c)))

def xk.is(k: Eng.Cls, +c: U32) -> {Spec.xk.of(k, c) == Eng.xk.of(k, c) : Eng.XK}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      xk.hexc(c)
    case Eng.KTk{}:
      xk.hexc(c)
    case Eng.KVc{}:
      %Equal.sym(Bool, Bool.or(U32.is_eq(c, 59), False{}), U32.is_eq(c, 59), or_f(U32.is_eq(c, 59))) :
        {Spec.xk.vc(_, Spec.byte.is(c, "="), Spec.byte.is(c, "\""), Spec.byte.is(c, "\\")) ==
          Eng.xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), U32.is_eq(c, 92)) : Eng.XK}
      %Equal.sym(Bool, Bool.or(U32.is_eq(c, 61), False{}), U32.is_eq(c, 61), or_f(U32.is_eq(c, 61))) :
        {Spec.xk.vc(U32.is_eq(c, 59), _, Spec.byte.is(c, "\""), Spec.byte.is(c, "\\")) ==
          Eng.xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), U32.is_eq(c, 92)) : Eng.XK}
      %Equal.sym(Bool, Bool.or(U32.is_eq(c, 34), False{}), U32.is_eq(c, 34), or_f(U32.is_eq(c, 34))) :
        {Spec.xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), _, Spec.byte.is(c, "\\")) ==
          Eng.xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), U32.is_eq(c, 92)) : Eng.XK}
      %Equal.sym(Bool, Bool.or(U32.is_eq(c, 92), False{}), U32.is_eq(c, 92), or_f(U32.is_eq(c, 92))) :
        {Spec.xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), _) ==
          Eng.xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), U32.is_eq(c, 92)) : Eng.XK}
      vc.is(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), U32.is_eq(c, 92))
    case Eng.KCt{}:
      {==}

# every U32's kind, on both sides
def xkc(+c: U32) -> {Spec.xk.of(Spec.cls(c), c) == Eng.xk.of(Eng.cls(c), c) : Eng.XK}:
  %br.cls(c) : {Spec.xk.of(Spec.cls(c), c) == Eng.xk.of(_, c) : Eng.XK}
  xk.is(Spec.cls(c), c)

# the reader's move on a byte is the spec's, mapped
def chk.eq(+at: Spec.At, +c: U32, +n: U32, +b: Bytes(), +left: U32, -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.chk(Eng.chk.next(at.eng(at), Eng.xk.of(Eng.cls(c), c)), n, b, left, pd, out) ==
    Eng.step.chk(go.eng(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c))), n, b, left, pd, out) : Eng.P}:
  %xkc(c) :
    {Eng.step.chk(Eng.chk.next(at.eng(at), _), n, b, left, pd, out) ==
      Eng.step.chk(go.eng(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c))), n, b, left, pd, out) : Eng.P}
  %Equal.sym(Eng.Mv, Eng.chk.next(at.eng(at), Spec.xk.of(Spec.cls(c), c)),
    go.eng(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c))), tbl(at, Spec.xk.of(Spec.cls(c), c))) :
    {Eng.step.chk(_, n, b, left, pd, out) ==
      Eng.step.chk(go.eng(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c))), n, b, left, pd, out) : Eng.P}
  {==}

# The walk, seen
# --------------
#
# The abstraction relation. REL(p, w, pd) holds when the reader p is
# where the spec's walk w says it is:
#   in a request line cur      p is a fresh reader fed cur
#   at the CR of an empty line  p is at that CR
#   in a field line cur of h   p is a reader at a line's start, with pd
#                              pending, fed cur; pd looks like h
#   at a line's CR, or the     p is at that CR, with pd pending;
#   head's                     pd looks like h
#   in a body                  p counts the same bytes down, holding the
#                              same body so far
#   in a chunked body's        p is at the same place in its grammar,
#   framing, or a chunk's data with the same size, body so far and
#                              budget, or counts the same data down
#   after an upgrade           p keeps the same bytes, in order
#   refused                    p is Bad, with the same requests
# and, but for the last two, p is a fresh reader with the requests done
# fed the bytes since the last one (BND): the reader restarts exactly
# where the spec says a request ends.

def BND(-p: Eng.P, -since: List<&2, U32>, -out: List<&2, Eng.Req>) -> Data:
  {p == Eng.feed(since, Eng.P{Eng.Pre{}, Eng.pend.new(), out}) : Eng.P}

def REL.m(-p: Eng.P, mode: Spec.Mode, -out: List<&2, Eng.Req>, -since: List<&2, U32>, -pd: Eng.Pend) -> Type:
  match mode:
    case Spec.MReq{+cur}:
      {p == Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}) : Eng.P} & (Plain(cur) & BND(p, since, out))
    case Spec.MBlank{}:
      {p == Eng.P{Eng.PreLf{}, Eng.pend.new(), out} : Eng.P} & BND(p, since, out)
    case Spec.MField{h, +cur}:
      PR(pd, h) & ({p == Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}) : Eng.P} & (Plain(cur) & BND(p, since, out)))
    case Spec.MEol{h}:
      PR(pd, h) & ({p == Eng.P{Eng.CrM{}, pd, out} : Eng.P} & BND(p, since, out))
    case Spec.MEoh{h}:
      PR(pd, h) & ({p == Eng.P{Eng.CrL{}, pd, out} : Eng.P} & BND(p, since, out))
    case Spec.MBody{h, more, got}:
      PR(pd, h) & ({p == Eng.P{Eng.Bod{more, Bytes.from_list(got)}, pd, out} : Eng.P} & BND(p, since, out))
    case Spec.MChunk{h, at, n, got, left}:
      PR(pd, h) & ({p == Eng.P{Eng.Chk{at.eng(at), n, Bytes.from_list(got), left}, pd, out} : Eng.P} &
        BND(p, since, out))
    case Spec.MData{h, more, got, left}:
      PR(pd, h) & ({p == Eng.P{Eng.Chd{more, Bytes.from_list(got), left}, pd, out} : Eng.P} & BND(p, since, out))
    case Spec.MUp{got}:
      {p == Eng.P{Eng.Rest{Bytes.from_list(got)}, Eng.pend.new(), out} : Eng.P}
    case Spec.MBad{}:
      Dead(p, out)

def REL(-p: Eng.P, w: Spec.W, -pd: Eng.Pend) -> Type:
  match w:
    case Spec.W{mode, out, since}:
      REL.m(p, mode, out, since, pd)

# some pending fields the relation holds with
def SR(-p: Eng.P, w: Spec.W) -> Type:
  &pd2: Eng.Pend -> REL(p, w, pd2)

# a step, and a byte of known class
def cstep(-p: Eng.P, -q: Eng.P, -c: U32, e: {p == q : Eng.P}) -> {Eng.step(p, c) == Eng.step(q, c) : Eng.P}:
  Equal.cong(Eng.P, Eng.P, x => Eng.step(x, c), p, q, e)

def fsnoc(xs: List<&2, U32>, +c: U32, +q: Eng.P) ->
  {Eng.step(Eng.feed(xs, q), c) == Eng.feed(Spec.snoc(xs, c), q) : Eng.P}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      fsnoc(t, c, Eng.step(q, x))

def adv(-p: Eng.P, +xs: List<&2, U32>, +c: U32, +q: Eng.P, e: {p == Eng.feed(xs, q) : Eng.P}) ->
  {Eng.step(p, c) == Eng.feed(Spec.snoc(xs, c), q) : Eng.P}:
  Equal.trans(Eng.P, Eng.step(p, c), Eng.step(Eng.feed(xs, q), c), Eng.feed(Spec.snoc(xs, c), q),
    cstep(p, Eng.feed(xs, q), c, e), fsnoc(xs, c, q))

def stepk(q: Eng.P, +c: U32, -k: Eng.Cls, ek: {Spec.cls(c) == k : Eng.Cls}) ->
  {SK(q, k, c) == Eng.step(q, c) : Eng.P}:
  match q:
    case Eng.P{st, pd, out}:
      %ek : {Eng.step.at(st, _, c, pd, out) == Eng.step(Eng.P{st, pd, out}, c) : Eng.P}
      stepc(Eng.P{st, pd, out}, c)

def atk(-p: Eng.P, +x: Eng.P, +c: U32, -k: Eng.Cls, ek: {Spec.cls(c) == k : Eng.Cls}, e: {p == x : Eng.P}) ->
  {Eng.step(p, c) == SK(x, k, c) : Eng.P}:
  Equal.trans(Eng.P, Eng.step(p, c), Eng.step(x, c), SK(x, k, c), cstep(p, x, c, e),
    Equal.sym(Eng.P, SK(x, k, c), Eng.step(x, c), stepk(x, c, k, ek)))

def deadvia(-p2: Eng.P, -q: Eng.P, -out: List<&2, Eng.Req>, e: {p2 == q : Eng.P}, d: Dead(q, out)) ->
  Dead(p2, out):
  %Equal.sym(Eng.P, p2, q, e) : Dead(_, out)
  d

def dq(-q: Eng.P, -x: Eng.P, -k: Eng.Cls, -c: U32, -out: List<&2, Eng.Req>, e: {q == x : Eng.P},
  d: Dead(SK(x, k, c), out)) -> Dead(SK(q, k, c), out):
  %Equal.sym(Eng.P, q, x, e) : Dead(SK(_, k, c), out)
  d

def skq(-q: Eng.P, -x: Eng.P, -k: Eng.Cls, -c: U32, e: {q == x : Eng.P}) -> {SK(q, k, c) == SK(x, k, c) : Eng.P}:
  Equal.cong(Eng.P, Eng.P, y => SK(y, k, c), q, x, e)

def ncof(-c: U32, -k: Eng.Cls, ek: {Spec.cls(c) == k : Eng.Cls}) ->
  {notcrlf(k) == True{} : Bool} -> {notcrlf(Spec.cls(c)) == True{} : Bool}:
  n =>
    %Equal.sym(Eng.Cls, Spec.cls(c), k, ek) : {notcrlf(_) == True{} : Bool}
    n

def bnd.step(-p: Eng.P, +c: U32, +since: List<&2, U32>, +out: List<&2, Eng.Req>, bnd: BND(p, since, out)) ->
  BND(Eng.step(p, c), Spec.snoc(since, c), out):
  adv(p, since, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, bnd)

# a request, completed: the reader emits what the spec does
def reqof(x: PV, body: Bytes()) -> Eng.Req:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match u:
        case UV{k, uu, c, v}:
          Eng.pend.req.fx(m, p, body, close, Eng.Asks{k, uu, c, v}, fx)

def e.req(pd: Eng.Pend, -body: Bytes()) -> {Eng.pend.req(pd, body) == reqof(pv(pd), body) : Eng.Req}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match ws fx:
        case Eng.Plain{} Eng.Fx{a, b, t}:
          {==}
        case Eng.Asks{k, u, c, v} y:
          {==}

def s.req(h: Spec.Head, -b: List<&2, U32>) ->
  {Spec.req(h, b) == reqof(hv(h), Bytes.from_list(b)) : Eng.Req}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f}:
      match k f:
        case Nil{} Eng.Fx{a, bb, x}:
          {==}
        case Con{y, r} Eng.Fx{a, bb, x}:
          {==}

def REQ(+pd: Eng.Pend, +h: Spec.Head, +b: List<&2, U32>, pr: PR(pd, h)) ->
  {Spec.req(h, b) == Eng.pend.req(pd, Bytes.from_list(b)) : Eng.Req}:
  Equal.trans(Eng.Req, Spec.req(h, b), reqof(hv(h), Bytes.from_list(b)), Eng.pend.req(pd, Bytes.from_list(b)),
    s.req(h, b),
    Equal.trans(Eng.Req, reqof(hv(h), Bytes.from_list(b)), reqof(pv(pd), Bytes.from_list(b)),
      Eng.pend.req(pd, Bytes.from_list(b)),
      Equal.cong(PV, Eng.Req, x => reqof(x, Bytes.from_list(b)), hv(h), pv(pd), Equal.sym(PV, pv(pd), hv(h), pr)),
      Equal.sym(Eng.Req, Eng.pend.req(pd, Bytes.from_list(b)), reqof(pv(pd), Bytes.from_list(b)),
        e.req(pd, Bytes.from_list(b)))))

def EMIT.ws(ws: Bool, -p2: Eng.P, +m: Eng.Meth, +pa: Bytes(), +bd: Bytes(), +cl: Bool, +key: Bytes(),
  +out: List<&2, Eng.Req>, +pd: Eng.Pend,
  e: {p2 == Eng.emit.go(Eng.Req{m, pa, bd, cl, ws, key}, out) : Eng.P}) ->
  SR(p2, Spec.emit.go(Eng.Req{m, pa, bd, cl, ws, key}, out)):
  match ws:
    case True{}:
      (pd, e)
    case False{}:
      +e2 = e
      (pd, (e2, (Unit{}, e2)))

def EMIT(+pd: Eng.Pend, h: Spec.Head, +b: List<&2, U32>, +out: List<&2, Eng.Req>, -p2: Eng.P,
  e: {p2 == Eng.emit(pd, Bytes.from_list(b), out) : Eng.P}, pr: PR(pd, h)) -> SR(p2, Spec.emit(h, b, out)):
  match h:
    case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf}:
      match hf:
        case Eng.Fx{+v10, +ka, +te}:
          EMIT.ws(Bool.not(v10) && (hu && hcu && Spec.has(hk) && Bool.not(hvb)), p2, hm, Bytes.from_list(ht),
            Bytes.from_list(b), hc || (v10 && Bool.not(ka)), Bytes.from_list(hk), out, pd,
            Equal.trans(Eng.P, p2, Eng.emit(pd, Bytes.from_list(b), out),
              Eng.emit.go(Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}}, b), out), e,
              Equal.cong(Eng.Req, Eng.P, x => Eng.emit.go(x, out), Eng.pend.req(pd, Bytes.from_list(b)),
                Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}}, b),
                Equal.sym(Eng.Req, Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}}, b),
                  Eng.pend.req(pd, Bytes.from_list(b)),
                  REQ(pd, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}}, b, pr)))))

# One byte
# --------

# the request line's CR: HTTP/1.1, HTTP/1.0, or refused
def CR.ver(b11: Bool, b10: Bool, -p: Eng.P, +m: List<&2, U32>, +t: List<&2, U32>, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, +c: U32, +pd: Eng.Pend,
  e: {Eng.step(p, c) == Eng.step.ver(b11, b10, pd2(m, t), out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out)) ->
  SR(Eng.step(p, c), Spec.req.ok(b11, b10, m, t, out, Spec.snoc(since, c))):
  match b11 b10:
    case True{} x:
      (pd2(m, t), (pr.new(m, t), (e, bnd)))
    case False{} True{}:
      (Eng.pend.v10(pd2(m, t)), (pr.new10(m, t), (e, bnd)))
    case False{} False{}:
      (pd, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd2(m, t), out}, out, e, {==}))

def ver2.eq(+vb: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.ver(Eng.bytes.eq(vb, "HTTP/1.1"), Eng.bytes.eq(vb, "HTTP/1.0"), pd, out) ==
    Eng.step.ver(Spec.eq(vb, "HTTP/1.1"), Spec.eq(vb, "HTTP/1.0"), pd, out) : Eng.P}:
  %eqs(vb, "HTTP/1.1") :
    {Eng.step.ver(_, Eng.bytes.eq(vb, "HTTP/1.0"), pd, out) ==
      Eng.step.ver(Spec.eq(vb, "HTTP/1.1"), Spec.eq(vb, "HTTP/1.0"), pd, out) : Eng.P}
  %eqs(vb, "HTTP/1.0") :
    {Eng.step.ver(Spec.eq(vb, "HTTP/1.1"), _, pd, out) ==
      Eng.step.ver(Spec.eq(vb, "HTTP/1.1"), Spec.eq(vb, "HTTP/1.0"), pd, out) : Eng.P}
  {==}

def CR.req(v: Spec.RLine, +q: Eng.P, +c: U32, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, lr: LR.req(q, v, out), e0: {Eng.step(p, c) == SK(q, Eng.KCr{}, c) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out)) ->
  SR(Eng.step(p, c), Spec.req.cr(v, out, Spec.snoc(since, c))):
  match v:
    case Spec.RNone{}:
      (pd, (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c), Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, e0,
        skq(q, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, Eng.KCr{}, c, lr)), bnd))
    case Spec.RMeth{m}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0,
        dq(q, Eng.P{Eng.InM{Bytes.from_list(m)}, Eng.pend.new(), out}, Eng.KCr{}, c, out, lr, {==})))
    case Spec.RTarget{m, t}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0,
        dq(q, Eng.P{Eng.InT{Bytes.from_list(t)}, pd1(m), out}, Eng.KCr{}, c, out, lr, {==})))
    case Spec.RVer{+m, +t, +v}:
      CR.ver(Spec.eq(Bytes.from_list(v), "HTTP/1.1"), Spec.eq(Bytes.from_list(v), "HTTP/1.0"), p, m, t, out,
        since, c, pd,
        Equal.trans(Eng.P, Eng.step(p, c),
          Eng.step.ver(Eng.bytes.eq(Bytes.from_list(v), "HTTP/1.1"), Eng.bytes.eq(Bytes.from_list(v), "HTTP/1.0"),
            pd2(m, t), out),
          Eng.step.ver(Spec.eq(Bytes.from_list(v), "HTTP/1.1"), Spec.eq(Bytes.from_list(v), "HTTP/1.0"),
            pd2(m, t), out),
          Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.step.ver(Eng.bytes.eq(Bytes.from_list(v), "HTTP/1.1"), Eng.bytes.eq(Bytes.from_list(v), "HTTP/1.0"),
              pd2(m, t), out), e0,
            skq(q, Eng.P{Eng.InV{Bytes.from_list(v)}, pd2(m, t), out}, Eng.KCr{}, c, lr)),
          ver2.eq(Bytes.from_list(v), pd2(m, t), out)),
        bnd)
    case Spec.RBad{}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0, dead.step(q, Eng.KCr{}, c, out)(lr)))

def LF.req(v: Spec.RLine, +q: Eng.P, +c: U32, -p: Eng.P, +out: List<&2, Eng.Req>, lr: LR.req(q, v, out),
  e0: {Eng.step(p, c) == SK(q, Eng.KLf{}, c) : Eng.P}) -> Dead(Eng.step(p, c), out):
  match v:
    case Spec.RNone{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.RMeth{m}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InM{Bytes.from_list(m)}, Eng.pend.new(), out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.RTarget{m, t}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InT{Bytes.from_list(t)}, pd1(m), out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.RVer{m, t, v}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InV{Bytes.from_list(v)}, pd2(m, t), out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.RBad{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0, dead.step(q, Eng.KLf{}, c, out)(lr))

def STEP.req.k(+k: Eng.Cls, +c: U32, +cur: List<&2, U32>, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, ek: {Spec.cls(c) == k : Eng.Cls},
  e1: {p == Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}) : Eng.P}, pl: Plain(cur),
  bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.req.byte(k, c, cur, out, Spec.snoc(since, c))):
  match k:
    case Eng.KCr{}:
      CR.req(Spec.req.view(cur), Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), c, p, pd, out, since,
        line.req(cur, out)(pl), atk(p, Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), c, Eng.KCr{}, ek, e1),
        bnd.step(p, c, since, out, bnd))
    case Eng.KLf{}:
      (pd, LF.req(Spec.req.view(cur), Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), c, p, out,
        line.req(cur, out)(pl), atk(p, Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), c, Eng.KLf{}, ek, e1)))
    case Eng.KSp{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KSp{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KHt{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KHt{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KCo{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KCo{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KCm{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KCm{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KDg{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KDg{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KTk{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KTk{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KVc{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KVc{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))
    case Eng.KCt{}:
      (pd, (adv(p, cur, c, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KCt{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd))))

# an empty line's CR, and a line's CR in a head
def STEP.blank.k(+k: Eng.Cls, +c: U32, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, ek: {Spec.cls(c) == k : Eng.Cls},
  e1: {p == Eng.P{Eng.PreLf{}, Eng.pend.new(), out} : Eng.P}, bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.blank.byte(k, out, Spec.snoc(since, c))):
  match k:
    case Eng.KLf{}:
      (pd, (atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KLf{}, ek, e1),
        (Unit{}, bnd.step(p, c, since, out, bnd))))
    case Eng.KSp{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KSp{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KSp{}, ek, e1), {==}))
    case Eng.KHt{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KHt{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KHt{}, ek, e1), {==}))
    case Eng.KCr{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KCr{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KCr{}, ek, e1), {==}))
    case Eng.KCo{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KCo{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KCo{}, ek, e1), {==}))
    case Eng.KCm{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KCm{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KCm{}, ek, e1), {==}))
    case Eng.KDg{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KDg{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KDg{}, ek, e1), {==}))
    case Eng.KTk{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KTk{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KTk{}, ek, e1), {==}))
    case Eng.KVc{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KVc{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KVc{}, ek, e1), {==}))
    case Eng.KCt{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, Eng.KCt{}, c), out,
        atk(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, c, Eng.KCt{}, ek, e1), {==}))

def STEP.eol.k(+k: Eng.Cls, +c: U32, +h: Spec.Head, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, ek: {Spec.cls(c) == k : Eng.Cls}, pr: PR(pd, h),
  e1: {p == Eng.P{Eng.CrM{}, pd, out} : Eng.P}, bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.eol.byte(k, h, out, Spec.snoc(since, c))):
  match k:
    case Eng.KLf{}:
      (pd, (pr, (atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KLf{}, ek, e1),
        (Unit{}, bnd.step(p, c, since, out, bnd)))))
    case Eng.KSp{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KSp{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KSp{}, ek, e1), {==}))
    case Eng.KHt{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KHt{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KHt{}, ek, e1), {==}))
    case Eng.KCr{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KCr{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KCr{}, ek, e1), {==}))
    case Eng.KCo{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KCo{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KCo{}, ek, e1), {==}))
    case Eng.KCm{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KCm{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KCm{}, ek, e1), {==}))
    case Eng.KDg{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KDg{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KDg{}, ek, e1), {==}))
    case Eng.KTk{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KTk{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KTk{}, ek, e1), {==}))
    case Eng.KVc{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KVc{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KVc{}, ek, e1), {==}))
    case Eng.KCt{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrM{}, pd, out}, Eng.KCt{}, c), out,
        atk(p, Eng.P{Eng.CrM{}, pd, out}, c, Eng.KCt{}, ek, e1), {==}))

# a field line's CR: a length
def PVcl(x: PV) -> Eng.Cl:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      cl

# the pending fields with the length set, and the head with it set
def pr.cl(+m: Eng.Meth, +pa: Bytes(), +cl: Eng.Cl, +cls: Bool, +host: Eng.Hosts, +ws: Eng.Up, +fx: Eng.Fx,
  +hm: Eng.Meth, +ht: List<&2, U32>, +l: Maybe<&2, U32>, +hc: Bool, +hs: Nat, +hk: List<&2, U32>,
  +hu: Bool, +hcu: Bool, +hvb: Bool, +hf: Eng.Fx, +w: U32,
  pr: PR(Eng.Pend{m, pa, cl, cls, host, ws, fx}, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf})) ->
  PR(Eng.Pend{m, pa, Eng.Has{w}, cls, host, ws, fx}, Spec.Head{hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf}):
  pr.by(x => pv.cl(x, Eng.Has{w}), Eng.Pend{m, pa, cl, cls, host, ws, fx}, Eng.Pend{m, pa, Eng.Has{w}, cls, host, ws, fx},
    Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf}, Spec.Head{hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf},
    {==}, {==}, pr)

def CR.dup(b: Bool, -p: Eng.P, +c: U32, +pd2: Eng.Pend, +h2: Spec.Head, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, e: {Eng.step(p, c) == Eng.step.clen.dup(pd2, out, b) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out), pr: PR(pd2, h2)) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.head.len.at(b, h2), out, Spec.snoc(since, c))):
  match b:
    case True{}:
      (pd2, (pr, (e, bnd)))
    case False{}:
      (pd2, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd2, out}, out, e, {==}))

def CR.clen.l(l: Maybe<&2, U32>, +n: U32, +m: Eng.Meth, +pa: Bytes(), +cl: Eng.Cl, +cls: Bool,
  +host: Eng.Hosts, +ws: Eng.Up, +fx: Eng.Fx, +hm: Eng.Meth, +ht: List<&2, U32>, +hc: Bool, +hs: Nat,
  +hk: List<&2, U32>, +hu: Bool, +hcu: Bool, +hvb: Bool, +hf: Eng.Fx, -p: Eng.P, +c: U32,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  e: {Eng.step(p, c) == Eng.step.clen.go(m, pa, clv(l), cls, host, ws, fx, n, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out),
  pr: PR(Eng.Pend{m, pa, cl, cls, host, ws, fx}, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf})) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.head.len(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf}, n), out,
    Spec.snoc(since, c))):
  match l:
    case None{}:
      (Eng.Pend{m, pa, Eng.Has{n}, cls, host, ws, fx},
        (pr.cl(m, pa, cl, cls, host, ws, fx, hm, ht, None{}, hc, hs, hk, hu, hcu, hvb, hf, n, pr), (e, bnd)))
    case Some{+w}:
      CR.dup(U32.is_eq(n, w), p, c, Eng.Pend{m, pa, Eng.Has{w}, cls, host, ws, fx},
        Spec.Head{hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf}, out, since, e, bnd,
        pr.cl(m, pa, cl, cls, host, ws, fx, hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf, w, pr))

def CR.clen(+n: U32, pd: Eng.Pend, h: Spec.Head, -p: Eng.P, +c: U32, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, e: {Eng.step(p, c) == Eng.step.clen(n, pd, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out), pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.head.len(h, n), out, Spec.snoc(since, c))):
  match pd:
    case Eng.Pend{+m, +pa, +cl, +cls, +host, +ws, +fx}:
      match h:
        case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf}:
          +pr2 = pr
          CR.clen.l(l, n, m, pa, cl, cls, host, ws, fx, hm, ht, hc, hs, hk, hu, hcu, hvb, hf, p, c, out, since,
            Equal.trans(Eng.P, Eng.step(p, c), Eng.step.clen.go(m, pa, cl, cls, host, ws, fx, n, out),
              Eng.step.clen.go(m, pa, clv(l), cls, host, ws, fx, n, out), e,
              Equal.cong(Eng.Cl, Eng.P, x => Eng.step.clen.go(m, pa, x, cls, host, ws, fx, n, out), cl, clv(l),
                Equal.cong(PV, Eng.Cl, y => PVcl(y), pv(Eng.Pend{m, pa, cl, cls, host, ws, fx}),
                  hv(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf}), pr2))),
            bnd, pr2)

# a field line's CR: the whole line read
def conn.eq(+pd: Eng.Pend, +out: List<&2, Eng.Req>, +cur: List<&2, U32>, +d: List<&2, List<&2, U32>>) ->
  {Eng.step.conn(lowb(cur), Spec.named("close", d), Spec.named("upgrade", d), Spec.named("keep-alive", d), pd, out) ==
    Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
      Spec.named("keep-alive", Con{cur, d})), out} : Eng.P}:
  %eqs(lowb(cur), "close") :
    {Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", d) || _,
      Spec.named("upgrade", d) || Eng.bytes.eq(lowb(cur), "upgrade"),
      Spec.named("keep-alive", d) || Eng.bytes.eq(lowb(cur), "keep-alive")), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), out} : Eng.P}
  %eqs(lowb(cur), "upgrade") :
    {Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", d) || _,
      Spec.named("keep-alive", d) || Eng.bytes.eq(lowb(cur), "keep-alive")), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), out} : Eng.P}
  %eqs(lowb(cur), "keep-alive") :
    {Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
      Spec.named("keep-alive", d) || _), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), out} : Eng.P}
  {==}

# a Transfer-Encoding's coding, read by each side
def te.ok.eq(+bv: Bytes(), -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.te(bv, pd, out) == Eng.step.te.at(Spec.eq(Spec.lows(bv), "chunked"), pd, out) : Eng.P}:
  %br.lows(bv) :
    {Eng.step.te.at(Eng.bytes.eq(_, Eng.te.lit()), pd, out) ==
      Eng.step.te.at(Spec.eq(Spec.lows(bv), "chunked"), pd, out) : Eng.P}
  %eqs(Spec.lows(bv), Eng.te.lit()) :
    {Eng.step.te.at(_, pd, out) == Eng.step.te.at(Spec.eq(Spec.lows(bv), "chunked"), pd, out) : Eng.P}
  {==}

def TE.b(bb: Bool, -p: Eng.P, +c: U32, +pd: Eng.Pend, +h: Spec.Head, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, pr: PR(pd, h), e: {Eng.step(p, c) == te.pick(bb, pd, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out)) ->
  SR(Eng.step(p, c), Spec.field.next(hte.pick(bb, h), out, Spec.snoc(since, c))):
  match bb:
    case True{}:
      (pend.teset(pd), (pr.te(pd, h, pr), (e, bnd)))
    case False{}:
      (pd, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd, out}, out, e, {==}))

def up.eq(+pd: Eng.Pend, +out: List<&2, Eng.Req>, +cur: List<&2, U32>, +d: List<&2, List<&2, U32>>) ->
  {Eng.step.upv(lowb(cur), Spec.named("websocket", d), pd, out) ==
    Eng.P{Eng.CrM{}, Eng.pend.up(pd, Spec.named("websocket", Con{cur, d})), out} : Eng.P}:
  %eqs(lowb(cur), "websocket") :
    {Eng.P{Eng.CrM{}, Eng.pend.up(pd, Spec.named("websocket", d) || _), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.up(pd, Spec.named("websocket", Con{cur, d})), out} : Eng.P}
  {==}

def key.eq(+pd: Eng.Pend, +out: List<&2, Eng.Req>, +k: List<&2, U32>) ->
  {Eng.step.key(Bytes.from_list(k), pd, out) ==
    Eng.P{Eng.CrM{}, Eng.pend.key(pd, Bytes.from_list(Spec.trim(k))), out} : Eng.P}:
  %trim.is(k) :
    {Eng.P{Eng.CrM{}, Eng.pend.key(pd, _), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.key(pd, Bytes.from_list(Spec.trim(k))), out} : Eng.P}
  {==}

def ver.eq(+pd: Eng.Pend, +out: List<&2, Eng.Req>, +v: List<&2, U32>) ->
  {Eng.step.wsv(Bytes.from_list(v), pd, out) ==
    Eng.P{Eng.CrM{}, Eng.pend.ver(pd, Spec.eq(Bytes.from_list(Spec.trim(v)), "13")), out} : Eng.P}:
  %trim.is(v) :
    {Eng.P{Eng.CrM{}, Eng.pend.ver(pd, Eng.bytes.eq(_, "13")), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.ver(pd, Spec.eq(Bytes.from_list(Spec.trim(v)), "13")), out} : Eng.P}
  %eqs(Bytes.from_list(Spec.trim(v)), "13") :
    {Eng.P{Eng.CrM{}, Eng.pend.ver(pd, _), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.ver(pd, Spec.eq(Bytes.from_list(Spec.trim(v)), "13")), out} : Eng.P}
  {==}

def CR.len(ws: Bool, +n: U32, +q: Eng.P, +c: U32, +h: Spec.Head, -p: Eng.P, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>, lr: LR.len(q, n, ws, pd, out),
  e0: {Eng.step(p, c) == SK(q, Eng.KCr{}, c) : Eng.P}, bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out),
  pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.head.len(h, n), out, Spec.snoc(since, c))):
  match ws:
    case True{}:
      CR.clen(n, pd, h, p, c, out, since,
        Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c), Eng.step.clen(n, pd, out), e0,
          skq(q, Eng.P{Eng.InLt{n}, pd, out}, Eng.KCr{}, c, lr)), bnd, pr)
    case False{}:
      CR.clen(n, pd, h, p, c, out, since,
        Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c), Eng.step.clen(n, pd, out), e0,
          skq(q, Eng.P{Eng.InL{n}, pd, out}, Eng.KCr{}, c, lr)), bnd, pr)

def CR.val(val: Spec.Val, +q: Eng.P, +c: U32, +h: Spec.Head, -p: Eng.P, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>, lr: LR.val(q, val, pd, out),
  e0: {Eng.step(p, c) == SK(q, Eng.KCr{}, c) : Eng.P}, bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out),
  pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.field.done(h, val), out, Spec.snoc(since, c))):
  match val:
    case Spec.VLen0{}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0,
        dq(q, Eng.P{Eng.InL0{}, pd, out}, Eng.KCr{}, c, out, lr, {==})))
    case Spec.VLen{n, ws}:
      CR.len(ws, n, q, c, h, p, pd, out, since, lr, e0, bnd, pr)
    case Spec.VConn{+d, +cur}:
      (Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})),
        (pr.conn(pd, h, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
          Spec.named("keep-alive", Con{cur, d}), pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
              Spec.named("keep-alive", Con{cur, d})), out},
            e0,
            Equal.trans(Eng.P, SK(q, Eng.KCr{}, c),
              Eng.step.conn(lowb(cur), Spec.named("close", d), Spec.named("upgrade", d), Spec.named("keep-alive", d),
                pd, out),
              Eng.P{Eng.CrM{}, Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
                Spec.named("keep-alive", Con{cur, d})), out},
              skq(q, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", d), Spec.named("upgrade", d),
                Spec.named("keep-alive", d)}, pd, out}, Eng.KCr{}, c, lr),
              conn.eq(pd, out, cur, d))),
          bnd)))
    case Spec.VUp{+d, +cur}:
      (Eng.pend.up(pd, Spec.named("websocket", Con{cur, d})),
        (pr.up(pd, h, Spec.named("websocket", Con{cur, d}), pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.up(pd, Spec.named("websocket", Con{cur, d})), out},
            e0,
            Equal.trans(Eng.P, SK(q, Eng.KCr{}, c),
              Eng.step.upv(lowb(cur), Spec.named("websocket", d), pd, out),
              Eng.P{Eng.CrM{}, Eng.pend.up(pd, Spec.named("websocket", Con{cur, d})), out},
              skq(q, Eng.P{Eng.InLu{lowb(cur), Spec.named("websocket", d)}, pd, out}, Eng.KCr{}, c, lr),
              up.eq(pd, out, cur, d))),
          bnd)))
    case Spec.VKey0{}:
      (Eng.pend.key(pd, Bytes.from_list(Nil{})),
        (pr.key(pd, h, Nil{}, pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.key(pd, Bytes.from_list(Nil{})), out}, e0,
            skq(q, Eng.P{Eng.InLk0{}, pd, out}, Eng.KCr{}, c, lr)), bnd)))
    case Spec.VKey{+k}:
      (Eng.pend.key(pd, Bytes.from_list(Spec.trim(k))),
        (pr.key(pd, h, Spec.trim(k), pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.key(pd, Bytes.from_list(Spec.trim(k))), out}, e0,
            Equal.trans(Eng.P, SK(q, Eng.KCr{}, c), Eng.step.key(Bytes.from_list(k), pd, out),
              Eng.P{Eng.CrM{}, Eng.pend.key(pd, Bytes.from_list(Spec.trim(k))), out},
              skq(q, Eng.P{Eng.InLk{Bytes.from_list(k)}, pd, out}, Eng.KCr{}, c, lr),
              key.eq(pd, out, k))), bnd)))
    case Spec.VVer{+v}:
      (Eng.pend.ver(pd, Spec.eq(Bytes.from_list(Spec.trim(v)), "13")),
        (pr.ver(pd, h, Spec.eq(Bytes.from_list(Spec.trim(v)), "13"), pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.ver(pd, Spec.eq(Bytes.from_list(Spec.trim(v)), "13")), out}, e0,
            Equal.trans(Eng.P, SK(q, Eng.KCr{}, c), Eng.step.wsv(Bytes.from_list(v), pd, out),
              Eng.P{Eng.CrM{}, Eng.pend.ver(pd, Spec.eq(Bytes.from_list(Spec.trim(v)), "13")), out},
              skq(q, Eng.P{Eng.InLv{Bytes.from_list(v)}, pd, out}, Eng.KCr{}, c, lr),
              ver.eq(pd, out, v))), bnd)))
    case Spec.VTe0{}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0,
        dq(q, Eng.P{Eng.InLe0{}, pd, out}, Eng.KCr{}, c, out, lr, {==})))
    case Spec.VTe{+t}:
      +pr2 = pr
      %s.te(h, Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked")) :
        SR(Eng.step(p, c), Spec.field.next(_, out, Spec.snoc(since, c)))
      %Equal.cong(PV, Bool, x => pv.teok(x, Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked")), pv(pd), hv(h), pr2) :
        SR(Eng.step(p, c), Spec.field.next(hte.pick(_, h), out, Spec.snoc(since, c)))
      TE.b(pv.teok(pv(pd), Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked")), p, c, pd, h, out, since, pr2,
        Equal.trans(Eng.P, Eng.step(p, c), Eng.step.te.at(Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked"), pd, out),
          te.pick(pv.teok(pv(pd), Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked")), pd, out),
          Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.step.te.at(Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked"), pd, out), e0,
            Equal.trans(Eng.P, SK(q, Eng.KCr{}, c), Eng.step.te(Bytes.from_list(t), pd, out),
              Eng.step.te.at(Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked"), pd, out),
              skq(q, Eng.P{Eng.InLe{Bytes.from_list(t)}, pd, out}, Eng.KCr{}, c, lr),
              te.ok.eq(Bytes.from_list(t), pd, out))),
          e.te(pd, Spec.eq(Spec.lows(Bytes.from_list(t)), "chunked"), out)),
        bnd)
    case Spec.VHost{}:
      (Eng.pend.host(pd),
        (pr.host(pd, h, pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.host(pd), out}, e0,
            skq(q, Eng.P{Eng.InLx{}, Eng.pend.host(pd), out}, Eng.KCr{}, c, lr)), bnd)))
    case Spec.VSkip{}:
      (pd, (pr, (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c), Eng.P{Eng.CrM{}, pd, out}, e0,
        skq(q, Eng.P{Eng.InLx{}, pd, out}, Eng.KCr{}, c, lr)), bnd)))

def CR.field(v: Spec.FLine, +q: Eng.P, +c: U32, +h: Spec.Head, -p: Eng.P, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>, lr: LR.field(q, v, pd, out),
  e0: {Eng.step(p, c) == SK(q, Eng.KCr{}, c) : Eng.P}, bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out),
  pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.field.cr(h, v, out, Spec.snoc(since, c))):
  match v:
    case Spec.FEmpty{}:
      (pd, (pr, (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c), Eng.P{Eng.CrL{}, pd, out}, e0,
        skq(q, Eng.P{Eng.Lin{}, pd, out}, Eng.KCr{}, c, lr)), bnd)))
    case Spec.FName{n}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0,
        dq(q, Eng.P{Eng.InN{Bytes.from_list(n)}, pd, out}, Eng.KCr{}, c, out, lr, {==})))
    case Spec.FVal{val}:
      CR.val(val, q, c, h, p, pd, out, since, lr, e0, bnd, pr)
    case Spec.FBad{}:
      (pd, deadvia(Eng.step(p, c), SK(q, Eng.KCr{}, c), out, e0, dead.step(q, Eng.KCr{}, c, out)(lr)))

# a bare LF inside a field line
def LF.len(ws: Bool, +n: U32, +q: Eng.P, +c: U32, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  lr: LR.len(q, n, ws, pd, out), e0: {Eng.step(p, c) == SK(q, Eng.KLf{}, c) : Eng.P}) -> Dead(Eng.step(p, c), out):
  match ws:
    case True{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLt{n}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case False{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InL{n}, pd, out}, Eng.KLf{}, c, out, lr, {==}))

def LF.val(val: Spec.Val, +q: Eng.P, +c: U32, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  lr: LR.val(q, val, pd, out), e0: {Eng.step(p, c) == SK(q, Eng.KLf{}, c) : Eng.P}) -> Dead(Eng.step(p, c), out):
  match val:
    case Spec.VLen0{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InL0{}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VLen{n, ws}:
      LF.len(ws, n, q, c, p, pd, out, lr, e0)
    case Spec.VConn{d, cur}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", d), Spec.named("upgrade", d),
          Spec.named("keep-alive", d)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VUp{d, cur}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLu{lowb(cur), Spec.named("websocket", d)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VKey0{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLk0{}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VKey{k}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLk{Bytes.from_list(k)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VVer{v}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLv{Bytes.from_list(v)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VTe0{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLe0{}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VTe{t}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLe{Bytes.from_list(t)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VHost{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLx{}, Eng.pend.host(pd), out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VSkip{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLx{}, pd, out}, Eng.KLf{}, c, out, lr, {==}))

def LF.field(v: Spec.FLine, +q: Eng.P, +c: U32, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  lr: LR.field(q, v, pd, out), e0: {Eng.step(p, c) == SK(q, Eng.KLf{}, c) : Eng.P}) -> Dead(Eng.step(p, c), out):
  match v:
    case Spec.FEmpty{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.Lin{}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.FName{n}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InN{Bytes.from_list(n)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.FVal{val}:
      LF.val(val, q, c, p, pd, out, lr, e0)
    case Spec.FBad{}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0, dead.step(q, Eng.KLf{}, c, out)(lr))

def STEP.field.k(+k: Eng.Cls, +c: U32, +h: Spec.Head, +cur: List<&2, U32>, -p: Eng.P, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>, ek: {Spec.cls(c) == k : Eng.Cls}, pr: PR(pd, h),
  e1: {p == Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}) : Eng.P}, pl: Plain(cur), bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.field.byte(k, c, h, cur, out, Spec.snoc(since, c))):
  match k:
    case Eng.KCr{}:
      CR.field(Spec.field.view(cur), Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), c, h, p, pd, out, since,
        line.field(cur, pd, out)(pl), atk(p, Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), c, Eng.KCr{}, ek, e1),
        bnd.step(p, c, since, out, bnd), pr)
    case Eng.KLf{}:
      (pd, LF.field(Spec.field.view(cur), Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), c, p, pd, out,
        line.field(cur, pd, out)(pl), atk(p, Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), c, Eng.KLf{}, ek, e1)))
    case Eng.KSp{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KSp{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KHt{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KHt{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KCo{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KCo{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KCm{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KCm{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KDg{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KDg{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KTk{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KTk{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KVc{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KVc{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))
    case Eng.KCt{}:
      (pd, (pr, (adv(p, cur, c, Eng.P{Eng.Lin{}, pd, out}, e1),
        (plain.snoc(cur, c, ncof(c, Eng.KCt{}, ek)({==}))(pl), bnd.step(p, c, since, out, bnd)))))

# the head's end
def HEAD.z(z: Bool, +n: U32, +pd: Eng.Pend, +h: Spec.Head, -p: Eng.P, +c: U32, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, e: {Eng.step(p, c) == Eng.step.head.len(pd, n, out, z) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out), pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.head.body(z, n, h, out, Spec.snoc(since, c))):
  match z:
    case True{}:
      EMIT(pd, h, Nil{}, out, Eng.step(p, c), e, pr)
    case False{}:
      (pd, (pr, (e, bnd)))

# what the head's end decides, read off what each side holds: whether
# its Hosts fit its version, and how its body is framed
def pv.hostok(x: PV) -> Bool:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match fx:
        case Eng.Fx{v10, ka, te}:
          Eng.hosts.ok(v10, host)

def pv.bd(x: PV) -> Eng.Bd:
  match x:
    case PV{m, p, cl, close, host, u, fx}:
      match fx:
        case Eng.Fx{v10, ka, te}:
          Eng.body.kind(te, v10, cl)

def e.head(pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.head(pd, out) == Eng.step.head.at(pd, pv.hostok(pv(pd)), pv.bd(pv(pd)), out) : Eng.P}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx}:
      match fx:
        case Eng.Fx{a, b, c}:
          {==}

def bdv(b: Spec.Body) -> Eng.Bd:
  match b:
    case Spec.BNone{}:
      Eng.BdNone{}
    case Spec.BLen{n}:
      Eng.BdLen{n}
    case Spec.BChunked{}:
      Eng.BdChunked{}
    case Spec.BBad{}:
      Eng.BdBad{}

def hok(v10: Bool, hs: Nat) -> {Eng.hosts.ok(v10, hsat(hs)) == Spec.hosts.ok(v10, hs) : Bool}:
  match v10:
    case True{}:
      match hs:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              {==}
    case False{}:
      match hs:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              {==}

def bok(te: Bool, v10: Bool, l: Maybe<&2, U32>) ->
  {Eng.body.kind(te, v10, clv(l)) == bdv(Spec.body.of(te, v10, l)) : Eng.Bd}:
  match te v10 l:
    case True{} True{} None{}:
      {==}
    case True{} True{} Some{n}:
      {==}
    case True{} False{} None{}:
      {==}
    case True{} False{} Some{n}:
      {==}
    case False{} True{} None{}:
      {==}
    case False{} True{} Some{n}:
      {==}
    case False{} False{} None{}:
      {==}
    case False{} False{} Some{n}:
      {==}

def head.eq(+v10: Bool, +te: Bool, +hs: Nat, +l: Maybe<&2, U32>, -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.head.at(pd, Eng.hosts.ok(v10, hsat(hs)), Eng.body.kind(te, v10, clv(l)), out) ==
    Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out) : Eng.P}:
  %hok(v10, hs) :
    {Eng.step.head.at(pd, Eng.hosts.ok(v10, hsat(hs)), Eng.body.kind(te, v10, clv(l)), out) ==
      Eng.step.head.at(pd, _, bdv(Spec.body.of(te, v10, l)), out) : Eng.P}
  %bok(te, v10, l) :
    {Eng.step.head.at(pd, Eng.hosts.ok(v10, hsat(hs)), Eng.body.kind(te, v10, clv(l)), out) ==
      Eng.step.head.at(pd, Eng.hosts.ok(v10, hsat(hs)), _, out) : Eng.P}
  {==}

def HEAD.at(ok: Bool, b: Spec.Body, +pd: Eng.Pend, +h: Spec.Head, -p: Eng.P, +c: U32,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  e: {Eng.step(p, c) == Eng.step.head.at(pd, ok, bdv(b), out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out), pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.head.at(ok, b, h, out, Spec.snoc(since, c))):
  match ok b:
    case False{} x:
      (pd, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd, out}, out, e, {==}))
    case True{} Spec.BBad{}:
      (pd, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd, out}, out, e, {==}))
    case True{} Spec.BNone{}:
      EMIT(pd, h, Nil{}, out, Eng.step(p, c), e, pr)
    case True{} Spec.BLen{+n}:
      HEAD.z(U32.is_zero(n), n, pd, h, p, c, out, since, e, bnd, pr)
    case True{} Spec.BChunked{}:
      (pd, (pr, (e, bnd)))

def HEAD(+pd: Eng.Pend, h: Spec.Head, -p: Eng.P, +c: U32, +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  e: {Eng.step(p, c) == Eng.step.head(pd, out) : Eng.P}, bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out),
  pr: PR(pd, h)) -> SR(Eng.step(p, c), Spec.head.done(h, out, Spec.snoc(since, c))):
  match h:
    case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf}:
      match hf:
        case Eng.Fx{+v10, +ka, +te}:
          +pr2 = pr
          HEAD.at(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l), pd,
            Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}}, p, c, out, since,
            Equal.trans(Eng.P, Eng.step(p, c), Eng.step.head(pd, out),
              Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out), e,
              Equal.trans(Eng.P, Eng.step.head(pd, out), Eng.step.head.at(pd, pv.hostok(pv(pd)), pv.bd(pv(pd)), out),
                Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out),
                e.head(pd, out),
                Equal.trans(Eng.P, Eng.step.head.at(pd, pv.hostok(pv(pd)), pv.bd(pv(pd)), out),
                  Eng.step.head.at(pd, Eng.hosts.ok(v10, hsat(hs)), Eng.body.kind(te, v10, clv(l)), out),
                  Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out),
                  Equal.cong(PV, Eng.P, x => Eng.step.head.at(pd, pv.hostok(x), pv.bd(x), out), pv(pd),
                    hv(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}}), pr2),
                  head.eq(v10, te, hs, l, pd, out)))),
            bnd, pr2)

def STEP.eoh.k(+k: Eng.Cls, +c: U32, +h: Spec.Head, -p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, ek: {Spec.cls(c) == k : Eng.Cls}, pr: PR(pd, h),
  e1: {p == Eng.P{Eng.CrL{}, pd, out} : Eng.P}, bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.eoh.byte(k, h, out, Spec.snoc(since, c))):
  match k:
    case Eng.KLf{}:
      HEAD(pd, h, p, c, out, since, atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KLf{}, ek, e1),
        bnd.step(p, c, since, out, bnd), pr)
    case Eng.KSp{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KSp{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KSp{}, ek, e1), {==}))
    case Eng.KHt{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KHt{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KHt{}, ek, e1), {==}))
    case Eng.KCr{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KCr{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KCr{}, ek, e1), {==}))
    case Eng.KCo{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KCo{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KCo{}, ek, e1), {==}))
    case Eng.KCm{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KCm{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KCm{}, ek, e1), {==}))
    case Eng.KDg{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KDg{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KDg{}, ek, e1), {==}))
    case Eng.KTk{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KTk{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KTk{}, ek, e1), {==}))
    case Eng.KVc{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KVc{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KVc{}, ek, e1), {==}))
    case Eng.KCt{}:
      (pd, deadvia(Eng.step(p, c), SK(Eng.P{Eng.CrL{}, pd, out}, Eng.KCt{}, c), out,
        atk(p, Eng.P{Eng.CrL{}, pd, out}, c, Eng.KCt{}, ek, e1), {==}))

# a body byte, and a byte after an upgrade
def STEP.body(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, -p: Eng.P, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>, pr: PR(pd, h),
  e1: {p == Eng.P{Eng.Bod{more, Bytes.from_list(got)}, pd, out} : Eng.P}, bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.body.byte(more, c, h, got, out, Spec.snoc(since, c))):
  match more:
    case 0n:
      EMIT(pd, h, Spec.snoc(got, c), out, Eng.step(p, c),
        Equal.trans(Eng.P, Eng.step(p, c), Eng.emit(pd, Eng.push(Bytes.from_list(got), c), out),
          Eng.emit(pd, Bytes.from_list(Spec.snoc(got, c)), out),
          cstep(p, Eng.P{Eng.Bod{0n, Bytes.from_list(got)}, pd, out}, c, e1),
          Equal.cong(Bytes(), Eng.P, x => Eng.emit(pd, x, out), Eng.push(Bytes.from_list(got), c),
            Bytes.from_list(Spec.snoc(got, c)),
            Equal.sym(Bytes(), Bytes.from_list(Spec.snoc(got, c)), Eng.push(Bytes.from_list(got), c),
              fl.snoc(got, c)))),
        pr)
    case 1n+q:
      +e2 = e1
      (pd, (pr, (Equal.trans(Eng.P, Eng.step(p, c), Eng.P{Eng.Bod{q, Eng.push(Bytes.from_list(got), c)}, pd, out},
        Eng.P{Eng.Bod{q, Bytes.from_list(Spec.snoc(got, c))}, pd, out},
        cstep(p, Eng.P{Eng.Bod{1n+q, Bytes.from_list(got)}, pd, out}, c, e2),
        Equal.cong(Bytes(), Eng.P, x => Eng.P{Eng.Bod{q, x}, pd, out}, Eng.push(Bytes.from_list(got), c),
          Bytes.from_list(Spec.snoc(got, c)),
          Equal.sym(Bytes(), Bytes.from_list(Spec.snoc(got, c)), Eng.push(Bytes.from_list(got), c),
            fl.snoc(got, c)))),
        bnd.step(p, c, since, out, bnd))))

def STEP.up(+c: U32, +got: List<&2, U32>, -p: Eng.P, +out: List<&2, Eng.Req>,
  e1: {p == Eng.P{Eng.Rest{Bytes.from_list(got)}, Eng.pend.new(), out} : Eng.P}) ->
  {Eng.step(p, c) == Eng.P{Eng.Rest{Bytes.from_list(Spec.snoc(got, c))}, Eng.pend.new(), out} : Eng.P}:
  Equal.trans(Eng.P, Eng.step(p, c), Eng.P{Eng.Rest{Eng.push(Bytes.from_list(got), c)}, Eng.pend.new(), out},
    Eng.P{Eng.Rest{Bytes.from_list(Spec.snoc(got, c))}, Eng.pend.new(), out},
    cstep(p, Eng.P{Eng.Rest{Bytes.from_list(got)}, Eng.pend.new(), out}, c, e1),
    Equal.cong(Bytes(), Eng.P, x => Eng.P{Eng.Rest{x}, Eng.pend.new(), out}, Eng.push(Bytes.from_list(got), c),
      Bytes.from_list(Spec.snoc(got, c)),
      Equal.sym(Bytes(), Bytes.from_list(Spec.snoc(got, c)), Eng.push(Bytes.from_list(got), c), fl.snoc(got, c))))

# a byte of a chunked body's framing: the budget, the chunk line's end,
# the body's end
def CH.to(over: Bool, -p: Eng.P, +c: U32, +h: Spec.Head, +at2: Spec.At, +n: U32, +got: List<&2, U32>,
  +left: U32, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>, pr: PR(pd, h),
  e: {Eng.step(p, c) == Eng.chk.paid(over, at.eng(at2), n, Bytes.from_list(got), left, pd, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out)) ->
  SR(Eng.step(p, c), Spec.chunk.paid(over, h, at2, n, got, left, out, Spec.snoc(since, c))):
  match over:
    case True{}:
      (pd, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd, out}, out, e, {==}))
    case False{}:
      (pd, (pr, (e, bnd)))

def CH.line(z: Bool, -p: Eng.P, +c: U32, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>, pr: PR(pd, h),
  e: {Eng.step(p, c) == Eng.chk.line(z, n, Bytes.from_list(got), left, pd, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out)) ->
  SR(Eng.step(p, c), Spec.chunk.line(z, h, n, got, left, out, Spec.snoc(since, c))):
  match z:
    case True{}:
      (pd, (pr, (e, bnd)))
    case False{}:
      (pd, (pr, (e, bnd)))

def APPLY(g: Spec.Go, -p: Eng.P, +c: U32, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>, pr: PR(pd, h),
  e: {Eng.step(p, c) == Eng.step.chk(go.eng(g), n, Bytes.from_list(got), left, pd, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out)) ->
  SR(Eng.step(p, c), Spec.chunk.go(g, h, n, got, left, out, Spec.snoc(since, c))):
  match g:
    case Spec.GBad{}:
      (pd, deadvia(Eng.step(p, c), Eng.P{Eng.Bad{}, pd, out}, out, e, {==}))
    case Spec.GTo{+at2, paid}:
      match paid:
        case True{}:
          CH.to(U32.is_le(left, n), p, c, h, at2, n, got, left, pd, out, since, pr, e, bnd)
        case False{}:
          (pd, (pr, (e, bnd)))
    case Spec.GDigit{+d}:
      CH.to(U32.is_le(left, (n * 16 + d : U32)), p, c, h, Spec.ASize{}, (n * 16 + d : U32), got, left, pd, out,
        since, pr, e, bnd)
    case Spec.GLine{}:
      CH.line(U32.is_zero(n), p, c, h, n, got, left, pd, out, since, pr, e, bnd)
    case Spec.GDone{}:
      EMIT(pd, h, got, out, Eng.step(p, c), e, pr)

def STEP.chunk(+at: Spec.At, +c: U32, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32, -p: Eng.P,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>, pr: PR(pd, h),
  e1: {p == Eng.P{Eng.Chk{at.eng(at), n, Bytes.from_list(got), left}, pd, out} : Eng.P},
  bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.chunk.go(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c)), h, n, got, left, out,
    Spec.snoc(since, c))):
  APPLY(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c)), p, c, h, n, got, left, pd, out, since, pr,
    Equal.trans(Eng.P, Eng.step(p, c),
      Eng.step.chk(Eng.chk.next(at.eng(at), Eng.xk.of(Eng.cls(c), c)), n, Bytes.from_list(got), left, pd, out),
      Eng.step.chk(go.eng(Spec.chunk.step(at, Spec.xk.of(Spec.cls(c), c))), n, Bytes.from_list(got), left, pd, out),
      cstep(p, Eng.P{Eng.Chk{at.eng(at), n, Bytes.from_list(got), left}, pd, out}, c, e1),
      chk.eq(at, c, n, Bytes.from_list(got), left, pd, out)),
    bnd.step(p, c, since, out, bnd))

# a byte of a chunk's data
def STEP.data(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, +left: U32, -p: Eng.P, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>, pr: PR(pd, h),
  e1: {p == Eng.P{Eng.Chd{more, Bytes.from_list(got), left}, pd, out} : Eng.P}, bnd: BND(p, since, out)) ->
  SR(Eng.step(p, c), Spec.data.byte(more, c, h, got, left, out, Spec.snoc(since, c))):
  match more:
    case 0n:
      (pd, (pr, (Equal.trans(Eng.P, Eng.step(p, c),
        Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Eng.push(Bytes.from_list(got), c), left}, pd, out},
        Eng.P{Eng.Chk{Eng.CDataCr{}, 0, Bytes.from_list(Spec.snoc(got, c)), left}, pd, out},
        cstep(p, Eng.P{Eng.Chd{0n, Bytes.from_list(got), left}, pd, out}, c, e1),
        Equal.cong(Bytes(), Eng.P, x => Eng.P{Eng.Chk{Eng.CDataCr{}, 0, x, left}, pd, out},
          Eng.push(Bytes.from_list(got), c), Bytes.from_list(Spec.snoc(got, c)),
          Equal.sym(Bytes(), Bytes.from_list(Spec.snoc(got, c)), Eng.push(Bytes.from_list(got), c),
            fl.snoc(got, c)))),
        bnd.step(p, c, since, out, bnd))))
    case 1n+q:
      (pd, (pr, (Equal.trans(Eng.P, Eng.step(p, c),
        Eng.P{Eng.Chd{q, Eng.push(Bytes.from_list(got), c), left}, pd, out},
        Eng.P{Eng.Chd{q, Bytes.from_list(Spec.snoc(got, c)), left}, pd, out},
        cstep(p, Eng.P{Eng.Chd{1n+q, Bytes.from_list(got), left}, pd, out}, c, e1),
        Equal.cong(Bytes(), Eng.P, x => Eng.P{Eng.Chd{q, x, left}, pd, out},
          Eng.push(Bytes.from_list(got), c), Bytes.from_list(Spec.snoc(got, c)),
          Equal.sym(Bytes(), Bytes.from_list(Spec.snoc(got, c)), Eng.push(Bytes.from_list(got), c),
            fl.snoc(got, c)))),
        bnd.step(p, c, since, out, bnd))))

# LEMMA: one byte moves the reader and the spec's walk together
def STEP.m(mode: Spec.Mode, +c: U32, +p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  r: REL.m(p, mode, out, since, pd)) ->
  SR(Eng.step(p, c), Spec.next.at(mode, Spec.cls(c), c, out, Spec.snoc(since, c))):
  match mode:
    case Spec.MReq{+cur}:
      (e1, r2) = r
      (pl, bnd) = r2
      STEP.req.k(Spec.cls(c), c, cur, p, pd, out, since, {==}, e1, pl, bnd)
    case Spec.MBlank{}:
      (e1, bnd) = r
      STEP.blank.k(Spec.cls(c), c, p, pd, out, since, {==}, e1, bnd)
    case Spec.MField{+h, +cur}:
      (pr, r2) = r
      (e1, r3) = r2
      (pl, bnd) = r3
      STEP.field.k(Spec.cls(c), c, h, cur, p, pd, out, since, {==}, pr, e1, pl, bnd)
    case Spec.MEol{+h}:
      (pr, r2) = r
      (e1, bnd) = r2
      STEP.eol.k(Spec.cls(c), c, h, p, pd, out, since, {==}, pr, e1, bnd)
    case Spec.MEoh{+h}:
      (pr, r2) = r
      (e1, bnd) = r2
      STEP.eoh.k(Spec.cls(c), c, h, p, pd, out, since, {==}, pr, e1, bnd)
    case Spec.MBody{+h, more, +got}:
      (pr, r2) = r
      (e1, bnd) = r2
      STEP.body(more, c, h, got, p, pd, out, since, pr, e1, bnd)
    case Spec.MChunk{+h, +at, +n, +got, +left}:
      (pr, r2) = r
      (e1, bnd) = r2
      STEP.chunk(at, c, h, n, got, left, p, pd, out, since, pr, e1, bnd)
    case Spec.MData{+h, more, +got, +left}:
      (pr, r2) = r
      (e1, bnd) = r2
      STEP.data(more, c, h, got, left, p, pd, out, since, pr, e1, bnd)
    case Spec.MUp{+got}:
      (pd, STEP.up(c, got, p, out, r))
    case Spec.MBad{}:
      (pd, dead.byte(p, c, out)(r))

def STEP(w: Spec.W, +c: U32, +p: Eng.P, +pd: Eng.Pend, r: REL(p, w, pd)) ->
  SR(Eng.step(p, c), Spec.next(w, c)):
  match w:
    case Spec.W{mode, +out, +since}:
      STEP.m(mode, c, p, pd, out, since, r)

# The end
# -------

def rr(xs: List<&2, Eng.Req>, -acc: List<&2, Eng.Req>) ->
  {List.reverse.go(&2, Eng.Req, List.reverse.go(&2, Eng.Req, xs, acc), Nil{}) ==
    List.reverse.go(&2, Eng.Req, acc, xs) : List<&2, Eng.Req>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rr(t, Con{h, acc})

def rev.rev(xs: List<&2, Eng.Req>) ->
  {xs == List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, xs)) : List<&2, Eng.Req>}:
  Equal.sym(List<&2, Eng.Req>, List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, xs)), xs, rr(xs, Nil{}))

def look.kill(p: Eng.P) -> {Laws.look(p) == Laws.look(kill(p)) : List<&2, Eng.Req> & Laws.Look}:
  match p:
    case Eng.P{st, pd, out}:
      {==}

def REFUSED(+p: Eng.P, +out: List<&2, Eng.Req>, d: Dead(p, out)) ->
  Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.Refused{}):
  Equal.trans(List<&2, Eng.Req> & Laws.Look, Laws.look(p), Laws.look(kill(p)), Laws.look(Eng.P{Eng.Bad{}, Eng.pend.new(), out}),
    look.kill(p), Equal.cong(Eng.P, List<&2, Eng.Req> & Laws.Look, x => Laws.look(x), kill(p),
      Eng.P{Eng.Bad{}, Eng.pend.new(), out}, d))

def rev.open(-p: Eng.P, +out: List<&2, Eng.Req>, -since: List<&2, U32>, bnd: BND(p, since, out)) ->
  {p == Eng.feed(since, Eng.P{Eng.Pre{}, Eng.pend.new(),
    List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, out))}) : Eng.P}:
  %rev.rev(out) : {p == Eng.feed(since, Eng.P{Eng.Pre{}, Eng.pend.new(), _}) : Eng.P}
  bnd

def OPEN(-p: Eng.P, -x: Eng.P, +out: List<&2, Eng.Req>, +since: List<&2, U32>, e: {p == x : Eng.P},
  lk: {Laws.look(x) == (List.reverse(&2, Eng.Req, out), Laws.Reading{}) : List<&2, Eng.Req> & Laws.Look},
  bnd: BND(p, since, out)) -> Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.Open{since}):
  (Equal.trans(List<&2, Eng.Req> & Laws.Look, Laws.look(p), Laws.look(x), (List.reverse(&2, Eng.Req, out), Laws.Reading{}),
    Equal.cong(Eng.P, List<&2, Eng.Req> & Laws.Look, y => Laws.look(y), p, x, e), lk),
   rev.open(p, out, since, bnd))

def END.req(v: Spec.RLine, +q: Eng.P, +p: Eng.P, +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  lr: LR.req(q, v, out), e1: {p == q : Eng.P}, bnd: BND(p, since, out)) ->
  Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.req.end(v, since)):
  match v:
    case Spec.RNone{}:
      OPEN(p, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, e1, lr), {==}, bnd)
    case Spec.RMeth{m}:
      OPEN(p, Eng.P{Eng.InM{Bytes.from_list(m)}, Eng.pend.new(), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InM{Bytes.from_list(m)}, Eng.pend.new(), out}, e1, lr), {==}, bnd)
    case Spec.RTarget{m, t}:
      OPEN(p, Eng.P{Eng.InT{Bytes.from_list(t)}, pd1(m), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InT{Bytes.from_list(t)}, pd1(m), out}, e1, lr), {==}, bnd)
    case Spec.RVer{m, t, v}:
      OPEN(p, Eng.P{Eng.InV{Bytes.from_list(v)}, pd2(m, t), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InV{Bytes.from_list(v)}, pd2(m, t), out}, e1, lr), {==}, bnd)
    case Spec.RBad{}:
      REFUSED(p, out, deadvia(p, q, out, e1, lr))

def END.len(ws: Bool, +n: U32, +q: Eng.P, +p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, lr: LR.len(q, n, ws, pd, out), e1: {p == q : Eng.P}, bnd: BND(p, since, out)) ->
  Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.Open{since}):
  match ws:
    case True{}:
      OPEN(p, Eng.P{Eng.InLt{n}, pd, out}, out, since, Equal.trans(Eng.P, p, q, Eng.P{Eng.InLt{n}, pd, out}, e1, lr),
        {==}, bnd)
    case False{}:
      OPEN(p, Eng.P{Eng.InL{n}, pd, out}, out, since, Equal.trans(Eng.P, p, q, Eng.P{Eng.InL{n}, pd, out}, e1, lr),
        {==}, bnd)

def END.val(val: Spec.Val, +q: Eng.P, +p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, lr: LR.val(q, val, pd, out), e1: {p == q : Eng.P}, bnd: BND(p, since, out)) ->
  Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.Open{since}):
  match val:
    case Spec.VLen0{}:
      OPEN(p, Eng.P{Eng.InL0{}, pd, out}, out, since, Equal.trans(Eng.P, p, q, Eng.P{Eng.InL0{}, pd, out}, e1, lr),
        {==}, bnd)
    case Spec.VLen{n, ws}:
      END.len(ws, n, q, p, pd, out, since, lr, e1, bnd)
    case Spec.VConn{d, cur}:
      OPEN(p, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", d), Spec.named("upgrade", d),
        Spec.named("keep-alive", d)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", d), Spec.named("upgrade", d),
          Spec.named("keep-alive", d)}, pd, out}, e1, lr), {==}, bnd)
    case Spec.VUp{d, cur}:
      OPEN(p, Eng.P{Eng.InLu{lowb(cur), Spec.named("websocket", d)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLu{lowb(cur), Spec.named("websocket", d)}, pd, out}, e1, lr), {==}, bnd)
    case Spec.VKey0{}:
      OPEN(p, Eng.P{Eng.InLk0{}, pd, out}, out, since, Equal.trans(Eng.P, p, q, Eng.P{Eng.InLk0{}, pd, out}, e1, lr),
        {==}, bnd)
    case Spec.VKey{k}:
      OPEN(p, Eng.P{Eng.InLk{Bytes.from_list(k)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLk{Bytes.from_list(k)}, pd, out}, e1, lr), {==}, bnd)
    case Spec.VVer{v}:
      OPEN(p, Eng.P{Eng.InLv{Bytes.from_list(v)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLv{Bytes.from_list(v)}, pd, out}, e1, lr), {==}, bnd)
    case Spec.VTe0{}:
      OPEN(p, Eng.P{Eng.InLe0{}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLe0{}, pd, out}, e1, lr), {==}, bnd)
    case Spec.VTe{t}:
      OPEN(p, Eng.P{Eng.InLe{Bytes.from_list(t)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLe{Bytes.from_list(t)}, pd, out}, e1, lr), {==}, bnd)
    case Spec.VHost{}:
      OPEN(p, Eng.P{Eng.InLx{}, Eng.pend.host(pd), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLx{}, Eng.pend.host(pd), out}, e1, lr), {==}, bnd)
    case Spec.VSkip{}:
      OPEN(p, Eng.P{Eng.InLx{}, pd, out}, out, since, Equal.trans(Eng.P, p, q, Eng.P{Eng.InLx{}, pd, out}, e1, lr),
        {==}, bnd)

def END.field(v: Spec.FLine, +q: Eng.P, +p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, lr: LR.field(q, v, pd, out), e1: {p == q : Eng.P}, bnd: BND(p, since, out)) ->
  Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.field.end(v, since)):
  match v:
    case Spec.FEmpty{}:
      OPEN(p, Eng.P{Eng.Lin{}, pd, out}, out, since, Equal.trans(Eng.P, p, q, Eng.P{Eng.Lin{}, pd, out}, e1, lr),
        {==}, bnd)
    case Spec.FName{n}:
      OPEN(p, Eng.P{Eng.InN{Bytes.from_list(n)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InN{Bytes.from_list(n)}, pd, out}, e1, lr), {==}, bnd)
    case Spec.FVal{val}:
      END.val(val, q, p, pd, out, since, lr, e1, bnd)
    case Spec.FBad{}:
      REFUSED(p, out, deadvia(p, q, out, e1, lr))

# LEMMA: wherever the walk ends, the reader agrees with the framing
def END.m(mode: Spec.Mode, +p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  r: REL.m(p, mode, out, since, pd)) ->
  Laws.agree.end(p, List.reverse(&2, Eng.Req, out), Spec.finish.end(mode, since)):
  match mode:
    case Spec.MReq{+cur}:
      (e1, r2) = r
      (pl, bnd) = r2
      END.req(Spec.req.view(cur), Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), p, out, since,
        line.req(cur, out)(pl), e1, bnd)
    case Spec.MBlank{}:
      (e1, bnd) = r
      OPEN(p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, out, since, e1, {==}, bnd)
    case Spec.MField{h, +cur}:
      (pr, r2) = r
      (e1, r3) = r2
      (pl, bnd) = r3
      END.field(Spec.field.view(cur), Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), p, pd, out, since,
        line.field(cur, pd, out)(pl), e1, bnd)
    case Spec.MEol{h}:
      (pr, r2) = r
      (e1, bnd) = r2
      OPEN(p, Eng.P{Eng.CrM{}, pd, out}, out, since, e1, {==}, bnd)
    case Spec.MEoh{h}:
      (pr, r2) = r
      (e1, bnd) = r2
      OPEN(p, Eng.P{Eng.CrL{}, pd, out}, out, since, e1, {==}, bnd)
    case Spec.MBody{h, more, got}:
      (pr, r2) = r
      (e1, bnd) = r2
      OPEN(p, Eng.P{Eng.Bod{more, Bytes.from_list(got)}, pd, out}, out, since, e1, {==}, bnd)
    case Spec.MChunk{h, at, n, got, left}:
      (pr, r2) = r
      (e1, bnd) = r2
      OPEN(p, Eng.P{Eng.Chk{at.eng(at), n, Bytes.from_list(got), left}, pd, out}, out, since, e1, {==}, bnd)
    case Spec.MData{h, more, got, left}:
      (pr, r2) = r
      (e1, bnd) = r2
      OPEN(p, Eng.P{Eng.Chd{more, Bytes.from_list(got), left}, pd, out}, out, since, e1, {==}, bnd)
    case Spec.MUp{got}:
      %rev.rev(out) : {p == Eng.P{Eng.Rest{Bytes.from_list(got)}, Eng.pend.new(), _} : Eng.P}
      r
    case Spec.MBad{}:
      REFUSED(p, out, r)

def END(w: Spec.W, +p: Eng.P, +pd: Eng.Pend, r: REL(p, w, pd)) -> Laws.agree(p, Spec.finish(w)):
  match w:
    case Spec.W{mode, +out, +since}:
      END.m(mode, p, pd, out, since, r)

# the walk: induction on the input, one byte at a time
def walk.lem(bs: List<&2, U32>, +w: Spec.W, +p: Eng.P, s: SR(p, w)) ->
  Laws.agree(Eng.feed(bs, p), Spec.finish(Spec.walk(bs, w))):
  match bs:
    case Nil{}:
      (pd, r) = s
      END(w, p, pd, r)
    case Con{+c, t}:
      (pd, r) = s
      walk.lem(t, Spec.next(w, c), Eng.step(p, c), STEP(w, c, p, pd, r))

# THEOREM: for every input, the reader agrees with the framing
def frame.sim(bs: List<&2, U32>) -> Laws.agree(Eng.feed(bs, Eng.p.new()), Spec.frame(bs)):
  walk.lem(bs, Spec.W{Spec.MReq{Nil{}}, Nil{}, Nil{}}, Eng.p.new(), (Eng.pend.new(), ({==}, (Unit{}, {==}))))

# The laws, whole
# ---------------

def Laws.frame_sim(bs):
  frame.sim(bs)

def Laws.frame_sim_buf(b):
  %Equal.sym(Eng.P, Eng.feed_buf(b, Eng.p.new()), Eng.feed(Bytes.to_list(b), Eng.p.new()),
    Laws.feed_buf_is_feed(b, Eng.p.new())) : Laws.agree(_, Spec.frame(Bytes.to_list(b)))
  frame.sim(Bytes.to_list(b))

# reads fed one after another are their bytes fed at once
def reads.is(rs: List<&2, Bytes()>, +p: Eng.P) ->
  {Laws.reads(rs, p) == Eng.feed(Bytes.to_list(Bytes.concat(rs)), p) : Eng.P}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      Equal.trans(Eng.P, Laws.reads(t, Eng.feed_buf(r, p)),
        Eng.feed(Bytes.to_list(Bytes.concat(t)), Eng.feed_buf(r, p)),
        Eng.feed(Bytes.to_list(Bytes.append(r, Bytes.concat(t))), p),
        reads.is(t, Eng.feed_buf(r, p)),
        Equal.trans(Eng.P, Eng.feed(Bytes.to_list(Bytes.concat(t)), Eng.feed_buf(r, p)),
          Eng.feed(Bytes.to_list(Bytes.concat(t)), Eng.feed(Bytes.to_list(r), p)),
          Eng.feed(Bytes.to_list(Bytes.append(r, Bytes.concat(t))), p),
          Equal.cong(Eng.P, Eng.P, x => Eng.feed(Bytes.to_list(Bytes.concat(t)), x), Eng.feed_buf(r, p),
            Eng.feed(Bytes.to_list(r), p), Laws.feed_buf_is_feed(r, p)),
          Equal.trans(Eng.P, Eng.feed(Bytes.to_list(Bytes.concat(t)), Eng.feed(Bytes.to_list(r), p)),
            Eng.feed(List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), p),
            Eng.feed(Bytes.to_list(Bytes.append(r, Bytes.concat(t))), p),
            Equal.sym(Eng.P, Eng.feed(List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), p),
              Eng.feed(Bytes.to_list(Bytes.concat(t)), Eng.feed(Bytes.to_list(r), p)),
              Laws.feed_split(Bytes.to_list(r), Bytes.to_list(Bytes.concat(t)), p)),
            Equal.cong(List<&2, U32>, Eng.P, x => Eng.feed(x, p),
              List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
              Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
              Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
                List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
                Bytes.to_list_append(r, Bytes.concat(t)))))))

def Laws.frame_sim_reads(rs):
  %Equal.sym(Eng.P, Laws.reads(rs, Eng.p.new()), Eng.feed(Bytes.to_list(Bytes.concat(rs)), Eng.p.new()),
    reads.is(rs, Eng.p.new())) : Laws.agree(_, Spec.frame(Bytes.to_list(Bytes.concat(rs))))
  frame.sim(Bytes.to_list(Bytes.concat(rs)))

def Laws.chunk_size_capped(c, d, n, b, left, pd, out, e, f):
  %xkc(c) : {Eng.step.chk(Eng.chk.next(Eng.CSize{}, _), n, b, left, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Eng.XK, Spec.xk.of(Spec.cls(c), c), Eng.XHex{d}, e) :
    {Eng.step.chk(Eng.chk.next(Eng.CSize{}, _), n, b, left, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Bool, U32.is_le(left, (n * 16 + d : U32)), True{}, f) :
    {Eng.chk.paid(_, Eng.CSize{}, (n * 16 + d : U32), b, left, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  {==}

def Laws.chunk_ext_capped(c, pos, to, n, b, left, pd, out, e, f):
  %xkc(c) : {Eng.step.chk(Eng.chk.next(pos, _), n, b, left, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Eng.Mv, Eng.chk.next(pos, Spec.xk.of(Spec.cls(c), c)), Eng.MvTo{to, True{}}, e) :
    {Eng.step.chk(_, n, b, left, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Bool, U32.is_le(left, n), True{}, f) :
    {Eng.chk.paid(_, to, n, b, left, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  {==}

def Laws.frame_get():
  {==}

def Laws.frame_upgrade():
  {==}

def Laws.frame_refuse_fold():
  {==}

def Laws.refuse_te_cl():
  {==}

def Laws.refuse_te_space():
  {==}

def Laws.refuse_te_xchunked():
  {==}

def Laws.refuse_te_list():
  {==}

def Laws.refuse_te_te():
  {==}

def Laws.refuse_te_twice():
  {==}

def Laws.refuse_te_10():
  {==}

def Laws.refuse_chunk_bare_lf():
  {==}

def Laws.refuse_chunk_data_lf():
  {==}

def Laws.refuse_chunk_long():
  {==}

def Laws.refuse_chunk_ws():
  {==}

def Laws.refuse_chunk_no_size():
  {==}

def Laws.refuse_chunk_past_cap():
  {==}

def Laws.refuse_chunk_wrap():
  {==}

def Laws.refuse_chunk_ext():
  {==}

def Laws.refuse_trailer_fold():
  {==}

def Laws.refuse_10_two_hosts():
  {==}

def Laws.parse_10():
  {==}

def Laws.parse_10_keepalive():
  {==}

def Laws.parse_10_upgrade():
  {==}

def Laws.parse_chunked():
  {==}

def Laws.parse_chunked_ext():
  {==}

def Laws.chunk_cuts():
  {==}

def Laws.chunk_bytes():
  {==}

def Laws.frame_chunked():
  {==}

def Laws.frame_10():
  {==}
