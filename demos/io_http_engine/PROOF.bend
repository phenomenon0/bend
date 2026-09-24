# The proofs of the HTTP engine laws.
#
# feed_split and bad_feeds, and the block walk's laws, are the reader
# kit's (wire/reader.bend), proven once there for every reader and
# instantiated here at Eng.step; the engine proves the kit's two
# obligations, that a refused reader is a fixed point of the step
# (bad_absorbs) and that every move of its block walk lands where
# stepping its bytes does (lem.adv). bad_absorbs and the five reply laws compute: the
# machine's last row sends Bad{} to Bad{} whatever the byte class is,
# and each written-out reply normalises to the same string the builder
# does.
import Base
import ../../wire/reader.bend as Wr
import ../../wire/loop.bend as L
import ../../wire/world.bend as WW
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./ws.bend as Ws
import ./spec.bend as Spec
import ./world.bend as W
import ./cond.bend as C
import ./LAWS.bend as Laws

def Laws.feed_split(a, b, p):
  Wr.feed_split(~Unit, ~Eng.P, ~Eng.wstep, Unit{}, a, b, p)

def Laws.bad_absorbs(c, pd, out):
  {==}

# a refused reader, as the kit's absorbing states, and the obligation
type BadAt is Data:
  BadAt{pd: Eng.Pend, out: List<&2, Eng.Req>}

def bad(x: BadAt) -> Eng.P:
  match x:
    case BadAt{pd, out}:
      Eng.P{Eng.Bad{}, pd, out}

def absorbs(+u: Unit, +x: BadAt, +c: U32) -> {Eng.wstep(u, bad(x), c) == bad(x) : Eng.P}:
  match x:
    case BadAt{pd, out}:
      Laws.bad_absorbs(c, pd, out)

def Laws.bad_feeds(s, pd, out):
  Wr.bad_feeds(~Unit, ~Eng.P, ~Eng.wstep, ~BadAt, ~bad, ~absorbs, Unit{}, s, BadAt{pd, out})

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
  Wr.slow_is_feed(~Unit, ~Eng.P, ~Eng.wstep, Unit{}, s, p)

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

# A value's run (RX): every byte in [32, 127) is one a value passed on
# carries, so its run starts with a span of them
def lem.rx.sym(co: Bool, cm: Bool, tk: Bool) ->
  {Eng.run.stay(Eng.RX{}, Eng.cls.sym(co, cm, tk)) == True{} : Bool}:
  match co cm tk:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def lem.rx.vis(+c: U32, al: Bool, dg: Bool) ->
  {Eng.run.stay(Eng.RX{}, Eng.cls.vis(c, al, dg)) == True{} : Bool}:
  match al dg:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      lem.rx.sym(U32.is_eq(c, 58), U32.is_eq(c, 44), Eng.tsym(c))

def lem.rx.go(+c: U32, x: Bool, y: Bool) ->
  {Bool.and(Bool.not(x), Bool.not(y)) == True{} : Bool} ->
  {Eng.run.stay(Eng.RX{}, Eng.cls.go(c, x, y)) == True{} : Bool}:
  match x y:
    case True{} True{}:
      e =>
        %e : BT(_, {Eng.run.stay(Eng.RX{}, Eng.cls.go(c, True{}, True{})) == True{} : Bool})
        Unit{}
    case True{} False{}:
      e =>
        %e : BT(_, {Eng.run.stay(Eng.RX{}, Eng.cls.go(c, True{}, False{})) == True{} : Bool})
        Unit{}
    case False{} True{}:
      e =>
        %e : BT(_, {Eng.run.stay(Eng.RX{}, Eng.cls.go(c, False{}, True{})) == True{} : Bool})
        Unit{}
    case False{} False{}:
      e => lem.rx.vis(c, Eng.alpha(c), Eng.digit(c))

# a space, whatever else the byte is tested for below 33
def lem.rx.sp(ht: Bool, cr: Bool, lf: Bool) ->
  {Eng.run.stay(Eng.RX{}, Eng.cls.low(True{}, ht, cr, lf)) == True{} : Bool}:
  match ht cr lf:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# a byte in [32, 127) is one a value passed on carries: past 32 it is
# the visible ASCII above, and below 33 it is 32, the space (lo <= c <
# lo + 1 is c == lo, base's U32.eq_of_lt_succ)
def lem.rx.in.at(+c: U32, x: Bool, +e: {Bytes.span.in(c, 32, 127) == True{} : Bool}) ->
  {U32.is_lt(c, 33) == x : Bool} ->
  {Eng.run.stay(Eng.RX{}, Eng.cls.go(c, x, U32.is_le(127, c))) == True{} : Bool}:
  match x:
    case True{}:
      xe =>
        %Equal.sym(Bool, U32.is_eq(c, 32), True{},
          U32.eq_of_lt_succ(c, 32, 33,
            Bool.and_l(Bool.not(U32.is_lt(c, 32)), Bool.not(U32.is_le(127, c)), e), xe, {==})) :
          {Eng.run.stay(Eng.RX{}, Eng.cls.low(_, U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))) ==
            True{} : Bool}
        lem.rx.sp(U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))
    case False{}:
      xe => lem.rx.go(c, False{}, U32.is_le(127, c))(
        Bool.and_r(Bool.not(U32.is_lt(c, 32)), Bool.not(U32.is_le(127, c)), e))

def lem.rx.in(+c: U32) ->
  {Bytes.span.in(c, 32, 127) == True{} : Bool} ->
  {Eng.run.stay(Eng.RX{}, Eng.cls(c)) == True{} : Bool}:
  +e => lem.rx.in.at(c, U32.is_lt(c, 33), e)({==})

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

# A run counted by spans of [lo, hi): when every byte in the range is one
# the run stays on, the run is the span, then the run from past it
def VRg(-sel: Eng.Run, -lo: U32, -hi: U32, -s: Bytes()) -> Type:
  {Eng.run.len(s, True{}, sel, 0n) ==
    Nat.add(Bytes.span.go(s, lo, hi),
      Eng.run.len(String.drop(s, Bytes.span.go(s, lo, hi)), True{}, sel, 0n)) : Nat}

def lem.span.at(+sel: Eng.Run, +lo: U32, +hi: U32, +c: U32, +t: Bytes(), b: Bool,
  inok: {Bytes.span.in(c, lo, hi) == True{} : Bool} -> {Eng.run.stay(sel, Eng.cls(c)) == True{} : Bool},
  ih: VRg(sel, lo, hi, t)) ->
  {Bytes.span.in(c, lo, hi) == b : Bool} ->
  {Eng.run.len(SCon{Chr{c}, t}, True{}, sel, 0n) ==
    Nat.add(Bytes.span.at(b, t, lo, hi),
      Eng.run.len(String.drop(SCon{Chr{c}, t}, Bytes.span.at(b, t, lo, hi)), True{}, sel, 0n)) : Nat}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        %Equal.sym(Bool, Eng.run.stay(sel, Eng.cls(c)), True{}, inok(e)) :
          {Eng.run.len(t, _, sel, Eng.run.inc(_, 0n)) ==
            1n+Nat.add(Bytes.span.go(t, lo, hi),
              Eng.run.len(String.drop(t, Bytes.span.go(t, lo, hi)), True{}, sel, 0n)) : Nat}
        Equal.trans(Nat, Eng.run.len(t, True{}, sel, 1n),
          1n+Eng.run.len(t, True{}, sel, 0n),
          1n+Nat.add(Bytes.span.go(t, lo, hi),
            Eng.run.len(String.drop(t, Bytes.span.go(t, lo, hi)), True{}, sel, 0n)),
          lem.shift(t, True{}, sel, 0n),
          Equal.cong(Nat, Nat, y => 1n+y, Eng.run.len(t, True{}, sel, 0n),
            Nat.add(Bytes.span.go(t, lo, hi),
              Eng.run.len(String.drop(t, Bytes.span.go(t, lo, hi)), True{}, sel, 0n)), ih))

# A name's lowercase letters: a byte in [97, 123) is a letter (base's
# span-range lemmas: inside [33, 127), and 97 <= c <= 122), so a token
def lem.nm.tk(+c: U32, dg: Bool) ->
  {Eng.run.stay(Eng.RN{}, Eng.cls.vis(c, True{}, dg)) == True{} : Bool}:
  match dg:
    case True{}:
      {==}
    case False{}:
      {==}

def lem.nm.alpha(+c: U32, +e: {Bytes.span.in(c, 97, 123) == True{} : Bool}) ->
  {Eng.alpha(c) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le(97, c), True{}, Bytes.span.in_lo(c, 97, 123, e)) :
    {Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(_, U32.is_le(c, 122))) ==
      True{} : Bool}
  %Equal.sym(Bool, U32.is_le(c, 122), True{},
    Equal.trans(Bool, U32.is_le(c, 122), U32.is_lt(c, 123), True{},
      Equal.sym(Bool, U32.is_lt(c, 123), U32.is_le(c, 122), U32.lt_succ(c, 122, 123, {==})),
      Bytes.span.in_hi(c, 97, 123, e))) :
    {Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(True{}, _)) == True{} : Bool}
  Bool.or_true(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)))

def lem.nm.in(+c: U32) ->
  {Bytes.span.in(c, 97, 123) == True{} : Bool} ->
  {Eng.run.stay(Eng.RN{}, Eng.cls(c)) == True{} : Bool}:
  +e =>
    +w = Bytes.span.in_widen(c, 97, 123, 33, 127, e, {==}, {==})
    %Equal.sym(Bool, U32.is_lt(c, 33), False{},
      Bool.not_true(U32.is_lt(c, 33), Bool.and_l(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
      {Eng.run.stay(Eng.RN{}, Eng.cls.go(c, _, U32.is_le(127, c))) == True{} : Bool}
    %Equal.sym(Bool, U32.is_le(127, c), False{},
      Bool.not_true(U32.is_le(127, c), Bool.and_r(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
      {Eng.run.stay(Eng.RN{}, Eng.cls.go(c, False{}, _)) == True{} : Bool}
    %Equal.sym(Bool, Eng.alpha(c), True{}, lem.nm.alpha(c, e)) :
      {Eng.run.stay(Eng.RN{}, Eng.cls.vis(c, _, Eng.digit(c))) == True{} : Bool}
    lem.nm.tk(c, Eng.digit(c))

# a name's run is its first span of lowercase letters, then the rest
def lem.nm.span(+s: Bytes()) -> VRg(Eng.RN{}, 97, 123, s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      lem.span.at(Eng.RN{}, 97, 123, c, t, Bytes.span.in(c, 97, 123), lem.nm.in(c),
        lem.nm.span(t))({==})

# a value's run is its first span of the space and visible ASCII, then
# the rest
def lem.rx.span(+s: Bytes()) -> VRg(Eng.RX{}, 32, 127, s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      lem.span.at(Eng.RX{}, 32, 127, c, t, Bytes.span.in(c, 32, 127), lem.rx.in(c),
        lem.rx.span(t))({==})

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
    case SNil{} Eng.RX{}:
      {==}
    case SCon{h, t} Eng.RX{}:
      lem.rx.span(SCon{h, t})

def lem.go.run(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.run.go(sel, acc, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  lem.cut(sel, acc, s, pd, out, Eng.run.fast(s, sel))(lem.fast(s, sel))

# Positions in a read: the byte at i is the first of the read from i;
# dropping i + 1 is dropping i, then one; dropping twice is dropping the sum
def hd(u: Bytes()) -> U32:
  match u:
    case SNil{}:
      256
    case SCon{Chr{c}, t}:
      c

def get_hd(+s: Bytes(), +i: Nat) -> {Bytes.get(s, i) == hd(String.drop(s, i)) : U32}:
  match s i:
    case SNil{} _:
      {==}
    case SCon{Chr{c}, t} 0n:
      {==}
    case SCon{Chr{c}, t} 1n+p:
      get_hd(t, p)

def drop_one(+s: Bytes(), +i: Nat) -> {String.drop(s, 1n+i) == String.drop(String.drop(s, i), 1n) : Bytes()}:
  match s i:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      drop_one(t, p)

def drop_add(+s: Bytes(), +a: Nat, +b: Nat) ->
  {String.drop(String.drop(s, a), b) == String.drop(s, Nat.add(a, b)) : Bytes()}:
  match s a:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      drop_add(t, p, b)

# the name's count from i, once the byte at i is known
def lem.nm.more(j: Nat, +s: Bytes(), +i: Nat, +w: Bytes(),
  eD1: {String.drop(s, 1n+i) == w : Bytes()},
  ih: @+i2: Nat -> {Eng.nm.go(j, s, i2, Eng.nm.ok(s, i2)) ==
    Eng.run.len(String.drop(s, i2), True{}, Eng.RN{}, 0n) : Nat}) ->
  {1n+Nat.add(Bytes.span(s, 1n+i, 97, 123),
    Eng.nm.go(j, s, Nat.add(1n+i, Bytes.span(s, 1n+i, 97, 123)),
      Eng.nm.ok(s, Nat.add(1n+i, Bytes.span(s, 1n+i, 97, 123))))) ==
    Eng.run.len(w, True{}, Eng.RN{}, 1n) : Nat}:
  +D1 = String.drop(s, 1n+i)
  +N = Bytes.span.go(D1, 97, 123)
  Equal.trans(Nat,
    1n+Nat.add(N, Eng.nm.go(j, s, Nat.add(1n+i, N), Eng.nm.ok(s, Nat.add(1n+i, N)))),
    1n+Nat.add(N, Eng.run.len(String.drop(D1, N), True{}, Eng.RN{}, 0n)),
    Eng.run.len(w, True{}, Eng.RN{}, 1n),
    Equal.cong(Nat, Nat, y => 1n+Nat.add(N, y),
      Eng.nm.go(j, s, Nat.add(1n+i, N), Eng.nm.ok(s, Nat.add(1n+i, N))),
      Eng.run.len(String.drop(D1, N), True{}, Eng.RN{}, 0n),
      Equal.trans(Nat, Eng.nm.go(j, s, Nat.add(1n+i, N), Eng.nm.ok(s, Nat.add(1n+i, N))),
        Eng.run.len(String.drop(s, Nat.add(1n+i, N)), True{}, Eng.RN{}, 0n),
        Eng.run.len(String.drop(D1, N), True{}, Eng.RN{}, 0n),
        ih(Nat.add(1n+i, N)),
        Equal.cong(Bytes(), Nat, u => Eng.run.len(u, True{}, Eng.RN{}, 0n),
          String.drop(s, Nat.add(1n+i, N)), String.drop(D1, N),
          Equal.sym(Bytes(), String.drop(D1, N), String.drop(s, Nat.add(1n+i, N)), drop_add(s, 1n+i, N))))),
    Equal.trans(Nat, 1n+Nat.add(N, Eng.run.len(String.drop(D1, N), True{}, Eng.RN{}, 0n)),
      1n+Eng.run.len(D1, True{}, Eng.RN{}, 0n),
      Eng.run.len(w, True{}, Eng.RN{}, 1n),
      Equal.cong(Nat, Nat, y => 1n+y,
        Nat.add(N, Eng.run.len(String.drop(D1, N), True{}, Eng.RN{}, 0n)),
        Eng.run.len(D1, True{}, Eng.RN{}, 0n),
        Equal.sym(Nat, Eng.run.len(D1, True{}, Eng.RN{}, 0n),
          Nat.add(N, Eng.run.len(String.drop(D1, N), True{}, Eng.RN{}, 0n)),
          lem.nm.span(D1))),
      %Equal.sym(Bytes(), String.drop(s, 1n+i), w, eD1) :
        {1n+Eng.run.len(_, True{}, Eng.RN{}, 0n) == Eng.run.len(w, True{}, Eng.RN{}, 1n) : Nat}
      Equal.sym(Nat, Eng.run.len(w, True{}, Eng.RN{}, 1n), 1n+Eng.run.len(w, True{}, Eng.RN{}, 0n),
        lem.shift(w, True{}, Eng.RN{}, 0n))))

def lem.nm.nil(k: Nat, -s: Bytes(), -i: Nat) -> {Eng.nm.go(k, s, i, False{}) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

# the count from i when the byte at i is c, and the read goes on with w
def lem.nm.c0(+s: Bytes(), +i: Nat, +c: U32, +w: Bytes(), ok: Bool,
  +eu: {String.drop(s, i) == SCon{Chr{c}, w} : Bytes()}) ->
  {Eng.run.stay(Eng.RN{}, Eng.cls(c)) == ok : Bool} ->
  {Eng.nm.go(0n, s, i, ok) == Eng.run.len(SCon{Chr{c}, w}, True{}, Eng.RN{}, 0n) : Nat}:
  match ok:
    case False{}:
      oke =>
        %Equal.sym(Bool, Eng.run.stay(Eng.RN{}, Eng.cls(c)), False{}, oke) :
          {0n == Eng.run.len(w, _, Eng.RN{}, Eng.run.inc(_, 0n)) : Nat}
        Equal.sym(Nat, Eng.run.len(w, False{}, Eng.RN{}, 0n), 0n, lem.len0(w, Eng.RN{}))
    case True{}:
      oke =>
        %Equal.sym(Bytes(), String.drop(s, i), SCon{Chr{c}, w}, eu) :
          {Eng.run.len(_, True{}, Eng.RN{}, 0n) == Eng.run.len(SCon{Chr{c}, w}, True{}, Eng.RN{}, 0n) : Nat}
        {==}

def lem.nm.cS(j: Nat, +s: Bytes(), +i: Nat, +c: U32, +w: Bytes(), ok: Bool,
  +eu: {String.drop(s, i) == SCon{Chr{c}, w} : Bytes()},
  ih: @+i2: Nat -> {Eng.nm.go(j, s, i2, Eng.nm.ok(s, i2)) ==
    Eng.run.len(String.drop(s, i2), True{}, Eng.RN{}, 0n) : Nat}) ->
  {Eng.run.stay(Eng.RN{}, Eng.cls(c)) == ok : Bool} ->
  {Eng.nm.go(1n+j, s, i, ok) == Eng.run.len(SCon{Chr{c}, w}, True{}, Eng.RN{}, 0n) : Nat}:
  match ok:
    case False{}:
      oke =>
        %Equal.sym(Bool, Eng.run.stay(Eng.RN{}, Eng.cls(c)), False{}, oke) :
          {0n == Eng.run.len(w, _, Eng.RN{}, Eng.run.inc(_, 0n)) : Nat}
        Equal.sym(Nat, Eng.run.len(w, False{}, Eng.RN{}, 0n), 0n, lem.len0(w, Eng.RN{}))
    case True{}:
      oke =>
        %Equal.sym(Bool, Eng.run.stay(Eng.RN{}, Eng.cls(c)), True{}, oke) :
          {Eng.nm.go(1n+j, s, i, True{}) == Eng.run.len(w, _, Eng.RN{}, Eng.run.inc(_, 0n)) : Nat}
        lem.nm.more(j, s, i, w,
          Equal.trans(Bytes(), String.drop(s, 1n+i), String.drop(String.drop(s, i), 1n), w,
            drop_one(s, i),
            %Equal.sym(Bytes(), String.drop(s, i), SCon{Chr{c}, w}, eu) : {String.drop(_, 1n) == w : Bytes()}
            drop0(w)),
          ih)

# the count from i, with the read from i named u
def lem.nm.gen(+k: Nat, +s: Bytes(), +i: Nat, +u: Bytes()) ->
  {String.drop(s, i) == u : Bytes()} ->
  {Eng.nm.go(k, s, i, Eng.run.stay(Eng.RN{}, Eng.cls(hd(u)))) == Eng.run.len(u, True{}, Eng.RN{}, 0n) : Nat}:
  match k u:
    case _ SNil{}:
      eu => lem.nm.nil(k, s, i)
    case 0n SCon{Chr{+c}, +w}:
      +eu => lem.nm.c0(s, i, c, w, Eng.run.stay(Eng.RN{}, Eng.cls(c)), eu)({==})
    case 1n+j SCon{Chr{+c}, +w}:
      +eu => lem.nm.cS(j, s, i, c, w, Eng.run.stay(Eng.RN{}, Eng.cls(c)), eu,
        i2 => Equal.trans(Nat, Eng.nm.go(j, s, i2, Eng.nm.ok(s, i2)),
          Eng.nm.go(j, s, i2, Eng.run.stay(Eng.RN{}, Eng.cls(hd(String.drop(s, i2))))),
          Eng.run.len(String.drop(s, i2), True{}, Eng.RN{}, 0n),
          Equal.cong(U32, Nat, x => Eng.nm.go(j, s, i2, Eng.run.stay(Eng.RN{}, Eng.cls(x))),
            Bytes.get(s, i2), hd(String.drop(s, i2)), get_hd(s, i2)),
          lem.nm.gen(j, s, i2, String.drop(s, i2))({==})))({==})

def lem.nm.go(k: Nat, +s: Bytes(), +i: Nat) ->
  {Eng.nm.go(k, s, i, Eng.nm.ok(s, i)) == Eng.run.len(String.drop(s, i), True{}, Eng.RN{}, 0n) : Nat}:
  %Equal.sym(U32, Bytes.get(s, i), hd(String.drop(s, i)), get_hd(s, i)) :
    {Eng.nm.go(k, s, i, Eng.run.stay(Eng.RN{}, Eng.cls(_))) ==
      Eng.run.len(String.drop(s, i), True{}, Eng.RN{}, 0n) : Nat}
  lem.nm.gen(k, s, i, String.drop(s, i))({==})

# run.nm counts what run.len does
def lem.nm(+s: Bytes()) -> {Eng.run.nm(s) == Eng.run.len(s, True{}, Eng.RN{}, 0n) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      +S: Bytes() = SCon{h, t}
      +N = Bytes.span.go(S, 97, 123)
      Equal.trans(Nat, Nat.add(N, Eng.nm.go(Bytes.len(S), S, N, Eng.nm.ok(S, N))),
        Nat.add(N, Eng.run.len(String.drop(S, N), True{}, Eng.RN{}, 0n)),
        Eng.run.len(S, True{}, Eng.RN{}, 0n),
        Equal.cong(Nat, Nat, y => Nat.add(N, y), Eng.nm.go(Bytes.len(S), S, N, Eng.nm.ok(S, N)),
          Eng.run.len(String.drop(S, N), True{}, Eng.RN{}, 0n), lem.nm.go(Bytes.len(S), S, N)),
        Equal.sym(Nat, Eng.run.len(S, True{}, Eng.RN{}, 0n),
          Nat.add(N, Eng.run.len(String.drop(S, N), True{}, Eng.RN{}, 0n)),
          lem.nm.span(S)))

def lem.ent.len(+e: Eng.Ent, +s: Bytes()) ->
  {Eng.run.len(s, True{}, Eng.ent.sel(e), 0n) == Eng.ent.len(e, s) : Nat}:
  match e:
    case Eng.EMeth{}:
      {==}
    case Eng.EName{}:
      Equal.sym(Nat, Eng.run.nm(s), Eng.run.len(s, True{}, Eng.RN{}, 0n), lem.nm(s))

def lem.ent(+e: Eng.Ent, +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.ent.go(e, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.ent.st(e), pd, out}) : Eng.P}:
  lem.ent.cut(e, s, pd, out, Eng.ent.len(e, s))(lem.ent.len(e, s))

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
    case Eng.InLx{v}:
      lem.go.run(Eng.RX{}, v, s, pd, out)
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
    case Eng.InLc{t, a, b, x, ms}:
      lem.one(Eng.P{Eng.InLc{t, a, b, x, ms}, pd, out}, s)
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

def lem.adv.one(+s: Bytes(), p: Eng.P) ->
  {Eng.feed_buf.last(Eng.adv.one(s, p)) == Eng.feed_buf.slow(s, p) : Eng.P}:
  match p:
    case Eng.P{st, pd, out}:
      lem.adv.at(st, s, pd, out)

# a move from where the one before it landed lands where that one's
# rest, stepped, does
def lem.then(q: Eng.P & Bytes()) ->
  {Eng.feed_buf.last(Eng.adv.then(q)) == Eng.feed_buf.last(q) : Eng.P}:
  match q:
    case (p, s):
      lem.adv.one(s, p)

def lem.adv(+s: Bytes(), +p: Eng.P) ->
  {Eng.feed_buf.last(Eng.adv(s, p)) == Eng.feed_buf.slow(s, p) : Eng.P}:
  Equal.trans(Eng.P, Eng.feed_buf.last(Eng.adv.then(Eng.adv.then(Eng.adv.then(Eng.adv.one(s, p))))), Eng.feed_buf.last(Eng.adv.then(Eng.adv.then(Eng.adv.one(s, p)))),
    Eng.feed_buf.slow(s, p), lem.then(Eng.adv.then(Eng.adv.then(Eng.adv.one(s, p)))),
    Equal.trans(Eng.P, Eng.feed_buf.last(Eng.adv.then(Eng.adv.then(Eng.adv.one(s, p)))), Eng.feed_buf.last(Eng.adv.then(Eng.adv.one(s, p))), Eng.feed_buf.slow(s, p),
      lem.then(Eng.adv.then(Eng.adv.one(s, p))),
      Equal.trans(Eng.P, Eng.feed_buf.last(Eng.adv.then(Eng.adv.one(s, p))), Eng.feed_buf.last(Eng.adv.one(s, p)), Eng.feed_buf.slow(s, p),
        lem.then(Eng.adv.one(s, p)), lem.adv.one(s, p))))

# the kit's obligation: every move lands where stepping its bytes does
def adv_ok(+u: Unit, +s: Bytes(), p: Eng.P) ->
  {Wr.feed_buf.last(~Unit, ~Eng.P, ~Eng.wstep, u, Eng.wadv(u, s, p)) ==
    Wr.feed_buf.slow(~Unit, ~Eng.P, ~Eng.wstep, u, s, p) : Eng.P}:
  match u:
    case Unit{}:
      lem.adv(s, p)

# the fuel never matters (the kit's go_is_slow)
def lem.go(n: Nat, q: Eng.P & Bytes()) ->
  {Wr.feed_buf.go(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, Unit{}, n, q) == Eng.feed_buf.last(q) : Eng.P}:
  Wr.go_is_slow(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, ~adv_ok, Unit{}, n, q)

def Laws.feed_buf_is_feed(b, p):
  Wr.feed_buf_is_feed(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, ~adv_ok, Unit{}, b, p)

def Laws.feed_buf_split(a, b, p):
  Wr.feed_buf_split(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, ~adv_ok, Unit{}, a, b, p)

def Laws.bad_feeds_buf(s, pd, out):
  Wr.bad_feeds_buf(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, ~adv_ok, ~BadAt, ~bad, ~absorbs, Unit{}, s,
    BadAt{pd, out})

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
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
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
  -v10: Bool, -ka: Bool, -hx: Eng.Hx, -nx: Maybe<&2, Eng.Pend>, -out: List<&2, Eng.Req>) ->
  {Eng.step.te.at(ok, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, True{}}, hx, nx}, out) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, True{}}, hx, nx}, out} : Eng.P}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.te_once(v, m, path, l, cl, h, ws, v10, ka, hx, nx, out):
  te.twice(Eng.bytes.eq(Eng.lows(v), Eng.te.lit()), m, path, l, cl, h, ws, v10, ka, hx, nx, out)

def Laws.te_cl_refused(m, path, v, cl, h, ws, v10, ka, hx, nx, out):
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

def Laws.te_10_refused(m, path, l, cl, h, ws, ka, hx, nx, out):
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

def Laws.clen_disagree(v, w, m, path, cl, h, ws, fx, hx, nx, out, e):
  %Equal.sym(Bool, U32.is_eq(w, v), False{}, e) :
    {Eng.step.clen.dup(Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, fx, hx, nx}, out, _) ==
      Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, fx, hx, nx}, out} : Eng.P}
  {==}

def Laws.host_once(m, path, l, cl, h, ws, v10, ka, te, hx, nx, out, e):
  match h v10:
    case Eng.H0{} True{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, Eng.H0{}, ws, Eng.Fx{True{}, ka, te}, hx, nx}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, Eng.H0{}, ws, Eng.Fx{True{}, ka, te}, hx, nx}, out} : Eng.P})
      Unit{}
    case Eng.H1{} True{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{True{}, ka, te}, hx, nx}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{True{}, ka, te}, hx, nx}, out} : Eng.P})
      Unit{}
    case Eng.H2{} True{}:
      {==}
    case Eng.H0{} False{}:
      {==}
    case Eng.H1{} False{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{False{}, ka, te}, hx, nx}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, Eng.H1{}, ws, Eng.Fx{False{}, ka, te}, hx, nx}, out} : Eng.P})
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
  k: Eng.Cls, c: U32, v: Bytes(), pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLx{v}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{v}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.value_refuses(c, pd, out, v, e):
  value_bad(Eng.cls(c), c, v, pd, out, e)

def conn_bad(
  k: Eng.Cls, c: U32, t: Bytes(), a: Bool, b: Bool, x: Bool, ms: List<&2, Bytes()>, pd: Eng.Pend,
  out: List<&2, Eng.Req>, e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLc{t, a, b, x, ms}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b, x, ms}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.conn_refuses(c, t, a, b, x, ms, pd, out, e):
  conn_bad(Eng.cls(c), c, t, a, b, x, ms, pd, out, e)

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

def Laws.parse_fields():
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

# page_is_spec: the fast walk (Eng.fast.go) is a state machine over the
# path's bytes -- at a segment's start or inside one -- and each of its
# facts is proved of the reference's pieces by one induction over the
# bytes, walking segs.go's Cut from the end: the segments joined are the
# bytes (pg.join), the first is never empty (pg.lead), every one is a
# name fname.ok takes (pg.ok), every byte is one clean takes (pg.clean),
# and the last '.' the walk finds is the last segment's (pg.ext). Over
# names the normaliser reverses twice (pg.norm), so fnames.of hands back
# the segments whole and page.name builds the Page the fast path did.

# U32 equality is equality (as io_proxy's proof has it)
def beq.b(ab: Bool, bb: Bool, h: {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool}) -> {ab == bb : Bool}:
  match ab bb:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      no({True{} == False{} : Bool}, h)
    case False{} True{}:
      no({False{} == True{} : Bool}, h)

def fin.eq(+ab: Bool, +bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) ->
  {Cmp.is_eq(t) == True{} : Bool} & {ab == bb : Bool}:
  match t:
    case LT{}:
      no({Cmp.is_eq(LT{}) == True{} : Bool} & {ab == bb : Bool}, h)
    case GT{}:
      no({Cmp.is_eq(GT{}) == True{} : Bool} & {ab == bb : Bool}, h)
    case EQ{}:
      ({==}, beq.b(ab, bb, h))

def word.at(p: Nat, +ab: Bool, +at: Word(p), +bb: Bool, +bt: Word(p),
  hh: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} & {ab == bb : Bool},
  ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}) ->
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  (e1, e2) = hh
  %e2 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
  Equal.cong(Word(p), Word(1n+p), w => WCon{ab, w}, at, bt, ih(e1))

def word.eq(n: Nat, a: Word(n), b: Word(n), h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          word.at(p, ab, at, bb, bt, fin.eq(ab, bb, Word.cmp(p, at, bt), h), e => word.eq(p, at, bt, e))

def u32.eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word.eq(32n, x, y, h))

def or.false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# a byte fname.byte takes is not '/'
def pg.fb47(+c: U32, e: {Eng.fname.byte(c) == True{} : Bool}) -> {U32.is_eq(c, 47) == False{} : Bool}:
  Bool.not_true(U32.is_eq(c, 47),
    Bool.and_r(Bool.and(U32.is_le(33, c), U32.is_le(c, 126)), Bool.not(U32.is_eq(c, 47)),
      Bool.and_l(Bool.and(Bool.and(U32.is_le(33, c), U32.is_le(c, 126)), Bool.not(U32.is_eq(c, 47))),
        Bool.not(U32.is_eq(c, 92)), e)))

# what one step of the fast walk says of its byte and of the rest
def pg.fw.ok(+st: Bool, +c: U32, t: Bytes(), e: {Eng.fast.go(SCon{Chr{c}, t}, st) == True{} : Bool}) ->
  {Eng.fast.ok(st, c) == True{} : Bool}:
  Bool.and_l(Eng.fast.ok(st, c), Eng.fast.go(t, U32.is_eq(c, 47)), e)

def pg.fw.rest(+st: Bool, +c: U32, t: Bytes(), e: {Eng.fast.go(SCon{Chr{c}, t}, st) == True{} : Bool}) ->
  {Eng.fast.go(t, U32.is_eq(c, 47)) == True{} : Bool}:
  Bool.and_r(Eng.fast.ok(st, c), Eng.fast.go(t, U32.is_eq(c, 47)), e)

def pg.fw.clean(+st: Bool, +c: U32, e: {Eng.fast.ok(st, c) == True{} : Bool}) ->
  {Eng.clean.pick(Eng.ctl(c), c) == True{} : Bool}:
  Bool.and_l(Eng.clean.pick(Eng.ctl(c), c), Eng.fast.ok.go(st, c), e)

def pg.fw.go(+st: Bool, +c: U32, e: {Eng.fast.ok(st, c) == True{} : Bool}) ->
  {Eng.fast.ok.go(st, c) == True{} : Bool}:
  Bool.and_r(Eng.clean.pick(Eng.ctl(c), c), Eng.fast.ok.go(st, c), e)

# at a segment's start the byte is a name's, and not '/'
def pg.fw.start(+c: U32, e: {Eng.fast.ok(True{}, c) == True{} : Bool}) -> {Eng.fname.byte(c) == True{} : Bool}:
  Bool.and_l(Eng.fname.byte(c), Bool.not(U32.is_eq(c, 46)), pg.fw.go(True{}, c, e))

def pg.fw.nodot(+c: U32, e: {Eng.fast.ok(True{}, c) == True{} : Bool}) -> {U32.is_eq(c, 46) == False{} : Bool}:
  Bool.not_true(U32.is_eq(c, 46),
    Bool.and_r(Eng.fname.byte(c), Bool.not(U32.is_eq(c, 46)), pg.fw.go(True{}, c, e)))

# the cut of what is left of a path
def pg.K(r: Bytes()) -> Eng.Cut:
  Eng.segs.go(Bytes.to_list(r))

def pg.cut.lead(k: Eng.Cut) -> Bool:
  match k:
    case Eng.Cut{Nil{}, rest}:
      False{}
    case Eng.Cut{Con{c, t}, rest}:
      True{}

def pg.lead.at(+c: U32, k: Eng.Cut, f: {U32.is_eq(c, 47) == False{} : Bool}) ->
  {pg.cut.lead(Eng.segs.at(U32.is_eq(c, 47), c, k)) == True{} : Bool}:
  match k:
    case Eng.Cut{cur, rest}:
      %Equal.sym(Bool, U32.is_eq(c, 47), False{}, f) :
        {pg.cut.lead(Eng.segs.at(_, c, Eng.Cut{cur, rest})) == True{} : Bool}
      {==}

# at a segment's start the walk reads a name: the cut's first segment
# is not empty
def pg.lead(r: Bytes()) -> {Eng.fast.go(r, True{}) == True{} : Bool} -> {pg.cut.lead(pg.K(r)) == True{} : Bool}:
  match r:
    case SNil{}:
      e => no({pg.cut.lead(pg.K(SNil{})) == True{} : Bool}, e)
    case SCon{Chr{+c}, +t}:
      e => pg.lead.at(c, pg.K(t), pg.fb47(c, pg.fw.start(c, pg.fw.ok(True{}, c, t, e))))


# the bytes a cut stands for: its first segment, then '/' and each after
def pg.cut.join(k: Eng.Cut) -> List<&2, U32>:
  match k:
    case Eng.Cut{cur, rest}:
      Eng.cat(cur, Eng.join.rest(rest))

# a '/': the segment after it is not empty, so it stays a segment
def pg.join.sl(+c: U32, k: Eng.Cut, xs: List<&2, U32>, c47: {c == 47 : U32},
  lead: {pg.cut.lead(k) == True{} : Bool}, ih: {pg.cut.join(k) == xs : List<&2, U32>}) ->
  {pg.cut.join(Eng.segs.at(True{}, c, k)) == Con{c, xs} : List<&2, U32>}:
  match k:
    case Eng.Cut{Nil{}, rest}:
      no({pg.cut.join(Eng.segs.at(True{}, c, Eng.Cut{Nil{}, rest})) == Con{c, xs} : List<&2, U32>}, lead)
    case Eng.Cut{Con{h, u}, rest}:
      %Equal.sym(U32, c, 47, c47) :
        {pg.cut.join(Eng.segs.at(True{}, c, Eng.Cut{Con{h, u}, rest})) == Con{_, xs} : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{47, ys}, pg.cut.join(Eng.Cut{Con{h, u}, rest}), xs, ih)

# a name's byte joins the segment it is in
def pg.join.ch(+c: U32, k: Eng.Cut, xs: List<&2, U32>, ih: {pg.cut.join(k) == xs : List<&2, U32>}) ->
  {pg.cut.join(Eng.segs.at(False{}, c, k)) == Con{c, xs} : List<&2, U32>}:
  match k:
    case Eng.Cut{cur, rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{c, ys}, pg.cut.join(Eng.Cut{cur, rest}), xs, ih)

def pg.join.at(+c: U32, +t: Bytes(), b: Bool,
  er: {Eng.fast.go(t, U32.is_eq(c, 47)) == True{} : Bool},
  ih: {pg.cut.join(pg.K(t)) == Bytes.to_list(t) : List<&2, U32>},
  lead: {Eng.fast.go(t, True{}) == True{} : Bool} -> {pg.cut.lead(pg.K(t)) == True{} : Bool}) ->
  {U32.is_eq(c, 47) == b : Bool} ->
  {pg.cut.join(Eng.segs.at(U32.is_eq(c, 47), c, pg.K(t))) == Con{c, Bytes.to_list(t)} : List<&2, U32>}:
  match b:
    case True{}:
      +eb =>
        %Equal.sym(Bool, U32.is_eq(c, 47), True{}, eb) :
          {pg.cut.join(Eng.segs.at(_, c, pg.K(t))) == Con{c, Bytes.to_list(t)} : List<&2, U32>}
        pg.join.sl(c, pg.K(t), Bytes.to_list(t), u32.eq(c, 47, eb),
          lead(Equal.trans(Bool, Eng.fast.go(t, True{}), Eng.fast.go(t, U32.is_eq(c, 47)), True{},
            Equal.cong(Bool, Bool, x => Eng.fast.go(t, x), True{}, U32.is_eq(c, 47),
              Equal.sym(Bool, U32.is_eq(c, 47), True{}, eb)), er)), ih)
    case False{}:
      +eb =>
        %Equal.sym(Bool, U32.is_eq(c, 47), False{}, eb) :
          {pg.cut.join(Eng.segs.at(_, c, pg.K(t))) == Con{c, Bytes.to_list(t)} : List<&2, U32>}
        pg.join.ch(c, pg.K(t), Bytes.to_list(t), ih)

# the segments of a path the fast walk takes, joined, are its bytes
def pg.join(r: Bytes(), +st: Bool) ->
  {Eng.fast.go(r, st) == True{} : Bool} -> {pg.cut.join(pg.K(r)) == Bytes.to_list(r) : List<&2, U32>}:
  match r:
    case SNil{}:
      e => {==}
    case SCon{Chr{+c}, +t}:
      +e => pg.join.at(c, t, U32.is_eq(c, 47), pg.fw.rest(st, c, t, e),
        pg.join(t, U32.is_eq(c, 47))(pg.fw.rest(st, c, t, e)), pg.lead(t))({==})

# the segments after a cut's first are names by fname.ok, and its first
# segment's bytes are a name's (OKT False) -- or, at a segment's start,
# every segment it stands for is (OKT True)
def pg.cut.okF(k: Eng.Cut) -> Bool:
  match k:
    case Eng.Cut{cur, rest}:
      Bool.and(Eng.fname.bytes(cur), Eng.fnames.ok(False{}, rest))

def pg.OKT(st: Bool, k: Eng.Cut) -> Type:
  match st:
    case True{}:
      {Eng.fnames.ok(False{}, Eng.segs.out(k)) == True{} : Bool}
    case False{}:
      {pg.cut.okF(k) == True{} : Bool}

def pg.cast(b0: Bool, b1: Bool, k: Eng.Cut, e: {b0 == b1 : Bool}, h: pg.OKT(b0, k)) -> pg.OKT(b1, k):
  %e : pg.OKT(_, k)
  h

def pg.ok.nil(st: Bool) -> {Eng.fast.go(SNil{}, st) == True{} : Bool} -> pg.OKT(st, pg.K(SNil{})):
  match st:
    case True{}:
      e => no(pg.OKT(True{}, pg.K(SNil{})), e)
    case False{}:
      e => {==}

def pg.ok.sl(+c: U32, k: Eng.Cut, ih: pg.OKT(True{}, k)) -> {pg.cut.okF(Eng.segs.at(True{}, c, k)) == True{} : Bool}:
  match k:
    case Eng.Cut{cur, rest}:
      ih

def pg.ok.ch(+c: U32, k: Eng.Cut, fb: {Eng.fname.byte(c) == True{} : Bool}, ih: {pg.cut.okF(k) == True{} : Bool}) ->
  {pg.cut.okF(Eng.segs.at(False{}, c, k)) == True{} : Bool}:
  match k:
    case Eng.Cut{cur, rest}:
      %Equal.sym(Bool, Eng.fname.byte(c), True{}, fb) :
        {Bool.and(Bool.and(_, Eng.fname.bytes(cur)), Eng.fnames.ok(False{}, rest)) == True{} : Bool}
      ih

def pg.ok.st(+c: U32, k: Eng.Cut, fb: {Eng.fname.byte(c) == True{} : Bool},
  nd: {U32.is_eq(c, 46) == False{} : Bool}, ih: {pg.cut.okF(k) == True{} : Bool}) ->
  {Eng.fnames.ok(False{}, Eng.segs.out(Eng.segs.at(False{}, c, k))) == True{} : Bool}:
  match k:
    case Eng.Cut{cur, rest}:
      %Equal.sym(Bool, U32.is_eq(c, 46), False{}, nd) :
        {Bool.and(Bool.and(Bool.not(_), Bool.and(Eng.fname.byte(c), Eng.fname.bytes(cur))),
          Eng.fnames.ok(False{}, rest)) == True{} : Bool}
      %Equal.sym(Bool, Eng.fname.byte(c), True{}, fb) :
        {Bool.and(Bool.and(_, Eng.fname.bytes(cur)), Eng.fnames.ok(False{}, rest)) == True{} : Bool}
      ih

# inside a name, a byte that is not '/' is a name's byte
def pg.fw.inner(+c: U32, eo: {Eng.fast.ok(False{}, c) == True{} : Bool}, eb: {U32.is_eq(c, 47) == False{} : Bool}) ->
  {Eng.fname.byte(c) == True{} : Bool}:
  %eb : {Bool.or(_, Eng.fname.byte(c)) == True{} : Bool}
  pg.fw.go(False{}, c, eo)

# '/' where a name must start is refused
def pg.fw.sl.start(+c: U32, eo: {Eng.fast.ok(True{}, c) == True{} : Bool}, eb: {U32.is_eq(c, 47) == True{} : Bool}) ->
  {False{} == True{} : Bool}:
  Equal.trans(Bool, False{}, U32.is_eq(c, 47), True{},
    Equal.sym(Bool, U32.is_eq(c, 47), False{}, pg.fb47(c, pg.fw.start(c, eo))), eb)

def pg.ok.sw(+c: U32, +t: Bytes(), eb: {U32.is_eq(c, 47) == True{} : Bool}, ih: pg.OKT(U32.is_eq(c, 47), pg.K(t)),
  st: Bool) -> {Eng.fast.ok(st, c) == True{} : Bool} -> pg.OKT(st, Eng.segs.at(True{}, c, pg.K(t))):
  match st:
    case True{}:
      eo => no(pg.OKT(True{}, Eng.segs.at(True{}, c, pg.K(t))), pg.fw.sl.start(c, eo, eb))
    case False{}:
      eo => pg.ok.sl(c, pg.K(t), pg.cast(U32.is_eq(c, 47), True{}, pg.K(t), eb, ih))

def pg.ok.sn(+c: U32, +t: Bytes(), +eb: {U32.is_eq(c, 47) == False{} : Bool}, ih: pg.OKT(U32.is_eq(c, 47), pg.K(t)),
  st: Bool) -> {Eng.fast.ok(st, c) == True{} : Bool} -> pg.OKT(st, Eng.segs.at(False{}, c, pg.K(t))):
  match st:
    case False{}:
      eo => pg.ok.ch(c, pg.K(t), pg.fw.inner(c, eo, eb), pg.cast(U32.is_eq(c, 47), False{}, pg.K(t), eb, ih))
    case True{}:
      +eo => pg.ok.st(c, pg.K(t), pg.fw.start(c, eo), pg.fw.nodot(c, eo),
        pg.cast(U32.is_eq(c, 47), False{}, pg.K(t), eb, ih))

def pg.ok.at(st: Bool, +c: U32, +t: Bytes(), b: Bool, ih: pg.OKT(U32.is_eq(c, 47), pg.K(t))) ->
  {Eng.fast.ok(st, c) == True{} : Bool} -> {U32.is_eq(c, 47) == b : Bool} ->
  pg.OKT(st, Eng.segs.at(U32.is_eq(c, 47), c, pg.K(t))):
  match b:
    case True{}:
      eo => +eb =>
        %Equal.sym(Bool, U32.is_eq(c, 47), True{}, eb) : pg.OKT(st, Eng.segs.at(_, c, pg.K(t)))
        pg.ok.sw(c, t, eb, ih, st)(eo)
    case False{}:
      eo => +eb =>
        %Equal.sym(Bool, U32.is_eq(c, 47), False{}, eb) : pg.OKT(st, Eng.segs.at(_, c, pg.K(t)))
        pg.ok.sn(c, t, eb, ih, st)(eo)

def pg.ok(r: Bytes(), +st: Bool) -> {Eng.fast.go(r, st) == True{} : Bool} -> pg.OKT(st, pg.K(r)):
  match r:
    case SNil{}:
      pg.ok.nil(st)
    case SCon{Chr{+c}, +t}:
      +e => pg.ok.at(st, c, t, U32.is_eq(c, 47),
        pg.ok(t, U32.is_eq(c, 47))(pg.fw.rest(st, c, t, e)))(pg.fw.ok(st, c, t, e), {==})

# every byte the fast walk takes is one clean() takes
def pg.clean(r: Bytes(), +st: Bool) ->
  {Eng.fast.go(r, st) == True{} : Bool} -> {Eng.clean.go(Bytes.to_list(r), True{}) == True{} : Bool}:
  match r:
    case SNil{}:
      e => {==}
    case SCon{Chr{+c}, +t}:
      +e =>
        %Equal.sym(Bool, Eng.clean.pick(Eng.ctl(c), c), True{}, pg.fw.clean(st, c, pg.fw.ok(st, c, t, e))) :
          {Eng.clean.go(Bytes.to_list(t), _) == True{} : Bool}
        pg.clean(t, U32.is_eq(c, 47))(pg.fw.rest(st, c, t, e))

# the type a cut's path has: the bytes after the last '.' of its last
# segment, or of the one being read (from cur) when it is the last
def pg.ext.tail(rs: List<&2, List<&2, U32>>, p: List<&2, U32>, cur: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Eng.ext.go(p, cur)
    case Con{s, u}:
      Eng.ext.go(Eng.last(u, s), Nil{})

def pg.cut.ext(k: Eng.Cut, cur: List<&2, U32>) -> List<&2, U32>:
  match k:
    case Eng.Cut{p, rs}:
      pg.ext.tail(rs, p, cur)

def pg.ext.sl(+c: U32, k: Eng.Cut, cur: List<&2, U32>, lead: {pg.cut.lead(k) == True{} : Bool}) ->
  {pg.cut.ext(k, Nil{}) == pg.cut.ext(Eng.segs.at(True{}, c, k), cur) : List<&2, U32>}:
  match k:
    case Eng.Cut{Nil{}, rs}:
      no({pg.cut.ext(Eng.Cut{Nil{}, rs}, Nil{}) == pg.cut.ext(Eng.segs.at(True{}, c, Eng.Cut{Nil{}, rs}), cur) :
        List<&2, U32>}, lead)
    case Eng.Cut{Con{h, u}, Nil{}}:
      {==}
    case Eng.Cut{Con{h, u}, Con{s, v}}:
      {==}

def pg.ext.ch(+c: U32, k: Eng.Cut, cur: List<&2, U32>) ->
  {pg.cut.ext(k, Eng.ext.step(cur, c, U32.is_eq(c, 46))) == pg.cut.ext(Eng.segs.at(False{}, c, k), cur) :
    List<&2, U32>}:
  match k:
    case Eng.Cut{p, Nil{}}:
      {==}
    case Eng.Cut{p, Con{s, v}}:
      {==}

def pg.ext.at(+c: U32, +t: Bytes(), +cur: List<&2, U32>, b: Bool,
  ih0: {Eng.ext.buf(t, Nil{}) == pg.cut.ext(pg.K(t), Nil{}) : List<&2, U32>},
  ih1: {Eng.ext.buf(t, Eng.ext.step(cur, c, U32.is_eq(c, 46))) ==
    pg.cut.ext(pg.K(t), Eng.ext.step(cur, c, U32.is_eq(c, 46))) : List<&2, U32>},
  lead: {Eng.fast.go(t, True{}) == True{} : Bool} -> {pg.cut.lead(pg.K(t)) == True{} : Bool},
  er: {Eng.fast.go(t, U32.is_eq(c, 47)) == True{} : Bool}) ->
  {U32.is_eq(c, 47) == b : Bool} ->
  {Eng.ext.buf(t, Eng.ext.step(cur, c, Bool.or(U32.is_eq(c, 46), U32.is_eq(c, 47)))) ==
    pg.cut.ext(Eng.segs.at(U32.is_eq(c, 47), c, pg.K(t)), cur) : List<&2, U32>}:
  match b:
    case True{}:
      +eb =>
        %Equal.sym(Bool, U32.is_eq(c, 47), True{}, eb) :
          {Eng.ext.buf(t, Eng.ext.step(cur, c, Bool.or(U32.is_eq(c, 46), _))) ==
            pg.cut.ext(Eng.segs.at(_, c, pg.K(t)), cur) : List<&2, U32>}
        %Equal.sym(Bool, Bool.or(U32.is_eq(c, 46), True{}), True{}, Bool.or_true(U32.is_eq(c, 46))) :
          {Eng.ext.buf(t, Eng.ext.step(cur, c, _)) == pg.cut.ext(Eng.segs.at(True{}, c, pg.K(t)), cur) :
            List<&2, U32>}
        Equal.trans(List<&2, U32>, Eng.ext.buf(t, Nil{}), pg.cut.ext(pg.K(t), Nil{}),
          pg.cut.ext(Eng.segs.at(True{}, c, pg.K(t)), cur), ih0,
          pg.ext.sl(c, pg.K(t), cur, lead(Equal.trans(Bool, Eng.fast.go(t, True{}), Eng.fast.go(t, U32.is_eq(c, 47)),
            True{}, Equal.cong(Bool, Bool, x => Eng.fast.go(t, x), True{}, U32.is_eq(c, 47),
              Equal.sym(Bool, U32.is_eq(c, 47), True{}, eb)), er))))
    case False{}:
      +eb =>
        %Equal.sym(Bool, U32.is_eq(c, 47), False{}, eb) :
          {Eng.ext.buf(t, Eng.ext.step(cur, c, Bool.or(U32.is_eq(c, 46), _))) ==
            pg.cut.ext(Eng.segs.at(_, c, pg.K(t)), cur) : List<&2, U32>}
        %Equal.sym(Bool, Bool.or(U32.is_eq(c, 46), False{}), U32.is_eq(c, 46), or.false(U32.is_eq(c, 46))) :
          {Eng.ext.buf(t, Eng.ext.step(cur, c, _)) == pg.cut.ext(Eng.segs.at(False{}, c, pg.K(t)), cur) :
            List<&2, U32>}
        Equal.trans(List<&2, U32>, Eng.ext.buf(t, Eng.ext.step(cur, c, U32.is_eq(c, 46))),
          pg.cut.ext(pg.K(t), Eng.ext.step(cur, c, U32.is_eq(c, 46))),
          pg.cut.ext(Eng.segs.at(False{}, c, pg.K(t)), cur), ih1, pg.ext.ch(c, pg.K(t), cur))

# the type the fast walk reads is the type of the segments' last
def pg.ext(r: Bytes(), +st: Bool, +cur: List<&2, U32>) ->
  {Eng.fast.go(r, st) == True{} : Bool} -> {Eng.ext.buf(r, cur) == pg.cut.ext(pg.K(r), cur) : List<&2, U32>}:
  match r:
    case SNil{}:
      e => {==}
    case SCon{Chr{+c}, +t}:
      +e => pg.ext.at(c, t, cur, U32.is_eq(c, 47),
        pg.ext(t, U32.is_eq(c, 47), Nil{})(pg.fw.rest(st, c, t, e)),
        pg.ext(t, U32.is_eq(c, 47), Eng.ext.step(cur, c, U32.is_eq(c, 46)))(pg.fw.rest(st, c, t, e)),
        pg.lead(t), pg.fw.rest(st, c, t, e))({==})

# a name is not "." or ".."
def pg.beqf(u: List<&2, U32>, xs: List<&2, U32>) -> {Eng.beq(u, xs, False{}) == False{} : Bool}:
  match u xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, w}:
      {==}
    case Con{x, t} Nil{}:
      {==}
    case Con{x, t} Con{y, w}:
      pg.beqf(t, w)

def pg.piece(s: List<&2, U32>) -> {Eng.fname.ok(False{}, s) == True{} : Bool} -> {Eng.piece(s) == Eng.Name{} : Eng.Piece}:
  match s:
    case Nil{}:
      e => no({Eng.piece(Nil{}) == Eng.Name{} : Eng.Piece}, e)
    case Con{+c, +u}:
      e =>
        %Equal.sym(Bool, U32.is_eq(c, 46), False{}, Bool.not_true(U32.is_eq(c, 46),
          Bool.and_l(Bool.not(U32.is_eq(c, 46)), Eng.fname.bytes(Con{c, u}), e))) :
          {Eng.piece.of(Eng.beq(u, [46], _), Eng.beq(u, Nil{}, _)) == Eng.Name{} : Eng.Piece}
        %Equal.sym(Bool, Eng.beq(u, [46], False{}), False{}, pg.beqf(u, [46])) :
          {Eng.piece.of(_, Eng.beq(u, Nil{}, False{})) == Eng.Name{} : Eng.Piece}
        %Equal.sym(Bool, Eng.beq(u, Nil{}, False{}), False{}, pg.beqf(u, Nil{})) :
          {Eng.piece.of(False{}, _) == Eng.Name{} : Eng.Piece}
        {==}

# over names, the normaliser only reverses, twice
def pg.norm.go(ss: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) ->
  {Eng.fnames.ok(False{}, ss) == True{} : Bool} ->
  {Eng.norm.go(ss, Some{acc}) == Some{List.reverse.go(&2, List<&2, U32>, ss, acc)} :
    Maybe<&2, List<&2, List<&2, U32>>>}:
  match ss:
    case Nil{}:
      e => {==}
    case Con{+s, +t}:
      +e =>
        %Equal.sym(Eng.Piece, Eng.piece(s), Eng.Name{},
          pg.piece(s)(Bool.and_l(Eng.fname.ok(False{}, s), Eng.fnames.ok(False{}, t), e))) :
          {Eng.norm.go(t, Eng.norm.step(_, s, acc)) ==
            Some{List.reverse.go(&2, List<&2, U32>, t, Con{s, acc})} : Maybe<&2, List<&2, List<&2, U32>>>}
        pg.norm.go(t, Con{s, acc})(Bool.and_r(Eng.fname.ok(False{}, s), Eng.fnames.ok(False{}, t), e))

def pg.rr(xs: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) ->
  {List.reverse.go(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, xs, acc), Nil{}) ==
    List.reverse.go(&2, List<&2, U32>, acc, xs) : List<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      pg.rr(t, Con{h, acc})

def pg.norm(+ss: List<&2, List<&2, U32>>, e: {Eng.fnames.ok(False{}, ss) == True{} : Bool}) ->
  {Eng.norm(ss) == Some{ss} : Maybe<&2, List<&2, List<&2, U32>>>}:
  %Equal.sym(Maybe<&2, List<&2, List<&2, U32>>>, Eng.norm.go(ss, Some{Nil{}}),
    Some{List.reverse.go(&2, List<&2, U32>, ss, Nil{})}, pg.norm.go(ss, Nil{})(e)) :
    {Eng.norm.rev(_) == Some{ss} : Maybe<&2, List<&2, List<&2, U32>>>}
  %Equal.sym(List<&2, List<&2, U32>>,
    List.reverse.go(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, ss, Nil{}), Nil{}),
    List.reverse.go(&2, List<&2, U32>, Nil{}, ss), pg.rr(ss, Nil{})) :
    {Some{_} == Some{ss} : Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

def pg.ft(b: Bytes()) -> {Bytes.from_list(Bytes.to_list(b)) == b : Bytes()}:
  match b:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{Chr{c}, x}, Bytes.from_list(Bytes.to_list(t)), t, pg.ft(t))

def pg.drop0(r: Bytes()) -> {String.drop(r, 0n) == r : Bytes()}:
  match r:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def pg.last(rs: List<&2, List<&2, U32>>, p: List<&2, U32>) ->
  {pg.ext.tail(rs, p, Nil{}) == Eng.ext.go(Eng.last(rs, p), Nil{}) : List<&2, U32>}:
  match rs:
    case Nil{}:
      {==}
    case Con{s, u}:
      {==}

# the reference, at a path the fast walk took, names the same file
def pg.fin(root: Bytes(), +r: Bytes(), head: Bool, +c0: U32, k: Eng.Cut,
  lead: {pg.cut.lead(k) == True{} : Bool}, j: {pg.cut.join(k) == Bytes.to_list(r) : List<&2, U32>},
  +ok: {Eng.fnames.ok(False{}, Eng.segs.out(k)) == True{} : Bool},
  x: {Eng.ext.buf(r, Nil{}) == pg.cut.ext(k, Nil{}) : List<&2, U32>}) ->
  {L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
    Eng.page.pick(root, Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(True{}, c0, k)))), head) :
    L.Seg}:
  match k:
    case Eng.Cut{Nil{}, rs}:
      no({L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
        Eng.page.pick(root, Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(True{}, c0,
          Eng.Cut{Nil{}, rs})))), head) : L.Seg}, lead)
    case Eng.Cut{Con{+h, +u}, +rs}:
      %Equal.sym(Maybe<&2, List<&2, List<&2, U32>>>, Eng.norm(Con{Con{h, u}, rs}), Some{Con{Con{h, u}, rs}},
        pg.norm(Con{Con{h, u}, rs}, ok)) :
        {L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
          Eng.page.pick(root, Eng.fnames.guard(False{}, _), head) : L.Seg}
      %Equal.sym(Bool, Eng.fnames.ok(False{}, Con{Con{h, u}, rs}), True{}, ok) :
        {L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
          Eng.page.pick(root, Eng.fnames.keep(Con{Con{h, u}, rs}, _), head) : L.Seg}
      %Equal.sym(List<&2, U32>, pg.cut.join(Eng.Cut{Con{h, u}, rs}), Bytes.to_list(r), j) :
        {L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
          L.Page{root, Bytes.from_list(_),
            Eng.mime.head(Bytes.from_list(Eng.ext.go(Eng.last(rs, Con{h, u}), Nil{}))), Nil{}, head} : L.Seg}
      %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(r)), r, pg.ft(r)) :
        {L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
          L.Page{root, _, Eng.mime.head(Bytes.from_list(Eng.ext.go(Eng.last(rs, Con{h, u}), Nil{}))), Nil{}, head} :
          L.Seg}
      %Equal.sym(List<&2, U32>, Eng.ext.buf(r, Nil{}), pg.cut.ext(Eng.Cut{Con{h, u}, rs}, Nil{}), x) :
        {L.Page{root, r, Eng.mime.head(Bytes.from_list(_)), Nil{}, head} ==
          L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.go(Eng.last(rs, Con{h, u}), Nil{}))), Nil{}, head} :
          L.Seg}
      %Equal.sym(List<&2, U32>, pg.ext.tail(rs, Con{h, u}, Nil{}), Eng.ext.go(Eng.last(rs, Con{h, u}), Nil{}),
        pg.last(rs, Con{h, u})) :
        {L.Page{root, r, Eng.mime.head(Bytes.from_list(_)), Nil{}, head} ==
          L.Page{root, r, Eng.mime.head(Bytes.from_list(Eng.ext.go(Eng.last(rs, Con{h, u}), Nil{}))), Nil{}, head} :
          L.Seg}
      {==}

def pg.fast.at(root: Bytes(), +c0: U32, +r: Bytes(), head: Bool,
  +e: {Eng.fast(SCon{Chr{c0}, r}) == True{} : Bool}) ->
  {Eng.page.go(root, SCon{Chr{c0}, r}, head, True{}) == Eng.page.spec(root, Bytes.to_list(SCon{Chr{c0}, r}), head) :
    L.Seg}:
  +ea = Bool.and_l(Bool.and(Eng.clean.pick(Eng.ctl(c0), c0), U32.is_eq(c0, 47)), Eng.fast.go(r, True{}), e)
  +er = Bool.and_r(Bool.and(Eng.clean.pick(Eng.ctl(c0), c0), U32.is_eq(c0, 47)), Eng.fast.go(r, True{}), e)
  %Equal.sym(Bool, U32.is_eq(c0, 47), True{}, Bool.and_r(Eng.clean.pick(Eng.ctl(c0), c0), U32.is_eq(c0, 47), ea)) :
    {L.Page{root, String.drop(r, 0n),
      Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Eng.ext.step(Nil{}, c0, Bool.or(U32.is_eq(c0, 46), _))))), Nil{}, head} ==
      Eng.page.pick(root, Eng.fnames.gate(Eng.clean.go(Bytes.to_list(r), Eng.clean.pick(Eng.ctl(c0), c0)),
        Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(_, c0, pg.K(r)))))), head) : L.Seg}
  %Equal.sym(Bool, Bool.or(U32.is_eq(c0, 46), True{}), True{}, Bool.or_true(U32.is_eq(c0, 46))) :
    {L.Page{root, String.drop(r, 0n),
      Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Eng.ext.step(Nil{}, c0, _)))), Nil{}, head} ==
      Eng.page.pick(root, Eng.fnames.gate(Eng.clean.go(Bytes.to_list(r), Eng.clean.pick(Eng.ctl(c0), c0)),
        Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(True{}, c0, pg.K(r)))))), head) : L.Seg}
  %Equal.sym(Bool, Eng.clean.pick(Eng.ctl(c0), c0), True{},
    Bool.and_l(Eng.clean.pick(Eng.ctl(c0), c0), U32.is_eq(c0, 47), ea)) :
    {L.Page{root, String.drop(r, 0n), Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
      Eng.page.pick(root, Eng.fnames.gate(Eng.clean.go(Bytes.to_list(r), _),
        Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(True{}, c0, pg.K(r)))))), head) : L.Seg}
  %Equal.sym(Bool, Eng.clean.go(Bytes.to_list(r), True{}), True{}, pg.clean(r, True{})(er)) :
    {L.Page{root, String.drop(r, 0n), Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
      Eng.page.pick(root, Eng.fnames.gate(_,
        Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(True{}, c0, pg.K(r)))))), head) : L.Seg}
  %Equal.sym(Bytes(), String.drop(r, 0n), r, pg.drop0(r)) :
    {L.Page{root, _, Eng.mime.head(Bytes.from_list(Eng.ext.buf(r, Nil{}))), Nil{}, head} ==
      Eng.page.pick(root, Eng.fnames.guard(False{}, Eng.norm(Eng.segs.out(Eng.segs.at(True{}, c0, pg.K(r))))), head) :
      L.Seg}
  pg.fin(root, r, head, c0, pg.K(r), pg.lead(r)(er), pg.join(r, True{})(er), pg.ok(r, True{})(er),
    pg.ext(r, True{}, Nil{})(er))

def pg.fast(root: Bytes(), t: Bytes(), head: Bool) ->
  {Eng.fast(t) == True{} : Bool} ->
  {Eng.page.go(root, t, head, True{}) == Eng.page.spec(root, Bytes.to_list(t), head) : L.Seg}:
  match t:
    case SNil{}:
      e => no({Eng.page.go(root, SNil{}, head, True{}) == Eng.page.spec(root, Bytes.to_list(SNil{}), head) :
        L.Seg}, e)
    case SCon{Chr{+c0}, +r}:
      +e => pg.fast.at(root, c0, r, head, e)

def pg.page(root: Bytes(), +t: Bytes(), head: Bool, b: Bool) ->
  {Eng.fast(t) == b : Bool} ->
  {Eng.page.go(root, t, head, b) == Eng.page.spec(root, Bytes.to_list(t), head) : L.Seg}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e => pg.fast(root, t, head)(e)

def Laws.page_is_spec(root, t, head):
  pg.page(root, t, head, Eng.fast(t))({==})


# Heads built in place are their pieces
# =====================================
#
# A writer f appends s: whatever the buffer a, f(a) is a followed by s.
# Writers compose, each appending after the last, and a chain of them
# appends its pieces joined; so each head cond.bend grows in place is the
# list of pieces hd.*.is names, joined.
def cd.app_assoc(+a: Bytes(), -b: Bytes(), -c: Bytes()) ->
  {Bytes.append(Bytes.append(a, b), c) == Bytes.append(a, Bytes.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %cd.app_assoc(t, b, c) : {SCon{h, Bytes.append(Bytes.append(t, b), c)} == SCon{h, _} : Bytes()}
      {==}

def cd.Is(-f: Bytes() -> Bytes(), -s: Bytes()) -> Type:
  @+a: Bytes() -> {f(a) == Bytes.append(a, s) : Bytes()}

def cd.cmp(f: Bytes() -> Bytes(), -s: Bytes(), -g: Bytes() -> Bytes(), -t: Bytes(),
  wf: cd.Is(f, s), wg: cd.Is(g, t)) -> cd.Is(a => g(f(a)), Bytes.append(s, t)):
  +a => Equal.trans(Bytes(), g(f(a)), Bytes.append(f(a), t), Bytes.append(a, Bytes.append(s, t)),
    wg(f(a)),
    Equal.trans(Bytes(), Bytes.append(f(a), t), Bytes.append(Bytes.append(a, s), t),
      Bytes.append(a, Bytes.append(s, t)),
      Equal.cong(Bytes(), Bytes(), x => Bytes.append(x, t), f(a), Bytes.append(a, s), wf(a)),
      cd.app_assoc(a, s, t)))

def cd.id() -> cd.Is(a => a, ""):
  +a => Equal.sym(Bytes(), Bytes.append(a, ""), a, WW.wl.app_nil(a))

def cd.push(-c: U32) -> cd.Is(a => Bytes.push(a, c), SCon{Chr{c}, SNil{}}):
  +a => {==}

def cd.app(-s: Bytes()) -> cd.Is(a => Bytes.append(a, s), s):
  +a => {==}

# a writer's pieces are what it writes into nothing
def cd.fix(f: Bytes() -> Bytes(), -s: Bytes(), w: cd.Is(f, s), w2: cd.Is(f, s)) -> cd.Is(f, f("")):
  +a => %Equal.sym(Bytes(), f(""), s, w2("")) : {f(a) == Bytes.append(a, _) : Bytes()}
    w(a)

def cd.p2.qr(ab: Nat & Nat) -> cd.Is(a => C.p2.qr(a, ab), C.d2.qr(ab)):
  match ab:
    case (x, y):
      +a => cd.app_assoc(a, SCon{Chr{C.dig(x)}, SNil{}}, SCon{Chr{C.dig(y)}, SNil{}})

def cd.p2(+n: Nat) -> cd.Is(a => C.p2(a, n), C.d2(n)):
  cd.p2.qr(Nat.divmod(n, 10n))

def cd.num.go(+f: Nat, +b: Nat, qr: Nat & Nat) -> cd.Is(a => C.num.go(f, b, a, qr), C.num.go(f, b, "", qr)):
  match f:
    case 0n:
      cd.id()
    case 1n+g:
      match qr:
        case (+q, +r):
          match q:
            case 0n:
              cd.push(C.hdig(r))
            case 1n+p:
              cd.cmp(a => C.num.go(g, b, a, Nat.divmod(1n+p, b)), C.num.go(g, b, "", Nat.divmod(1n+p, b)),
                a => Bytes.push(a, C.hdig(r)), SCon{Chr{C.hdig(r)}, SNil{}},
                cd.num.go(g, b, Nat.divmod(1n+p, b)), cd.push(C.hdig(r)))

def cd.num(+n: Nat) -> cd.Is(a => C.num.into(a, n), C.num(n)):
  cd.num.go(20n, 10n, Nat.divmod(n, 10n))

def cd.hex.go(+f: Nat, on: Bool, +x: U32) -> cd.Is(a => C.hex.go(f, on, x, a), C.hex.go(f, on, x, "")):
  match f:
    case 0n:
      cd.id()
    case 1n+g:
      match on:
        case True{}:
          +a => Equal.trans(Bytes(),
            C.hex.go(g, True{}, x, Bytes.push(a, C.hdig(U32.to_nat(C.nib(x, g))))),
            Bytes.append(Bytes.push(a, C.hdig(U32.to_nat(C.nib(x, g)))), C.hex.go(g, True{}, x, "")),
            Bytes.append(a, C.hex.go(g, True{}, x, Bytes.push("", C.hdig(U32.to_nat(C.nib(x, g)))))),
            cd.hex.go(g, True{}, x)(Bytes.push(a, C.hdig(U32.to_nat(C.nib(x, g))))),
            Equal.trans(Bytes(),
              Bytes.append(Bytes.push(a, C.hdig(U32.to_nat(C.nib(x, g)))), C.hex.go(g, True{}, x, "")),
              Bytes.append(a, Bytes.append(SCon{Chr{C.hdig(U32.to_nat(C.nib(x, g)))}, SNil{}}, C.hex.go(g, True{}, x, ""))),
              Bytes.append(a, C.hex.go(g, True{}, x, Bytes.push("", C.hdig(U32.to_nat(C.nib(x, g)))))),
              cd.app_assoc(a, SCon{Chr{C.hdig(U32.to_nat(C.nib(x, g)))}, SNil{}}, C.hex.go(g, True{}, x, "")),
              Equal.cong(Bytes(), Bytes(), y => Bytes.append(a, y),
                Bytes.append(SCon{Chr{C.hdig(U32.to_nat(C.nib(x, g)))}, SNil{}}, C.hex.go(g, True{}, x, "")),
                C.hex.go(g, True{}, x, Bytes.push("", C.hdig(U32.to_nat(C.nib(x, g))))),
                Equal.sym(Bytes(),
                  C.hex.go(g, True{}, x, Bytes.push("", C.hdig(U32.to_nat(C.nib(x, g))))),
                  Bytes.append(SCon{Chr{C.hdig(U32.to_nat(C.nib(x, g)))}, SNil{}}, C.hex.go(g, True{}, x, "")),
                  cd.hex.go(g, True{}, x)(SCon{Chr{C.hdig(U32.to_nat(C.nib(x, g)))}, SNil{}})))))
        case False{}:
          cd.hex.go(g, C.hex.on(x, g), x)

def cd.hex(+x: U32) -> cd.Is(a => C.hex(a, x), C.hex("", x)):
  cd.hex.go(8n, C.hex.on(x, 8n), x)

def cd.etag(+mt: U32, +n: U32) -> cd.Is(a => C.etag.into(a, mt, n), C.etag.of(mt, n)):
  cd.fix(a => C.etag.into(a, mt, n), Bytes.append(SCon{Chr{34}, SNil{}}, Bytes.append(C.hex("", mt), Bytes.append(SCon{Chr{45}, SNil{}}, Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}})))),
    cd.cmp(z => Bytes.push(z, 34), SCon{Chr{34}, SNil{}},
      z => Bytes.push(C.hex(Bytes.push(C.hex(z, mt), 45), n), 34), Bytes.append(C.hex("", mt), Bytes.append(SCon{Chr{45}, SNil{}}, Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}}))),
      cd.push(34),
      cd.cmp(z => C.hex(z, mt), C.hex("", mt),
        z => Bytes.push(C.hex(Bytes.push(z, 45), n), 34), Bytes.append(SCon{Chr{45}, SNil{}}, Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}})),
        cd.hex(mt),
        cd.cmp(z => Bytes.push(z, 45), SCon{Chr{45}, SNil{}},
          z => Bytes.push(C.hex(z, n), 34), Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}}),
          cd.push(45),
          cd.cmp(z => C.hex(z, n), C.hex("", n),
            z => Bytes.push(z, 34), SCon{Chr{34}, SNil{}},
            cd.hex(n),
            cd.push(34))))),
    cd.cmp(z => Bytes.push(z, 34), SCon{Chr{34}, SNil{}},
      z => Bytes.push(C.hex(Bytes.push(C.hex(z, mt), 45), n), 34), Bytes.append(C.hex("", mt), Bytes.append(SCon{Chr{45}, SNil{}}, Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}}))),
      cd.push(34),
      cd.cmp(z => C.hex(z, mt), C.hex("", mt),
        z => Bytes.push(C.hex(Bytes.push(z, 45), n), 34), Bytes.append(SCon{Chr{45}, SNil{}}, Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}})),
        cd.hex(mt),
        cd.cmp(z => Bytes.push(z, 45), SCon{Chr{45}, SNil{}},
          z => Bytes.push(C.hex(z, n), 34), Bytes.append(C.hex("", n), SCon{Chr{34}, SNil{}}),
          cd.push(45),
          cd.cmp(z => C.hex(z, n), C.hex("", n),
            z => Bytes.push(z, 34), SCon{Chr{34}, SNil{}},
            cd.hex(n),
            cd.push(34))))))

def cd.y(yy: Nat & Nat, -tf: Bytes() -> Bytes(), -ts: List<&2, Bytes()>, wt: cd.Is(tf, Bytes.concat(ts))) ->
  cd.Is(a => tf(C.di.y(a, yy)), Bytes.concat(C.date.y(yy, ts))):
  match yy:
    case (+p, +q):
      cd.cmp(z => C.p2(z, p), C.d2(p),
        z => tf(Bytes.push(C.p2(z, q), 32)), Bytes.append(C.d2(q), Bytes.append(SCon{Chr{32}, SNil{}}, Bytes.concat(ts))),
        cd.p2(p),
        cd.cmp(z => C.p2(z, q), C.d2(q),
          z => tf(Bytes.push(z, 32)), Bytes.append(SCon{Chr{32}, SNil{}}, Bytes.concat(ts)),
          cd.p2(q),
          cd.cmp(z => Bytes.push(z, 32), SCon{Chr{32}, SNil{}},
            z => tf(z), Bytes.concat(ts),
            cd.push(32),
            wt)))

def cd.ymd.jd(+k: Nat, jd: Nat & Nat, -tf: Bytes() -> Bytes(), -ts: List<&2, Bytes()>,
  wt: cd.Is(tf, Bytes.concat(ts))) ->
  cd.Is(a => tf(C.di.ymd(a, (k, jd))), Bytes.concat(C.date.ymd((k, jd), ts))):
  match jd:
    case (+j, +d):
      cd.cmp(z => C.p2(z, 1n+d), C.d2(1n+d),
        z => tf(C.di.y(Bytes.append(Bytes.push(z, 32), C.nth(C.monc(), j)), Nat.divmod(Nat.add(k, 1970n), 100n))), Bytes.append(SCon{Chr{32}, SNil{}}, Bytes.append(C.nth(C.monc(), j), Bytes.concat(C.date.y(Nat.divmod(Nat.add(k, 1970n), 100n), ts)))),
        cd.p2(1n+d),
        cd.cmp(z => Bytes.push(z, 32), SCon{Chr{32}, SNil{}},
          z => tf(C.di.y(Bytes.append(z, C.nth(C.monc(), j)), Nat.divmod(Nat.add(k, 1970n), 100n))), Bytes.append(C.nth(C.monc(), j), Bytes.concat(C.date.y(Nat.divmod(Nat.add(k, 1970n), 100n), ts))),
          cd.push(32),
          cd.cmp(z => Bytes.append(z, C.nth(C.monc(), j)), C.nth(C.monc(), j),
            z => tf(C.di.y(z, Nat.divmod(Nat.add(k, 1970n), 100n))), Bytes.concat(C.date.y(Nat.divmod(Nat.add(k, 1970n), 100n), ts)),
            cd.app(C.nth(C.monc(), j)),
            cd.y(Nat.divmod(Nat.add(k, 1970n), 100n), tf, ts, wt))))

def cd.ymd(kjd: Nat & Nat & Nat, -tf: Bytes() -> Bytes(), -ts: List<&2, Bytes()>, wt: cd.Is(tf, Bytes.concat(ts))) ->
  cd.Is(a => tf(C.di.ymd(a, kjd)), Bytes.concat(C.date.ymd(kjd, ts))):
  match kjd:
    case (+k, jd):
      cd.ymd.jd(k, jd, tf, ts, wt)

def cd.ds(+days: Nat, +h: Nat, +m: Nat, +x: Nat) ->
  cd.Is(a => C.di.ds(a, days, h, m, x), Bytes.concat(C.date.ds(days, h, m, x))):
  cd.cmp(z => Bytes.append(z, C.nth(C.wkc(), Nat.mod(Nat.add(4n, days), 7n))), C.nth(C.wkc(), Nat.mod(Nat.add(4n, days), 7n)),
    z => Bytes.append(C.p2(Bytes.push(C.p2(Bytes.push(C.p2(C.di.ymd(z, C.civil(days)), h), 58), m), 58), x), " GMT"), Bytes.concat(C.date.ymd(C.civil(days), [C.d2(h), ":", C.d2(m), ":", C.d2(x), " GMT"])),
    cd.app(C.nth(C.wkc(), Nat.mod(Nat.add(4n, days), 7n))),
    cd.ymd(C.civil(days), b => Bytes.append(C.p2(Bytes.push(C.p2(Bytes.push(C.p2(b, h), 58), m), 58), x), " GMT"), [C.d2(h), ":", C.d2(m), ":", C.d2(x), " GMT"],
    cd.cmp(z => C.p2(z, h), C.d2(h),
      z => Bytes.append(C.p2(Bytes.push(C.p2(Bytes.push(z, 58), m), 58), x), " GMT"), Bytes.append(SCon{Chr{58}, SNil{}}, Bytes.append(C.d2(m), Bytes.append(SCon{Chr{58}, SNil{}}, Bytes.append(C.d2(x), Bytes.append(" GMT", ""))))),
      cd.p2(h),
      cd.cmp(z => Bytes.push(z, 58), SCon{Chr{58}, SNil{}},
        z => Bytes.append(C.p2(Bytes.push(C.p2(z, m), 58), x), " GMT"), Bytes.append(C.d2(m), Bytes.append(SCon{Chr{58}, SNil{}}, Bytes.append(C.d2(x), Bytes.append(" GMT", "")))),
        cd.push(58),
        cd.cmp(z => C.p2(z, m), C.d2(m),
          z => Bytes.append(C.p2(Bytes.push(z, 58), x), " GMT"), Bytes.append(SCon{Chr{58}, SNil{}}, Bytes.append(C.d2(x), Bytes.append(" GMT", ""))),
          cd.p2(m),
          cd.cmp(z => Bytes.push(z, 58), SCon{Chr{58}, SNil{}},
            z => Bytes.append(C.p2(z, x), " GMT"), Bytes.append(C.d2(x), Bytes.append(" GMT", "")),
            cd.push(58),
            cd.cmp(z => C.p2(z, x), C.d2(x),
              z => Bytes.append(z, " GMT"), Bytes.append(" GMT", ""),
              cd.p2(x),
              cd.cmp(z => Bytes.append(z, " GMT"), " GMT",
                z => z, "",
                cd.app(" GMT"),
                cd.id()))))))))

def cd.q3(+m: Nat, +x: Nat, dh: Nat & Nat) -> cd.Is(a => C.di.q3(a, m, x, dh), C.date.q3(m, x, dh)):
  match dh:
    case (+days, +h):
      cd.ds(days, h, m, x)

def cd.q2(+x: Nat, hm: Nat & Nat) -> cd.Is(a => C.di.q2(a, x, hm), C.date.q2(x, hm)):
  match hm:
    case (+hs, +m):
      cd.q3(m, x, Nat.divmod(hs, 24n))

def cd.q1(mx: Nat & Nat) -> cd.Is(a => C.di.q1(a, mx), C.date.q1(mx)):
  match mx:
    case (+ms, +x):
      cd.q2(x, Nat.divmod(ms, 60n))

def cd.date(+t: Nat) -> cd.Is(a => C.date.into(a, t), C.date.fmt(t)):
  cd.q1(Nat.divmod(t, 60n))

def cd.vals(+mt: U32, +n: U32, -tf: Bytes() -> Bytes(), -ts: List<&2, Bytes()>, wt: cd.Is(tf, Bytes.concat(ts))) ->
  cd.Is(a => tf(C.vals(a, mt, n)), Bytes.concat(C.vals.is(mt, n, ts))):
  cd.cmp(z => Bytes.append(z, "\r\nlast-modified: "), "\r\nlast-modified: ",
    z => tf(C.etag.into(Bytes.append(C.date.into(z, U32.to_nat(mt)), "\r\netag: "), mt, n)), Bytes.append(C.date.fmt(U32.to_nat(mt)), Bytes.append("\r\netag: ", Bytes.append(C.etag.of(mt, n), Bytes.concat(ts)))),
    cd.app("\r\nlast-modified: "),
    cd.cmp(z => C.date.into(z, U32.to_nat(mt)), C.date.fmt(U32.to_nat(mt)),
      z => tf(C.etag.into(Bytes.append(z, "\r\netag: "), mt, n)), Bytes.append("\r\netag: ", Bytes.append(C.etag.of(mt, n), Bytes.concat(ts))),
      cd.date(U32.to_nat(mt)),
      cd.cmp(z => Bytes.append(z, "\r\netag: "), "\r\netag: ",
        z => tf(C.etag.into(z, mt, n)), Bytes.append(C.etag.of(mt, n), Bytes.concat(ts)),
        cd.app("\r\netag: "),
        cd.cmp(z => C.etag.into(z, mt, n), C.etag.of(mt, n),
          z => tf(z), Bytes.concat(ts),
          cd.etag(mt, n),
          wt))))

def cd.full(ct: Bytes(), +n: U32, +mt: U32) -> {C.hd.full(ct, n, mt) == C.hd.full.is(ct, n, mt) : Bytes()}:
  (cd.cmp(z => Bytes.append(z, ct), ct,
      z => Bytes.append(C.vals(C.num.into(z, U32.to_nat(n)), mt, n), C.ranges()), Bytes.append(C.num(U32.to_nat(n)), Bytes.concat(C.vals.is(mt, n, [C.ranges()]))),
      cd.app(ct),
      cd.cmp(z => C.num.into(z, U32.to_nat(n)), C.num(U32.to_nat(n)),
        z => Bytes.append(C.vals(z, mt, n), C.ranges()), Bytes.concat(C.vals.is(mt, n, [C.ranges()])),
        cd.num(U32.to_nat(n)),
        cd.vals(mt, n, b => Bytes.append(b, C.ranges()), [C.ranges()],
      cd.cmp(z => Bytes.append(z, C.ranges()), C.ranges(),
        z => z, "",
        cd.app(C.ranges()),
        cd.id())))))("")

def cd.same(+mt: U32, +n: U32) -> {C.hd.same(mt, n) == C.hd.same.is(mt, n) : Bytes()}:
  (cd.cmp(z => Bytes.append(z, "HTTP/1.1 304 Not Modified"), "HTTP/1.1 304 Not Modified",
      z => Bytes.append(C.vals(z, mt, n), C.ka()), Bytes.concat(C.vals.is(mt, n, [C.ka()])),
      cd.app("HTTP/1.1 304 Not Modified"),
      cd.vals(mt, n, b => Bytes.append(b, C.ka()), [C.ka()],
      cd.cmp(z => Bytes.append(z, C.ka()), C.ka(),
        z => z, "",
        cd.app(C.ka()),
        cd.id()))))("")

def cd.part(+ct: Bytes(), +a: Nat, +b: Nat, +n: U32, +mt: U32) ->
  {C.hd.part(ct, a, b, n, mt) == C.hd.part.is(ct, a, b, n, mt) : Bytes()}:
  (cd.cmp(z => Bytes.append(z, "HTTP/1.1 206 Partial Content\r\n"), "HTTP/1.1 206 Partial Content\r\n",
      z => Bytes.append(C.vals(Bytes.append(Bytes.append(Bytes.append(z, Bytes.drop(ct, 17n)), C.num(Nat.sub(1n+b, a))), Bytes.concat(C.crange(a, b, U32.to_nat(n)))), mt, n), C.ka()), Bytes.append(Bytes.drop(ct, 17n), Bytes.append(C.num(Nat.sub(1n+b, a)), Bytes.append(Bytes.concat(C.crange(a, b, U32.to_nat(n))), Bytes.concat(C.vals.is(mt, n, [C.ka()]))))),
      cd.app("HTTP/1.1 206 Partial Content\r\n"),
      cd.cmp(z => Bytes.append(z, Bytes.drop(ct, 17n)), Bytes.drop(ct, 17n),
        z => Bytes.append(C.vals(Bytes.append(Bytes.append(z, C.num(Nat.sub(1n+b, a))), Bytes.concat(C.crange(a, b, U32.to_nat(n)))), mt, n), C.ka()), Bytes.append(C.num(Nat.sub(1n+b, a)), Bytes.append(Bytes.concat(C.crange(a, b, U32.to_nat(n))), Bytes.concat(C.vals.is(mt, n, [C.ka()])))),
        cd.app(Bytes.drop(ct, 17n)),
        cd.cmp(z => Bytes.append(z, C.num(Nat.sub(1n+b, a))), C.num(Nat.sub(1n+b, a)),
          z => Bytes.append(C.vals(Bytes.append(z, Bytes.concat(C.crange(a, b, U32.to_nat(n)))), mt, n), C.ka()), Bytes.append(Bytes.concat(C.crange(a, b, U32.to_nat(n))), Bytes.concat(C.vals.is(mt, n, [C.ka()]))),
          cd.app(C.num(Nat.sub(1n+b, a))),
          cd.cmp(z => Bytes.append(z, Bytes.concat(C.crange(a, b, U32.to_nat(n)))), Bytes.concat(C.crange(a, b, U32.to_nat(n))),
            z => Bytes.append(C.vals(z, mt, n), C.ka()), Bytes.concat(C.vals.is(mt, n, [C.ka()])),
            cd.app(Bytes.concat(C.crange(a, b, U32.to_nat(n)))),
            cd.vals(mt, n, b => Bytes.append(b, C.ka()), [C.ka()],
      cd.cmp(z => Bytes.append(z, C.ka()), C.ka(),
        z => z, "",
        cd.app(C.ka()),
        cd.id())))))))("")

# file_head_is_built: every row of the table, and the row for what no
# row names, keeps the head mime.pre builds from its type's name; so
# does whichever row the lookup lands on. A request that asks nothing
# of the file is decided Full, and the head built in place is hd.full.is.
def pg.FH(m: Eng.Mime) -> Type:
  {Eng.mime.head.of(m) == Eng.mime.pre(Eng.mime.name.of(m)) : Bytes()}

def pg.fh.row(hit: Bool, m: Eng.Mime, a: pg.FH(m)) -> pg.FH(Eng.mime.row(hit, m)):
  match hit:
    case True{}:
      a
    case False{}:
      {==}

def pg.fh.at.pdf(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.pdf(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "pdf"), Eng.mime.pdf(), {==})
    case False{}:
      {==}

def pg.fh.at.wasm(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.wasm(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "wasm"), Eng.mime.wasm(), {==})
    case False{}:
      pg.fh.at.pdf(U32.is_eq(k, 7366147), k, e)

def pg.fh.at.ico(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.ico(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "ico"), Eng.mime.ico(), {==})
    case False{}:
      pg.fh.at.wasm(U32.is_eq(k, 7826692), k, e)

def pg.fh.at.gif(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.gif(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "gif"), Eng.mime.gif(), {==})
    case False{}:
      pg.fh.at.ico(U32.is_eq(k, 6909699), k, e)

def pg.fh.at.jpeg(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.jpeg(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "jpeg"), Eng.mime.jpeg(), {==})
    case False{}:
      pg.fh.at.gif(U32.is_eq(k, 6776323), k, e)

def pg.fh.at.jpg(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.jpg(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "jpg"), Eng.mime.jpg(), {==})
    case False{}:
      pg.fh.at.jpeg(U32.is_eq(k, 6973188), k, e)

def pg.fh.at.png(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.png(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "png"), Eng.mime.png(), {==})
    case False{}:
      pg.fh.at.jpg(U32.is_eq(k, 6973187), k, e)

def pg.fh.at.svg(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.svg(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "svg"), Eng.mime.svg(), {==})
    case False{}:
      pg.fh.at.png(U32.is_eq(k, 7366403), k, e)

def pg.fh.at.txt(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.txt(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "txt"), Eng.mime.txt(), {==})
    case False{}:
      pg.fh.at.svg(U32.is_eq(k, 7563011), k, e)

def pg.fh.at.json(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.json(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "json"), Eng.mime.json(), {==})
    case False{}:
      pg.fh.at.txt(U32.is_eq(k, 7631875), k, e)

def pg.fh.at.js(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.js(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "js"), Eng.mime.js(), {==})
    case False{}:
      pg.fh.at.json(U32.is_eq(k, 6974980), k, e)

def pg.fh.at.css(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.css(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "css"), Eng.mime.css(), {==})
    case False{}:
      pg.fh.at.js(U32.is_eq(k, 6976258), k, e)

def pg.fh.at.htm(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.htm(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "htm"), Eng.mime.htm(), {==})
    case False{}:
      pg.fh.at.css(U32.is_eq(k, 6517507), k, e)

def pg.fh.at.html(hit: Bool, +k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at.html(hit, k, e)):
  match hit:
    case True{}:
      pg.fh.row(Eng.bytes.eq(e, "html"), Eng.mime.html(), {==})
    case False{}:
      pg.fh.at.htm(U32.is_eq(k, 6843651), k, e)

def pg.fh.at(+k: U32, +e: Bytes()) -> pg.FH(Eng.mime.at(k, e)):
  pg.fh.at.html(U32.is_eq(k, 6843396), k, e)

def Laws.file_head_is_built(e, head, n, mt):
  %pg.fh.at(Eng.mime.key(e), e) :
    {Eng.h.fhead(Eng.mime.head(e), Nil{}, head, n, mt) == L.Fr{C.hd.full.is(_, n, mt), 0, n} : L.Fr}
  %cd.full(Eng.mime.head(e), n, mt) : {Eng.h.fhead(Eng.mime.head(e), Nil{}, head, n, mt) == L.Fr{_, 0, n} : L.Fr}
  {==}

# Conditional and range requests
# ==============================
#
# The proofs of cond.bend's laws: Nat and division as they need them,
# the calendar there and back, the date's pieces read by their tokens,
# the round trip, and the ranges in the file.

# Nat, as the proofs of cond.bend need it
# ========================================

def cp.no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  Bool.no(g, e)

def cp.add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, cp.add_zero(p))

def cp.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), cp.add_succ(p, b))

def cp.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, cp.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), cp.add_succ(b, p)) :
        {1n+Nat.add(p, b) == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), cp.add_comm(p, b))

def cp.add_assoc(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
        cp.add_assoc(p, b, c))

def cp.le0(+b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def cp.le_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cp.le_succ(p)

# a <= a + b
def cp.le_add(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      cp.le0(b)
    case 1n+p:
      cp.le_add(p, b)

# b <= a + b
def cp.le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), cp.add_comm(a, b)) :
    {Nat.is_le(b, _) == True{} : Bool}
  cp.le_add(b, a)

def cp.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cp.le_refl(p)

# l <= r: l + (r - l) is r
def cp.add_sub(+l: Nat, +r: Nat, e: {Nat.is_le(l, r) == True{} : Bool}) ->
  {Nat.add(l, Nat.sub(r, l)) == r : Nat}:
  match l r:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      cp.no({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, cp.add_sub(p, q, e))

def cp.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a - b <= a
def cp.sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      cp.le_refl(p)
    case 1n+p 1n+q:
      Nat.is_le_trans(Nat.sub(p, q), p, 1n+p, cp.sub_le(p, q), cp.le_succ(p))

# Division
# ========
#
# Nat.divmod(a, b) is a quotient and a remainder: q * b + r is a, and r is
# below b. Its walk counts a down, and a countdown m from b - 1 beside a
# remainder r so far, their sum b - 1 throughout.
def cp.dm(+b: Nat, +a: Nat, p: Nat & Nat) -> Type:
  (q, r) = p
  {Nat.add(Nat.mul(q, b), r) == a : Nat} & {Nat.is_lt(r, b) == True{} : Bool}

def cp.dm.lt(+r: Nat, +m: Nat, +bp: Nat, inv: {Nat.add(m, r) == bp : Nat}) ->
  {Nat.is_lt(r, 1n+bp) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(r, 1n+bp), Nat.is_le(r, bp), Nat.lt_succ(r, bp)) : {_ == True{} : Bool}
  %inv : {Nat.is_le(r, _) == True{} : Bool}
  cp.le_add_l(m, r)

def cp.dm.e0(+M: Nat, +bp: Nat, +np: Nat) ->
  {Nat.add(Nat.add(Nat.add(1n+bp, M), 0n), np) == Nat.add(Nat.add(M, bp), 1n+np) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(1n+bp, M), 0n), Nat.add(1n+bp, M), cp.add_zero(Nat.add(1n+bp, M))) :
    {Nat.add(_, np) == Nat.add(Nat.add(M, bp), 1n+np) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(M, bp), 1n+np), 1n+Nat.add(Nat.add(M, bp), np),
    cp.add_succ(Nat.add(M, bp), np)) :
    {1n+Nat.add(Nat.add(bp, M), np) == _ : Nat}
  %cp.add_comm(bp, M) : {1n+Nat.add(Nat.add(bp, M), np) == 1n+Nat.add(_, np) : Nat}
  {==}

# with r the countdown's full length: the step that closes a quotient
def cp.dm.e0r(+M: Nat, +r: Nat, +bp: Nat, +np: Nat, inv: {r == bp : Nat}) ->
  {Nat.add(Nat.add(M, r), 1n+np) == Nat.add(Nat.add(Nat.add(1n+bp, M), 0n), np) : Nat}:
  %Equal.sym(Nat, r, bp, inv) : {Nat.add(Nat.add(M, _), 1n+np) == Nat.add(Nat.add(Nat.add(1n+bp, M), 0n), np) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(Nat.add(1n+bp, M), 0n), np), Nat.add(Nat.add(M, bp), 1n+np),
    cp.dm.e0(M, bp, np))

def cp.dm.e1(+M: Nat, +r: Nat, +np: Nat) ->
  {Nat.add(Nat.add(M, 1n+r), np) == Nat.add(Nat.add(M, r), 1n+np) : Nat}:
  %Equal.sym(Nat, Nat.add(M, 1n+r), 1n+Nat.add(M, r), cp.add_succ(M, r)) :
    {Nat.add(_, np) == Nat.add(Nat.add(M, r), 1n+np) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(M, r), 1n+np), 1n+Nat.add(Nat.add(M, r), np),
    cp.add_succ(Nat.add(M, r), np))

law cp.dm_go:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +bp: Nat
  for +inv: {Nat.add(m, r) == bp : Nat}
  cp.dm(1n+bp, Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), n), Nat.divmod.go(n, m, d, r))

def cp.dm_go(n, m, d, r, bp, inv):
  match n:
    case 0n:
      (Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 0n), Nat.add(Nat.mul(d, 1n+bp), r),
        cp.add_zero(Nat.add(Nat.mul(d, 1n+bp), r))), cp.dm.lt(r, m, bp, inv))
    case 1n+np:
      match m:
        case 0n:
          %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 1n+np),
            Nat.add(Nat.add(Nat.mul(1n+d, 1n+bp), 0n), np),
            cp.dm.e0r(Nat.mul(d, 1n+bp), r, bp, np, inv)) :
            cp.dm(1n+bp, _, Nat.divmod.go(np, r, 1n+d, 0n))
          cp.dm_go(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, cp.add_zero(r), inv))
        case 1n+mp:
          %cp.dm.e1(Nat.mul(d, 1n+bp), r, np) :
            cp.dm(1n+bp, _, Nat.divmod.go(np, mp, d, 1n+r))
          cp.dm_go(np, mp, d, 1n+r, bp,
            Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, cp.add_succ(mp, r), inv))

# LAW: a quotient and a remainder, for every a and every b
def cp.divmod(+a: Nat, +bp: Nat) -> cp.dm(1n+bp, a, Nat.divmod(a, 1n+bp)):
  cp.dm_go(a, bp, 0n, 0n, bp, cp.add_zero(bp))

# b + x <= b + y is x <= y
def cp.le_addl(+b: Nat, +x: Nat, +y: Nat) ->
  {Nat.is_le(Nat.add(b, x), Nat.add(b, y)) == Nat.is_le(x, y) : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      cp.le_addl(p, x, y)

# k <= q: k * b <= q * b
def cp.mul_le(+k: Nat, +q: Nat, +b: Nat, e: {Nat.is_le(k, q) == True{} : Bool}) ->
  {Nat.is_le(Nat.mul(k, b), Nat.mul(q, b)) == True{} : Bool}:
  match k:
    case 0n:
      cp.le0(Nat.mul(q, b))
    case 1n+kp:
      match q:
        case 0n:
          cp.no({Nat.is_le(Nat.mul(1n+kp, b), Nat.mul(0n, b)) == True{} : Bool}, e)
        case 1n+qp:
          %Equal.sym(Bool, Nat.is_le(Nat.add(b, Nat.mul(kp, b)), Nat.add(b, Nat.mul(qp, b))),
            Nat.is_le(Nat.mul(kp, b), Nat.mul(qp, b)), cp.le_addl(b, Nat.mul(kp, b), Nat.mul(qp, b))) :
            {_ == True{} : Bool}
          cp.mul_le(kp, qp, b, e)

# not a < b: b <= a
def cp.nlt(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  %Nat.lt_flip(a, b) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(a, b), False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

# a < b and b <= a cannot both hold
def cp.lt_le_no(-g: Type, +a: Nat, +b: Nat, lt: {Nat.is_lt(a, b) == True{} : Bool},
  le: {Nat.is_le(b, a) == True{} : Bool}) -> g:
  cp.no(g, Equal.trans(Bool, False{}, Nat.is_lt(a, b), True{},
    Equal.trans(Bool, False{}, Bool.not(Nat.is_le(b, a)), Nat.is_lt(a, b),
      Equal.cong(Bool, Bool, Bool.not, True{}, Nat.is_le(b, a), Equal.sym(Bool, Nat.is_le(b, a), True{}, le)),
      Nat.le_flip(b, a)),
    lt))

# a quotient is below k when its dividend is below k * b
def cp.qb.at(c: Bool, +q: Nat, +r: Nat, +a: Nat, +k: Nat, +b: Nat,
  eq: {Nat.add(Nat.mul(q, b), r) == a : Nat}, lt: {Nat.is_lt(a, Nat.mul(k, b)) == True{} : Bool}) ->
  {Nat.is_lt(q, k) == c : Bool} -> {Nat.is_lt(q, k) == True{} : Bool}:
  match c:
    case True{}:
      e => e
    case False{}:
      e => cp.lt_le_no({Nat.is_lt(q, k) == True{} : Bool}, a, Nat.mul(k, b), lt,
        Nat.is_le_trans(Nat.mul(k, b), Nat.mul(q, b), a, cp.mul_le(k, q, b, cp.nlt(q, k, e)),
          %eq : {Nat.is_le(Nat.mul(q, b), _) == True{} : Bool}
          cp.le_add(Nat.mul(q, b), r)))

def cp.qb(+q: Nat, +r: Nat, +a: Nat, +k: Nat, +b: Nat,
  eq: {Nat.add(Nat.mul(q, b), r) == a : Nat}, lt: {Nat.is_lt(a, Nat.mul(k, b)) == True{} : Bool}) ->
  {Nat.is_lt(q, k) == True{} : Bool}:
  cp.qb.at(Nat.is_lt(q, k), q, r, a, k, b, eq, lt)({==})

# x < 0 is never so
def cp.lt0(+x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cp.lt0.no(-g: Type, +x: Nat, lt: {Nat.is_lt(x, 0n) == True{} : Bool}) -> g:
  cp.no(g, Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, cp.lt0(x)), lt))

# Digits read back
# ================
#
# A digit written is read as itself: ten cases, each computed, and past
# nine the bound refutes itself.
def cp.dg(+a: Nat, +r: Bytes(), lt: {Nat.is_lt(a, 10n) == True{} : Bool}) ->
  {C.rd.dig(SCon{Chr{C.dig(a)}, r}) == Some{(a, r)} : Maybe<&1, Nat & Bytes()>}:
  match a:
    case 0n:
      {==}
    case 1n+a1:
      match a1:
        case 0n:
          {==}
        case 1n+a2:
          match a2:
            case 0n:
              {==}
            case 1n+a3:
              match a3:
                case 0n:
                  {==}
                case 1n+a4:
                  match a4:
                    case 0n:
                      {==}
                    case 1n+a5:
                      match a5:
                        case 0n:
                          {==}
                        case 1n+a6:
                          match a6:
                            case 0n:
                              {==}
                            case 1n+a7:
                              match a7:
                                case 0n:
                                  {==}
                                case 1n+a8:
                                  match a8:
                                    case 0n:
                                      {==}
                                    case 1n+a9:
                                      match a9:
                                        case 0n:
                                          {==}
                                        case 1n+a10:
                                          cp.lt0.no({C.rd.dig(SCon{Chr{C.dig(10n+a10)}, r}) == Some{(10n+a10, r)} : Maybe<&1, Nat & Bytes()>}, a10, lt)

# two digits written are read as their number, for every number under 100
def cp.d2.ab(+a: Nat, +b: Nat, +n: Nat, +r: Bytes(), eq: {Nat.add(Nat.mul(a, 10n), b) == n : Nat},
  la: {Nat.is_lt(a, 10n) == True{} : Bool}, lb: {Nat.is_lt(b, 10n) == True{} : Bool}) ->
  {C.rd.d2(Bytes.append(C.d2.qr((a, b)), r)) == Some{(n, r)} : Maybe<&1, Nat & Bytes()>}:
  %Equal.sym(Maybe<&1, Nat & Bytes()>, C.rd.dig(SCon{Chr{C.dig(a)}, SCon{Chr{C.dig(b)}, r}}),
    Some{(a, SCon{Chr{C.dig(b)}, r})}, cp.dg(a, SCon{Chr{C.dig(b)}, r}, la)) :
    {C.rd.d2.a(_) == Some{(n, r)} : Maybe<&1, Nat & Bytes()>}
  %Equal.sym(Maybe<&1, Nat & Bytes()>, C.rd.dig(SCon{Chr{C.dig(b)}, r}), Some{(b, r)}, cp.dg(b, r, lb)) :
    {C.rd.d2.b(a, _) == Some{(n, r)} : Maybe<&1, Nat & Bytes()>}
  %eq : {Some{(Nat.add(Nat.mul(a, 10n), b), r)} == Some{(_, r)} : Maybe<&1, Nat & Bytes()>}
  {==}

def cp.d2.qr(p: Nat & Nat, +n: Nat, +r: Bytes(), dm: cp.dm(10n, n, p),
  lt: {Nat.is_lt(n, 100n) == True{} : Bool}) ->
  {C.rd.d2(Bytes.append(C.d2.qr(p), r)) == Some{(n, r)} : Maybe<&1, Nat & Bytes()>}:
  (+a, +b) = p
  (+eq, lb) = dm
  cp.d2.ab(a, b, n, r, eq, cp.qb(a, b, n, 10n, 10n, eq, lt), lb)

law cp.d2:
  for +n: Nat
  for +r: Bytes()
  for lt: {Nat.is_lt(n, 100n) == True{} : Bool}
  {C.rd.d2(Bytes.append(C.d2(n), r)) == Some{(n, r)} : Maybe<&1, Nat & Bytes()>}

def cp.d2(n, r, lt):
  cp.d2.qr(Nat.divmod(n, 10n), n, r, cp.divmod(n, 9n), lt)

# The calendar read back
# ======================

def cp.sum(ls: List<&2, Nat>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{l, t}:
      Nat.add(l, cp.sum(t))

# rem < l + s and l <= rem: rem - l < s
def cp.sub_lt(+l: Nat, +rem: Nat, +s: Nat, lt: {Nat.is_lt(rem, Nat.add(l, s)) == True{} : Bool},
  le: {Nat.is_le(l, rem) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(rem, l), s) == True{} : Bool}:
  match l:
    case 0n:
      %Equal.sym(Nat, Nat.sub(rem, 0n), rem, cp.sub_zero(rem)) : {Nat.is_lt(_, s) == True{} : Bool}
      lt
    case 1n+lp:
      match rem:
        case 0n:
          cp.no({Nat.is_lt(Nat.sub(0n, 1n+lp), s) == True{} : Bool}, le)
        case 1n+rp:
          cp.sub_lt(lp, rp, s, lt, le)

# a month walked one on: its place is one on, its day the same, and the
# days before it are the first month's more
def cp.mon.up(+l: Nat, +ls: List<&2, Nat>, jd: Nat & Nat, +x: Nat,
  e: {C.mdays.p(ls, jd) == Some{x} : Maybe<&2, Nat>}) ->
  {C.mdays.p(Con{l, ls}, C.mon.up(jd)) == Some{Nat.add(l, x)} : Maybe<&2, Nat>}:
  (j, d) = jd
  %Equal.sym(Maybe<&2, Nat>, C.mdays(ls, j, d), Some{x}, e) : {C.mdays.add(l, _) == Some{Nat.add(l, x)} : Maybe<&2, Nat>}
  {==}

def cp.lt_add0(+rem: Nat, +l: Nat, lt: {Nat.is_lt(rem, Nat.add(l, 0n)) == True{} : Bool}) ->
  {Nat.is_lt(rem, l) == True{} : Bool}:
  %cp.add_zero(l) : {Nat.is_lt(rem, _) == True{} : Bool}
  lt

# a day of the months, walked month by month, is the days before its
# month and its day
law cp.mon:
  for +t: List<&2, Nat>
  for +l: Nat
  for +rem: Nat
  for +c: Bool
  for +ec: {Nat.is_lt(rem, l) == c : Bool}
  for +lt: {Nat.is_lt(rem, Nat.add(l, cp.sum(t))) == True{} : Bool}
  {C.mdays.p(Con{l, t}, C.mon(t, l, c, rem)) == Some{rem} : Maybe<&2, Nat>}

def cp.mon(t, l, rem, c, ec, lt):
  match t:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_lt(rem, l), True{}, cp.lt_add0(rem, l, lt)) :
        {C.mdays.fit(_, rem) == Some{rem} : Maybe<&2, Nat>}
      {==}
    case Con{+l2, +t2}:
      match c:
        case True{}:
          %Equal.sym(Bool, Nat.is_lt(rem, l), True{}, ec) :
            {C.mdays.fit(_, rem) == Some{rem} : Maybe<&2, Nat>}
          {==}
        case False{}:
          +le = cp.nlt(rem, l, ec)
          +r2 = Nat.sub(rem, l)
          %cp.add_sub(l, rem, le) :
            {C.mdays.p(Con{l, Con{l2, t2}}, C.mon.up(C.mon(t2, l2, Nat.is_lt(r2, l2), r2))) == Some{_} :
              Maybe<&2, Nat>}
          cp.mon.up(l, Con{l2, t2}, C.mon(t2, l2, Nat.is_lt(r2, l2), r2), r2,
            cp.mon(t2, l2, r2, Nat.is_lt(r2, l2), {==}, cp.sub_lt(l, rem, Nat.add(l2, cp.sum(t2)), lt, le)))

def cp.cd(kjd: Nat & Nat & Nat) -> Maybe<&2, Nat>:
  (k, jd) = kjd
  C.days.of(k, jd)

# the day rem of year k, when the year has it: its month and its day are
# the days before them in that year
def cp.cal.mon(+lp: Bool, +k: Nat, +rem: Nat, el: {C.leap(k) == lp : Bool},
  lt: {Nat.is_lt(rem, C.ylen.of(lp)) == True{} : Bool}) ->
  {C.days.of(k, C.mon.of(C.mlens(C.leap(k)), rem)) == Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}:
  match lp:
    case True{}:
      %Equal.sym(Bool, C.leap(k), True{}, el) :
        {C.mdays.add(C.before(k), C.mdays.p(C.mlens(_), C.mon.of(C.mlens(_), rem))) ==
          Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>,
        C.mdays.p(C.mlens(True{}), C.mon([29n, 31n, 30n, 31n, 30n, 31n, 31n, 30n, 31n, 30n, 31n], 31n,
          Nat.is_lt(rem, 31n), rem)), Some{rem},
        cp.mon([29n, 31n, 30n, 31n, 30n, 31n, 31n, 30n, 31n, 30n, 31n], 31n, rem, Nat.is_lt(rem, 31n), {==},
          lt)) :
        {C.mdays.add(C.before(k), _) == Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, C.leap(k), False{}, el) :
        {C.mdays.add(C.before(k), C.mdays.p(C.mlens(_), C.mon.of(C.mlens(_), rem))) ==
          Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>,
        C.mdays.p(C.mlens(False{}), C.mon([28n, 31n, 30n, 31n, 30n, 31n, 31n, 30n, 31n, 30n, 31n], 31n,
          Nat.is_lt(rem, 31n), rem)), Some{rem},
        cp.mon([28n, 31n, 30n, 31n, 30n, 31n, 31n, 30n, 31n, 30n, 31n], 31n, rem, Nat.is_lt(rem, 31n), {==},
          lt)) :
        {C.mdays.add(C.before(k), _) == Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}
      {==}

# a year is at least a day: its length is one more than something
def cp.ylen.pos(+lp: Bool) -> {C.ylen.of(lp) == 1n+Nat.sub(C.ylen.of(lp), 1n) : Nat}:
  match lp:
    case True{}:
      {==}
    case False{}:
      {==}

# rem < 2 + g and y = 1 + yp: rem < y + (1 + g)
def cp.lt_two(+rem: Nat, +gp: Nat, +yp: Nat, lt: {Nat.is_lt(rem, 1n+1n+gp) == True{} : Bool}) ->
  {Nat.is_lt(rem, Nat.add(1n+yp, 1n+gp)) == True{} : Bool}:
  Nat.is_lt_le_trans(rem, 1n+1n+gp, Nat.add(1n+yp, 1n+gp), lt, cp.le_add_l(yp, 1n+gp))

# past year k: the days before year k + 1 and what is left are the days
# before year k and all of rem
def cp.cal.skip(+b: Nat, +y: Nat, +rem: Nat, le: {Nat.is_le(y, rem) == True{} : Bool}) ->
  {Nat.add(Nat.add(b, y), Nat.sub(rem, y)) == Nat.add(b, rem) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(b, y), Nat.sub(rem, y)), Nat.add(b, Nat.add(y, Nat.sub(rem, y))),
    cp.add_assoc(b, y, Nat.sub(rem, y))) : {_ == Nat.add(b, rem) : Nat}
  Equal.cong(Nat, Nat, x => Nat.add(b, x), Nat.add(y, Nat.sub(rem, y)), rem, cp.add_sub(y, rem, le))

# the walk of the years: from year k with rem days to go, what it lands
# on is the days before year k and rem, when the fuel covers rem
law cp.cal:
  for +g: Nat
  for +rem: Nat
  for +k: Nat
  for +c: Bool
  for +ec: {Nat.is_lt(rem, C.ylen(k)) == c : Bool}
  for +fuel: {Nat.is_lt(rem, 1n+g) == True{} : Bool}
  {cp.cd(C.cal(1n+g, c, rem, k, C.ylen(k))) == Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}

# year k has at least 365 days, so a first day of it is within it
def cp.cal.first(+lp: Bool) -> {Nat.is_lt(0n, C.ylen.of(lp)) == True{} : Bool}:
  match lp:
    case True{}:
      {==}
    case False{}:
      {==}

def cp.cal.zero(-g: Type, +rem: Nat, +k: Nat, ec: {Nat.is_lt(rem, C.ylen(k)) == False{} : Bool},
  fuel: {Nat.is_lt(rem, 1n) == True{} : Bool}) -> g:
  match rem:
    case 0n:
      cp.no(g, Equal.trans(Bool, False{}, Nat.is_lt(0n, C.ylen(k)), True{},
        Equal.sym(Bool, Nat.is_lt(0n, C.ylen(k)), False{}, ec), cp.cal.first(C.leap(k))))
    case 1n+rp:
      cp.lt0.no(g, rp, fuel)

def cp.cal(g, rem, k, c, ec, fuel):
  match g:
    case 0n:
      match c:
        case True{}:
          cp.cal.mon(C.leap(k), k, rem, {==}, ec)
        case False{}:
          cp.cal.zero({cp.cd(C.cal(1n, False{}, rem, k, C.ylen(k))) == Some{Nat.add(C.before(k), rem)} :
            Maybe<&2, Nat>}, rem, k, ec, fuel)
    case 1n+gp:
      match c:
        case True{}:
          cp.cal.mon(C.leap(k), k, rem, {==}, ec)
        case False{}:
          +le = cp.nlt(rem, C.ylen(k), ec)
          +r2 = Nat.sub(rem, C.ylen(k))
          %cp.cal.skip(C.before(k), C.ylen(k), rem, le) :
            {cp.cd(C.cal(1n+gp, Nat.is_lt(r2, C.ylen(1n+k)), r2, 1n+k, C.ylen(1n+k))) == Some{_} :
              Maybe<&2, Nat>}
          cp.cal(gp, r2, 1n+k, Nat.is_lt(r2, C.ylen(1n+k)), {==},
            cp.sub_lt(C.ylen(k), rem, 1n+gp,
              %Equal.sym(Nat, C.ylen.of(C.leap(k)), 1n+Nat.sub(C.ylen.of(C.leap(k)), 1n),
                cp.ylen.pos(C.leap(k))) : {Nat.is_lt(rem, Nat.add(_, 1n+gp)) == True{} : Bool}
              cp.lt_two(rem, gp, Nat.sub(C.ylen(k), 1n), fuel),
              le))

def cp.lt_self(+r: Nat) -> {Nat.is_lt(r, 1n+r) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(r, 1n+r), Nat.is_le(r, r), Nat.lt_succ(r, r)) : {_ == True{} : Bool}
  cp.le_refl(r)

# a walk started at year k, b days in, with days - b to go
# the rest of a day's walk, a year at a time from year k with r days to
# go: the days before year k and r
def cp.cf(+k: Nat, +r: Nat) -> {cp.cd(C.civil.from((k, r))) == Some{Nat.add(C.before(k), r)} : Maybe<&2, Nat>}:
  cp.cal(r, r, k, Nat.is_lt(r, C.ylen(k)), {==}, cp.lt_self(r))

# four years on: the days before them are the days before the first and
# the four years' lengths
def cp.four(q: Nat) -> Nat:
  match q:
    case 0n:
      0n
    case 1n+p:
      1n+1n+1n+1n+cp.four(p)

def cp.S4(+k: Nat) -> Nat:
  Nat.add(C.ylen(k), Nat.add(C.ylen(1n+k), Nat.add(C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k))))

def cp.b4(+k: Nat) -> {C.before(1n+1n+1n+1n+k) == Nat.add(C.before(k), cp.S4(k)) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(Nat.add(Nat.add(C.before(k), C.ylen(k)), C.ylen(1n+k)), C.ylen(1n+1n+k)), C.ylen(1n+1n+1n+k)),
    Nat.add(Nat.add(Nat.add(C.before(k), C.ylen(k)), C.ylen(1n+k)), Nat.add(C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k))),
    Nat.add(C.before(k), cp.S4(k)),
    cp.add_assoc(Nat.add(Nat.add(C.before(k), C.ylen(k)), C.ylen(1n+k)), C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k)),
    Equal.trans(Nat,
      Nat.add(Nat.add(Nat.add(C.before(k), C.ylen(k)), C.ylen(1n+k)), Nat.add(C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k))),
      Nat.add(Nat.add(C.before(k), C.ylen(k)), Nat.add(C.ylen(1n+k), Nat.add(C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k)))),
      Nat.add(C.before(k), cp.S4(k)),
      cp.add_assoc(Nat.add(C.before(k), C.ylen(k)), C.ylen(1n+k), Nat.add(C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k))),
      cp.add_assoc(C.before(k), C.ylen(k), Nat.add(C.ylen(1n+k), Nat.add(C.ylen(1n+1n+k), C.ylen(1n+1n+1n+k))))))

# each of the first 32 blocks from 1970 has 1461 days, counted by the
# checker block by block
def cp.s4(q0: Nat, lt: {Nat.is_lt(q0, 32n) == True{} : Bool}) -> {cp.S4(cp.four(q0)) == 1461n : Nat}:
  match q0:
    case 0n:
      {==}
    case 1n+q1:
      match q1:
        case 0n:
          {==}
        case 1n+q2:
          match q2:
            case 0n:
              {==}
            case 1n+q3:
              match q3:
                case 0n:
                  {==}
                case 1n+q4:
                  match q4:
                    case 0n:
                      {==}
                    case 1n+q5:
                      match q5:
                        case 0n:
                          {==}
                        case 1n+q6:
                          match q6:
                            case 0n:
                              {==}
                            case 1n+q7:
                              match q7:
                                case 0n:
                                  {==}
                                case 1n+q8:
                                  match q8:
                                    case 0n:
                                      {==}
                                    case 1n+q9:
                                      match q9:
                                        case 0n:
                                          {==}
                                        case 1n+q10:
                                          match q10:
                                            case 0n:
                                              {==}
                                            case 1n+q11:
                                              match q11:
                                                case 0n:
                                                  {==}
                                                case 1n+q12:
                                                  match q12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+q13:
                                                      match q13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+q14:
                                                          match q14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+q15:
                                                              match q15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+q16:
                                                                  match q16:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+q17:
                                                                      match q17:
                                                                        case 0n:
                                                                          {==}
                                                                        case 1n+q18:
                                                                          match q18:
                                                                            case 0n:
                                                                              {==}
                                                                            case 1n+q19:
                                                                              match q19:
                                                                                case 0n:
                                                                                  {==}
                                                                                case 1n+q20:
                                                                                  match q20:
                                                                                    case 0n:
                                                                                      {==}
                                                                                    case 1n+q21:
                                                                                      match q21:
                                                                                        case 0n:
                                                                                          {==}
                                                                                        case 1n+q22:
                                                                                          match q22:
                                                                                            case 0n:
                                                                                              {==}
                                                                                            case 1n+q23:
                                                                                              match q23:
                                                                                                case 0n:
                                                                                                  {==}
                                                                                                case 1n+q24:
                                                                                                  match q24:
                                                                                                    case 0n:
                                                                                                      {==}
                                                                                                    case 1n+q25:
                                                                                                      match q25:
                                                                                                        case 0n:
                                                                                                          {==}
                                                                                                        case 1n+q26:
                                                                                                          match q26:
                                                                                                            case 0n:
                                                                                                              {==}
                                                                                                            case 1n+q27:
                                                                                                              match q27:
                                                                                                                case 0n:
                                                                                                                  {==}
                                                                                                                case 1n+q28:
                                                                                                                  match q28:
                                                                                                                    case 0n:
                                                                                                                      {==}
                                                                                                                    case 1n+q29:
                                                                                                                      match q29:
                                                                                                                        case 0n:
                                                                                                                          {==}
                                                                                                                        case 1n+q30:
                                                                                                                          match q30:
                                                                                                                            case 0n:
                                                                                                                              {==}
                                                                                                                            case 1n+q31:
                                                                                                                              match q31:
                                                                                                                                case 0n:
                                                                                                                                  {==}
                                                                                                                                case 1n+q32:
                                                                                                                                  cp.lt0.no({cp.S4(cp.four(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q32)) == 1461n : Nat}, q32, lt)

def cp.s4k(+q: Nat, +k: Nat, ek: {k == cp.four(q) : Nat}, lt: {Nat.is_lt(q, 32n) == True{} : Bool}) ->
  {cp.S4(k) == 1461n : Nat}:
  %Equal.sym(Nat, k, cp.four(q), ek) : {cp.S4(_) == 1461n : Nat}
  cp.s4(q, lt)

# the walk by blocks: from block q (year k, the four(q)th), rem days to
# go, what it lands on is the days before year k and rem
def cp.blk(f: Nat, ok: Bool, +q: Nat, +k: Nat, +rem: Nat, +ek: {k == cp.four(q) : Nat},
  +eok: {Bool.and(Nat.is_lt(q, 32n), Nat.is_le(1461n, rem)) == ok : Bool}) ->
  {cp.cd(C.civil.from(C.blk(f, ok, q, k, rem))) == Some{Nat.add(C.before(k), rem)} : Maybe<&2, Nat>}:
  match f:
    case 0n:
      cp.cf(k, rem)
    case 1n+g:
      match ok:
        case False{}:
          cp.cf(k, rem)
        case True{}:
          +lt = Bool.and_l(Nat.is_lt(q, 32n), Nat.is_le(1461n, rem), eok)
          +le = Bool.and_r(Nat.is_lt(q, 32n), Nat.is_le(1461n, rem), eok)
          %cp.cal.skip(C.before(k), 1461n, rem, le) :
            {cp.cd(C.civil.from(C.blk(g, Nat.is_lt(1n+q, 32n) && Nat.is_le(1461n, Nat.sub(rem, 1461n)), 1n+q,
              1n+1n+1n+1n+k, Nat.sub(rem, 1461n)))) == Some{_} : Maybe<&2, Nat>}
          %cp.s4k(q, k, ek, lt) :
            {cp.cd(C.civil.from(C.blk(g, Nat.is_lt(1n+q, 32n) && Nat.is_le(1461n, Nat.sub(rem, 1461n)), 1n+q,
              1n+1n+1n+1n+k, Nat.sub(rem, 1461n)))) == Some{Nat.add(Nat.add(C.before(k), _), Nat.sub(rem, 1461n))} :
              Maybe<&2, Nat>}
          %cp.b4(k) :
            {cp.cd(C.civil.from(C.blk(g, Nat.is_lt(1n+q, 32n) && Nat.is_le(1461n, Nat.sub(rem, 1461n)), 1n+q,
              1n+1n+1n+1n+k, Nat.sub(rem, 1461n)))) == Some{Nat.add(_, Nat.sub(rem, 1461n))} : Maybe<&2, Nat>}
          cp.blk(g, Nat.is_lt(1n+q, 32n) && Nat.is_le(1461n, Nat.sub(rem, 1461n)), 1n+q, 1n+1n+1n+1n+k,
            Nat.sub(rem, 1461n),
            Equal.cong(Nat, Nat, x => 1n+1n+1n+1n+x, k, cp.four(q), ek), {==})

# LAW: every day, placed in the calendar, is the days before its year,
# its month and its day
def cp.civil(+days: Nat) -> {cp.cd(C.civil(days)) == Some{days} : Maybe<&2, Nat>}:
  cp.blk(32n, Nat.is_lt(0n, 32n) && Nat.is_le(1461n, days), 0n, 0n, days, {==}, {==})

# a month and a day the months have are within them: the month one of
# them, the day before its month's end
def cp.ns(-g: Type, +x: Nat, e: {None{} == Some{x} : Maybe<&2, Nat>}) -> g:
  cp.no(g, Equal.cong(Maybe<&2, Nat>, Bool, m => Maybe.is_some(&2, Nat, m), None{}, Some{x}, e))

def cp.all_le(ls: List<&2, Nat>, +b: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{+l, t}:
      Nat.is_le(l, b) && cp.all_le(t, b)

def cp.fit.at(c: Bool, +d: Nat, +l: Nat, +x: Nat) -> {Nat.is_lt(d, l) == c : Bool} ->
  {C.mdays.fit(c, d) == Some{x} : Maybe<&2, Nat>} -> {Nat.is_lt(d, l) == True{} : Bool}:
  match c:
    case True{}:
      ec => e => ec
    case False{}:
      ec => e => cp.ns({Nat.is_lt(d, l) == True{} : Bool}, x, e)

law cp.mdays_in:
  for +ls: List<&2, Nat>
  for +j: Nat
  for +d: Nat
  for +x: Nat
  for +al: {cp.all_le(ls, 31n) == True{} : Bool}
  for e: {C.mdays(ls, j, d) == Some{x} : Maybe<&2, Nat>}
  {Nat.is_lt(j, List.length(&2, Nat, ls)) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}

def cp.madd(m: Maybe<&2, Nat>, +l: Nat, +t: List<&2, Nat>, +i: Nat, +d: Nat, +x: Nat,
  ih: @y: Nat -> {C.mdays(t, i, d) == Some{y} : Maybe<&2, Nat>} ->
    {Nat.is_lt(i, List.length(&2, Nat, t)) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}) ->
  {C.mdays(t, i, d) == m : Maybe<&2, Nat>} ->
  {C.mdays.add(l, m) == Some{x} : Maybe<&2, Nat>} ->
  {Nat.is_lt(i, List.length(&2, Nat, t)) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}:
  match m:
    case None{}:
      em => e => cp.ns({Nat.is_lt(i, List.length(&2, Nat, t)) == True{} : Bool} &
        {Nat.is_lt(d, 31n) == True{} : Bool}, x, e)
    case Some{y}:
      em => e => ih(y, em)

def cp.mdays_in(ls, j, d, x, al, e):
  match ls:
    case Nil{}:
      cp.ns({Nat.is_lt(j, 0n) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}, x, e)
    case Con{+l, +t}:
      match j:
        case 0n:
          ({==}, Nat.is_lt_le_trans(d, l, 31n,
            cp.fit.at(Nat.is_lt(d, l), d, l, x)({==})(e),
            Bool.and_l(Nat.is_le(l, 31n), cp.all_le(t, 31n), al)))
        case 1n+i:
          cp.madd(C.mdays(t, i, d), l, t, i, d, x,
            y => ey => cp.mdays_in(t, i, d, y, Bool.and_r(Nat.is_le(l, 31n), cp.all_le(t, 31n), al), ey))({==})(e)

# a name written is read as its place in its list: each place computed,
# and past the list's end the bound refutes itself
def cp.nm.wk(+i: Nat, +r: Bytes(), lt: {Nat.is_lt(i, 7n) == True{} : Bool}) ->
  {C.rd.name(Bytes.append(C.nth(C.wkc(), i), r), C.wkc()) == Some{(i, r)} : Maybe<&1, Nat & Bytes()>}:
  match i:
    case 0n:
      {==}
    case 1n+i1:
      match i1:
        case 0n:
          {==}
        case 1n+i2:
          match i2:
            case 0n:
              {==}
            case 1n+i3:
              match i3:
                case 0n:
                  {==}
                case 1n+i4:
                  match i4:
                    case 0n:
                      {==}
                    case 1n+i5:
                      match i5:
                        case 0n:
                          {==}
                        case 1n+i6:
                          match i6:
                            case 0n:
                              {==}
                            case 1n+i7:
                              cp.lt0.no({C.rd.name(Bytes.append(C.nth(C.wkc(), 7n+i7), r), C.wkc()) == Some{(7n+i7, r)} : Maybe<&1, Nat & Bytes()>}, i7, lt)

def cp.nm.mo(+i: Nat, +r: Bytes(), lt: {Nat.is_lt(i, 12n) == True{} : Bool}) ->
  {C.rd.name(Bytes.append(C.nth(C.monc(), i), r), C.monc()) == Some{(i, r)} : Maybe<&1, Nat & Bytes()>}:
  match i:
    case 0n:
      {==}
    case 1n+i1:
      match i1:
        case 0n:
          {==}
        case 1n+i2:
          match i2:
            case 0n:
              {==}
            case 1n+i3:
              match i3:
                case 0n:
                  {==}
                case 1n+i4:
                  match i4:
                    case 0n:
                      {==}
                    case 1n+i5:
                      match i5:
                        case 0n:
                          {==}
                        case 1n+i6:
                          match i6:
                            case 0n:
                              {==}
                            case 1n+i7:
                              match i7:
                                case 0n:
                                  {==}
                                case 1n+i8:
                                  match i8:
                                    case 0n:
                                      {==}
                                    case 1n+i9:
                                      match i9:
                                        case 0n:
                                          {==}
                                        case 1n+i10:
                                          match i10:
                                            case 0n:
                                              {==}
                                            case 1n+i11:
                                              match i11:
                                                case 0n:
                                                  {==}
                                                case 1n+i12:
                                                  cp.lt0.no({C.rd.name(Bytes.append(C.nth(C.monc(), 12n+i12), r), C.monc()) == Some{(12n+i12, r)} : Maybe<&1, Nat & Bytes()>}, i12, lt)

# The token walk over pieces
# ==========================
#
# A date's text is pieces, each read by one token as one value. When
# every piece reads so, the walk over their text is the walk after them,
# with every value put in its slot: by induction over the pieces.
type cp.Cell is Data:
  cp.Cell{t: C.Tok, p: Bytes(), v: Nat}

def cp.cput(dt: C.Dt, c: cp.Cell) -> C.Dt:
  match c:
    case cp.Cell{t, p, v}:
      match t:
        case C.TName{xs, sl}:
          C.dt.put(dt, sl, v)
        case C.TLit{q}:
          dt
        case C.TD2{sl}:
          C.dt.put(dt, sl, v)
        case C.TSd{sl}:
          C.dt.put(dt, sl, v)

def cp.cok(+c: cp.Cell) -> Type:
  match c:
    case cp.Cell{+t, +p, +v}:
      @r: Bytes() -> @dt: C.Dt ->
        {C.tok.read(t, Bytes.append(p, r), dt) == Some{(cp.cput(dt, cp.Cell{t, p, v}), r)} :
          Maybe<&1, C.Dt & Bytes()>}

def cp.All(+cs: List<&2, cp.Cell>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{+c, +t}:
      cp.cok(c) & cp.All(t)

def cp.toks(cs: List<&2, cp.Cell>, tail: List<&2, C.Tok>) -> List<&2, C.Tok>:
  match cs:
    case Nil{}:
      tail
    case Con{c, t}:
      match c:
        case cp.Cell{tk, p, v}:
          Con{tk, cp.toks(t, tail)}

def cp.text(cs: List<&2, cp.Cell>, r: Bytes()) -> Bytes():
  match cs:
    case Nil{}:
      r
    case Con{c, t}:
      match c:
        case cp.Cell{tk, p, v}:
          Bytes.append(p, cp.text(t, r))

def cp.fold(cs: List<&2, cp.Cell>, dt: C.Dt) -> C.Dt:
  match cs:
    case Nil{}:
      dt
    case Con{+c, t}:
      cp.fold(t, cp.cput(dt, c))

law cp.run_cells:
  for +cs: List<&2, cp.Cell>
  for +tail: List<&2, C.Tok>
  for +dt: C.Dt
  for +r: Bytes()
  for all: cp.All(cs)
  {C.run(cp.toks(cs, tail), Some{(dt, cp.text(cs, r))}) == C.run(tail, Some{(cp.fold(cs, dt), r)}) :
    Maybe<&2, C.Dt>}

def cp.run_cells(cs, tail, dt, r, all):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      match c:
        case cp.Cell{+tk, +p, +v}:
          (ok, rest) = all
          %Equal.sym(Maybe<&1, C.Dt & Bytes()>, C.tok.read(tk, Bytes.append(p, cp.text(t, r)), dt),
            Some{(cp.cput(dt, cp.Cell{tk, p, v}), cp.text(t, r))}, ok(cp.text(t, r), dt)) :
            {C.run(cp.toks(t, tail), _) == C.run(tail, Some{(cp.fold(t, cp.cput(dt, cp.Cell{tk, p, v})), r)}) :
              Maybe<&2, C.Dt>}
          cp.run_cells(t, tail, cp.cput(dt, cp.Cell{tk, p, v}), r, rest)

# The round trip
# ==============
#
# What the reader makes of the date's fields is the time they came from:
# the hour, minute and second are in range and fold back into the
# seconds as they were split out of them; the year's two halves are the
# year, 1970 or later, and its month and day are where the calendar
# placed the day.
# k + c - c is k
def cp.sub_add_r(+k: Nat, +c: Nat) -> {Nat.sub(Nat.add(k, c), c) == k : Nat}:
  %cp.add_comm(c, k) : {Nat.sub(_, c) == k : Nat}
  WW.wl.sub_add(c, k)

def cp.rt.stamp(+days: Nat, +t: Nat, +k: Nat, +j: Nat, +d: Nat, +yh: Nat, +yl: Nat,
  +h: Nat, +hs: Nat, +m: Nat, +ms: Nat, +x: Nat,
  eq1: {Nat.add(Nat.mul(ms, 60n), x) == t : Nat},
  eq2: {Nat.add(Nat.mul(hs, 60n), m) == ms : Nat},
  eq3: {Nat.add(Nat.mul(days, 24n), h) == hs : Nat},
  eq4: {Nat.add(Nat.mul(yh, 100n), yl) == Nat.add(k, 1970n) : Nat},
  ec: {C.days.of(k, (j, d)) == Some{days} : Maybe<&2, Nat>},
  lh: {Nat.is_lt(h, 24n) == True{} : Bool}, lm: {Nat.is_lt(m, 60n) == True{} : Bool},
  lx: {Nat.is_lt(x, 60n) == True{} : Bool}) ->
  {C.stamp(Nat.add(yl, Nat.mul(yh, 100n)), j, 1n+d, h, m, x) == Some{t} : Maybe<&2, Nat>}:
  %cp.add_comm(Nat.mul(yh, 100n), yl) : {C.stamp(_, j, 1n+d, h, m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.add(Nat.mul(yh, 100n), yl), Nat.add(k, 1970n), eq4) :
    {C.stamp(_, j, 1n+d, h, m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_lt(h, 24n), True{}, lh) :
    {C.stamp.ok(Bool.and(_, Bool.and(Nat.is_lt(m, 60n), Nat.is_lt(x, 60n))), Nat.add(k, 1970n), j, 1n+d, h,
      m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_lt(m, 60n), True{}, lm) :
    {C.stamp.ok(Bool.and(True{}, Bool.and(_, Nat.is_lt(x, 60n))), Nat.add(k, 1970n), j, 1n+d, h,
      m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_lt(x, 60n), True{}, lx) :
    {C.stamp.ok(Bool.and(True{}, Bool.and(True{}, _)), Nat.add(k, 1970n), j, 1n+d, h,
      m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_le(1970n, Nat.add(k, 1970n)), True{}, cp.le_add_l(k, 1970n)) :
    {C.stamp.go(_, Nat.add(k, 1970n), j, 1n+d, h, m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.sub(Nat.add(k, 1970n), 1970n), k, cp.sub_add_r(k, 1970n)) :
    {C.stamp.at(C.days.of(_, (j, d)), h, m, x) == Some{t} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, C.days.of(k, (j, d)), Some{days}, ec) :
    {C.stamp.at(_, h, m, x) == Some{t} : Maybe<&2, Nat>}
  %eq1 : {Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(days, 24n), h), 60n), m), 60n), x)} ==
    Some{_} : Maybe<&2, Nat>}
  %eq2 : {Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(days, 24n), h), 60n), m), 60n), x)} ==
    Some{Nat.add(Nat.mul(_, 60n), x)} : Maybe<&2, Nat>}
  %eq3 : {Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(days, 24n), h), 60n), m), 60n), x)} ==
    Some{Nat.add(Nat.mul(Nat.add(Nat.mul(_, 60n), m), 60n), x)} : Maybe<&2, Nat>}
  {==}

# each piece of an IMF-fixdate is read by its token as its value
def cp.ok.d2.at(sl: C.Sl, +n: Nat, lt: {Nat.is_lt(n, 100n) == True{} : Bool}, +r: Bytes(), dt: C.Dt) ->
  {C.tok.read(C.TD2{sl}, Bytes.append(C.d2(n), r), dt) == Some{(C.dt.put(dt, sl, n), r)} :
    Maybe<&1, C.Dt & Bytes()>}:
  %Equal.sym(Maybe<&1, Nat & Bytes()>, C.rd.d2(Bytes.append(C.d2(n), r)), Some{(n, r)}, cp.d2(n, r, lt)) :
    {C.tok.num(_, sl, dt) == Some{(C.dt.put(dt, sl, n), r)} : Maybe<&1, C.Dt & Bytes()>}
  {==}

def cp.ok.d2(+sl: C.Sl, +n: Nat, +lt: {Nat.is_lt(n, 100n) == True{} : Bool}) ->
  cp.cok(cp.Cell{C.TD2{sl}, C.d2(n), n}):
  r => dt => cp.ok.d2.at(sl, n, lt, r, dt)

def cp.ok.wk.at(+w: Nat, lt: {Nat.is_lt(w, 7n) == True{} : Bool}, +r: Bytes(), dt: C.Dt) ->
  {C.tok.read(C.TName{C.wkc(), C.SNone{}}, Bytes.append(C.nth(C.wkc(), w), r), dt) ==
    Some{(C.dt.put(dt, C.SNone{}, w), r)} : Maybe<&1, C.Dt & Bytes()>}:
  %Equal.sym(Maybe<&1, Nat & Bytes()>, C.rd.name(Bytes.append(C.nth(C.wkc(), w), r), C.wkc()), Some{(w, r)},
    cp.nm.wk(w, r, lt)) :
    {C.tok.num(_, C.SNone{}, dt) == Some{(C.dt.put(dt, C.SNone{}, w), r)} : Maybe<&1, C.Dt & Bytes()>}
  {==}

def cp.ok.wk(+w: Nat, +lt: {Nat.is_lt(w, 7n) == True{} : Bool}) ->
  cp.cok(cp.Cell{C.TName{C.wkc(), C.SNone{}}, C.nth(C.wkc(), w), w}):
  r => dt => cp.ok.wk.at(w, lt, r, dt)

def cp.ok.mo.at(+j: Nat, lt: {Nat.is_lt(j, 12n) == True{} : Bool}, +r: Bytes(), dt: C.Dt) ->
  {C.tok.read(C.TName{C.monc(), C.SMon{}}, Bytes.append(C.nth(C.monc(), j), r), dt) ==
    Some{(C.dt.put(dt, C.SMon{}, j), r)} : Maybe<&1, C.Dt & Bytes()>}:
  %Equal.sym(Maybe<&1, Nat & Bytes()>, C.rd.name(Bytes.append(C.nth(C.monc(), j), r), C.monc()), Some{(j, r)},
    cp.nm.mo(j, r, lt)) :
    {C.tok.num(_, C.SMon{}, dt) == Some{(C.dt.put(dt, C.SMon{}, j), r)} : Maybe<&1, C.Dt & Bytes()>}
  {==}

def cp.ok.mo(+j: Nat, +lt: {Nat.is_lt(j, 12n) == True{} : Bool}) ->
  cp.cok(cp.Cell{C.TName{C.monc(), C.SMon{}}, C.nth(C.monc(), j), j}):
  r => dt => cp.ok.mo.at(j, lt, r, dt)

def cp.ok.lit.sp() -> cp.cok(cp.Cell{C.TLit{" "}, " ", 0n}):
  r => dt => {==}

def cp.ok.lit.c() -> cp.cok(cp.Cell{C.TLit{":"}, ":", 0n}):
  r => dt => {==}

def cp.ok.lit.gmt() -> cp.cok(cp.Cell{C.TLit{" GMT"}, " GMT", 0n}):
  r => dt => {==}

def cp.imf.cells(+w: Nat, +d1: Nat, +j: Nat, +yh: Nat, +yl: Nat, +h: Nat, +m: Nat, +x: Nat) ->
  List<&2, cp.Cell>:
  [cp.Cell{C.TName{C.wkc(), C.SNone{}}, C.nth(C.wkc(), w), w},
    cp.Cell{C.TD2{C.SDay{}}, C.d2(d1), d1},
    cp.Cell{C.TLit{" "}, " ", 0n},
    cp.Cell{C.TName{C.monc(), C.SMon{}}, C.nth(C.monc(), j), j},
    cp.Cell{C.TD2{C.SYh{}}, C.d2(yh), yh},
    cp.Cell{C.TD2{C.SYl{}}, C.d2(yl), yl},
    cp.Cell{C.TLit{" "}, " ", 0n},
    cp.Cell{C.TD2{C.SH{}}, C.d2(h), h},
    cp.Cell{C.TLit{":"}, ":", 0n},
    cp.Cell{C.TD2{C.SM{}}, C.d2(m), m},
    cp.Cell{C.TLit{":"}, ":", 0n},
    cp.Cell{C.TD2{C.SS{}}, C.d2(x), x},
    cp.Cell{C.TLit{" GMT"}, " GMT", 0n}]

def cp.imf.all(+w: Nat, +d1: Nat, +j: Nat, +yh: Nat, +yl: Nat, +h: Nat, +m: Nat, +x: Nat,
  +lw: {Nat.is_lt(w, 7n) == True{} : Bool}, +ld: {Nat.is_lt(d1, 100n) == True{} : Bool},
  +lj: {Nat.is_lt(j, 12n) == True{} : Bool}, +lyh: {Nat.is_lt(yh, 100n) == True{} : Bool},
  +lyl: {Nat.is_lt(yl, 100n) == True{} : Bool}, +lh: {Nat.is_lt(h, 100n) == True{} : Bool},
  +lm: {Nat.is_lt(m, 100n) == True{} : Bool}, +lx: {Nat.is_lt(x, 100n) == True{} : Bool}) ->
  cp.All(cp.imf.cells(w, d1, j, yh, yl, h, m, x)):
  (cp.ok.wk(w, lw), (cp.ok.d2(C.SDay{}, d1, ld), (cp.ok.lit.sp(), (cp.ok.mo(j, lj),
    (cp.ok.d2(C.SYh{}, yh, lyh), (cp.ok.d2(C.SYl{}, yl, lyl), (cp.ok.lit.sp(), (cp.ok.d2(C.SH{}, h, lh),
      (cp.ok.lit.c(), (cp.ok.d2(C.SM{}, m, lm), (cp.ok.lit.c(), (cp.ok.d2(C.SS{}, x, lx),
        (cp.ok.lit.gmt(), Unit{})))))))))))))

# a month and a day the calendar has: January to December, and the day
# below 31, since no month is longer
def cp.ml.len(+lp: Bool) -> {List.length(&2, Nat, C.mlens(lp)) == 12n : Nat}:
  match lp:
    case True{}:
      {==}
    case False{}:
      {==}

def cp.ml.al(+lp: Bool) -> {cp.all_le(C.mlens(lp), 31n) == True{} : Bool}:
  match lp:
    case True{}:
      {==}
    case False{}:
      {==}

def cp.jd.ls(+ls: List<&2, Nat>, +l0: Nat, +j: Nat, +d: Nat, +x: Nat,
  +al: {cp.all_le(ls, 31n) == True{} : Bool},
  e: {C.mdays.add(l0, C.mdays(ls, j, d)) == Some{x} : Maybe<&2, Nat>}) ->
  {Nat.is_lt(j, List.length(&2, Nat, ls)) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}:
  cp.madd(C.mdays(ls, j, d), l0, ls, j, d, x, y => ey => cp.mdays_in(ls, j, d, y, al, ey))({==})(e)

def cp.jd(+k: Nat, +j: Nat, +d: Nat, +days: Nat,
  ec: {C.days.of(k, (j, d)) == Some{days} : Maybe<&2, Nat>}) ->
  {Nat.is_lt(j, 12n) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}:
  %cp.ml.len(C.leap(k)) : {Nat.is_lt(j, _) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}
  cp.jd.ls(C.mlens(C.leap(k)), C.before(k), j, d, days, cp.ml.al(C.leap(k)), ec)

# the weekday is below 7
def cp.rt.wk(+a: Nat, qr: Nat & Nat, dm: cp.dm(7n, a, qr)) -> {Nat.is_lt(Nat.mod.fin(qr), 7n) == True{} : Bool}:
  match qr:
    case (q, r):
      (e, l) = dm
      l

# a Maybe that is Some is what Maybe.or keeps
def cp.or.some(-a: Maybe<&2, Nat>, -b: Maybe<&2, Nat>, +t: Nat, e: {a == Some{t} : Maybe<&2, Nat>}) ->
  {Maybe.or(&2, Nat, a, b) == Some{t} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, a, Some{t}, e) : {Maybe.or(&2, Nat, _, b) == Some{t} : Maybe<&2, Nat>}
  {==}

def cp.rt.fin(+t: Nat, +days: Nat, +h: Nat, +m: Nat, +x: Nat, +ms: Nat, +hs: Nat, +k: Nat, +j: Nat,
  +d: Nat, yy: Nat & Nat,
  +eq1: {Nat.add(Nat.mul(ms, 60n), x) == t : Nat},
  +eq2: {Nat.add(Nat.mul(hs, 60n), m) == ms : Nat},
  +eq3: {Nat.add(Nat.mul(days, 24n), h) == hs : Nat},
  +lh: {Nat.is_lt(h, 24n) == True{} : Bool}, +lm: {Nat.is_lt(m, 60n) == True{} : Bool},
  +lx: {Nat.is_lt(x, 60n) == True{} : Bool},
  +ec: {C.days.of(k, (j, d)) == Some{days} : Maybe<&2, Nat>},
  +ey: {Nat.is_lt(C.year.hi(yy), 100n) == True{} : Bool},
  dmy: cp.dm(100n, Nat.add(k, 1970n), yy),
  +wl: {Nat.is_lt(Nat.mod(Nat.add(4n, days), 7n), 7n) == True{} : Bool},
  jdb: {Nat.is_lt(j, 12n) == True{} : Bool} & {Nat.is_lt(d, 31n) == True{} : Bool}) ->
  {C.rd.form(C.imf.toks(), Bytes.concat(Con{C.nth(C.wkc(), Nat.mod(Nat.add(4n, days), 7n)),
    Con{C.d2(1n+d), Con{" ", Con{C.nth(C.monc(), j),
      C.date.y(yy, [C.d2(h), ":", C.d2(m), ":", C.d2(x), " GMT"])}}}})) == Some{t} : Maybe<&2, Nat>}:
  match yy:
    case (+yh, +yl):
      (+eq4, +lyl) = dmy
      (+lj, +ld) = jdb
      %Equal.sym(Maybe<&2, C.Dt>,
        C.run(cp.toks(cp.imf.cells(Nat.mod(Nat.add(4n, days), 7n), 1n+d, j, yh, yl, h, m, x), Nil{}),
          Some{(C.dt0(), cp.text(cp.imf.cells(Nat.mod(Nat.add(4n, days), 7n), 1n+d, j, yh, yl, h, m, x), ""))}),
        C.run(Nil{}, Some{(cp.fold(cp.imf.cells(Nat.mod(Nat.add(4n, days), 7n), 1n+d, j, yh, yl, h, m, x),
          C.dt0()), "")}),
        cp.run_cells(cp.imf.cells(Nat.mod(Nat.add(4n, days), 7n), 1n+d, j, yh, yl, h, m, x), Nil{}, C.dt0(), "",
          cp.imf.all(Nat.mod(Nat.add(4n, days), 7n), 1n+d, j, yh, yl, h, m, x, wl,
            Nat.is_lt_le_trans(d, 31n, 99n, ld, {==}), lj,
            ey, lyl,
            Nat.is_lt_le_trans(h, 24n, 100n, lh, {==}), Nat.is_lt_le_trans(m, 60n, 100n, lm, {==}),
            Nat.is_lt_le_trans(x, 60n, 100n, lx, {==})))) :
        {C.dt.stamp(_) == Some{t} : Maybe<&2, Nat>}
      cp.rt.stamp(days, t, k, j, d, yh, yl, h, hs, m, ms, x, eq1, eq2, eq3, eq4, ec, lh, lm, lx)

def cp.rt.jd(+t: Nat, +ms: Nat, +x: Nat, +hs: Nat, +m: Nat, +days: Nat, +h: Nat,
  +eq1: {Nat.add(Nat.mul(ms, 60n), x) == t : Nat},
  +lx: {Nat.is_lt(x, 60n) == True{} : Bool},
  +eq2: {Nat.add(Nat.mul(hs, 60n), m) == ms : Nat},
  +lm: {Nat.is_lt(m, 60n) == True{} : Bool},
  +eq3: {Nat.add(Nat.mul(days, 24n), h) == hs : Nat},
  +lh: {Nat.is_lt(h, 24n) == True{} : Bool},
  +k: Nat, jd: Nat & Nat,
  +ec: {C.days.of(k, jd) == Some{days} : Maybe<&2, Nat>},
  +ey: {Nat.is_lt(C.year.hi(Nat.divmod(Nat.add(k, 1970n), 100n)), 100n) == True{} : Bool},
  +wl: {Nat.is_lt(Nat.mod(Nat.add(4n, days), 7n), 7n) == True{} : Bool}) ->
  {C.rd.form(C.imf.toks(), Bytes.concat(Con{C.nth(C.wkc(), Nat.mod(Nat.add(4n, days), 7n)),
    C.date.ymd((k, jd), [C.d2(h), ":", C.d2(m), ":", C.d2(x), " GMT"])})) == Some{t} : Maybe<&2, Nat>}:
  match jd:
    case (+j, +d):
      cp.rt.fin(t, days, h, m, x, ms, hs, k, j, d, Nat.divmod(Nat.add(k, 1970n), 100n), eq1, eq2, eq3,
        lh, lm, lx, ec, ey, cp.divmod(Nat.add(k, 1970n), 99n), wl, cp.jd(k, j, d, days, ec))

def cp.rt.cal(+t: Nat, +ms: Nat, +x: Nat, +hs: Nat, +m: Nat, +days: Nat, +h: Nat,
  +eq1: {Nat.add(Nat.mul(ms, 60n), x) == t : Nat},
  +lx: {Nat.is_lt(x, 60n) == True{} : Bool},
  +eq2: {Nat.add(Nat.mul(hs, 60n), m) == ms : Nat},
  +lm: {Nat.is_lt(m, 60n) == True{} : Bool},
  +eq3: {Nat.add(Nat.mul(days, 24n), h) == hs : Nat},
  +lh: {Nat.is_lt(h, 24n) == True{} : Bool},
  kjd: Nat & Nat & Nat,
  +ec: {cp.cd(kjd) == Some{days} : Maybe<&2, Nat>},
  +ey: {Nat.is_lt(C.year.hi(Nat.divmod(C.year.of(kjd), 100n)), 100n) == True{} : Bool},
  +wl: {Nat.is_lt(Nat.mod(Nat.add(4n, days), 7n), 7n) == True{} : Bool}) ->
  {C.rd.form(C.imf.toks(), Bytes.concat(Con{C.nth(C.wkc(), Nat.mod(Nat.add(4n, days), 7n)),
    C.date.ymd(kjd, [C.d2(h), ":", C.d2(m), ":", C.d2(x), " GMT"])})) == Some{t} : Maybe<&2, Nat>}:
  match kjd:
    case (+k, jd):
      cp.rt.jd(t, ms, x, hs, m, days, h, eq1, lx, eq2, lm, eq3, lh, k, jd, ec, ey, wl)

def cp.rt.q3(+t: Nat, +ms: Nat, +x: Nat, +hs: Nat, +m: Nat,
  +eq1: {Nat.add(Nat.mul(ms, 60n), x) == t : Nat},
  +lx: {Nat.is_lt(x, 60n) == True{} : Bool},
  +eq2: {Nat.add(Nat.mul(hs, 60n), m) == ms : Nat},
  +lm: {Nat.is_lt(m, 60n) == True{} : Bool},
  dh: Nat & Nat, dm: cp.dm(24n, hs, dh),
  +ey: {Nat.is_lt(C.year.hi(Nat.divmod(C.year.q3(dh), 100n)), 100n) == True{} : Bool}) ->
  {C.rd.form(C.imf.toks(), C.date.q3(m, x, dh)) == Some{t} : Maybe<&2, Nat>}:
  match dh:
    case (+days, +h):
      (eq3, lh) = dm
      cp.rt.cal(t, ms, x, hs, m, days, h, eq1, lx, eq2, lm, eq3, lh, C.civil(days), cp.civil(days), ey,
        cp.rt.wk(Nat.add(4n, days), Nat.divmod(Nat.add(4n, days), 7n), cp.divmod(Nat.add(4n, days), 6n)))

def cp.rt.q2(+t: Nat, +ms: Nat, +x: Nat,
  +eq1: {Nat.add(Nat.mul(ms, 60n), x) == t : Nat},
  +lx: {Nat.is_lt(x, 60n) == True{} : Bool},
  hm: Nat & Nat, dm: cp.dm(60n, ms, hm),
  +ey: {Nat.is_lt(C.year.hi(Nat.divmod(C.year.q2(hm), 100n)), 100n) == True{} : Bool}) ->
  {C.rd.form(C.imf.toks(), C.date.q2(x, hm)) == Some{t} : Maybe<&2, Nat>}:
  match hm:
    case (+hs, +m):
      (eq2, lm) = dm
      cp.rt.q3(t, ms, x, hs, m, eq1, lx, eq2, lm, Nat.divmod(hs, 24n), cp.divmod(hs, 23n), ey)

def cp.rt.q1(+t: Nat, mx: Nat & Nat, dm: cp.dm(60n, t, mx),
  +ey: {Nat.is_lt(C.year.hi(Nat.divmod(C.year.q1(mx), 100n)), 100n) == True{} : Bool}) ->
  {C.rd.form(C.imf.toks(), C.date.q1(mx)) == Some{t} : Maybe<&2, Nat>}:
  match mx:
    case (+ms, +x):
      (eq1, lx) = dm
      cp.rt.q2(t, ms, x, eq1, lx, Nat.divmod(ms, 60n), cp.divmod(ms, 59n), ey)

# every time before the year 10000 is written as an IMF-fixdate that
# reads back as itself
def cp.date_rt(+t: Nat, +ey: {C.year.ok(t) == True{} : Bool}) ->
  {C.date.read(C.date.fmt(t)) == Some{t} : Maybe<&2, Nat>}:
  cp.or.some(C.rd.form(C.imf.toks(), C.date.fmt(t)),
    Maybe.or(&2, Nat, C.rd.form(C.rfc850.toks(), C.date.fmt(t)), C.rd.form(C.asctime.toks(), C.date.fmt(t))),
    t, cp.rt.q1(t, Nat.divmod(t, 60n), cp.divmod(t, 59n), ey))

# Ranges are in the file
# ======================
#
# What want gives is a range of the file, a <= b < n, whatever spec it is
# handed; so is every Part the decision comes to, since each is a want's.
def cq.W(w: C.Want, +n: Nat) -> Type:
  match w:
    case C.Span{a, b}:
      {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_lt(b, n) == True{} : Bool}
    case C.Unsat{}:
      Unit

def cq.G(g: C.Got, +n: Nat) -> Type:
  match g:
    case C.Part{a, b}:
      {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_lt(b, n) == True{} : Bool}
    case _:
      Unit

def cq.le_min(+a: Nat, +x: Nat, +y: Nat, ax: {Nat.is_le(a, x) == True{} : Bool},
  ay: {Nat.is_le(a, y) == True{} : Bool}) -> {Nat.is_le(a, Nat.min(x, y)) == True{} : Bool}:
  match a:
    case 0n:
      cp.le0(Nat.min(x, y))
    case 1n+ap:
      match x:
        case 0n:
          cp.no({Nat.is_le(1n+ap, Nat.min(0n, y)) == True{} : Bool}, ax)
        case 1n+xp:
          match y:
            case 0n:
              cp.no({Nat.is_le(1n+ap, Nat.min(1n+xp, 0n)) == True{} : Bool}, ay)
            case 1n+yp:
              cq.le_min(ap, xp, yp, ax, ay)

def cq.min_le(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.min(x, y), y) == True{} : Bool}:
  match x:
    case 0n:
      cp.le0(y)
    case 1n+xp:
      match y:
        case 0n:
          {==}
        case 1n+yp:
          cq.min_le(xp, yp)

def cq.want.from.none(c: Bool, +a: Nat, +m: Nat, e: {Nat.is_lt(a, 1n+m) == c : Bool}) ->
  cq.W(C.want.from(c, a, m), 1n+m):
  match c:
    case True{}:
      (%Nat.lt_succ(a, m) : {_ == True{} : Bool}
        e, cp.lt_self(m))
    case False{}:
      Unit{}

def cq.want.from.some(c: Bool, +a: Nat, +b2: Nat, +m: Nat,
  +e: {Bool.and(Nat.is_lt(a, 1n+m), Nat.is_le(a, b2)) == c : Bool}) ->
  cq.W(C.want.from(c, a, Nat.min(b2, m)), 1n+m):
  match c:
    case True{}:
      (cq.le_min(a, b2, m, Bool.and_r(Nat.is_lt(a, 1n+m), Nat.is_le(a, b2), e),
        %Nat.lt_succ(a, m) : {_ == True{} : Bool}
          Bool.and_l(Nat.is_lt(a, 1n+m), Nat.is_le(a, b2), e)),
        %Equal.sym(Bool, Nat.is_lt(Nat.min(b2, m), 1n+m), Nat.is_le(Nat.min(b2, m), m),
          Nat.lt_succ(Nat.min(b2, m), m)) : {_ == True{} : Bool}
          cq.min_le(b2, m))
    case False{}:
      Unit{}

def cq.want.n(+a: Nat, b: Maybe<&2, Nat>, +n: Nat) -> cq.W(C.want(C.From{a, b}, n), n):
  match b:
    case None{}:
      match n:
        case 0n:
          %Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, cp.lt0(a)) : cq.W(C.want.from(_, a, Nat.sub(0n, 1n)), 0n)
          Unit{}
        case 1n+m:
          %Equal.sym(Nat, Nat.sub(m, 0n), m, cp.sub_zero(m)) : cq.W(C.want.from(Nat.is_lt(a, 1n+m), a, _), 1n+m)
          cq.want.from.none(Nat.is_lt(a, 1n+m), a, m, {==})
    case Some{+b2}:
      match n:
        case 0n:
          %Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, cp.lt0(a)) : cq.W(C.want.from(Bool.and(_, Nat.is_le(a, b2)), a, Nat.min(b2, Nat.sub(0n, 1n))), 0n)
          Unit{}
        case 1n+m:
          %Equal.sym(Nat, Nat.sub(m, 0n), m, cp.sub_zero(m)) :
            cq.W(C.want.from(Bool.and(Nat.is_lt(a, 1n+m), Nat.is_le(a, b2)), a, Nat.min(b2, _)), 1n+m)
          cq.want.from.some(Bool.and(Nat.is_lt(a, 1n+m), Nat.is_le(a, b2)), a, b2, m, {==})

def cq.want.last(+n: Nat, +k: Nat) -> cq.W(C.want.last(n, k), n):
  match n:
    case 0n:
      Unit{}
    case 1n+m:
      match k:
        case 0n:
          Unit{}
        case 1n+j:
          (cp.sub_le(m, Nat.min(j, m)), cp.lt_self(m))

def cq.want(sp: C.Spec, +n: Nat) -> cq.W(C.want(sp, n), n):
  match sp:
    case C.From{+a, b}:
      cq.want.n(a, b, n)
    case C.Last{+k}:
      cq.want.last(n, k)

def cq.Ws(ws: List<&2, C.Want>, +n: Nat) -> Type:
  match ws:
    case Nil{}:
      Unit
    case Con{w, t}:
      cq.W(w, n) & cq.Ws(t, n)

def cq.Hp(ab: Nat & Nat, +n: Nat) -> Type:
  (a, b) = ab
  {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_lt(b, n) == True{} : Bool}

def cq.H(hit: Maybe<&1, Nat & Nat>, +n: Nat) -> Type:
  match hit:
    case None{}:
      Unit
    case Some{ab}:
      cq.Hp(ab, n)

def cq.one(p: Nat, ab: Nat & Nat, +n: Nat, h: cq.Hp(ab, n)) -> cq.G(C.got.one(p, ab), n):
  match p:
    case 0n:
      match ab:
        case (a, b):
          h
    case 1n+q:
      Unit{}

def cq.fin(hit: Maybe<&1, Nat & Nat>, +k: Nat, +n: Nat, h: cq.H(hit, n)) -> cq.G(C.got.fin(hit, k), n):
  match hit:
    case None{}:
      Unit{}
    case Some{ab}:
      cq.one(Nat.sub(k, 1n), ab, n, h)

def cq.of(ws: List<&2, C.Want>, hit: Maybe<&1, Nat & Nat>, +k: Nat, +n: Nat, al: cq.Ws(ws, n),
  h: cq.H(hit, n)) -> cq.G(C.got.of(ws, hit, k), n):
  match ws:
    case Nil{}:
      cq.fin(hit, k, n, h)
    case Con{w, t}:
      match w:
        case C.Span{a, b}:
          (aw, at) = al
          cq.of(t, Some{(a, b)}, 1n+k, n, at, aw)
        case C.Unsat{}:
          (aw, at) = al
          cq.of(t, hit, k, n, at, h)

def cq.wants(sp: List<&2, C.Spec>, +n: Nat) -> cq.Ws(C.wants(sp, n), n):
  match sp:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      (cq.want(h, n), cq.wants(t, n))

def cq.ranged(m: Maybe<&2, List<&2, C.Spec>>, +n: Nat) -> cq.G(C.ranged(m, n), n):
  match m:
    case None{}:
      Unit{}
    case Some{+sp}:
      cq.of(C.wants(sp, n), None{}, 0n, n, cq.wants(sp, n), Unit{})

def cq.pick(c: Bool, -x: C.Got, -y: C.Got, +n: Nat, gx: cq.G(x, n), gy: cq.G(y, n)) ->
  cq.G(Bool.pick(C.Got, c, x, y), n):
  match c:
    case True{}:
      gx
    case False{}:
      gy

def cq.partgo(ir: Maybe<&2, Bytes()>, v: Bytes(), +mt32: U32, +n32: U32, +n: Nat) ->
  cq.G(C.part.go(ir, v, mt32, n32, n), n):
  match ir:
    case None{}:
      cq.ranged(C.rg.parse(v), n)
    case Some{w}:
      cq.pick(C.ir.ok(w, mt32, n32), C.ranged(C.rg.parse(v), n), C.Full{}, n, cq.ranged(C.rg.parse(v), n),
        Unit{})

def cq.part(rg: Maybe<&2, Bytes()>, ir: Maybe<&2, Bytes()>, +mt32: U32, +n32: U32, +n: Nat) ->
  cq.G(C.part(rg, ir, mt32, n32, n), n):
  match rg:
    case None{}:
      Unit{}
    case Some{v}:
      match n:
        case 0n:
          Unit{}
        case 1n+p:
          cq.partgo(ir, v, mt32, n32, 1n+p)

def cq.ims(m: Maybe<&2, Nat>, +mt: Nat, -later: C.Got, +n: Nat, gl: cq.G(later, n)) ->
  cq.G(C.ims.go(m, mt, later), n):
  match m:
    case None{}:
      gl
    case Some{d}:
      cq.pick(Nat.is_le(mt, d), C.Same{}, later, n, Unit{}, gl)

def cq.cond(inm: Maybe<&2, Bytes()>, ims: Maybe<&2, Bytes()>, +mt32: U32, +n32: U32, -later: C.Got, +n: Nat,
  gl: cq.G(later, n)) -> cq.G(C.cond(inm, ims, mt32, n32, later), n):
  match inm:
    case Some{v}:
      cq.pick(C.tags.hit(v, C.etag.of(mt32, n32), False{}), C.Same{}, later, n, Unit{}, gl)
    case None{}:
      match ims:
        case None{}:
          gl
        case Some{v}:
          cq.ims(C.date.read(v), U32.to_nat(mt32), later, n, gl)

def cq.decide(k: C.Ask, +mt32: U32, +n32: U32) -> cq.G(C.decide(k, mt32, n32), U32.to_nat(n32)):
  match k:
    case C.Ask{im, ius, inm, ims, rg, ir}:
      cq.pick(C.pre.ok(im, ius, mt32, n32), C.cond(inm, ims, mt32, n32, C.part(rg, ir, mt32, n32, U32.to_nat(n32))),
        C.Fails{}, U32.to_nat(n32),
        cq.cond(inm, ims, mt32, n32, C.part(rg, ir, mt32, n32, U32.to_nat(n32)), U32.to_nat(n32),
          cq.part(rg, ir, mt32, n32, U32.to_nat(n32))), Unit{})

def cq.part_in(k: C.Ask, +mt32: U32, +n32: U32, -a: Nat, -b: Nat,
  e: {C.decide(k, mt32, n32) == C.Part{a, b} : C.Got}) ->
  {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_lt(b, U32.to_nat(n32)) == True{} : Bool}:
  %e : cq.G(_, U32.to_nat(n32))
  cq.decide(k, mt32, n32)

# a range of the file is all there: bytes a to b of a file longer than b
# are b + 1 - a of them
def cq.le_s(+b: Nat, +n: Nat) -> {Nat.is_le(1n+b, n) == Nat.is_lt(b, n) : Bool}:
  match b n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      cp.le0(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cq.le_s(p, q)

def cq.drop_le(+s: Bytes(), +a: Nat, +l: Nat, e: {Nat.is_le(Nat.add(a, l), Bytes.len(s)) == True{} : Bool}) ->
  {Nat.is_le(l, Bytes.len(String.drop(s, a))) == True{} : Bool}:
  match s a:
    case SNil{} 0n:
      e
    case SNil{} 1n+p:
      cp.no({Nat.is_le(l, Bytes.len(String.drop(SNil{}, 1n+p))) == True{} : Bool}, e)
    case SCon{h, t} 0n:
      e
    case SCon{h, +t} 1n+p:
      cq.drop_le(t, p, l,
        %Bytes.len.shift(t, 0n) : {Nat.is_le(1n+Nat.add(p, l), _) == True{} : Bool}
        e)

def cq.part_ep(+body: Bytes(), +a: Nat, +b: Nat,
  ea: {U32.to_nat(U32.from_nat(a)) == a : Nat},
  el: {U32.to_nat(U32.from_nat(Nat.sub(1n+b, a))) == Nat.sub(1n+b, a) : Nat},
  le: {Nat.is_le(a, b) == True{} : Bool}, lt: {Nat.is_lt(b, Bytes.len(body)) == True{} : Bool}) ->
  {WW.wl.part(body, U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(a)), a, ea) :
    {Nat.is_eq(Bytes.len(String.take(String.drop(body, _), U32.to_nat(U32.from_nat(Nat.sub(1n+b, a))))),
      U32.to_nat(U32.from_nat(Nat.sub(1n+b, a)))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.sub(1n+b, a))), Nat.sub(1n+b, a), el) :
    {Nat.is_eq(Bytes.len(String.take(String.drop(body, a), _)), _) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(Bytes.len(String.take(String.drop(body, a), Nat.sub(1n+b, a))), Nat.sub(1n+b, a)),
    Nat.is_le(Nat.sub(1n+b, a), Bytes.len(String.drop(body, a))), WW.wl.eq_le(String.drop(body, a), Nat.sub(1n+b, a))) :
    {_ == True{} : Bool}
  cq.drop_le(body, a, Nat.sub(1n+b, a),
    %Equal.sym(Nat, Nat.add(a, Nat.sub(1n+b, a)), 1n+b,
      cp.add_sub(a, 1n+b, Nat.is_le_trans(a, b, 1n+b, le, cp.le_succ(b)))) :
      {Nat.is_le(_, Bytes.len(body)) == True{} : Bool}
    %Equal.sym(Bool, Nat.is_le(1n+b, Bytes.len(body)), Nat.is_lt(b, Bytes.len(body)), cq.le_s(b, Bytes.len(body))) :
      {_ == True{} : Bool}
    lt)

def Laws.date_round_trip(t, ey):
  cp.date_rt(t, ey)

def Laws.date_rfc_example():
  {==}

def Laws.date_leap_2000():
  {==}

def Laws.date_leap_2024():
  {==}

def Laws.date_no_leap_2100():
  {==}

def Laws.date_epoch():
  {==}

def Laws.date_year_end():
  {==}

def Laws.date_last_u32():
  {==}

def Laws.read_imf():
  {==}

def Laws.read_rfc850():
  {==}

def Laws.read_asctime():
  {==}

def Laws.days_rfc_example():
  {==}

def Laws.days_leap_2000():
  {==}

def Laws.no_feb_30():
  {==}

def Laws.no_feb_29_2100():
  {==}

def Laws.no_hour_24():
  {==}

def Laws.not_a_date():
  {==}

def Laws.before_epoch():
  {==}

def Laws.etag_hex():
  {==}

def Laws.etag_zero():
  {==}

def Laws.tags_same():
  {==}

def Laws.tags_weak():
  {==}

def Laws.tags_weak_not_strong():
  {==}

def Laws.tags_in_list():
  {==}

def Laws.tags_other():
  {==}

def Laws.tags_unquoted():
  {==}

def Laws.tags_star():
  {==}

def Laws.ask_read():
  {==}

def Laws.same_head_is_built(mt, n):
  cd.same(mt, n)

def Laws.part_head_is_built(ct, a, b, n, mt):
  cd.part(ct, a, b, n, mt)

def Laws.head_vectors():
  {==}

def Laws.not_modified_no_body(ct, fs, head, n, mt, e):
  %Equal.sym(C.Got, C.decide(C.ask.of(fs), mt, n), C.Same{}, e) :
    {C.fr.of(_, ct, head, n, mt) == L.Fr{C.hd.same.is(mt, n), 0, 0} : L.Fr}
  %cd.same(mt, n) : {L.Fr{C.hd.same(mt, n), 0, 0} == L.Fr{_, 0, 0} : L.Fr}
  {==}

def Laws.inm_over_ims(im, ius, v, ims1, ims2, rg, ir, mt, n):
  {==}

def Laws.tag_hit_not_modified(v, ims, rg, ir, mt, n, e):
  %Equal.sym(Bool, C.tags.hit(v, C.etag.of(mt, n), False{}), True{}, e) :
    {Bool.pick(C.Got, _, C.Same{}, C.part(rg, ir, mt, n, U32.to_nat(n))) == C.Same{} : C.Got}
  {==}

def Laws.star_not_modified(ims, rg, ir, mt, n):
  {==}

def Laws.ims_not_modified(v, rg, ir, mt, n, d, e, le):
  %Equal.sym(Maybe<&2, Nat>, C.date.read(v), Some{d}, e) :
    {C.ims.go(_, U32.to_nat(mt), C.part(rg, ir, mt, n, U32.to_nat(n))) == C.Same{} : C.Got}
  %Equal.sym(Bool, Nat.is_le(U32.to_nat(mt), d), True{}, le) :
    {Bool.pick(C.Got, _, C.Same{}, C.part(rg, ir, mt, n, U32.to_nat(n))) == C.Same{} : C.Got}
  {==}

def Laws.ims_echo(rg, ir, mt, n, ey):
  Laws.ims_not_modified(C.date.fmt(U32.to_nat(mt)), rg, ir, mt, n, U32.to_nat(mt),
    cp.date_rt(U32.to_nat(mt), ey), cp.le_refl(U32.to_nat(mt)))

def Laws.ims_changed(v, rg, ir, mt, n, d, e, gt):
  %Equal.sym(Maybe<&2, Nat>, C.date.read(v), Some{d}, e) :
    {C.ims.go(_, U32.to_nat(mt), C.part(rg, ir, mt, n, U32.to_nat(n))) ==
      C.part(rg, ir, mt, n, U32.to_nat(n)) : C.Got}
  %Equal.sym(Bool, Nat.is_le(U32.to_nat(mt), d), False{}, gt) :
    {Bool.pick(C.Got, _, C.Same{}, C.part(rg, ir, mt, n, U32.to_nat(n))) ==
      C.part(rg, ir, mt, n, U32.to_nat(n)) : C.Got}
  {==}

def Laws.ims_unreadable(v, rg, ir, mt, n, e):
  %Equal.sym(Maybe<&2, Nat>, C.date.read(v), None{}, e) :
    {C.ims.go(_, U32.to_nat(mt), C.part(rg, ir, mt, n, U32.to_nat(n))) ==
      C.part(rg, ir, mt, n, U32.to_nat(n)) : C.Got}
  {==}

def Laws.if_match_fails(v, ius, inm, ims, rg, ir, mt, n, e):
  %Equal.sym(Bool, C.tags.hit(v, C.etag.of(mt, n), True{}), False{}, e) :
    {Bool.pick(C.Got, _, C.cond(inm, ims, mt, n, C.part(rg, ir, mt, n, U32.to_nat(n))), C.Fails{}) ==
      C.Fails{} : C.Got}
  {==}

def Laws.ius_fails(v, inm, ims, rg, ir, mt, n, d, e, gt):
  %Equal.sym(Maybe<&2, Nat>, C.date.read(v), Some{d}, e) :
    {Bool.pick(C.Got, C.pre.ius(_, U32.to_nat(mt)), C.cond(inm, ims, mt, n, C.part(rg, ir, mt, n, U32.to_nat(n))),
      C.Fails{}) == C.Fails{} : C.Got}
  %Equal.sym(Bool, Nat.is_le(U32.to_nat(mt), d), False{}, gt) :
    {Bool.pick(C.Got, _, C.cond(inm, ims, mt, n, C.part(rg, ir, mt, n, U32.to_nat(n))), C.Fails{}) ==
      C.Fails{} : C.Got}
  {==}

def Laws.ius_unreadable(v, inm, ims, rg, ir, mt, n, e):
  %Equal.sym(Maybe<&2, Nat>, C.date.read(v), None{}, e) :
    {Bool.pick(C.Got, C.pre.ius(_, U32.to_nat(mt)), C.cond(inm, ims, mt, n, C.part(rg, ir, mt, n, U32.to_nat(n))),
      C.Fails{}) == C.cond(inm, ims, mt, n, C.part(rg, ir, mt, n, U32.to_nat(n))) : C.Got}
  {==}

def Laws.range_from_unsat(a, mb, n, e):
  match mb:
    case None{}:
      %Equal.sym(Bool, Nat.is_lt(a, n), False{}, e) :
        {C.want.from(_, a, Nat.sub(n, 1n)) == C.Unsat{} : C.Want}
      {==}
    case Some{b}:
      %Equal.sym(Bool, Nat.is_lt(a, n), False{}, e) :
        {C.want.from(Bool.and(_, Nat.is_le(a, b)), a, Nat.min(b, Nat.sub(n, 1n))) == C.Unsat{} : C.Want}
      {==}

def Laws.range_from(a, n, e):
  %Equal.sym(Bool, Nat.is_lt(a, n), True{}, e) :
    {C.want.from(_, a, Nat.sub(n, 1n)) == C.Span{a, Nat.sub(n, 1n)} : C.Want}
  {==}

def Laws.range_from_to(a, b, n, e, le):
  %Equal.sym(Bool, Nat.is_lt(a, n), True{}, e) :
    {C.want.from(Bool.and(_, Nat.is_le(a, b)), a, Nat.min(b, Nat.sub(n, 1n))) ==
      C.Span{a, Nat.min(b, Nat.sub(n, 1n))} : C.Want}
  %Equal.sym(Bool, Nat.is_le(a, b), True{}, le) :
    {C.want.from(_, a, Nat.min(b, Nat.sub(n, 1n))) == C.Span{a, Nat.min(b, Nat.sub(n, 1n))} : C.Want}
  {==}

def Laws.range_suffix_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def Laws.range_suffix(j, m):
  {==}

def Laws.range_vectors():
  {==}

def Laws.part_in_file(k, mt, n, a, b, e):
  cq.part_in(k, mt, n, a, b, e)

def Laws.one_range(v, sp, mt, n, p, a, b, e, w):
  %Equal.sym(Maybe<&2, List<&2, C.Spec>>, C.rg.parse(v), Some{[sp]}, e) :
    {C.ranged(_, 1n+p) == C.Part{a, b} : C.Got}
  %Equal.sym(C.Want, C.want(sp, 1n+p), C.Span{a, b}, w) :
    {C.got.of(Con{_, Nil{}}, None{}, 0n) == C.Part{a, b} : C.Got}
  {==}

def Laws.no_range(v, sp, mt, n, p, e, w):
  %Equal.sym(Maybe<&2, List<&2, C.Spec>>, C.rg.parse(v), Some{[sp]}, e) :
    {C.ranged(_, 1n+p) == C.NoPart{} : C.Got}
  %Equal.sym(C.Want, C.want(sp, 1n+p), C.Unsat{}, w) :
    {C.got.of(Con{_, Nil{}}, None{}, 0n) == C.NoPart{} : C.Got}
  {==}

def Laws.two_ranges(v, s1, s2, mt, n, p, a, b, c, d, e, w1, w2):
  %Equal.sym(Maybe<&2, List<&2, C.Spec>>, C.rg.parse(v), Some{[s1, s2]}, e) :
    {C.ranged(_, 1n+p) == C.Full{} : C.Got}
  %Equal.sym(C.Want, C.want(s1, 1n+p), C.Span{a, b}, w1) :
    {C.got.of(Con{_, Con{C.want(s2, 1n+p), Nil{}}}, None{}, 0n) == C.Full{} : C.Got}
  %Equal.sym(C.Want, C.want(s2, 1n+p), C.Span{c, d}, w2) :
    {C.got.of(Con{C.Span{a, b}, Con{_, Nil{}}}, None{}, 0n) == C.Full{} : C.Got}
  {==}

def cq.pick_full(c: Bool) -> {Bool.pick(C.Got, c, C.Full{}, C.Full{}) == C.Full{} : C.Got}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.range_ignored(v, n, ir, mt, n32, e):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match ir:
        case None{}:
          %Equal.sym(Maybe<&2, List<&2, C.Spec>>, C.rg.parse(v), None{}, e) :
            {C.ranged(_, 1n+p) == C.Full{} : C.Got}
          {==}
        case Some{w}:
          %Equal.sym(Maybe<&2, List<&2, C.Spec>>, C.rg.parse(v), None{}, e) :
            {Bool.pick(C.Got, C.ir.ok(w, mt, n32), C.ranged(_, 1n+p), C.Full{}) == C.Full{} : C.Got}
          cq.pick_full(C.ir.ok(w, mt, n32))

def Laws.if_range_stale(v, w, mt, n, p, e):
  %Equal.sym(Bool, C.ir.ok(w, mt, n), False{}, e) :
    {Bool.pick(C.Got, _, C.ranged(C.rg.parse(v), 1n+p), C.Full{}) == C.Full{} : C.Got}
  {==}

def Laws.if_range_fresh(v, w, mt, n, p, e):
  %Equal.sym(Bool, C.ir.ok(w, mt, n), True{}, e) :
    {Bool.pick(C.Got, _, C.ranged(C.rg.parse(v), 1n+p), C.Full{}) == C.ranged(C.rg.parse(v), 1n+p) : C.Got}
  {==}

def Laws.parse_vectors():
  {==}

def Laws.part_frame(ct, head, a, b, n, mt):
  %cd.part(ct, a, b, n, mt) :
    {L.Fr{C.hd.part(ct, a, b, n, mt), U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a))} ==
      L.Fr{_, U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a))} : L.Fr}
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
  Wr.feed_split(~Unit, ~Ws.W, ~Ws.wstep, Unit{}, a, b, w)

def Laws.ws_bad_absorbs(c, out):
  {==}

# a refused frame reader, as the kit's absorbing states
def ws.bad(out: List<&2, Ws.Frm>) -> Ws.W:
  Ws.W{Ws.Bad{}, out}

def ws.absorbs(+u: Unit, +out: List<&2, Ws.Frm>, +c: U32) ->
  {Ws.wstep(u, ws.bad(out), c) == ws.bad(out) : Ws.W}:
  {==}

def Laws.ws_bad_feeds(s, out):
  Wr.bad_feeds(~Unit, ~Ws.W, ~Ws.wstep, ~List<&2, Ws.Frm>, ~ws.bad, ~ws.absorbs, Unit{}, s, out)

# the frame reader walks a read a byte at a time, so its block laws are
# the kit's for the slow walk, with no obligation
def Laws.ws_feed_buf(b, w):
  Wr.slow_is_feed(~Unit, ~Ws.W, ~Ws.wstep, Unit{}, b, w)

def Laws.ws_feed_buf_split(a, b, w):
  Wr.slow_split(~Unit, ~Ws.W, ~Ws.wstep, Unit{}, a, b, w)

def Laws.ws_bad_feeds_buf(s, out):
  Wr.bad_feeds_slow(~Unit, ~Ws.W, ~Ws.wstep, ~List<&2, Ws.Frm>, ~ws.bad, ~ws.absorbs, Unit{}, s,
    out)

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

# batch_under is the loop's (wire/world.bend)
def Laws.batch_under(k):
  WW.batch_under(k)

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
  WW.hw_rest(hw)

def Laws.hw_keeps(t0, n):
  WW.hw_keeps(t0, n)

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
# The loops are bend-wire's, and so are their laws: wire/world.bend
# proves each once, for every protocol's hooks, and each law of the
# engine's world below is that law at the engine's hooks (world.bend).
# The one obligation the loop's laws ask of a protocol, that an event
# of a stream is never empty (stall_ends), the engine discharges by
# computation (W.event_ok). What is the engine's own is the refusal:
# refuse_* walk answer.go one request at a time, and plan.ans through
# the owed replies.

def Laws.end_is_last(srv, w, out, hw, g, v):
  WW.end_is_last(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, w, out, hw, g, v)

def Laws.stop_is_last(srv, w, hw, g, v):
  WW.stop_is_last(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, w, hw, g, v)

def Laws.go_order(srv, w, out, p2, hw, g, v):
  WW.go_order(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, w, out, p2, hw, g, v)

def Laws.fail_go(srv, g, v, m, p, hw, e):
  WW.fail_go(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, g, v, m, p, hw, e)

def Laws.fail_ws(srv, g, v, m, wr, e):
  WW.fail_up(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, g, v, m, wr, e)

def Laws.fail_feed(srv, g, v, m, n, e):
  WW.fail_feed(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, g, v, m, n, e)

def Laws.head_expires(srv, w, p, t0, n, e):
  WW.head_expires(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.resp.big(), srv, w, p, t0, n, e)

def Laws.head_capped(srv, w, may, p, t0, n):
  WW.head_capped(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.h.plan, ~Eng.resp.big(), srv, w, may, p, t0, n)

def Laws.hold_fine(ms, s, acc):
  WW.hold_fine(ms, s, acc)

def Laws.raw_fine(ms, may, bs, st):
  WW.raw_fine(~Eng.h.lnote, ms, may, bs, st)

def Laws.page_fine(ms, root, path, ct, ask, head, may, sh, st):
  WW.page_fine(~Eng.h.shut, ~Eng.h.fhead, ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, ms, root, path, ct, ask, head, may, sh, st)

def Laws.page_wire(ms, root, path, ct, ask, may, sh, rd, now, fs, out, acc, body, hd, off, len, ef, en, efr, ep):
  WW.page_wire(~Eng.h.shut, ~Eng.h.fhead, ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, ms, root, path,
    ct, ask, may, sh, rd, now, fs, out, acc, body, hd, off, len, ef, en, efr, ep)

# range_wire: the decision's Part frames the file as page_wire needs it
# (the head hd.part, the offset a, the length b + 1 - a), the part is all
# in the file (part_in_file), and hd.part is hd.part.is
def cq.range_ep(+body: Bytes(), +a: Nat, +b: Nat,
  +ea: {U32.to_nat(U32.from_nat(a)) == a : Nat},
  +el: {U32.to_nat(U32.from_nat(Nat.sub(1n+b, a))) == Nat.sub(1n+b, a) : Nat},
  +en: {U32.to_nat(U32.from_nat(Bytes.len(body))) == Bytes.len(body) : Nat},
  pin: {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_lt(b, U32.to_nat(U32.from_nat(Bytes.len(body)))) == True{} : Bool}) ->
  {WW.wl.part(body, U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a))) == True{} : Bool}:
  (le, lt) = pin
  cq.part_ep(body, a, b, ea, el, le,
    %en : {Nat.is_lt(b, _) == True{} : Bool}
    lt)

def Laws.range_wire(ms, root, path, ct, ask, may, sh, rd, now, fs, out, acc, body, a, b, ef, en, er, ea, el):
  %cd.part(ct, a, b, U32.from_nat(Bytes.len(body)), 0) :
    {W.sim.page(ms, root, path, ct, ask, False{}, may, sh, L.Em{WW.eager(rd, now, fs, out), acc, True{}}) ==
      L.Em{WW.eager(rd, now, fs, Bytes.append(Bytes.append(out, Bytes.append(acc, Eng.h.shut(sh, _))),
        String.take(String.drop(body, a), Nat.sub(1n+b, a)))), "", True{}} : L.Em<WW.World>}
  %ea :
    {W.sim.page(ms, root, path, ct, ask, False{}, may, sh, L.Em{WW.eager(rd, now, fs, out), acc, True{}}) ==
      L.Em{WW.eager(rd, now, fs, Bytes.append(Bytes.append(out, Bytes.append(acc,
        Eng.h.shut(sh, C.hd.part(ct, a, b, U32.from_nat(Bytes.len(body)), 0)))),
        String.take(String.drop(body, _), Nat.sub(1n+b, a)))), "", True{}} : L.Em<WW.World>}
  %el :
    {W.sim.page(ms, root, path, ct, ask, False{}, may, sh, L.Em{WW.eager(rd, now, fs, out), acc, True{}}) ==
      L.Em{WW.eager(rd, now, fs, Bytes.append(Bytes.append(out, Bytes.append(acc,
        Eng.h.shut(sh, C.hd.part(ct, a, b, U32.from_nat(Bytes.len(body)), 0)))),
        String.take(String.drop(body, U32.to_nat(U32.from_nat(a))), _))), "", True{}} : L.Em<WW.World>}
  Laws.page_wire(ms, root, path, ct, ask, may, sh, rd, now, fs, out, acc, body,
    C.hd.part(ct, a, b, U32.from_nat(Bytes.len(body)), 0), U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a)),
    ef, en,
    %Equal.sym(C.Got, C.decide(C.ask.of(ask), 0, U32.from_nat(Bytes.len(body))), C.Part{a, b}, er) :
      {C.fr.of(_, ct, False{}, U32.from_nat(Bytes.len(body)), 0) ==
        L.Fr{C.hd.part(ct, a, b, U32.from_nat(Bytes.len(body)), 0), U32.from_nat(a),
          U32.from_nat(Nat.sub(1n+b, a))} : L.Fr}
    {==},
    cq.range_ep(body, a, b, ea, el, en, cq.part_in(C.ask.of(ask), 0, U32.from_nat(Bytes.len(body)), a, b, er)))

def Laws.page_fail(s, f, e):
  WW.page_fail(s, f, e)

def Laws.page_head_fail(ms, f, off, len, s, e):
  WW.page_head_fail(ms, f, off, len, s, e)

def Laws.accept_calm(k, evs, served, e):
  WW.accept_calm(k, evs, served, e)

def Laws.accept_ends(k, sp, evs, served):
  WW.accept_ends(k, sp, evs, served)

# one request's step through answer.go, when its reply keeps the
# connection: the reply joins the batch as it was, and the walk goes on
law wl.ag_step:
  for +srv: Eng.Srv
  for +t: List<&2, Eng.Req>
  for c: Bool
  for +s: U32
  for k: Bool
  for +o: List<&2, L.Seg>
  for +acc: List<&2, List<&2, L.Seg>>
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
  for +acc: List<&2, List<&2, L.Seg>>
  for +e: {W.all.keep(srv, rs) == True{} : Bool}
  {Eng.answer.go(srv, rs, True{}, True{}, c, s, k, acc) ==
    Eng.Ans{Eng.answer.flat(acc, W.owed(srv, rs, W.bad.reply())), True{}, 0, False{}} : Eng.Ans}

def wl.ag_owed(srv, rs, c, s, k, acc, e):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      wl.ag_step(srv, t, W.ag.c(srv, r), W.ag.s(srv, r), W.ag.k(srv, r), W.ag.o(srv, r), acc,
        WW.wl.and_l(W.keeps(srv, r), W.all.keep(srv, t), e),
        wl.ag_owed(srv, t, W.ag.c(srv, r), W.ag.s(srv, r), W.ag.k(srv, r), Con{W.ag.o(srv, r), acc},
          WW.wl.and_r(W.keeps(srv, r), W.all.keep(srv, t), e)))

law wl.ans_end_app:
  for xs: List<&2, L.Seg>
  for +ys: List<&2, L.Seg>
  for +q: Eng.P
  for e: {Eng.plan.ans(Eng.Ans{ys, True{}, 0, False{}}, q) == L.End{ys} : Eng.Plan()}
  {Eng.plan.ans(Eng.Ans{List.append(&2, L.Seg, xs, ys), True{}, 0, False{}}, q) ==
    L.End{List.append(&2, L.Seg, xs, ys)} : Eng.Plan()}

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
    L.End{W.owed(srv, rs, W.bad.reply())} : Eng.Plan()}

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
    {Eng.plan.ans(_, q) == L.End{W.owed(srv, rs, W.bad.reply())} : Eng.Plan()}
  wl.ans_end_owed(srv, rs, q)

def Laws.refuse_conn(srv, w, q, rs, hw, g, v, e):
  %Equal.sym(Eng.Plan(), Eng.plan.take(srv, (q, rs), True{}), L.End{W.owed(srv, rs, W.bad.reply())},
    Laws.refuse_plan(srv, rs, q, e)) :
    {W.sim.conn(1n+g, srv, ((w, _), hw), v) ==
      L.put.s(WW.World, W.sim.segs(w, W.owed(srv, rs, W.bad.reply()), Eng.srv.idle(srv))) : WW.World}
  {==}

def Laws.segs_wire(xs, ms, rd, now, fs, out, e):
  WW.segs_wire(~Eng.h.shut, ~Eng.h.fhead, ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, xs, ms, rd, now, fs, out, e)

def Laws.stall_ends(srv, w, pl, hw, g, v):
  WW.stall_ends(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, ~W.event_ok, srv, w, pl, hw, g, v)

def Laws.rx_model(rd, wr, eager, now, fs, out, max, ms, e):
  WW.rx_model(rd, wr, eager, now, fs, out, max, ms, e)

def Laws.tx_stalled(rd, now, fs, out, h, t, ms):
  WW.tx_stalled(rd, now, fs, out, h, t, ms)

def Laws.tx_served(rd, now, fs, out, a, ms):
  WW.tx_served(rd, now, fs, out, a, ms)

def Laws.fread_model(f, n):
  WW.fread_model(f, n)

def Laws.fsend_model(rd, now, fs, out, f, off, len, ms):
  WW.fsend_model(rd, now, fs, out, f, off, len, ms)

def Laws.fsend_stalled(rd, now, fs, out, f, off, len, ms, h, t, e):
  WW.fsend_stalled(rd, now, fs, out, f, off, len, ms, h, t, e)

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

def pd1(+m: List<&2, U32>) -> Eng.Pend:
  Eng.pend.meth(Eng.pend.new(), Eng.meth.of(Bytes.from_list(m)), Bytes.from_list(m))

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
        Spec.named("keep-alive", d), Spec.lowall(d)}, pd, out} : Eng.P}
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
    case Spec.VHost{n, v}:
      {p == Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(Eng.pend.host(pd), n), out} : Eng.P}
    case Spec.VSkip{n, v}:
      {p == Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(pd, n), out} : Eng.P}

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

# a value passed on: the Host's, or any field's this engine does not act
# on, kept as it came, with the field's name
def G.pass(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  Dead(Eng.feed(rest, Eng.step.at(Eng.InLx{Bytes.append("", Bytes.from_list(v))}, k, c, pd, out)), out)

def K.pass.at(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TVal{}, k) == False{} : Bool},
  nc: {notcrlf(k) == True{} : Bool}) -> G.pass(k, c, rest, v, pd, out):
  match k:
    case Eng.KCr{}:
      no(G.pass(Eng.KCr{}, c, rest, v, pd, out), nc)
    case Eng.KLf{}:
      dead.bad(rest, pd, out)
    case Eng.KCt{}:
      dead.bad(rest, pd, out)
    case Eng.KSp{}:
      no2(G.pass(Eng.KSp{}, c, rest, v, pd, out), mx)
    case Eng.KHt{}:
      no2(G.pass(Eng.KHt{}, c, rest, v, pd, out), mx)
    case Eng.KCo{}:
      no2(G.pass(Eng.KCo{}, c, rest, v, pd, out), mx)
    case Eng.KCm{}:
      no2(G.pass(Eng.KCm{}, c, rest, v, pd, out), mx)
    case Eng.KDg{}:
      no2(G.pass(Eng.KDg{}, c, rest, v, pd, out), mx)
    case Eng.KTk{}:
      no2(G.pass(Eng.KTk{}, c, rest, v, pd, out), mx)
    case Eng.KVc{}:
      no2(G.pass(Eng.KVc{}, c, rest, v, pd, out), mx)

def K.pass.sat(+k: Eng.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>,
  sw: {Spec.allows(Spec.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.pass(k, c, rest, v, pd, out):
  (mx, np) = sw
  (nc, pr) = np
  K.pass.at(k, c, rest, v, pd, out, mx, nc)

def K.host(sp: Spec.Span, +n: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelR{Eng.RX{}}, "", Eng.pend.nm(Eng.pend.host(pd), n), out), Spec.host.view(n, sp), pd, out):
  match sp:
    case Spec.Span{r, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{r, Spec.SAt{k, c, rest}}:
      sw => K.pass.sat(k, c, rest, r, Eng.pend.nm(Eng.pend.host(pd), n), out, sw)

def K.other(sp: Spec.Span, +n: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> SW(Spec.TVal{}, sp) ->
  LR.field(RES(sp, SelR{Eng.RX{}}, "", Eng.pend.nm(pd, n), out), Spec.skip.view(n, sp), pd, out):
  match sp:
    case Spec.Span{r, Spec.SEnd{}}:
      sw => {==}
    case Spec.Span{r, Spec.SAt{k, c, rest}}:
      sw => K.pass.sat(k, c, rest, r, Eng.pend.nm(pd, n), out, sw)

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
  LR.field(Eng.feed(x, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)}, pd, out}),
    Spec.list.view(True{}, Spec.members(x, True{}, done, cur)), pd, out)

def G.memc(+k: Eng.Cls, +c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>,
  +cur: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(t, Eng.step.at(Eng.InLc{lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)},
      k, c, pd, out)),
    Spec.list.view(True{}, Spec.members(t, Spec.allows(Spec.TVal{}, k), Spec.mem.done(Spec.mem.sep(k), done, cur),
      Spec.mem.cur(Spec.mem.sep(k), cur, c))), pd, out)

def MEMc.sep(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pt: Plain(t), ih: Plain(t) -> MC(t, Con{cur, done}, Nil{}, pd, out)) ->
  LR.field(Eng.feed(t, Eng.P{Eng.tok.conn(lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)), pd, out}),
    Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out):
  %eqs(lowb(cur), "close") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{"", Spec.named("close", done) || _,
      Spec.named("upgrade", done) || Eng.bytes.eq(lowb(cur), "upgrade"),
      Spec.named("keep-alive", done) || Eng.bytes.eq(lowb(cur), "keep-alive"), Con{lowb(cur), Spec.lowall(done)}}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  %eqs(lowb(cur), "upgrade") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{"", Spec.named("close", done) || Spec.eq(lowb(cur), "close"),
      Spec.named("upgrade", done) || _,
      Spec.named("keep-alive", done) || Eng.bytes.eq(lowb(cur), "keep-alive"), Con{lowb(cur), Spec.lowall(done)}}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  %eqs(lowb(cur), "keep-alive") :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{"", Spec.named("close", done) || Spec.eq(lowb(cur), "close"),
      Spec.named("upgrade", done) || Spec.eq(lowb(cur), "upgrade"),
      Spec.named("keep-alive", done) || _, Con{lowb(cur), Spec.lowall(done)}}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, Con{cur, done}, Nil{})), pd, out)
  ih(pt)

def MEMc.in(+c: U32, +t: List<&2, U32>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +pd: Eng.Pend, +out: List<&2, Eng.Req>, pt: Plain(t), ih: Plain(t) -> MC(t, done, Spec.snoc(cur, c), pd, out)) ->
  LR.field(Eng.feed(t, Eng.P{Eng.InLc{Eng.push(lowb(cur), Eng.lower(c)), Spec.named("close", done),
      Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)}, pd, out}),
    Spec.list.view(True{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out):
  %br.lower(c) :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{Eng.push(lowb(cur), _), Spec.named("close", done),
      Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)}, pd, out}),
      Spec.list.view(True{}, Spec.members(t, True{}, done, Spec.snoc(cur, c))), pd, out)
  %lb.snoc(cur, c) :
    LR.field(Eng.feed(t, Eng.P{Eng.InLc{_, Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)}, pd, out}),
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
  %feedc(c, t, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", done), Spec.named("upgrade", done), Spec.named("keep-alive", done), Spec.lowall(done)}, pd, out}) :
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

# A name looked up only when as long as a name in the table
# (fld.name): a name of another length is spelled with none of the
# table's bytes, so the lookup would have found no field
def or_f_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Bool.no({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, e))

def or_f_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Bool.no({b == False{} : Bool}, Equal.sym(Bool, True{}, False{}, e))

def and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and3(a: Bool, x: Bool, -e: Bool, ih: {Bool.and(a, e) == e : Bool}) ->
  {Bool.and(a, Bool.and(x, e)) == Bool.and(x, e) : Bool}:
  match x:
    case False{}:
      and_f(a)
    case True{}:
      ih

# two blocks of different lengths are not equal
def eq_and(+a: Bytes(), +b: Bytes()) ->
  {Bool.and(Nat.is_eq(Bytes.len(a), Bytes.len(b)), Spec.eq(a, b)) == Spec.eq(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{y}, u}:
      and_f(Nat.is_eq(0n, String.length.go(u, 1n)))
    case SCon{Chr{x}, t} SNil{}:
      and_f(Nat.is_eq(String.length.go(t, 1n), 0n))
    case SCon{Chr{+x}, +t} SCon{Chr{+y}, +u}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {Bool.and(Nat.is_eq(_, String.length.go(u, 1n)), Bool.and(U32.is_eq(x, y), Spec.eq(t, u))) ==
          Bool.and(U32.is_eq(x, y), Spec.eq(t, u)) : Bool}
      %Equal.sym(Nat, String.length.go(u, 1n), 1n+String.length.go(u, 0n), len_shift(u)) :
        {Bool.and(Nat.is_eq(1n+String.length.go(t, 0n), _), Bool.and(U32.is_eq(x, y), Spec.eq(t, u))) ==
          Bool.and(U32.is_eq(x, y), Spec.eq(t, u)) : Bool}
      and3(Nat.is_eq(String.length.go(t, 0n), String.length.go(u, 0n)), U32.is_eq(x, y), Spec.eq(t, u),
        eq_and(t, u))

def eq_len(+a: Bytes(), +b: Bytes(), e: {Nat.is_eq(Bytes.len(a), Bytes.len(b)) == False{} : Bool}) ->
  {Spec.eq(a, b) == False{} : Bool}:
  Equal.trans(Bool, Spec.eq(a, b), Bool.and(Nat.is_eq(Bytes.len(a), Bytes.len(b)), Spec.eq(a, b)), False{},
    Equal.sym(Bool, Bool.and(Nat.is_eq(Bytes.len(a), Bytes.len(b)), Spec.eq(a, b)), Spec.eq(a, b), eq_and(a, b)),
    %Equal.sym(Bool, Nat.is_eq(Bytes.len(a), Bytes.len(b)), False{}, e) :
      {Bool.and(_, Spec.eq(a, b)) == False{} : Bool}
    {==})

# a table none of whose names is as long as k finds no field for k
def find_miss(+k: Bytes(), tbl: List<&2, Eng.Known>,
  +e: {Eng.fld.len.any(Bytes.len(k), tbl) == False{} : Bool}) -> {Spec.find(k, tbl) == Eng.FOther{} : Eng.Fld}:
  match tbl:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Eng.Known{+n, f}:
          %Equal.sym(Bool, Spec.eq(k, n), False{},
            eq_len(k, n, or_f_l(Nat.is_eq(Bytes.len(k), Bytes.len(n)), Eng.fld.len.any(Bytes.len(k), t), e))) :
            {Eng.fld.pick(_, f, Spec.find(k, t)) == Eng.FOther{} : Eng.Fld}
          find_miss(k, t, or_f_r(Nat.is_eq(Bytes.len(k), Bytes.len(n)), Eng.fld.len.any(Bytes.len(k), t), e))

# lowercasing keeps a name's length
def lows_len(s: Bytes(), -m: Nat) -> {String.length.go(String.to_lower(s), m) == String.length.go(s, m) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      lows_len(t, 1n+m)

def fld_miss(+n: Bytes(), e: {Eng.fld.len.ok(Bytes.len(n)) == False{} : Bool}) ->
  {Eng.fld.of(Eng.lows(n)) == Eng.FOther{} : Eng.Fld}:
  Equal.trans(Eng.Fld, Eng.fld.of(Eng.lows(n)), Spec.find(Eng.lows(n), Eng.fld.table()), Eng.FOther{},
    scan_is(Eng.fld.table(), Eng.lows(n), None{}),
    find_miss(Eng.lows(n), Eng.fld.table(),
      %Equal.sym(Nat, Bytes.len(Eng.lows(n)), Bytes.len(n), lows_len(n, 0n)) :
        {Eng.fld.len.any(_, Eng.fld.table()) == False{} : Bool}
      e))

def fld_gate(+n: Bytes(), b: Bool) -> {Eng.fld.len.ok(Bytes.len(n)) == b : Bool} ->
  {Eng.fld.gate(b, n) == Eng.fld.of(Eng.lows(n)) : Eng.Fld}:
  match b:
    case True{}:
      e => {==}
    case False{}:
      e => Equal.sym(Eng.Fld, Eng.fld.of(Eng.lows(n)), Eng.FOther{}, fld_miss(n, e))

def fld_name(+n: Bytes()) -> {Eng.fld.name(n) == Eng.fld.of(Eng.lows(n)) : Eng.Fld}:
  fld_gate(n, Eng.fld.len.ok(Bytes.len(n)))({==})

# a field, by its name: the value read the way the name says
def fbb(+k: Bytes()) -> {Spec.field(k) == Eng.fld.of(k) : Eng.Fld}:
  Equal.sym(Eng.Fld, Eng.fld.of(k), Spec.field(k), scan_is(Eng.fld.table(), k, None{}))

def K.of(f: Eng.Fld, +nm: Bytes(), +v: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>) -> Plain(v) ->
  LR.field(Eng.feed(v, Eng.step.name(f, nm, pd, out)), Spec.field.of(f, Eng.lows(nm), v), pd, out):
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
        %RS(v, SelR{Eng.RX{}}, "", Eng.pend.nm(Eng.pend.host(pd), Eng.lows(nm)), out) :
          LR.field(_, Spec.host.view(Eng.lows(nm), Spec.span(Spec.TVal{}, v)), pd, out)
        K.host(Spec.span(Spec.TVal{}, v), Eng.lows(nm), pd, out)(span.sw(Spec.TVal{}, v)(pl))
    case Eng.FVer{}:
      pl =>
        %RS(v, SelLv{}, "", pd, out) : LR.field(_, Spec.ver.view(Spec.span(Spec.TVal{}, v)), pd, out)
        K.vv(Spec.span(Spec.TVal{}, v), pd, out)(span.sw(Spec.TVal{}, v)(pl))
    case Eng.FOther{}:
      pl =>
        %RS(v, SelR{Eng.RX{}}, "", Eng.pend.nm(pd, Eng.lows(nm)), out) :
          LR.field(_, Spec.skip.view(Eng.lows(nm), Spec.span(Spec.TVal{}, v)), pd, out)
        K.other(Spec.span(Spec.TVal{}, v), Eng.lows(nm), pd, out)(span.sw(Spec.TVal{}, v)(pl))

# a name
def G.name(+k: Eng.Cls, +d: U32, +v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>) -> Type:
  LR.field(Eng.feed(v, Eng.step.at(Eng.InN{Bytes.from_list(Con{c, r})}, k, d, pd, out)),
    Spec.field.name(Spec.Span{Con{c, r}, Spec.SAt{k, d, v}}), pd, out)

def K.name.colon(+v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  pr: Plain(v)) ->
  LR.field(Eng.feed(v, Eng.step.name(Eng.fld.of(Eng.lows(Bytes.from_list(Con{c, r}))), Bytes.from_list(Con{c, r}), pd, out)),
    Spec.field.at(Spec.lows(Bytes.from_list(Con{c, r})), v), pd, out):
  %br.lows(Bytes.from_list(Con{c, r})) :
    LR.field(Eng.feed(v, Eng.step.name(Eng.fld.of(_), Bytes.from_list(Con{c, r}), pd, out)),
      Spec.field.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), Spec.lows(Bytes.from_list(Con{c, r})), v), pd, out)
  %fbb(Spec.lows(Bytes.from_list(Con{c, r}))) :
    LR.field(Eng.feed(v, Eng.step.name(_, Bytes.from_list(Con{c, r}), pd, out)),
      Spec.field.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), Spec.lows(Bytes.from_list(Con{c, r})), v), pd, out)
  %Equal.sym(Bytes(), Spec.lows(Bytes.from_list(Con{c, r})), Eng.lows(Bytes.from_list(Con{c, r})), br.lows(Bytes.from_list(Con{c, r}))) :
    LR.field(Eng.feed(v, Eng.step.name(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), Bytes.from_list(Con{c, r}), pd, out)),
      Spec.field.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), _, v), pd, out)
  K.of(Spec.field(Spec.lows(Bytes.from_list(Con{c, r}))), Bytes.from_list(Con{c, r}), v, pd, out)(pr)

def K.name.at(+k: Eng.Cls, +d: U32, +v: List<&2, U32>, +c: U32, +r: List<&2, U32>, +pd: Eng.Pend,
  +out: List<&2, Eng.Req>, mx: {Spec.allows(Spec.TName{}, k) == False{} : Bool}, pr: Plain(v)) ->
  G.name(k, d, v, c, r, pd, out):
  match k:
    case Eng.KCo{}:
      %Equal.sym(Eng.Fld, Eng.fld.name(Bytes.from_list(Con{c, r})), Eng.fld.of(Eng.lows(Bytes.from_list(Con{c, r}))),
        fld_name(Bytes.from_list(Con{c, r}))) :
        LR.field(Eng.feed(v, Eng.step.name(_, Bytes.from_list(Con{c, r}), pd, out)),
          Spec.field.at(Spec.lows(Bytes.from_list(Con{c, r})), v), pd, out)
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
  PV{meth: Eng.Meth, path: Bytes(), cl: Eng.Cl, close: Bool, host: Eng.Hosts, u: UV, fx: Eng.Fx, hx: Eng.Hx}

def uv(ws: Eng.Up) -> UV:
  match ws:
    case Eng.Plain{}:
      UV{"", False{}, False{}, False{}}
    case Eng.Asks{k, u, c, v}:
      UV{k, u, c, v}

def pv(pd: Eng.Pend) -> PV:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      PV{m, p, cl, close, host, uv(ws), fx, hx}

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
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      PV{m, Bytes.from_list(t), clv(l), cl, hsat(hs), UV{Bytes.from_list(k), u, c, v}, f, hxx}

def PR(-pd: Eng.Pend, -h: Spec.Head) -> Data:
  {pv(pd) == hv(h) : PV}

# a change seen the same on both sides is the same change
def pr.by(-f: PV -> PV, -pd: Eng.Pend, -pd2: Eng.Pend, -h: Spec.Head, -h2: Spec.Head,
  e1: {pv(pd2) == f(pv(pd)) : PV}, e2: {f(hv(h)) == hv(h2) : PV}, pr: PR(pd, h)) -> PR(pd2, h2):
  Equal.trans(PV, pv(pd2), f(pv(pd)), hv(h2), e1,
    Equal.trans(PV, f(pv(pd)), f(hv(h)), hv(h2), Equal.cong(PV, PV, f, pv(pd), hv(h), pr), e2))

def pv.conn(x: PV, a: Bool, b: Bool, k: Bool) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close || a, host, UV{kk, uu, c || b, v}, Eng.fx.ka(fx, k), hx}

def pv.up(x: PV, w: Bool) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close, host, UV{kk, uu || w, c, v}, fx, hx}

def pv.key(x: PV, kb: Bytes()) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close, host, UV{kb, uu, c, v}, fx, hx}

def pv.ver(x: PV, ok: Bool) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match u:
        case UV{kk, uu, c, v}:
          PV{m, p, cl, close, host, UV{kk, uu, c, v || Bool.not(ok)}, fx, hx}

def pv.host(x: PV) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      PV{m, p, cl, close, Eng.hosts.more(host), u, fx, hx}

def pv.cl(x: PV, l: Eng.Cl) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      PV{m, p, l, close, host, u, fx, hx}

# a field passed on, and a Connection's members
def pv.fld(x: PV, +n: Bytes(), vb: Bytes()) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match hx:
        case Eng.Hx{mb, o, fs, cn}:
          PV{m, p, cl, close, host, u, fx, Eng.Hx{mb, n, Con{Wr.Field{n, vb}, fs}, cn}}

def pv.cn(x: PV, ms: List<&2, Bytes()>) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match hx:
        case Eng.Hx{mb, o, fs, cn}:
          PV{m, p, cl, close, host, u, fx, Eng.Hx{mb, o, fs, List.append(&2, Bytes(), ms, cn)}}

def pv.te(x: PV) -> PV:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match fx:
        case Eng.Fx{a, b, c}:
          PV{m, p, cl, close, host, u, Eng.Fx{a, b, True{}}, hx}

# the engine's side of each change
def e.conn(pd: Eng.Pend, +a: Bool, +b: Bool, +k: Bool) ->
  {pv(Eng.pend.conn(pd, a, b, k)) == pv.conn(pv(pd), a, b, k) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match ws b:
        case Eng.Plain{} False{}:
          {==}
        case Eng.Plain{} True{}:
          {==}
        case Eng.Asks{kk, u, c, v} w:
          {==}

def e.up(pd: Eng.Pend, +w: Bool) -> {pv(Eng.pend.up(pd, w)) == pv.up(pv(pd), w) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match ws w:
        case Eng.Plain{} False{}:
          {==}
        case Eng.Plain{} True{}:
          {==}
        case Eng.Asks{k, u, c, v} x:
          {==}

def e.key(pd: Eng.Pend, +kb: Bytes()) -> {pv(Eng.pend.key(pd, kb)) == pv.key(pv(pd), kb) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match ws:
        case Eng.Plain{}:
          {==}
        case Eng.Asks{k, u, c, v}:
          {==}

def e.ver(pd: Eng.Pend, +ok: Bool) -> {pv(Eng.pend.ver(pd, ok)) == pv.ver(pv(pd), ok) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match ws ok:
        case Eng.Plain{} True{}:
          {==}
        case Eng.Plain{} False{}:
          {==}
        case Eng.Asks{k, u, c, v} x:
          {==}

def e.host(pd: Eng.Pend) -> {pv(Eng.pend.host(pd)) == pv.host(pv(pd)) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      {==}

# and the spec's
def s.conn(h: Spec.Head, -a: Bool, -b: Bool, -k: Bool) ->
  {pv.conn(hv(h), a, b, k) == hv(Spec.head.conn(h, a, b, k)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, kk, u, c, v, f, hxx}:
      match f:
        case Eng.Fx{v10, ka, te}:
          {==}

def s.up(h: Spec.Head, -w: Bool) -> {pv.up(hv(h), w) == hv(Spec.head.up(h, w)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      {==}

def s.key(h: Spec.Head, -kl: List<&2, U32>) ->
  {pv.key(hv(h), Bytes.from_list(kl)) == hv(Spec.head.key(h, kl)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      {==}

def s.ver(h: Spec.Head, -ok: Bool) -> {pv.ver(hv(h), ok) == hv(Spec.head.ver(h, ok)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      {==}

def s.host(h: Spec.Head) -> {pv.host(hv(h)) == hv(Spec.head.host(h)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
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

def e.fld(pd: Eng.Pend, +n: Bytes(), -vb: Bytes()) ->
  {pv(Eng.pend.fld(Eng.pend.nm(pd, n), vb)) == pv.fld(pv(pd), n, vb) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match hx:
        case Eng.Hx{mb, o, fs, cn}:
          {==}

def s.fld(h: Spec.Head, +n: Bytes(), -v: List<&2, U32>) ->
  {pv.fld(hv(h), n, Bytes.from_list(v)) == hv(Spec.head.fld(h, n, v)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v2, f, hxx}:
      match hxx:
        case Eng.Hx{mb, o, fs, cn}:
          {==}

def e.cn(pd: Eng.Pend, -ms: List<&2, Bytes()>) -> {pv(Eng.pend.cn(pd, ms)) == pv.cn(pv(pd), ms) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match hx:
        case Eng.Hx{mb, o, fs, cn}:
          {==}

def s.cn(h: Spec.Head, -ms: List<&2, List<&2, U32>>) ->
  {pv.cn(hv(h), Spec.lowall(ms)) == hv(Spec.head.cn(h, ms)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      match hxx:
        case Eng.Hx{mb, o, fs, cn}:
          {==}

# a field passed on, named at its colon, joins both sides at its end
def pr.fld(+pd: Eng.Pend, +h: Spec.Head, +n: Bytes(), +v: List<&2, U32>, pr: PR(pd, h)) ->
  PR(Eng.pend.fld(Eng.pend.nm(pd, n), Bytes.from_list(v)), Spec.head.fld(h, n, v)):
  pr.by(x => pv.fld(x, n, Bytes.from_list(v)), pd, Eng.pend.fld(Eng.pend.nm(pd, n), Bytes.from_list(v)), h,
    Spec.head.fld(h, n, v), e.fld(pd, n, Bytes.from_list(v)), s.fld(h, n, v), pr)

def pr.cn(+pd: Eng.Pend, +h: Spec.Head, +ms: List<&2, List<&2, U32>>, pr: PR(pd, h)) ->
  PR(Eng.pend.cn(pd, Spec.lowall(ms)), Spec.head.cn(h, ms)):
  pr.by(x => pv.cn(x, Spec.lowall(ms)), pd, Eng.pend.cn(pd, Spec.lowall(ms)), h, Spec.head.cn(h, ms),
    e.cn(pd, Spec.lowall(ms)), s.cn(h, ms), pr)

def pr.host(+pd: Eng.Pend, +h: Spec.Head, pr: PR(pd, h)) -> PR(Eng.pend.host(pd), Spec.head.host(h)):
  pr.by(x => pv.host(x), pd, Eng.pend.host(pd), h, Spec.head.host(h), e.host(pd), s.host(h), pr)

# A Transfer-Encoding at its line's end, on both sides: taken when it
# says chunked and none came before it, refused otherwise. Each side's
# decision is read off what it holds (pv.teok), so the two are one
# decision.
def pv.teok(x: PV, ok: Bool) -> Bool:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match fx:
        case Eng.Fx{a, b, t}:
          ok && Bool.not(t)

def pend.teset(pd: Eng.Pend) -> Eng.Pend:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match fx:
        case Eng.Fx{a, b, t}:
          Eng.Pend{m, p, cl, close, host, ws, Eng.Fx{a, b, True{}}, hx, nx}

def head.teset(h: Spec.Head) -> Spec.Head:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      match f:
        case Eng.Fx{a, b, x}:
          Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{a, b, True{}}, hxx}

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
  -v10: Bool, -ka: Bool, -hx: Eng.Hx, -nx: Maybe<&2, Eng.Pend>, -out: List<&2, Eng.Req>, -t: Bool) ->
  {Eng.step.te.go(b, m, p, cl, close, host, ws, v10, ka, hx, nx, out, t) ==
    te.pick(b, Eng.Pend{m, p, cl, close, host, ws, Eng.Fx{v10, ka, t}, hx, nx}, out) : Eng.P}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def e.te(pd: Eng.Pend, +ok: Bool, -out: List<&2, Eng.Req>) ->
  {Eng.step.te.at(ok, pd, out) == te.pick(pv.teok(pv(pd), ok), pd, out) : Eng.P}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match fx:
        case Eng.Fx{a, b, +t}:
          e.te.go(ok && Bool.not(t), m, p, cl, close, host, ws, a, b, hx, nx, out, t)

def s.te.go(b: Bool, -m: Eng.Meth, -t: List<&2, U32>, -l: Maybe<&2, U32>, -cl: Bool, -hs: Nat,
  -k: List<&2, U32>, -u: Bool, -c: Bool, -v: Bool, -v10: Bool, -ka: Bool, -x: Bool, -hxx: Eng.Hx) ->
  {hte.pick(b, Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, x}, hxx}) ==
    Spec.head.te.at(b, m, t, l, cl, hs, k, u, c, v, v10, ka, hxx) : Maybe<&2, Spec.Head>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def s.te(h: Spec.Head, +ok: Bool) ->
  {hte.pick(pv.teok(hv(h), ok), h) == Spec.head.te(h, ok) : Maybe<&2, Spec.Head>}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      match f:
        case Eng.Fx{a, b, +x}:
          s.te.go(ok && Bool.not(x), m, t, l, cl, hs, k, u, c, v, a, b, x, hxx)

def e.teset(pd: Eng.Pend) -> {pv(pend.teset(pd)) == pv.te(pv(pd)) : PV}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match fx:
        case Eng.Fx{a, b, t}:
          {==}

def s.teset(h: Spec.Head) -> {pv.te(hv(h)) == hv(head.teset(h)) : PV}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
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
    {PV{_, Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{}, UV{"", False{}, False{}, False{}}, Eng.Fx{False{}, False{}, False{}},
      Eng.Hx{Bytes.from_list(m), "", Nil{}, Nil{}}} ==
      PV{Spec.method(Bytes.from_list(m)), Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{}, UV{"", False{}, False{}, False{}},
        Eng.Fx{False{}, False{}, False{}}, Eng.Hx{Bytes.from_list(m), "", Nil{}, Nil{}}} : PV}
  {==}

def pr.new10(+m: List<&2, U32>, +t: List<&2, U32>) ->
  PR(Eng.pend.v10(pd2(m, t)), Spec.head.new(m, t, True{})):
  %meth.is(Bytes.from_list(m)) :
    {PV{_, Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{}, UV{"", False{}, False{}, False{}}, Eng.Fx{True{}, False{}, False{}},
      Eng.Hx{Bytes.from_list(m), "", Nil{}, Nil{}}} ==
      PV{Spec.method(Bytes.from_list(m)), Bytes.from_list(t), Eng.NoCl{}, False{}, Eng.H0{}, UV{"", False{}, False{}, False{}},
        Eng.Fx{True{}, False{}, False{}}, Eng.Hx{Bytes.from_list(m), "", Nil{}, Nil{}}} : PV}
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
    case PV{m, p, cl, close, host, u, fx, hx}:
      match u:
        case UV{k, uu, c, v}:
          Eng.pend.req.fx(m, p, body, close, Eng.Asks{k, uu, c, v}, fx, hx)

def e.req(pd: Eng.Pend, -body: Bytes()) -> {Eng.pend.req(pd, body) == reqof(pv(pd), body) : Eng.Req}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match ws fx:
        case Eng.Plain{} Eng.Fx{a, b, t}:
          {==}
        case Eng.Asks{k, u, c, v} y:
          {==}

def s.req(h: Spec.Head, -b: List<&2, U32>) ->
  {Spec.req(h, b) == reqof(hv(h), Bytes.from_list(b)) : Eng.Req}:
  match h:
    case Spec.Head{m, t, l, cl, hs, k, u, c, v, f, hxx}:
      match k f hxx:
        case Nil{} Eng.Fx{a, bb, x} Eng.Hx{hm, hn, hf, hc}:
          {==}
        case Con{y, r} Eng.Fx{a, bb, x} Eng.Hx{hm, hn, hf, hc}:
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
  +hd: Eng.Hd, +out: List<&2, Eng.Req>, +pd: Eng.Pend,
  e: {p2 == Eng.emit.go(Eng.Req{m, pa, bd, cl, ws, key, hd}, out) : Eng.P}) ->
  SR(p2, Spec.emit.go(Eng.Req{m, pa, bd, cl, ws, key, hd}, out)):
  match ws:
    case True{}:
      (pd, e)
    case False{}:
      +e2 = e
      (pd, (e2, (Unit{}, e2)))

def EMIT(+pd: Eng.Pend, h: Spec.Head, +b: List<&2, U32>, +out: List<&2, Eng.Req>, -p2: Eng.P,
  e: {p2 == Eng.emit(pd, Bytes.from_list(b), out) : Eng.P}, pr: PR(pd, h)) -> SR(p2, Spec.emit(h, b, out)):
  match h:
    case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf, +hxx}:
      match hf:
        case Eng.Fx{+v10, +ka, +te}:
          EMIT.ws(Bool.not(v10) && (hu && hcu && Spec.has(hk) && Bool.not(hvb)), p2, hm, Bytes.from_list(ht),
            Bytes.from_list(b), hc || (v10 && Bool.not(ka)), Bytes.from_list(hk), Spec.hd(hxx, v10), out, pd,
            Equal.trans(Eng.P, p2, Eng.emit(pd, Bytes.from_list(b), out),
              Eng.emit.go(Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, b), out), e,
              Equal.cong(Eng.Req, Eng.P, x => Eng.emit.go(x, out), Eng.pend.req(pd, Bytes.from_list(b)),
                Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, b),
                Equal.sym(Eng.Req, Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, b),
                  Eng.pend.req(pd, Bytes.from_list(b)),
                  REQ(pd, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, b, pr)))))

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
    case PV{m, p, cl, close, host, u, fx, hx}:
      cl

# the pending fields with the length set, and the head with it set
def pr.cl(+m: Eng.Meth, +pa: Bytes(), +cl: Eng.Cl, +cls: Bool, +host: Eng.Hosts, +ws: Eng.Up, +fx: Eng.Fx,
  +hx: Eng.Hx, +nx: Maybe<&2, Eng.Pend>,
  +hm: Eng.Meth, +ht: List<&2, U32>, +l: Maybe<&2, U32>, +hc: Bool, +hs: Nat, +hk: List<&2, U32>,
  +hu: Bool, +hcu: Bool, +hvb: Bool, +hf: Eng.Fx, +hxx: Eng.Hx, +w: U32,
  pr: PR(Eng.Pend{m, pa, cl, cls, host, ws, fx, hx, nx}, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf, hxx})) ->
  PR(Eng.Pend{m, pa, Eng.Has{w}, cls, host, ws, fx, hx, nx}, Spec.Head{hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf, hxx}):
  pr.by(x => pv.cl(x, Eng.Has{w}), Eng.Pend{m, pa, cl, cls, host, ws, fx, hx, nx}, Eng.Pend{m, pa, Eng.Has{w}, cls, host, ws, fx, hx, nx},
    Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf, hxx}, Spec.Head{hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf, hxx},
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
  +host: Eng.Hosts, +ws: Eng.Up, +fx: Eng.Fx, +hx: Eng.Hx, +nx: Maybe<&2, Eng.Pend>,
  +hm: Eng.Meth, +ht: List<&2, U32>, +hc: Bool, +hs: Nat,
  +hk: List<&2, U32>, +hu: Bool, +hcu: Bool, +hvb: Bool, +hf: Eng.Fx, +hxx: Eng.Hx, -p: Eng.P, +c: U32,
  +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  e: {Eng.step(p, c) == Eng.step.clen.go(m, pa, clv(l), cls, host, ws, fx, hx, nx, n, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out),
  pr: PR(Eng.Pend{m, pa, cl, cls, host, ws, fx, hx, nx}, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf, hxx})) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.head.len(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf, hxx}, n), out,
    Spec.snoc(since, c))):
  match l:
    case None{}:
      (Eng.Pend{m, pa, Eng.Has{n}, cls, host, ws, fx, hx, nx},
        (pr.cl(m, pa, cl, cls, host, ws, fx, hx, nx, hm, ht, None{}, hc, hs, hk, hu, hcu, hvb, hf, hxx, n, pr), (e, bnd)))
    case Some{+w}:
      CR.dup(U32.is_eq(n, w), p, c, Eng.Pend{m, pa, Eng.Has{w}, cls, host, ws, fx, hx, nx},
        Spec.Head{hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf, hxx}, out, since, e, bnd,
        pr.cl(m, pa, cl, cls, host, ws, fx, hx, nx, hm, ht, Some{w}, hc, hs, hk, hu, hcu, hvb, hf, hxx, w, pr))

def CR.clen(+n: U32, pd: Eng.Pend, h: Spec.Head, -p: Eng.P, +c: U32, +out: List<&2, Eng.Req>,
  +since: List<&2, U32>, e: {Eng.step(p, c) == Eng.step.clen(n, pd, out) : Eng.P},
  bnd: BND(Eng.step(p, c), Spec.snoc(since, c), out), pr: PR(pd, h)) ->
  SR(Eng.step(p, c), Spec.field.next(Spec.head.len(h, n), out, Spec.snoc(since, c))):
  match pd:
    case Eng.Pend{+m, +pa, +cl, +cls, +host, +ws, +fx, +hx, +nx}:
      match h:
        case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf, +hxx}:
          +pr2 = pr
          CR.clen.l(l, n, m, pa, cl, cls, host, ws, fx, hx, nx, hm, ht, hc, hs, hk, hu, hcu, hvb, hf, hxx, p, c, out, since,
            Equal.trans(Eng.P, Eng.step(p, c), Eng.step.clen.go(m, pa, cl, cls, host, ws, fx, hx, nx, n, out),
              Eng.step.clen.go(m, pa, clv(l), cls, host, ws, fx, hx, nx, n, out), e,
              Equal.cong(Eng.Cl, Eng.P, x => Eng.step.clen.go(m, pa, x, cls, host, ws, fx, hx, nx, n, out), cl, clv(l),
                Equal.cong(PV, Eng.Cl, y => PVcl(y), pv(Eng.Pend{m, pa, cl, cls, host, ws, fx, hx, nx}),
                  hv(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, hf, hxx}), pr2))),
            bnd, pr2)

# a field line's CR: the whole line read
def conn.eq(+pd: Eng.Pend, +out: List<&2, Eng.Req>, +cur: List<&2, U32>, +d: List<&2, List<&2, U32>>) ->
  {Eng.step.conn(lowb(cur), Spec.named("close", d), Spec.named("upgrade", d), Spec.named("keep-alive", d),
    Spec.lowall(d), pd, out) ==
    Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
      Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})), out} : Eng.P}:
  %eqs(lowb(cur), "close") :
    {Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", d) || _,
      Spec.named("upgrade", d) || Eng.bytes.eq(lowb(cur), "upgrade"),
      Spec.named("keep-alive", d) || Eng.bytes.eq(lowb(cur), "keep-alive")), Spec.lowall(Con{cur, d})), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})), out} : Eng.P}
  %eqs(lowb(cur), "upgrade") :
    {Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", d) || _,
      Spec.named("keep-alive", d) || Eng.bytes.eq(lowb(cur), "keep-alive")), Spec.lowall(Con{cur, d})), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})), out} : Eng.P}
  %eqs(lowb(cur), "keep-alive") :
    {Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
      Spec.named("keep-alive", d) || _), Spec.lowall(Con{cur, d})), out} ==
      Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})), out} : Eng.P}
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
      (Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
        Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})),
        (pr.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
            Spec.named("keep-alive", Con{cur, d})),
          Spec.head.conn(h, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
            Spec.named("keep-alive", Con{cur, d})), Con{cur, d},
          pr.conn(pd, h, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
            Spec.named("keep-alive", Con{cur, d}), pr)),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
              Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})), out},
            e0,
            Equal.trans(Eng.P, SK(q, Eng.KCr{}, c),
              Eng.step.conn(lowb(cur), Spec.named("close", d), Spec.named("upgrade", d), Spec.named("keep-alive", d),
                Spec.lowall(d), pd, out),
              Eng.P{Eng.CrM{}, Eng.pend.cn(Eng.pend.conn(pd, Spec.named("close", Con{cur, d}), Spec.named("upgrade", Con{cur, d}),
                Spec.named("keep-alive", Con{cur, d})), Spec.lowall(Con{cur, d})), out},
              skq(q, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", d), Spec.named("upgrade", d),
                Spec.named("keep-alive", d), Spec.lowall(d)}, pd, out}, Eng.KCr{}, c, lr),
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
    case Spec.VHost{+n, +v}:
      (Eng.pend.fld(Eng.pend.nm(Eng.pend.host(pd), n), Bytes.from_list(v)),
        (pr.fld(Eng.pend.host(pd), Spec.head.host(h), n, v, pr.host(pd, h, pr)),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.fld(Eng.pend.nm(Eng.pend.host(pd), n), Bytes.from_list(v)), out}, e0,
            skq(q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(Eng.pend.host(pd), n), out}, Eng.KCr{}, c, lr)), bnd)))
    case Spec.VSkip{+n, +v}:
      (Eng.pend.fld(Eng.pend.nm(pd, n), Bytes.from_list(v)),
        (pr.fld(pd, h, n, v, pr),
          (Equal.trans(Eng.P, Eng.step(p, c), SK(q, Eng.KCr{}, c),
            Eng.P{Eng.CrM{}, Eng.pend.fld(Eng.pend.nm(pd, n), Bytes.from_list(v)), out}, e0,
            skq(q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(pd, n), out}, Eng.KCr{}, c, lr)), bnd)))

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
          Spec.named("keep-alive", d), Spec.lowall(d)}, pd, out}, Eng.KLf{}, c, out, lr, {==}))
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
    case Spec.VHost{n, v}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(Eng.pend.host(pd), n), out}, Eng.KLf{}, c, out, lr, {==}))
    case Spec.VSkip{n, v}:
      deadvia(Eng.step(p, c), SK(q, Eng.KLf{}, c), out, e0,
        dq(q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(pd, n), out}, Eng.KLf{}, c, out, lr, {==}))

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
    case PV{m, p, cl, close, host, u, fx, hx}:
      match fx:
        case Eng.Fx{v10, ka, te}:
          Eng.hosts.ok(v10, host)

def pv.bd(x: PV) -> Eng.Bd:
  match x:
    case PV{m, p, cl, close, host, u, fx, hx}:
      match fx:
        case Eng.Fx{v10, ka, te}:
          Eng.body.kind(te, v10, cl)

def e.head(pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  {Eng.step.head(pd, out) == Eng.step.head.at(pd, pv.hostok(pv(pd)), pv.bd(pv(pd)), out) : Eng.P}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
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
    case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf, +hxx}:
      match hf:
        case Eng.Fx{+v10, +ka, +te}:
          +pr2 = pr
          HEAD.at(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l), pd,
            Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, p, c, out, since,
            Equal.trans(Eng.P, Eng.step(p, c), Eng.step.head(pd, out),
              Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out), e,
              Equal.trans(Eng.P, Eng.step.head(pd, out), Eng.step.head.at(pd, pv.hostok(pv(pd)), pv.bd(pv(pd)), out),
                Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out),
                e.head(pd, out),
                Equal.trans(Eng.P, Eng.step.head.at(pd, pv.hostok(pv(pd)), pv.bd(pv(pd)), out),
                  Eng.step.head.at(pd, Eng.hosts.ok(v10, hsat(hs)), Eng.body.kind(te, v10, clv(l)), out),
                  Eng.step.head.at(pd, Spec.hosts.ok(v10, hs), bdv(Spec.body.of(te, v10, l)), out),
                  Equal.cong(PV, Eng.P, x => Eng.step.head.at(pd, pv.hostok(x), pv.bd(x), out), pv(pd),
                    hv(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}), pr2),
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
        Spec.named("keep-alive", d), Spec.lowall(d)}, pd, out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLc{lowb(cur), Spec.named("close", d), Spec.named("upgrade", d),
          Spec.named("keep-alive", d), Spec.lowall(d)}, pd, out}, e1, lr), {==}, bnd)
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
    case Spec.VHost{n, v}:
      OPEN(p, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(Eng.pend.host(pd), n), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(Eng.pend.host(pd), n), out}, e1, lr),
        {==}, bnd)
    case Spec.VSkip{n, v}:
      OPEN(p, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(pd, n), out}, out, since,
        Equal.trans(Eng.P, p, q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(pd, n), out}, e1, lr), {==}, bnd)

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

# reads fed one after another are their bytes fed at once (the kit's
# reads_is)
def reads.is(rs: List<&2, Bytes()>, +p: Eng.P) ->
  {Laws.reads(rs, p) == Eng.feed(Bytes.to_list(Bytes.concat(rs)), p) : Eng.P}:
  Wr.reads_is(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, ~adv_ok, Unit{}, rs, p)

def Laws.frame_sim_reads(rs):
  %Equal.sym(Eng.P, Laws.reads(rs, Eng.p.new()), Eng.feed(Bytes.to_list(Bytes.concat(rs)), Eng.p.new()),
    reads.is(rs, Eng.p.new())) : Laws.agree(_, Spec.frame(Bytes.to_list(Bytes.concat(rs))))
  frame.sim(Bytes.to_list(Bytes.concat(rs)))

# a reader that agrees with a framing has completed its requests, so it
# carries its requests' heads
def HDS(-p: Eng.P, f: Spec.Frames) -> Type:
  {Laws.hds(Pair.fst(List<&2, Eng.Req>, Laws.Look, Laws.look(p))) == Laws.hds(Laws.frames.reqs(f)) :
    List<&2, Eng.Hd>}

def hds.look(-p: Eng.P, -rs: List<&2, Eng.Req>, -k: Laws.Look,
  e: {Laws.look(p) == (rs, k) : List<&2, Eng.Req> & Laws.Look}) -> HDS(p, Spec.Frames{rs, Spec.Refused{}}):
  Equal.cong(List<&2, Eng.Req> & Laws.Look, List<&2, Eng.Hd>,
    z => Laws.hds(Pair.fst(List<&2, Eng.Req>, Laws.Look, z)), Laws.look(p), (rs, k), e)

def hds.open(-p: Eng.P, +rs: List<&2, Eng.Req>, -rest: List<&2, U32>,
  a: {Laws.look(p) == (rs, Laws.Reading{}) : List<&2, Eng.Req> & Laws.Look} &
    {p == Eng.feed(rest, Eng.P{Eng.Pre{}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs)}) : Eng.P}) ->
  HDS(p, Spec.Frames{rs, Spec.Refused{}}):
  (l, x) = a
  hds.look(p, rs, Laws.Reading{}, l)

def hds.agree(-p: Eng.P, f: Spec.Frames) -> Laws.agree(p, f) -> HDS(p, f):
  match f:
    case Spec.Frames{+rs, e}:
      match e:
        case Spec.Open{rest}:
          a => hds.open(p, rs, rest, a)
        case Spec.Refused{}:
          a => hds.look(p, rs, Laws.Refusing{}, a)
        case Spec.Upgraded{b}:
          a =>
            %Equal.sym(List<&2, Eng.Req>, rs, List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, rs)), rev.rev(rs)) :
              {Laws.hds(Pair.fst(List<&2, Eng.Req>, Laws.Look, Laws.look(p))) == Laws.hds(_) :
              List<&2, Eng.Hd>}
            Equal.cong(Eng.P, List<&2, Eng.Hd>, z => Laws.hds(Pair.fst(List<&2, Eng.Req>, Laws.Look, Laws.look(z))), p,
              Eng.P{Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs)}, a)

def Laws.hd_framed(bs):
  hds.agree(Eng.feed(bs, Eng.p.new()), Spec.frame(bs))(frame.sim(bs))

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
