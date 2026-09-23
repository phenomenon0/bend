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

def lem.go.run(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.run.go(sel, acc, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  lem.cut(sel, acc, s, pd, out, Eng.run.len(s, True{}, sel, 0n))({==})

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
    case Eng.InLc{t, a, b}:
      lem.one(Eng.P{Eng.InLc{t, a, b}, pd, out}, s)
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

def Laws.te_refused(k, pd, out, e):
  %Equal.sym(Eng.Fld, Eng.fld.of(Eng.lows(k)), Spec.field(Eng.lows(k)),
    Laws.field_by_bytes(Eng.lows(k))) :
    {Eng.step.name(_, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Bool, Spec.eq(Eng.lows(k), Spec.name("transfer-encoding")), True{}, e) :
    {Eng.step.name(Eng.fld.pick(_, Eng.FTe{}, Spec.find(Eng.lows(k), Spec.fields.rest())), pd, out) ==
      Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  {==}

def Laws.clen_disagree(v, w, m, path, cl, h, ws, out, e):
  %Equal.sym(Bool, U32.is_eq(w, v), False{}, e) :
    {Eng.step.clen.dup(Eng.Pend{m, path, Eng.Has{v}, cl, h, ws}, out, _) ==
      Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws}, out} : Eng.P}
  {==}

def Laws.host_once(m, path, l, cl, h, ws, out, e):
  match l h:
    case Eng.NoCl{} Eng.H0{}:
      {==}
    case Eng.Has{v} Eng.H0{}:
      {==}
    case Eng.NoCl{} Eng.H2{}:
      {==}
    case Eng.Has{v} Eng.H2{}:
      {==}
    case Eng.NoCl{} Eng.H1{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, Eng.NoCl{}, cl, Eng.H1{}, ws}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.NoCl{}, cl, Eng.H1{}, ws}, out} : Eng.P})
      Unit{}
    case Eng.Has{v} Eng.H1{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, Eng.Has{v}, cl, Eng.H1{}, ws}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, Eng.H1{}, ws}, out} : Eng.P})
      Unit{}

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
  k: Eng.Cls, c: U32, t: Bytes(), a: Bool, b: Bool, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLc{t, a, b}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.conn_refuses(c, t, a, b, pd, out, e):
  conn_bad(Eng.cls(c), c, t, a, b, pd, out, e)


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
