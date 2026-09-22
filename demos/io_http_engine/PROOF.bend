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
def lem.cut(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  k: Nat) ->
  {Eng.run.len(s, True{}, sel, 0n) == k : Nat} ->
  {Eng.feed_buf.last(Eng.run.cut(sel, acc, s, pd, out, k)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  match k:
    case 0n:
      e => lem.one(Eng.P{Eng.st.put(sel, acc), pd, out}, s)
    case 1n+j:
      e =>
        %e : {Eng.feed_buf.slow(String.drop(s, _),
          Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, _))), pd, out}) ==
          Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}
        Equal.sym(Eng.P, Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}),
          Eng.feed_buf.slow(String.drop(s, Eng.run.len(s, True{}, sel, 0n)),
            Eng.P{Eng.st.put(sel, Bytes.append(acc, String.take(s, Eng.run.len(s, True{}, sel, 0n)))),
              pd, out}),
          lem.run(sel, s, acc, pd, out))

def lem.go.run(+sel: Eng.Run, +acc: Bytes(), +s: Bytes(), +pd: Eng.Pend, +out: List<&2, Eng.Req>) ->
  {Eng.feed_buf.last(Eng.run.go(sel, acc, s, pd, out)) ==
    Eng.feed_buf.slow(s, Eng.P{Eng.st.put(sel, acc), pd, out}) : Eng.P}:
  lem.cut(sel, acc, s, pd, out, Eng.run.len(s, True{}, sel, 0n))({==})

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
      lem.go.run(Eng.RX{}, "", s, pd, out)
    case Eng.Bod{r, b}:
      lem.bod(s, r, b, pd, out)
    case Eng.Rest{bs}:
      Equal.sym(Eng.P, Eng.feed_buf.slow(s, Eng.P{Eng.Rest{bs}, pd, out}),
        Eng.P{Eng.Rest{Bytes.append(bs, s)}, pd, out}, lem.rest(s, bs, pd, out))
    case Eng.Bad{}:
      Equal.sym(Eng.P, Eng.feed_buf.slow(s, Eng.P{Eng.Bad{}, pd, out}),
        Eng.P{Eng.Bad{}, pd, out}, lem.bad(s, pd, out))
    case Eng.Pre{}:
      lem.one(Eng.P{Eng.Pre{}, pd, out}, s)
    case Eng.PreLf{}:
      lem.one(Eng.P{Eng.PreLf{}, pd, out}, s)
    case Eng.CrM{}:
      lem.one(Eng.P{Eng.CrM{}, pd, out}, s)
    case Eng.Lin{}:
      lem.one(Eng.P{Eng.Lin{}, pd, out}, s)
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

def find_is_spec(+k: Bytes(), tbl: List<&2, Eng.Known>) ->
  {Eng.fld.find(k, tbl) == Spec.find(k, tbl) : Eng.Fld}:
  match tbl:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Eng.Known{n, f}:
          %find_is_spec(k, t) : {Eng.fld.pick(Eng.bytes.eq(k, n), f, Eng.fld.find(k, t)) ==
            Eng.fld.pick(Spec.eq(k, n), f, _) : Eng.Fld}
          %eq_is_spec(k, n) : {Eng.fld.pick(Eng.bytes.eq(k, n), f, Eng.fld.find(k, t)) ==
            Eng.fld.pick(_, f, Eng.fld.find(k, t)) : Eng.Fld}
          {==}

def Laws.cls_is_spec():
  {==}

def Laws.lower_is_spec():
  {==}

def Laws.lows_is_spec():
  {==}

def Laws.field_by_bytes(k):
  find_is_spec(k, Eng.fld.table())

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
