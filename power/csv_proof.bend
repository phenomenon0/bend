# The proofs of power/csv_laws.bend.
#
# feed_split and bad_feeds are inductions on the input. feed_buf_is_feed
# follows the walk move by move: one byte is one step; a run is its
# bytes stepped one by one, each keeping the field's mode and adding
# itself (lem.stay), and the run stops where run.len says; a field
# entered by a run steps its first byte as the empty unquoted field
# does (lem.ent.step); after a refusal every byte is ignored. The fuel
# never matters. csv_sim is an induction on a fuel that bounds the
# input: at every byte, from every mode, the reader and csv_spec.bend's
# grammar land in states the claim relates again (STEP), and at the end
# of input they read the same (END). The cases where the grammar reads
# CRLF as one symbol, or a byte of a field against its room, or a line
# end against the record's width, go through one lemma each (ECR, QCR,
# PUT, LE); their leaves are written out case by case.
import Base
import ./csv.bend as Csv
import ./csv_spec.bend as Spec
import ./csv_laws.bend as Laws

# The reads
# =========

def Laws.feed_split(d, a, b, p):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.feed_split(d, t, b, Csv.step(d, p, c))

def Laws.bad_feeds(d, s, at, why, fl, cur, out, w, pos):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.bad_feeds(d, t, at, why, fl, cur, out, w, pos)

# The walk
# --------

def slow_is_feed(+d: Csv.Dialect, s: Bytes(), p: Csv.P) ->
  {Csv.feed_buf.slow(d, s, p) == Csv.feed(d, Bytes.to_list(s), p) : Csv.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      slow_is_feed(d, t, Csv.step(d, p, c))

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

# a field grown by one byte, then by more, is the field grown by all of them
def push_app(acc: Bytes(), -c: U32, -x: Bytes()) ->
  {Bytes.append(Csv.push(acc, c), x) == Bytes.append(acc, SCon{Chr{c}, x}) : Bytes()}:
  app_assoc(acc, Csv.one(c), x)

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# anything, from False == True
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : BD(_, g, Unit)
  Unit{}

# a Nat that is one more than something is not zero
def ZN(n: Nat, g: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      g

# One byte
def lem.one(+d: Csv.Dialect, p: Csv.P, s: Bytes()) ->
  {Csv.feed_buf.last(d, Csv.one.step(d, p, s)) == Csv.feed_buf.slow(d, s, p) : Csv.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      {==}

# A run
# -----

# a byte a run stays on is one step keeps the field on, one byte longer
def SG(+d: Csv.Dialect, -q: Bool, -k: Csv.K, -c: U32, -acc: Bytes(), -l: Nat, -fl: Nat,
  -cur: List<&2, Bytes()>, -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) ->
  Type:
  {Csv.step.at(d, Csv.grow(q, acc, 1n+l), k, c, fl, cur, out, w, pos) ==
    Csv.P{Csv.grow(q, Csv.push(acc, c), l), fl, cur, out, w, 1n+pos} : Csv.P}

def lem.stay(+d: Csv.Dialect, q: Bool, k: Csv.K, -c: U32, -acc: Bytes(), -l: Nat, -fl: Nat,
  -cur: List<&2, Bytes()>, -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) ->
  {Csv.stay(q, k) == True{} : Bool} -> SG(d, q, k, c, acc, l, fl, cur, out, w, pos):
  match q k:
    case True{} Csv.KQ{}:
      e => no(SG(d, True{}, Csv.KQ{}, c, acc, l, fl, cur, out, w, pos), e)
    case True{} Csv.KD{}:
      e => {==}
    case True{} Csv.KCR{}:
      e => {==}
    case True{} Csv.KLF{}:
      e => {==}
    case True{} Csv.KO{}:
      e => {==}
    case False{} Csv.KQ{}:
      e => no(SG(d, False{}, Csv.KQ{}, c, acc, l, fl, cur, out, w, pos), e)
    case False{} Csv.KD{}:
      e => no(SG(d, False{}, Csv.KD{}, c, acc, l, fl, cur, out, w, pos), e)
    case False{} Csv.KCR{}:
      e => no(SG(d, False{}, Csv.KCR{}, c, acc, l, fl, cur, out, w, pos), e)
    case False{} Csv.KLF{}:
      e => no(SG(d, False{}, Csv.KLF{}, c, acc, l, fl, cur, out, w, pos), e)
    case False{} Csv.KO{}:
      e => {==}

def lem.len0(+d: Csv.Dialect, t: Bytes(), -q: Bool, -l: Nat) ->
  {Csv.run.len(d, t, False{}, q, l, 0n) == 0n : Nat}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{x}, u}:
      {==}

def lem.shift.at(
  +d: Csv.Dialect, -u: Bytes(), -q: Bool, -l: Nat, -k: Nat, ok: Bool,
  ht: {Csv.run.len(d, u, True{}, q, l, 1n+1n+k) == 1n+Csv.run.len(d, u, True{}, q, l, 1n+k) : Nat},
  hf: {Csv.run.len(d, u, False{}, q, l, 1n+k) == 1n+Csv.run.len(d, u, False{}, q, l, k) : Nat}
) -> {Csv.run.len(d, u, ok, q, l, Csv.inc(ok, 1n+k)) ==
  1n+Csv.run.len(d, u, ok, q, l, Csv.inc(ok, k)) : Nat}:
  match ok:
    case True{}:
      ht
    case False{}:
      hf

# counting from k + 1 is counting from k, plus one
def lem.shift(+d: Csv.Dialect, +t: Bytes(), go: Bool, +q: Bool, +left: Nat, +k: Nat) ->
  {Csv.run.len(d, t, go, q, left, 1n+k) == 1n+Csv.run.len(d, t, go, q, left, k) : Nat}:
  match t go left:
    case SNil{} _ _:
      {==}
    case SCon{Chr{x}, u} False{} _:
      {==}
    case SCon{Chr{x}, u} True{} 0n:
      {==}
    case SCon{Chr{c}, u} True{} 1n+l:
      lem.shift.at(d, u, q, l, k, Csv.stay(q, Csv.cls(d, c)),
        lem.shift(d, u, True{}, q, l, 1n+k), lem.shift(d, u, False{}, q, l, k))

# what a run takes of s, stepped a byte at a time, is the field with
# those bytes added, and what follows is walked from there
def RL(+d: Csv.Dialect, +s: Bytes(), +q: Bool, +left: Nat) -> Nat:
  Csv.run.len(d, s, True{}, q, left, 0n)

def RG(+d: Csv.Dialect, +s: Bytes(), +q: Bool, +acc: Bytes(), +left: Nat, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  Type:
  {Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}) ==
    Csv.feed_buf.slow(d, String.drop(s, RL(d, s, q, left)),
      Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, RL(d, s, q, left))),
        Nat.sub(left, RL(d, s, q, left))), fl, cur, out, w, Nat.add(RL(d, s, q, left), pos)}) :
    Csv.P}

def lem.run.at(
  +d: Csv.Dialect, +q: Bool, +c: U32, +t: Bytes(), +acc: Bytes(), +l: Nat, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  ok: Bool, ih: RG(d, t, q, Csv.push(acc, c), l, fl, cur, out, w, 1n+pos)
) -> {Csv.stay(q, Csv.cls(d, c)) == ok : Bool} ->
  RG(d, SCon{Chr{c}, t}, q, acc, 1n+l, fl, cur, out, w, pos):
  match ok:
    case True{}:
      +e =>
        %Equal.sym(Bool, Csv.stay(q, Csv.cls(d, c)), True{}, e) :
          {Csv.feed_buf.slow(d, t, Csv.step.at(d, Csv.grow(q, acc, 1n+l), Csv.cls(d, c), c, fl, cur,
            out, w, pos)) ==
            Csv.feed_buf.slow(d, String.drop(SCon{Chr{c}, t}, Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n))),
              Csv.P{Csv.grow(q, Bytes.append(acc, String.take(SCon{Chr{c}, t},
                Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n)))),
                Nat.sub(1n+l, Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n)))), fl, cur, out, w,
                Nat.add(Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n)), pos)}) : Csv.P}
        %Equal.sym(Nat, Csv.run.len(d, t, True{}, q, l, 1n), 1n+Csv.run.len(d, t, True{}, q, l, 0n),
          lem.shift(d, t, True{}, q, l, 0n)) :
          {Csv.feed_buf.slow(d, t, Csv.step.at(d, Csv.grow(q, acc, 1n+l), Csv.cls(d, c), c, fl, cur,
            out, w, pos)) ==
            Csv.feed_buf.slow(d, String.drop(SCon{Chr{c}, t}, _),
              Csv.P{Csv.grow(q, Bytes.append(acc, String.take(SCon{Chr{c}, t}, _)),
                Nat.sub(1n+l, _)), fl, cur, out, w, Nat.add(_, pos)}) : Csv.P}
        %Equal.sym(Csv.P, Csv.step.at(d, Csv.grow(q, acc, 1n+l), Csv.cls(d, c), c, fl, cur, out, w, pos),
          Csv.P{Csv.grow(q, Csv.push(acc, c), l), fl, cur, out, w, 1n+pos},
          lem.stay(d, q, Csv.cls(d, c), c, acc, l, fl, cur, out, w, pos)(e)) :
          {Csv.feed_buf.slow(d, t, _) ==
            Csv.feed_buf.slow(d, String.drop(t, RL(d, t, q, l)),
              Csv.P{Csv.grow(q, Bytes.append(acc, SCon{Chr{c}, String.take(t, RL(d, t, q, l))}),
                Nat.sub(l, RL(d, t, q, l))), fl, cur, out, w, 1n+Nat.add(RL(d, t, q, l), pos)}) : Csv.P}
        %push_app(acc, c, String.take(t, RL(d, t, q, l))) :
          {Csv.feed_buf.slow(d, t, Csv.P{Csv.grow(q, Csv.push(acc, c), l), fl, cur, out, w, 1n+pos}) ==
            Csv.feed_buf.slow(d, String.drop(t, RL(d, t, q, l)),
              Csv.P{Csv.grow(q, _, Nat.sub(l, RL(d, t, q, l))), fl, cur, out, w,
                1n+Nat.add(RL(d, t, q, l), pos)}) : Csv.P}
        %add_succ(RL(d, t, q, l), pos) :
          {Csv.feed_buf.slow(d, t, Csv.P{Csv.grow(q, Csv.push(acc, c), l), fl, cur, out, w, 1n+pos}) ==
            Csv.feed_buf.slow(d, String.drop(t, RL(d, t, q, l)),
              Csv.P{Csv.grow(q, Bytes.append(Csv.push(acc, c), String.take(t, RL(d, t, q, l))),
                Nat.sub(l, RL(d, t, q, l))), fl, cur, out, w, _}) : Csv.P}
        ih
    case False{}:
      e =>
        %Equal.sym(Bool, Csv.stay(q, Csv.cls(d, c)), False{}, e) :
          {Csv.feed_buf.slow(d, t, Csv.step.at(d, Csv.grow(q, acc, 1n+l), Csv.cls(d, c), c, fl, cur,
            out, w, pos)) ==
            Csv.feed_buf.slow(d, String.drop(SCon{Chr{c}, t}, Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n))),
              Csv.P{Csv.grow(q, Bytes.append(acc, String.take(SCon{Chr{c}, t},
                Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n)))),
                Nat.sub(1n+l, Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n)))), fl, cur, out, w,
                Nat.add(Csv.run.len(d, t, _, q, l, Csv.inc(_, 0n)), pos)}) : Csv.P}
        %Equal.sym(Nat, Csv.run.len(d, t, False{}, q, l, 0n), 0n, lem.len0(d, t, q, l)) :
          {Csv.feed_buf.slow(d, t, Csv.step.at(d, Csv.grow(q, acc, 1n+l), Csv.cls(d, c), c, fl, cur,
            out, w, pos)) ==
            Csv.feed_buf.slow(d, String.drop(SCon{Chr{c}, t}, _),
              Csv.P{Csv.grow(q, Bytes.append(acc, String.take(SCon{Chr{c}, t}, _)),
                Nat.sub(1n+l, _)), fl, cur, out, w, Nat.add(_, pos)}) : Csv.P}
        %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
          {Csv.feed_buf.slow(d, t, Csv.step.at(d, Csv.grow(q, acc, 1n+l), Csv.cls(d, c), c, fl, cur,
            out, w, pos)) ==
            Csv.feed_buf.slow(d, t, Csv.step.at(d, Csv.grow(q, _, 1n+l), Csv.cls(d, c), c, fl, cur,
              out, w, pos)) : Csv.P}
        {==}

def lem.run(+d: Csv.Dialect, +s: Bytes(), +q: Bool, +acc: Bytes(), +left: Nat, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  RG(d, s, q, acc, left, fl, cur, out, w, pos):
  match s left:
    case SNil{} 0n:
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
        {Csv.P{Csv.grow(q, acc, 0n), fl, cur, out, w, pos} ==
          Csv.P{Csv.grow(q, _, 0n), fl, cur, out, w, pos} : Csv.P}
      {==}
    case SNil{} 1n+l:
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
        {Csv.P{Csv.grow(q, acc, 1n+l), fl, cur, out, w, pos} ==
          Csv.P{Csv.grow(q, _, 1n+l), fl, cur, out, w, pos} : Csv.P}
      {==}
    case SCon{Chr{x}, t} 0n:
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, app_nil(acc)) :
        {Csv.feed_buf.slow(d, SCon{Chr{x}, t}, Csv.P{Csv.grow(q, acc, 0n), fl, cur, out, w, pos}) ==
          Csv.feed_buf.slow(d, SCon{Chr{x}, t}, Csv.P{Csv.grow(q, _, 0n), fl, cur, out, w, pos}) : Csv.P}
      {==}
    case SCon{Chr{c}, t} 1n+l:
      lem.run.at(d, q, c, t, acc, l, fl, cur, out, w, pos, Csv.stay(q, Csv.cls(d, c)),
        lem.run(d, t, q, Csv.push(acc, c), l, fl, cur, out, w, 1n+pos))({==})

# a run cut where run.len says: the cut's two halves are what RG names
def lem.cut.took(+d: Csv.Dialect, +q: Bool, +acc: Bytes(), +left: Nat, +s: Bytes(), +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  j: Nat, e: {RL(d, s, q, left) == 1n+j : Nat}) ->
  {Csv.feed_buf.slow(d, String.drop(s, 1n+j),
    Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, 1n+j)), Nat.sub(left, 1n+j)), fl, cur, out,
      w, Nat.add(1n+j, pos)}) ==
    Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}) : Csv.P}:
  %e : {Csv.feed_buf.slow(d, String.drop(s, _),
    Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, _)), Nat.sub(left, _)), fl, cur, out, w,
      Nat.add(_, pos)}) ==
    Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}) : Csv.P}
  Equal.sym(Csv.P, Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}),
    Csv.feed_buf.slow(d, String.drop(s, RL(d, s, q, left)),
      Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, RL(d, s, q, left))),
        Nat.sub(left, RL(d, s, q, left))), fl, cur, out, w, Nat.add(RL(d, s, q, left), pos)}),
    lem.run(d, s, q, acc, left, fl, cur, out, w, pos))

def lem.took(+d: Csv.Dialect, +q: Bool, +acc: Bytes(), +left: Nat, +s: Bytes(), +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +j: Nat, e: {RL(d, s, q, left) == 1n+j : Nat}) ->
  {Csv.feed_buf.last(d, Csv.run.took(d, q, acc, left, j, fl, cur, out, w, pos, String.cut(s, 1n+j))) ==
    Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}) : Csv.P}:
  Equal.trans(Csv.P,
    Csv.feed_buf.last(d, Csv.one.step(d,
      Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, 1n+j)), Nat.sub(left, 1n+j)), fl, cur, out,
        w, Nat.add(1n+j, pos)}, String.drop(s, 1n+j))),
    Csv.feed_buf.slow(d, String.drop(s, 1n+j),
      Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, 1n+j)), Nat.sub(left, 1n+j)), fl, cur, out,
        w, Nat.add(1n+j, pos)}),
    Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}),
    lem.one(d, Csv.P{Csv.grow(q, Bytes.append(acc, String.take(s, 1n+j)), Nat.sub(left, 1n+j)), fl,
      cur, out, w, Nat.add(1n+j, pos)}, String.drop(s, 1n+j)),
    lem.cut.took(d, q, acc, left, s, fl, cur, out, w, pos, j, e))

def lem.cut(+d: Csv.Dialect, +q: Bool, +acc: Bytes(), +left: Nat, +s: Bytes(), +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +k: Nat) ->
  {RL(d, s, q, left) == k : Nat} ->
  {Csv.feed_buf.last(d, Csv.run.cut(d, q, acc, left, s, fl, cur, out, w, pos, k)) ==
    Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}) : Csv.P}:
  match k:
    case 0n:
      e => lem.one(d, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}, s)
    case 1n+j:
      e => lem.took(d, q, acc, left, s, fl, cur, out, w, pos, j, e)

def lem.go.run(+d: Csv.Dialect, +q: Bool, +acc: Bytes(), +left: Nat, +s: Bytes(), +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  {Csv.feed_buf.last(d, Csv.run.go(d, q, acc, left, s, fl, cur, out, w, pos)) ==
    Csv.feed_buf.slow(d, s, Csv.P{Csv.grow(q, acc, left), fl, cur, out, w, pos}) : Csv.P}:
  lem.cut(d, q, acc, left, s, fl, cur, out, w, pos, RL(d, s, q, left))({==})

# A field from its first byte
# ---------------------------

def ent.m(isr: Bool) -> Csv.Mode:
  match isr:
    case True{}:
      Csv.RS{}
    case False{}:
      Csv.FS{}

def ent.ko(+d: Csv.Dialect, isr: Bool, -c: U32, -fl: Nat, -cur: List<&2, Bytes()>,
  -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) ->
  {Csv.step.at(d, ent.m(isr), Csv.KO{}, c, fl, cur, out, w, pos) ==
    Csv.step.at(d, Csv.Unq{"", Csv.max_field(d)}, Csv.KO{}, c, fl, cur, out, w, pos) : Csv.P}:
  match isr:
    case True{}:
      {==}
    case False{}:
      {==}

# the start of a field steps a byte an unquoted run stays on exactly as
# the empty unquoted field does
def lem.ent.step(+d: Csv.Dialect, isr: Bool, k: Csv.K, -c: U32, -fl: Nat, -cur: List<&2, Bytes()>,
  -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) ->
  {Csv.stay(False{}, k) == True{} : Bool} ->
  {Csv.step.at(d, ent.m(isr), k, c, fl, cur, out, w, pos) ==
    Csv.step.at(d, Csv.Unq{"", Csv.max_field(d)}, k, c, fl, cur, out, w, pos) : Csv.P}:
  match k:
    case Csv.KQ{}:
      e => no({Csv.step.at(d, ent.m(isr), Csv.KQ{}, c, fl, cur, out, w, pos) ==
        Csv.step.at(d, Csv.Unq{"", Csv.max_field(d)}, Csv.KQ{}, c, fl, cur, out, w, pos) : Csv.P}, e)
    case Csv.KD{}:
      e => no({Csv.step.at(d, ent.m(isr), Csv.KD{}, c, fl, cur, out, w, pos) ==
        Csv.step.at(d, Csv.Unq{"", Csv.max_field(d)}, Csv.KD{}, c, fl, cur, out, w, pos) : Csv.P}, e)
    case Csv.KCR{}:
      e => no({Csv.step.at(d, ent.m(isr), Csv.KCR{}, c, fl, cur, out, w, pos) ==
        Csv.step.at(d, Csv.Unq{"", Csv.max_field(d)}, Csv.KCR{}, c, fl, cur, out, w, pos) : Csv.P}, e)
    case Csv.KLF{}:
      e => no({Csv.step.at(d, ent.m(isr), Csv.KLF{}, c, fl, cur, out, w, pos) ==
        Csv.step.at(d, Csv.Unq{"", Csv.max_field(d)}, Csv.KLF{}, c, fl, cur, out, w, pos) : Csv.P}, e)
    case Csv.KO{}:
      e => ent.ko(d, isr, c, fl, cur, out, w, pos)

def EG(+d: Csv.Dialect, -isr: Bool, -s: Bytes(), -fl: Nat, -cur: List<&2, Bytes()>,
  -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) -> Type:
  {Csv.feed_buf.slow(d, s, Csv.P{Csv.Unq{"", Csv.max_field(d)}, fl, cur, out, w, pos}) ==
    Csv.feed_buf.slow(d, s, Csv.P{ent.m(isr), fl, cur, out, w, pos}) : Csv.P}

def lem.ent.at(+d: Csv.Dialect, +isr: Bool, +c: U32, +t: Bytes(), +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +l: Nat, j: Nat, ok: Bool) ->
  {Csv.stay(False{}, Csv.cls(d, c)) == ok : Bool} ->
  {Csv.run.len(d, t, ok, False{}, l, Csv.inc(ok, 0n)) == 1n+j : Nat} ->
  EG(d, isr, SCon{Chr{c}, t}, fl, cur, out, w, pos):
  match ok:
    case True{}:
      st => eq =>
        %lem.ent.step(d, isr, Csv.cls(d, c), c, fl, cur, out, w, pos)(st) :
          {Csv.feed_buf.slow(d, t, _) ==
            Csv.feed_buf.slow(d, t, Csv.step.at(d, ent.m(isr), Csv.cls(d, c), c, fl, cur, out, w, pos)) :
            Csv.P}
        {==}
    case False{}:
      st => eq =>
        %Equal.trans(Nat, 0n, Csv.run.len(d, t, False{}, False{}, l, 0n), 1n+j,
          Equal.sym(Nat, Csv.run.len(d, t, False{}, False{}, l, 0n), 0n, lem.len0(d, t, False{}, l)),
          eq) : ZN(_, EG(d, isr, SCon{Chr{c}, t}, fl, cur, out, w, pos))
        Unit{}

# the run's room is the dialect's max_field; a run of one byte or more
# means the first byte stays and the room is not zero
def lem.ent.first(+d: Csv.Dialect, +isr: Bool, s: Bytes(), +mf: Nat, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  j: Nat) ->
  {Csv.max_field(d) == mf : Nat} ->
  {Csv.run.len(d, s, True{}, False{}, mf, 0n) == 1n+j : Nat} -> EG(d, isr, s, fl, cur, out, w, pos):
  match s mf:
    case SNil{} _:
      em => eq =>
        %eq : ZN(_, EG(d, isr, SNil{}, fl, cur, out, w, pos))
        Unit{}
    case SCon{Chr{c}, t} 0n:
      em => eq =>
        %eq : ZN(_, EG(d, isr, SCon{Chr{c}, t}, fl, cur, out, w, pos))
        Unit{}
    case SCon{Chr{+c}, t} 1n+l:
      em => eq => lem.ent.at(d, isr, c, t, fl, cur, out, w, pos, l, j,
        Csv.stay(False{}, Csv.cls(d, c)))({==}, eq)

def lem.ent.cut(+d: Csv.Dialect, +isr: Bool, +s: Bytes(), +fl: Nat, +cur: List<&2, Bytes()>,
  +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat, +k: Nat) ->
  {RL(d, s, False{}, Csv.max_field(d)) == k : Nat} ->
  {Csv.feed_buf.last(d, Csv.ent.cut(d, ent.m(isr), s, fl, cur, out, w, pos, k)) ==
    Csv.feed_buf.slow(d, s, Csv.P{ent.m(isr), fl, cur, out, w, pos}) : Csv.P}:
  match k:
    case 0n:
      eq => lem.one(d, Csv.P{ent.m(isr), fl, cur, out, w, pos}, s)
    case 1n+j:
      +eq => Equal.trans(Csv.P,
        Csv.feed_buf.last(d, Csv.run.took(d, False{}, "", Csv.max_field(d), j, fl, cur, out, w, pos,
          String.cut(s, 1n+j))),
        Csv.feed_buf.slow(d, s, Csv.P{Csv.Unq{"", Csv.max_field(d)}, fl, cur, out, w, pos}),
        Csv.feed_buf.slow(d, s, Csv.P{ent.m(isr), fl, cur, out, w, pos}),
        lem.took(d, False{}, "", Csv.max_field(d), s, fl, cur, out, w, pos, j, eq),
        lem.ent.first(d, isr, s, Csv.max_field(d), fl, cur, out, w, pos, j)({==}, eq))

def lem.ent(+d: Csv.Dialect, +isr: Bool, +s: Bytes(), +fl: Nat, +cur: List<&2, Bytes()>,
  +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  {Csv.feed_buf.last(d, Csv.ent.go(d, ent.m(isr), s, fl, cur, out, w, pos)) ==
    Csv.feed_buf.slow(d, s, Csv.P{ent.m(isr), fl, cur, out, w, pos}) : Csv.P}:
  lem.ent.cut(d, isr, s, fl, cur, out, w, pos, RL(d, s, False{}, Csv.max_field(d)))({==})

# After a refusal
def lem.bad(+d: Csv.Dialect, s: Bytes(), -at: Nat, -why: Csv.Why, -fl: Nat, -cur: List<&2, Bytes()>,
  -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) ->
  {Csv.feed_buf.slow(d, s, Csv.P{Csv.Bad{at, why}, fl, cur, out, w, pos}) ==
    Csv.P{Csv.Bad{at, why}, fl, cur, out, w, pos} : Csv.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      lem.bad(d, t, at, why, fl, cur, out, w, pos)

# Every move
def lem.adv.at(+d: Csv.Dialect, m: Csv.Mode, +s: Bytes(), +fl: Nat, +cur: List<&2, Bytes()>,
  +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  {Csv.feed_buf.last(d, Csv.adv.at(d, m, s, fl, cur, out, w, pos)) ==
    Csv.feed_buf.slow(d, s, Csv.P{m, fl, cur, out, w, pos}) : Csv.P}:
  match m:
    case Csv.RS{}:
      lem.ent(d, True{}, s, fl, cur, out, w, pos)
    case Csv.FS{}:
      lem.ent(d, False{}, s, fl, cur, out, w, pos)
    case Csv.Unq{acc, left}:
      lem.go.run(d, False{}, acc, left, s, fl, cur, out, w, pos)
    case Csv.Quo{acc, left}:
      lem.go.run(d, True{}, acc, left, s, fl, cur, out, w, pos)
    case Csv.QQ{acc, left}:
      lem.one(d, Csv.P{Csv.QQ{acc, left}, fl, cur, out, w, pos}, s)
    case Csv.CRp{acc, at}:
      lem.one(d, Csv.P{Csv.CRp{acc, at}, fl, cur, out, w, pos}, s)
    case Csv.Bad{at, why}:
      Equal.sym(Csv.P, Csv.feed_buf.slow(d, s, Csv.P{Csv.Bad{at, why}, fl, cur, out, w, pos}),
        Csv.P{Csv.Bad{at, why}, fl, cur, out, w, pos}, lem.bad(d, s, at, why, fl, cur, out, w, pos))

def lem.adv(+d: Csv.Dialect, +s: Bytes(), p: Csv.P) ->
  {Csv.feed_buf.last(d, Csv.adv(d, s, p)) == Csv.feed_buf.slow(d, s, p) : Csv.P}:
  match p:
    case Csv.P{m, fl, cur, out, w, pos}:
      lem.adv.at(d, m, s, fl, cur, out, w, pos)

# the fuel never matters
def lem.go(+d: Csv.Dialect, n: Nat, q: Csv.P & Bytes()) ->
  {Csv.feed_buf.go(d, n, q) == Csv.feed_buf.last(d, q) : Csv.P}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match q:
        case (p, SNil{}):
          {==}
        case (+p, SCon{+h, +t}):
          Equal.trans(Csv.P, Csv.feed_buf.go(d, m, Csv.adv(d, SCon{h, t}, p)),
            Csv.feed_buf.last(d, Csv.adv(d, SCon{h, t}, p)), Csv.feed_buf.slow(d, SCon{h, t}, p),
            lem.go(d, m, Csv.adv(d, SCon{h, t}, p)), lem.adv(d, SCon{h, t}, p))

def Laws.feed_buf_is_feed(d, b, p):
  Equal.trans(Csv.P, Csv.feed_buf(d, b, p), Csv.feed_buf.slow(d, b, p), Csv.feed(d, Bytes.to_list(b), p),
    lem.go(d, Bytes.len(b), (p, b)), slow_is_feed(d, b, p))

def split.buf(+d: Csv.Dialect, +a: Bytes(), +b: Bytes(), +p: Csv.P) ->
  {Csv.feed(d, Bytes.to_list(Bytes.append(a, b)), p) == Csv.feed_buf(d, b, Csv.feed_buf(d, a, p)) :
    Csv.P}:
  %Equal.sym(Csv.P, Csv.feed_buf(d, a, p), Csv.feed(d, Bytes.to_list(a), p),
    Laws.feed_buf_is_feed(d, a, p)) :
    {Csv.feed(d, Bytes.to_list(Bytes.append(a, b)), p) == Csv.feed_buf(d, b, _) : Csv.P}
  %Equal.sym(Csv.P, Csv.feed_buf(d, b, Csv.feed(d, Bytes.to_list(a), p)),
    Csv.feed(d, Bytes.to_list(b), Csv.feed(d, Bytes.to_list(a), p)),
    Laws.feed_buf_is_feed(d, b, Csv.feed(d, Bytes.to_list(a), p))) :
    {Csv.feed(d, Bytes.to_list(Bytes.append(a, b)), p) == _ : Csv.P}
  %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(a, b)),
    List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), Bytes.to_list_append(a, b)) :
    {Csv.feed(d, _, p) == Csv.feed(d, Bytes.to_list(b), Csv.feed(d, Bytes.to_list(a), p)) : Csv.P}
  Laws.feed_split(d, Bytes.to_list(a), Bytes.to_list(b), p)

def Laws.feed_buf_split(d, a, b, p):
  Equal.trans(Csv.P, Csv.feed_buf(d, Bytes.append(a, b), p),
    Csv.feed(d, Bytes.to_list(Bytes.append(a, b)), p), Csv.feed_buf(d, b, Csv.feed_buf(d, a, p)),
    Laws.feed_buf_is_feed(d, Bytes.append(a, b), p),
    split.buf(d, a, b, p))

# The grammar
# ===========
#
# csv_sim is an induction on the input that follows the reader byte by
# byte and the grammar production by production. It runs on the input's
# marks -- each byte with its class -- so the reader and the grammar see
# the same class for a byte by construction, and the classes are shown
# to be the grammar's own once, at the start (kind_is_cls). The spec
# reads CRLF two bytes at a time where the reader holds the CR (CRp),
# so the induction is on a fuel that bounds the input rather than on
# the input itself: a case that looks at the byte after a CR still has
# the whole rest to recurse on.

# the reader fed marks: each byte stepped with its mark's class
def stepk(+d: Csv.Dialect, p: Csv.P, x: Spec.Mark) -> Csv.P:
  match p:
    case Csv.P{m, fl, cur, out, w, pos}:
      match x:
        case Spec.Mark{k, c}:
          Csv.step.at(d, m, k, c, fl, cur, out, w, pos)

def feedk(+d: Csv.Dialect, ms: List<&2, Spec.Mark>, p: Csv.P) -> Csv.P:
  match ms:
    case Nil{}:
      p
    case Con{x, t}:
      feedk(d, t, stepk(d, p, x))

# what the reader reads of the marks, from p, to the end of input
def R(+d: Csv.Dialect, ms: List<&2, Spec.Mark>, p: Csv.P) -> Csv.Out:
  Csv.result(d, Csv.finish(d, feedk(d, ms, p)))

# the classes are the grammar's
def kind_cls(b1: Bool, b2: Bool, b3: Bool, b4: Bool) ->
  {Spec.kind.if(b1, Csv.KQ{}, Spec.kind.if(b2, Csv.KD{}, Spec.kind.if(b3, Csv.KCR{},
    Spec.kind.if(b4, Csv.KLF{}, Csv.KO{})))) ==
    Csv.k.pick(b1, Csv.KQ{}, Csv.k.pick(b2, Csv.KD{}, Csv.k.pick(b3, Csv.KCR{},
      Csv.k.pick(b4, Csv.KLF{}, Csv.KO{})))) : Csv.K}:
  match b1 b2 b3 b4:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} True{} _:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def kind_is_cls(d: Csv.Dialect, +c: U32) -> {Spec.kind(d, c) == Csv.cls(d, c) : Csv.K}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      kind_cls(U32.is_eq(c, q), U32.is_eq(c, dl), U32.is_eq(c, 13), U32.is_eq(c, 10))

def step_k(+d: Csv.Dialect, p: Csv.P, +c: U32) ->
  {Csv.step(d, p, c) == stepk(d, p, Spec.Mark{Csv.cls(d, c), c}) : Csv.P}:
  match p:
    case Csv.P{m, fl, cur, out, w, pos}:
      {==}

# the reader over bytes is the reader over their marks
def feed_is_feedk(+d: Csv.Dialect, bs: List<&2, U32>, +p: Csv.P) ->
  {Csv.feed(d, bs, p) == feedk(d, Spec.marks(d, bs), p) : Csv.P}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, t}:
      %Equal.sym(Csv.K, Spec.kind(d, c), Csv.cls(d, c), kind_is_cls(d, c)) :
        {Csv.feed(d, t, Csv.step(d, p, c)) ==
          feedk(d, Spec.marks(d, t), stepk(d, p, Spec.Mark{_, c})) : Csv.P}
      %Equal.sym(Csv.P, Csv.step(d, p, c), stepk(d, p, Spec.Mark{Csv.cls(d, c), c}), step_k(d, p, c)) :
        {Csv.feed(d, t, _) == feedk(d, Spec.marks(d, t), stepk(d, p, Spec.Mark{Csv.cls(d, c), c})) :
          Csv.P}
      feed_is_feedk(d, t, stepk(d, p, Spec.Mark{Csv.cls(d, c), c}))

# a refused reader reads the refusal, whatever follows
def BADR(+d: Csv.Dialect, ms: List<&2, Spec.Mark>, -at: Nat, -why: Csv.Why, -fl: Nat,
  -cur: List<&2, Bytes()>, -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) ->
  {R(d, ms, Csv.P{Csv.Bad{at, why}, fl, cur, out, w, pos}) == Csv.Refused{at, why} : Csv.Out}:
  match ms:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case Spec.Mark{k, c}:
          BADR(d, t, at, why, fl, cur, out, w, pos)

def absurd(-g: Type, e: Empty) -> g:
  match e:

# the header, taken the same way
def tbl(h: Bool, xs: List<&2, List<&2, Bytes()>>) ->
  {Csv.table.at(h, xs) == Spec.done.as(h, xs) : Csv.Out}:
  match h xs:
    case True{} Nil{}:
      {==}
    case True{} Con{r, t}:
      {==}
    case False{} _:
      {==}

# the fuel bounds the marks
def LEb(ms: List<&2, Spec.Mark>, n: Nat) -> Type:
  match ms n:
    case Nil{} _:
      Unit
    case Con{x, t} 0n:
      Empty
    case Con{x, t} 1n+k:
      LEb(t, k)

def lb.tail(-x: Spec.Mark, u: List<&2, Spec.Mark>, k: Nat) -> LEb(Con{x, u}, k) -> LEb(u, k):
  match u k:
    case Nil{} _:
      e => Unit{}
    case Con{y, v} 0n:
      e => absurd(LEb(Con{y, v}, 0n), e)
    case Con{y, v} 1n+j:
      e => lb.tail(y, v, j)(e)

def lb.refl(ms: List<&2, Spec.Mark>) -> LEb(ms, List.length(&2, Spec.Mark, ms)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      lb.refl(t)

# the grammar's production for a reader mode
def at_of(m: Csv.Mode) -> Spec.At:
  match m:
    case Csv.RS{}:
      Spec.Record{}
    case Csv.FS{}:
      Spec.Field{}
    case Csv.Unq{a, l}:
      Spec.Plain{a, l}
    case Csv.Quo{a, l}:
      Spec.Quoted{a, l}
    case Csv.QQ{a, l}:
      Spec.Closed{a, l}
    case Csv.CRp{a, at}:
      Spec.Record{}
    case Csv.Bad{at, why}:
      Spec.Record{}

# a CR held and a refusal are not modes the grammar is ever in
def Pre(m: Csv.Mode) -> Type:
  match m:
    case Csv.CRp{a, at}:
      Empty
    case Csv.Bad{at, why}:
      Empty
    case _:
      Unit

def lexd(+d: Csv.Dialect, ms: List<&2, Spec.Mark>) -> List<&2, Spec.Lx>:
  Spec.lex(ms, Spec.takes_crlf(d), Spec.takes_cr(d), Spec.takes_lf(d))

# the reader in mode m reads what the grammar in m's production reads
def SIM(-d: Csv.Dialect, -ms: List<&2, Spec.Mark>, -m: Csv.Mode, -fl: Nat, -cur: List<&2, Bytes()>,
  -out: List<&2, List<&2, Bytes()>>, -w: Maybe<&2, Nat>, -pos: Nat) -> Type:
  {R(d, ms, Csv.P{m, fl, cur, out, w, pos}) ==
    Spec.go(lexd(d, ms), d, at_of(m), fl, cur, out, w, pos) : Csv.Out}

# what the induction hands a case: the claim for every input the fuel k
# bounds, from every mode
def IH(-k: Nat, -d: Csv.Dialect) -> Type:
  @ms: List<&2, Spec.Mark> -> @m: Csv.Mode -> @fl: Nat -> @cur: List<&2, Bytes()> ->
    @out: List<&2, List<&2, Bytes()>> -> @w: Maybe<&2, Nat> -> @pos: Nat ->
    LEb(ms, k) -> Pre(m) -> SIM(d, ms, m, fl, cur, out, w, pos)

# Ends of fields and records
# --------------------------

# a record's end, continued: G is what the reader reads from the state
# after it, k what the grammar reads
def HK(-d: Csv.Dialect, -G: Csv.P -> Csv.Out,
  -k: List<&2, List<&2, Bytes()>> -> Maybe<&2, Nat> -> Csv.Out, -np: Nat) -> Type:
  @o: List<&2, List<&2, Bytes()>> -> @x: Maybe<&2, Nat> ->
    {G(Csv.P{Csv.RS{}, Csv.max_fields(d), Nil{}, o, x, np}) == k(o, x) : Csv.Out}

def HB(-G: Csv.P -> Csv.Out) -> Type:
  @a2: Nat -> @y: Csv.Why -> @f: Nat -> @c2: List<&2, Bytes()> -> @o2: List<&2, List<&2, Bytes()>> ->
    @w2: Maybe<&2, Nat> -> @p2: Nat ->
    {G(Csv.P{Csv.Bad{a2, y}, f, c2, o2, w2, p2}) == Csv.Refused{a2, y} : Csv.Out}

def LE.w(ok: Bool, +d: Csv.Dialect, +rec: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>,
  +x: Nat, +at: Nat, +np: Nat, -G: Csv.P -> Csv.Out,
  -k: List<&2, List<&2, Bytes()>> -> Maybe<&2, Nat> -> Csv.Out) ->
  HK(d, G, k, np) -> HB(G) ->
  {G(Csv.endr.ok(ok, d, rec, out, x, at, Csv.RS{}, np)) == Spec.wide(ok, rec, out, x, at, k) : Csv.Out}:
  match ok:
    case True{}:
      hk => hb => hk(Con{rec, out}, Some{x})
    case False{}:
      hk => hb => hb(at, Csv.Ragged{}, 0n, Nil{}, out, Some{x}, at)

# LEMMA: a line end, read by both: the same refusal, or the same record
# kept and the same state after it
def LE(+d: Csv.Dialect, +text: Bytes(), fl: Nat, +cur: List<&2, Bytes()>,
  +out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +at: Nat, +np: Nat, -G: Csv.P -> Csv.Out,
  -k: List<&2, List<&2, Bytes()>> -> Maybe<&2, Nat> -> Csv.Out) ->
  HK(d, G, k, np) -> HB(G) ->
  {G(Csv.endl(d, text, fl, cur, out, w, at, np)) == Spec.line.end(d, text, fl, cur, out, w, at, k) :
    Csv.Out}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      match fl:
        case 0n:
          hk => hb => hb(at, Csv.TooManyFields{}, 0n, cur, out, w, at)
        case 1n+f:
          match w:
            case None{}:
              hk => hb => hk(Con{List.reverse(&2, Bytes(), Con{text, cur}), out}, Some{f})
            case Some{+x}:
              LE.w(Bool.or(rg, Nat.is_eq(f, x)), Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd},
                List.reverse(&2, Bytes(), Con{text, cur}), out, x, at, np, G, k)

def hb.r(+d: Csv.Dialect, +ms: List<&2, Spec.Mark>) -> HB(p => R(d, ms, p)):
  a2 => y => f => c2 => o2 => w2 => p2 => BADR(d, ms, a2, y, f, c2, o2, w2, p2)

# LEMMA: a field's end at a delimiter
def FEL(fl: Nat, +d: Csv.Dialect, +text: Bytes(), +cur: List<&2, Bytes()>,
  +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat, +t: List<&2, Spec.Mark>) ->
  (@f: Nat -> @gs: List<&2, Bytes()> -> SIM(d, t, Csv.FS{}, f, gs, out, w, 1n+pos)) ->
  {R(d, t, Csv.endf(text, fl, cur, out, w, pos, Csv.FS{}, 1n+pos)) ==
    Spec.field.end(fl, text, cur, pos, m => gs => Spec.go(lexd(d, t), d, Spec.Field{}, m, gs, out, w,
      1n+pos)) : Csv.Out}:
  match fl:
    case 0n:
      h => BADR(d, t, pos, Csv.TooManyFields{}, 0n, cur, out, w, pos)
    case 1n+f:
      h => h(f, Con{text, cur})

# LEMMA: a byte of a field, if it has room
def PUT(l: Nat, +q: Bool, +d: Csv.Dialect, +c: U32, +acc: Bytes(), +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +t: List<&2, Spec.Mark>) ->
  (@l2: Nat -> SIM(d, t, Csv.grow(q, Csv.push(acc, c), l2), fl, cur, out, w, 1n+pos)) ->
  {R(d, t, Csv.put(q, c, acc, l, fl, cur, out, w, pos)) ==
    Spec.room(l, pos, m => Spec.go(lexd(d, t), d, at_of(Csv.grow(q, Csv.push(acc, c), m)), fl, cur,
      out, w, 1n+pos)) : Csv.Out}:
  match l:
    case 0n:
      h => BADR(d, t, pos, Csv.FieldTooLong{}, fl, cur, out, w, pos)
    case 1n+l2:
      h => h(l2)

# The four modes a field may end in: at the start of a record, after a
# delimiter, in an unquoted field, after a closing quote
type E is Data:
  ERec{}
  EFld{}
  EPl{text: Bytes(), r: Nat}
  ECl{text: Bytes(), r: Nat}

def e.m(e: E) -> Csv.Mode:
  match e:
    case ERec{}:
      Csv.RS{}
    case EFld{}:
      Csv.FS{}
    case EPl{t, r}:
      Csv.Unq{t, r}
    case ECl{t, r}:
      Csv.QQ{t, r}

def e.txt(e: E) -> Bytes():
  match e:
    case ERec{}:
      ""
    case EFld{}:
      ""
    case EPl{t, r}:
      t
    case ECl{t, r}:
      t

def hb.fin(+d: Csv.Dialect) -> HB(p => Csv.result(d, p)):
  a2 => y => f => c2 => o2 => w2 => p2 => {==}

# a delimiter where a field may end
def EKD(+d: Csv.Dialect, ee: E, +c: U32, +t: List<&2, Spec.Mark>, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  -k: Nat) -> IH(k, d) -> LEb(t, k) ->
  {R(d, t, Csv.endf(e.txt(ee), fl, cur, out, w, pos, Csv.FS{}, 1n+pos)) ==
    Spec.go(Con{Spec.LComma{c}, lexd(d, t)}, d, at_of(e.m(ee)), fl, cur, out, w, pos) : Csv.Out}:
  match ee:
    case ERec{}:
      ih => lb => FEL(fl, d, "", cur, out, w, pos, t)(f => gs => ih(t, Csv.FS{}, f, gs, out, w, 1n+pos)(lb)(Unit{}))
    case EFld{}:
      ih => lb => FEL(fl, d, "", cur, out, w, pos, t)(f => gs => ih(t, Csv.FS{}, f, gs, out, w, 1n+pos)(lb)(Unit{}))
    case EPl{tx, r}:
      ih => lb => FEL(fl, d, tx, cur, out, w, pos, t)(f => gs => ih(t, Csv.FS{}, f, gs, out, w, 1n+pos)(lb)(Unit{}))
    case ECl{tx, r}:
      ih => lb => FEL(fl, d, tx, cur, out, w, pos, t)(f => gs => ih(t, Csv.FS{}, f, gs, out, w, 1n+pos)(lb)(Unit{}))

# an LF where a field may end
def ELF(+d: Csv.Dialect, ee: E, +c: U32, +t: List<&2, Spec.Mark>, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +k: Nat) -> IH(k, d) -> LEb(t, k) ->
  {R(d, t, Csv.lf.at(d, e.txt(ee), fl, cur, out, w, pos)) ==
    Spec.go(Con{Spec.lone.lf(Spec.takes_lf(d), c), lexd(d, t)}, d, at_of(e.m(ee)), fl, cur, out, w, pos) :
    Csv.Out}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      match b ee:
        case True{} ERec{}:
          ih => lb => LE(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t, p),
            rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t), Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
            o => x => ih(t, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(hb.r(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t))
        case True{} EFld{}:
          ih => lb => LE(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t, p),
            rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t), Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
            o => x => ih(t, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(hb.r(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t))
        case True{} EPl{tx, r}:
          ih => lb => LE(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t, p),
            rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t), Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
            o => x => ih(t, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(hb.r(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t))
        case True{} ECl{tx, r}:
          ih => lb => LE(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t, p),
            rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t), Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
            o => x => ih(t, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(hb.r(Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, t))
        case False{} ERec{}:
          ih => lb => BADR(Csv.Dialect{dl, q, a, False{}, cr, h, mf, mn, rg, pd}, t, pos, Csv.BareLF{}, fl, cur, out, w, pos)
        case False{} EFld{}:
          ih => lb => BADR(Csv.Dialect{dl, q, a, False{}, cr, h, mf, mn, rg, pd}, t, pos, Csv.BareLF{}, fl, cur, out, w, pos)
        case False{} EPl{tx, r}:
          ih => lb => BADR(Csv.Dialect{dl, q, a, False{}, cr, h, mf, mn, rg, pd}, t, pos, Csv.BareLF{}, fl, cur, out, w, pos)
        case False{} ECl{tx, r}:
          ih => lb => BADR(Csv.Dialect{dl, q, a, False{}, cr, h, mf, mn, rg, pd}, t, pos, Csv.BareLF{}, fl, cur, out, w, pos)

# an LF inside quotes
def QLF(+d: Csv.Dialect, +c: U32, +t: List<&2, Spec.Mark>, +acc: Bytes(), +l: Nat, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  -k: Nat) -> IH(k, d) -> LEb(t, k) ->
  {R(d, t, Csv.put(True{}, c, acc, l, fl, cur, out, w, pos)) ==
    Spec.go(Con{Spec.lone.lf(Spec.takes_lf(d), c), lexd(d, t)}, d, Spec.Quoted{acc, l}, fl, cur, out, w,
      pos) : Csv.Out}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      match b:
        case True{}:
          ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, a, True{}, cr, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, t)(
            l2 => ih(t, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
        case False{}:
          ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, a, False{}, cr, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, t)(
            l2 => ih(t, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))

# a CR where a field may end: the reader holds it (CRp) and the byte
# after it says what it was; the grammar's lexer looks at that byte
def ECR(+d: Csv.Dialect, +c: U32, +t: List<&2, Spec.Mark>, ee: E, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +k: Nat) -> IH(k, d) -> LEb(t, k) ->
  {R(d, t, Csv.cr.at(d, e.txt(ee), fl, cur, out, w, pos)) ==
    Spec.go(Spec.lex(Con{Spec.Mark{Csv.KCR{}, c}, t}, Spec.takes_crlf(d), Spec.takes_cr(d),
      Spec.takes_lf(d)), d, at_of(e.m(ee)), fl, cur, out, w, pos) : Csv.Out}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      match a cr t:
        case True{} True{} Nil{}:
          match ee:
            case ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}))
            case EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}))
            case EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}))
            case ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}))
        case True{} True{} Con{Spec.Mark{k2, b0}, u}:
          match k2 ee:
            case Csv.KQ{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KQ{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KQ{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KQ{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KLF{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u))
            case Csv.KLF{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u))
            case Csv.KLF{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u))
            case Csv.KLF{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u))
            case Csv.KO{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
        case True{} False{} Nil{}:
          match ee:
            case ERec{}:
              ih => lb => {==}
            case EFld{}:
              ih => lb => {==}
            case EPl{tx, r}:
              ih => lb => {==}
            case ECl{tx, r}:
              ih => lb => {==}
        case True{} False{} Con{Spec.Mark{k2, b0}, u}:
          match k2 ee:
            case Csv.KQ{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KQ{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KQ{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KQ{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KD{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KD{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KD{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KD{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KCR{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KCR{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KCR{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KCR{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KLF{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u))
            case Csv.KLF{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u))
            case Csv.KLF{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u))
            case Csv.KLF{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+1n+pos, p => R(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, p),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u), Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+1n+pos))(
              o => x => ih(u, Csv.RS{}, mn, Nil{}, o, x, 1n+1n+pos)(lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(
                Unit{}))(hb.r(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u))
            case Csv.KO{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KO{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KO{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
            case Csv.KO{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, u, pos, Csv.BareCR{}, fl, cur, out, w, 1n+pos)
        case False{} True{} Nil{}:
          match ee:
            case ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}))
            case EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}))
            case EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}))
            case ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => Csv.result(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p),
              rs2 => f2 => Spec.go(Nil{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Nil{}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(Unit{})(Unit{}))(hb.fin(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}))
        case False{} True{} Con{Spec.Mark{k2, b0}, u}:
          match k2 ee:
            case Csv.KQ{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KQ{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KQ{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KQ{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KQ{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KD{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KD{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KCR{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KCR{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KLF{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KLF{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KLF{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KLF{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KLF{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KLF{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KLF{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KLF{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KLF{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KLF{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KLF{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KLF{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} ERec{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} EFld{}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} EPl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
            case Csv.KO{} ECl{tx, r}:
              ih => lb => LE(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, tx, fl, cur, out, w, pos, 1n+pos, p => R(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, Csv.fresh.after(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, p, Csv.KO{}, b0)),
              rs2 => f2 => Spec.go(lexd(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}), Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, Spec.Record{}, mn, Nil{}, rs2, f2, 1n+pos))(
              o => x => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.RS{}, mn, Nil{}, o, x, 1n+pos)(lb)(Unit{}))(
              a2 => y => f => c2 => o2 => w2 => p2 => BADR(Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, u, a2, y, f, c2, o2, w2, p2))
        case False{} False{} Nil{}:
          match ee:
            case ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Nil{}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Nil{}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Nil{}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Nil{}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
        case False{} False{} Con{Spec.Mark{k2, b0}, u}:
          match k2 ee:
            case Csv.KQ{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KQ{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KQ{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KQ{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KD{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KD{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KD{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KD{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KCR{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KCR{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KCR{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KCR{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KLF{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KLF{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KLF{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KLF{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KO{} ERec{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KO{} EFld{}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KO{} EPl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)
            case Csv.KO{} ECl{tx, r}:
              ih => lb => BADR(Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, b0}, u}, pos, Csv.BareCR{}, fl, cur, out, w, pos)

# a CR inside quotes: data, and so is an LF after it, one byte each
def QCR(+d: Csv.Dialect, +c: U32, +t: List<&2, Spec.Mark>, +acc: Bytes(), l: Nat, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat,
  +k: Nat) -> IH(k, d) -> LEb(t, k) ->
  {R(d, t, Csv.put(True{}, c, acc, l, fl, cur, out, w, pos)) ==
    Spec.go(Spec.lex(Con{Spec.Mark{Csv.KCR{}, c}, t}, Spec.takes_crlf(d), Spec.takes_cr(d),
      Spec.takes_lf(d)), d, Spec.Quoted{acc, l}, fl, cur, out, w, pos) : Csv.Out}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      match a cr t:
        case True{} True{} Nil{}:
          ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Nil{})(
            l2 => ih(Nil{}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(Unit{})(Unit{}))
        case True{} True{} Con{Spec.Mark{k2, b0}, u}:
          match k2 l:
            case Csv.KQ{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KQ{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KD{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KD{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KCR{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KCR{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KLF{} 0n:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}, pos, Csv.FieldTooLong{}, fl, cur, out, w, pos)
            case Csv.KLF{} 1n+l2:
              ih => lb => PUT(l2, True{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, b0, Csv.push(acc, c), fl, cur, out, w, 1n+pos, u)(
                j => ih(u, Csv.Quo{Csv.push(Csv.push(acc, c), b0), j}, fl, cur, out, w, 1n+1n+pos)(
                  lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(Unit{}))
            case Csv.KO{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KO{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
        case True{} False{} Nil{}:
          ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Nil{})(
            l2 => ih(Nil{}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(Unit{})(Unit{}))
        case True{} False{} Con{Spec.Mark{k2, b0}, u}:
          match k2 l:
            case Csv.KQ{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KQ{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KD{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KD{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KCR{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KCR{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KLF{} 0n:
              ih => lb => BADR(Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, b0}, u}, pos, Csv.FieldTooLong{}, fl, cur, out, w, pos)
            case Csv.KLF{} 1n+l2:
              ih => lb => PUT(l2, True{}, Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, b0, Csv.push(acc, c), fl, cur, out, w, 1n+pos, u)(
                j => ih(u, Csv.Quo{Csv.push(Csv.push(acc, c), b0), j}, fl, cur, out, w, 1n+1n+pos)(
                  lb.tail(Spec.Mark{Csv.KLF{}, b0}, u, k)(lb))(Unit{}))
            case Csv.KO{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, True{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KO{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
        case False{} True{} Nil{}:
          ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Nil{})(
            l2 => ih(Nil{}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(Unit{})(Unit{}))
        case False{} True{} Con{Spec.Mark{k2, b0}, u}:
          match k2 l:
            case Csv.KQ{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KQ{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KD{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KD{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KCR{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KCR{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KLF{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KLF{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KLF{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KO{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, True{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KO{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
        case False{} False{} Nil{}:
          ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Nil{})(
            l2 => ih(Nil{}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(Unit{})(Unit{}))
        case False{} False{} Con{Spec.Mark{k2, b0}, u}:
          match k2 l:
            case Csv.KQ{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KQ{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KQ{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KD{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KD{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KD{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KCR{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KCR{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KCR{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KLF{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KLF{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KLF{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
            case Csv.KO{} _:
              ih => lb => PUT(l, True{}, Csv.Dialect{dl, q, False{}, b, False{}, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, Con{Spec.Mark{Csv.KO{}, b0}, u})(
                l2 => ih(Con{Spec.Mark{Csv.KO{}, b0}, u}, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))

# the end of input, from every mode
def END(+d: Csv.Dialect, +m: Csv.Mode, +fl: Nat, +cur: List<&2, Bytes()>,
  +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  Pre(m) -> SIM(d, Nil{}, m, fl, cur, out, w, pos):
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      match m:
        case Csv.RS{}:
          pre => tbl(h, List.reverse(&2, List<&2, Bytes()>, out))
        case Csv.FS{}:
          pre => LE(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, "", fl, cur, out, w, pos, pos, p => Csv.result(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, p),
            rs2 => f2 => Spec.done(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, rs2))(
            o => x => tbl(h, List.reverse(&2, List<&2, Bytes()>, o)))(hb.fin(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}))
        case Csv.Unq{acc, l}:
          pre => LE(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, acc, fl, cur, out, w, pos, pos, p => Csv.result(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, p),
            rs2 => f2 => Spec.done(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, rs2))(
            o => x => tbl(h, List.reverse(&2, List<&2, Bytes()>, o)))(hb.fin(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}))
        case Csv.QQ{acc, l}:
          pre => LE(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, acc, fl, cur, out, w, pos, pos, p => Csv.result(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, p),
            rs2 => f2 => Spec.done(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, rs2))(
            o => x => tbl(h, List.reverse(&2, List<&2, Bytes()>, o)))(hb.fin(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}))
        case Csv.Quo{acc, l}:
          pre => {==}
        case Csv.CRp{acc, at}:
          pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Nil{}, Csv.CRp{acc, at}, fl, cur, out, w, pos), pre)
        case Csv.Bad{at, why}:
          pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Nil{}, Csv.Bad{at, why}, fl, cur, out, w, pos), pre)

# one byte, from every mode the grammar can be in
def STEP(+k: Nat, x: Spec.Mark, +d: Csv.Dialect, +m: Csv.Mode, +t: List<&2, Spec.Mark>, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  IH(k, d) -> LEb(t, k) -> Pre(m) -> SIM(d, Con{x, t}, m, fl, cur, out, w, pos):
  match x:
    case Spec.Mark{kk, +c}:
      match kk:
        case Csv.KQ{}:
          match d:
            case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
              match m:
                case Csv.RS{}:
                  ih => lb => pre => ih(t, Csv.Quo{"", mf}, fl, cur, out, w, 1n+pos)(lb)(Unit{})
                case Csv.FS{}:
                  ih => lb => pre => ih(t, Csv.Quo{"", mf}, fl, cur, out, w, 1n+pos)(lb)(Unit{})
                case Csv.Unq{acc, l}:
                  ih => lb => pre => BADR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, t, pos, Csv.QuoteInField{}, fl, cur, out, w, pos)
                case Csv.Quo{acc, l}:
                  ih => lb => pre => ih(t, Csv.QQ{acc, l}, fl, cur, out, w, 1n+pos)(lb)(Unit{})
                case Csv.QQ{acc, l}:
                  ih => lb => pre => PUT(l, True{}, Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, t)(
                      l2 => ih(t, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
                case Csv.CRp{acc, at}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, c}, t}, Csv.CRp{acc, at}, fl, cur, out, w, pos), pre)
                case Csv.Bad{at, why}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KQ{}, c}, t}, Csv.Bad{at, why}, fl, cur, out, w, pos), pre)
        case Csv.KD{}:
          match d:
            case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
              match m:
                case Csv.RS{}:
                  ih => lb => pre => EKD(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, ERec{}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.FS{}:
                  ih => lb => pre => EKD(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, EFld{}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.Unq{acc, l}:
                  ih => lb => pre => EKD(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, EPl{acc, l}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.Quo{acc, l}:
                  ih => lb => pre => PUT(l, True{}, Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, t)(
                      l2 => ih(t, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
                case Csv.QQ{acc, l}:
                  ih => lb => pre => EKD(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, ECl{acc, l}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.CRp{acc, at}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, c}, t}, Csv.CRp{acc, at}, fl, cur, out, w, pos), pre)
                case Csv.Bad{at, why}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KD{}, c}, t}, Csv.Bad{at, why}, fl, cur, out, w, pos), pre)
        case Csv.KCR{}:
          match d:
            case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
              match m:
                case Csv.RS{}:
                  ih => lb => pre => ECR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, t, ERec{}, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.FS{}:
                  ih => lb => pre => ECR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, t, EFld{}, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.Unq{acc, l}:
                  ih => lb => pre => ECR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, t, EPl{acc, l}, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.Quo{acc, l}:
                  ih => lb => pre => QCR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, t, acc, l, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.QQ{acc, l}:
                  ih => lb => pre => ECR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, t, ECl{acc, l}, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.CRp{acc, at}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, c}, t}, Csv.CRp{acc, at}, fl, cur, out, w, pos), pre)
                case Csv.Bad{at, why}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KCR{}, c}, t}, Csv.Bad{at, why}, fl, cur, out, w, pos), pre)
        case Csv.KLF{}:
          match d:
            case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
              match m:
                case Csv.RS{}:
                  ih => lb => pre => ELF(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, ERec{}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.FS{}:
                  ih => lb => pre => ELF(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, EFld{}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.Unq{acc, l}:
                  ih => lb => pre => ELF(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, EPl{acc, l}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.Quo{acc, l}:
                  ih => lb => pre => QLF(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, t, acc, l, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.QQ{acc, l}:
                  ih => lb => pre => ELF(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, ECl{acc, l}, c, t, fl, cur, out, w, pos, k)(ih)(lb)
                case Csv.CRp{acc, at}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, c}, t}, Csv.CRp{acc, at}, fl, cur, out, w, pos), pre)
                case Csv.Bad{at, why}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KLF{}, c}, t}, Csv.Bad{at, why}, fl, cur, out, w, pos), pre)
        case Csv.KO{}:
          match d:
            case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
              match m:
                case Csv.RS{}:
                  ih => lb => pre => PUT(mf, False{}, Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, "", fl, cur, out, w, pos, t)(
                      l2 => ih(t, Csv.Unq{Csv.push("", c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
                case Csv.FS{}:
                  ih => lb => pre => PUT(mf, False{}, Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, "", fl, cur, out, w, pos, t)(
                      l2 => ih(t, Csv.Unq{Csv.push("", c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
                case Csv.Unq{acc, l}:
                  ih => lb => pre => PUT(l, False{}, Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, t)(
                      l2 => ih(t, Csv.Unq{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
                case Csv.Quo{acc, l}:
                  ih => lb => pre => PUT(l, True{}, Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, c, acc, fl, cur, out, w, pos, t)(
                      l2 => ih(t, Csv.Quo{Csv.push(acc, c), l2}, fl, cur, out, w, 1n+pos)(lb)(Unit{}))
                case Csv.QQ{acc, l}:
                  ih => lb => pre => BADR(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, t, pos, Csv.AfterQuote{}, fl, cur, out, w, pos)
                case Csv.CRp{acc, at}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, c}, t}, Csv.CRp{acc, at}, fl, cur, out, w, pos), pre)
                case Csv.Bad{at, why}:
                  ih => lb => pre => absurd(SIM(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Con{Spec.Mark{Csv.KO{}, c}, t}, Csv.Bad{at, why}, fl, cur, out, w, pos), pre)

# THEOREM: on every input the fuel bounds, from every mode the grammar
# can be in, the reader reads what the grammar reads
def sim(+n: Nat, ms: List<&2, Spec.Mark>, +d: Csv.Dialect, +m: Csv.Mode, +fl: Nat,
  +cur: List<&2, Bytes()>, +out: List<&2, List<&2, Bytes()>>, +w: Maybe<&2, Nat>, +pos: Nat) ->
  LEb(ms, n) -> Pre(m) -> SIM(d, ms, m, fl, cur, out, w, pos):
  match n ms:
    case _ Nil{}:
      lb => pre => END(d, m, fl, cur, out, w, pos)(pre)
    case 0n Con{x, t}:
      lb => pre => absurd(SIM(d, Con{x, t}, m, fl, cur, out, w, pos), lb)
    case 1n+k Con{x, t}:
      lb => pre => STEP(k, x, d, m, t, fl, cur, out, w, pos)(
        ms2 => m2 => fl2 => cur2 => out2 => w2 => pos2 =>
          sim(k, ms2, d, m2, fl2, cur2, out2, w2, pos2))(lb)(pre)

# the laws, whole
def sim.new(+d: Csv.Dialect, +bs: List<&2, U32>) ->
  {R(d, Spec.marks(d, bs), Csv.new(d)) == Spec.parse(bs, d) : Csv.Out}:
  match d:
    case Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}:
      sim(List.length(&2, Spec.Mark, Spec.marks(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, bs)), Spec.marks(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, bs), Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, Csv.RS{}, mn,
        Nil{}, Nil{}, None{}, 0n)(lb.refl(Spec.marks(Csv.Dialect{dl, q, a, b, cr, h, mf, mn, rg, pd}, bs)))(Unit{})

def Laws.csv_sim(d, bs):
  Equal.trans(Csv.Out, Csv.result(d, Csv.finish(d, Csv.feed(d, bs, Csv.new(d)))),
    R(d, Spec.marks(d, bs), Csv.new(d)), Spec.parse(bs, d),
    Equal.cong(Csv.P, Csv.Out, p => Csv.result(d, Csv.finish(d, p)), Csv.feed(d, bs, Csv.new(d)),
      feedk(d, Spec.marks(d, bs), Csv.new(d)), feed_is_feedk(d, bs, Csv.new(d))),
    sim.new(d, bs))

def Laws.csv_sim_buf(d, b):
  %Equal.sym(Csv.P, Csv.feed_buf(d, b, Csv.new(d)), Csv.feed(d, Bytes.to_list(b), Csv.new(d)),
    Laws.feed_buf_is_feed(d, b, Csv.new(d))) :
    {Csv.result(d, Csv.finish(d, _)) == Spec.parse(Bytes.to_list(b), d) : Csv.Out}
  Laws.csv_sim(d, Bytes.to_list(b))

# reads fed one after another are their bytes fed at once
def reads.is(+d: Csv.Dialect, rs: List<&2, Bytes()>, +p: Csv.P) ->
  {Laws.reads(d, rs, p) == Csv.feed(d, Bytes.to_list(Bytes.concat(rs)), p) : Csv.P}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      Equal.trans(Csv.P, Laws.reads(d, t, Csv.feed_buf(d, r, p)),
        Csv.feed(d, Bytes.to_list(Bytes.concat(t)), Csv.feed_buf(d, r, p)),
        Csv.feed(d, Bytes.to_list(Bytes.append(r, Bytes.concat(t))), p),
        reads.is(d, t, Csv.feed_buf(d, r, p)),
        Equal.trans(Csv.P, Csv.feed(d, Bytes.to_list(Bytes.concat(t)), Csv.feed_buf(d, r, p)),
          Csv.feed(d, Bytes.to_list(Bytes.concat(t)), Csv.feed(d, Bytes.to_list(r), p)),
          Csv.feed(d, Bytes.to_list(Bytes.append(r, Bytes.concat(t))), p),
          Equal.cong(Csv.P, Csv.P, x => Csv.feed(d, Bytes.to_list(Bytes.concat(t)), x), Csv.feed_buf(d, r, p),
            Csv.feed(d, Bytes.to_list(r), p), Laws.feed_buf_is_feed(d, r, p)),
          Equal.trans(Csv.P, Csv.feed(d, Bytes.to_list(Bytes.concat(t)), Csv.feed(d, Bytes.to_list(r), p)),
            Csv.feed(d, List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), p),
            Csv.feed(d, Bytes.to_list(Bytes.append(r, Bytes.concat(t))), p),
            Equal.sym(Csv.P, Csv.feed(d, List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), p),
              Csv.feed(d, Bytes.to_list(Bytes.concat(t)), Csv.feed(d, Bytes.to_list(r), p)),
              Laws.feed_split(d, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t)), p)),
            Equal.cong(List<&2, U32>, Csv.P, x => Csv.feed(d, x, p),
              List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
              Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
              Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
                List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
                Bytes.to_list_append(r, Bytes.concat(t)))))))

def Laws.csv_sim_reads(d, rs):
  %Equal.sym(Csv.P, Laws.reads(d, rs, Csv.new(d)), Csv.feed(d, Bytes.to_list(Bytes.concat(rs)), Csv.new(d)),
    reads.is(d, rs, Csv.new(d))) :
    {Csv.result(d, Csv.finish(d, _)) == Spec.parse(Bytes.to_list(Bytes.concat(rs)), d) : Csv.Out}
  Laws.csv_sim(d, Bytes.to_list(Bytes.concat(rs)))

