# Types
# =====

# Data
# ----

type Empty is Data:

type Unit is Data:
  Unit{}

type Bool is Data:
  False{}
  True{}

type Cmp is Data:
  LT{}
  EQ{}
  GT{}

type Either<a, b, -A: Kind(a), -B: Kind(b)> is Kind(a <&> b):
  Inl{value: A}
  Inr{value: B}

type Sigma<a, b, -A: Kind(a), -B: @-x: A -> Kind(b)> is Kind(a <&> b):
  Tuple{fst: A, snd: B(fst)}

type Nat is Data:
  Zero{}
  Succ{pred: Nat}

type Maybe<a, -A: Kind(a)> is Kind(a):
  None{}
  Some{value: A}

type Result<a, b, -E: Kind(a), -A: Kind(b)> is Kind(a <&> b):
  Fail{error: E}
  Done{value: A}

type List<a, -A: Kind(a)> is Kind(a):
  Nil{}
  Con{head: A, tail: List<a, A>}

law Word:
  for n: Nat
  Data

type Word.Nil is Data:
  WNil{}

type Word.Con<-p: Nat> is Data:
  WCon{head: Bool, tail: Word(p)}

type U32 is Data:
  U32{data: Word(32n)}

type F32 is Data:
  F32{data: Word(32n)}

type F64 is Data:
  F64{data: Word(64n)}

type Char is Data:
  Chr{code: U32}

type String is Data:
  SNil{}
  SCon{head: Char, tail: String}

type Array<-T: Type> is Type:
  ALeaf{value: T}
  ANode{xs: Array<T>, ys: Array<T>}

type Image is Data:
  Pix{color: U32}
  Qua{tl: Image, tr: Image, bl: Image, br: Image}

type Event is Data:
  Key{code: U32, down: Bool}
  Mouse{x: U32, y: U32, button: U32, down: Bool}
  Move{x: U32, y: U32}
  Close{}

type Map<a, -V: Kind(a)> is Kind(a):
  MTip{}
  MLeaf{key: String, val: V}
  MNode{pos: Nat, lo: Map<a, V>, hi: Map<a, V>}

type Re is Data:
  RLit{c: Char}
  RAny{}
  RSet{neg: Bool, rs: List<&2, Sigma<&2, &2, U32, _ => U32>>}
  RCat{a: Re, b: Re}
  RAlt{a: Re, b: Re}
  RRep{r: Re, lo: Nat, hi: Maybe<&2, Nat>, greedy: Bool}
  RCap{n: Nat, r: Re}
  RBol{}
  REol{}
  RWordB{neg: Bool}
  REmpty{}

type Inst is Data:
  IChr{c: U32}
  IAny{}
  ISet{neg: Bool, rs: List<&2, Sigma<&2, &2, U32, _ => U32>>}
  ISplit{x: Nat, y: Nat}
  IJmp{x: Nat}
  ISave{slot: Nat}
  IBol{multi: Bool}
  IEol{multi: Bool}
  IWordB{neg: Bool}
  IMatch{}

type Regex is Data:
  Regex{prog: List<&2, Inst>, ngroups: Nat}

type Match is Data:
  Match{start: Nat, end: Nat, groups: List<&2, Maybe<&2, Sigma<&2, &2, Nat, _ => Nat>>>}

type Regex.Error is Data:
  RErr{pos: Nat, msg: String}

# Parser scratch: one frame per open group (cap = its number), the finished
# alternatives and the current one both newest-first, q = what the last
# item was (0 nothing to repeat, 1 an atom, 2 a fresh greedy repeat)
type Regex.Frame is Data:
  Frame{cap: Maybe<&2, Nat>, alts: List<&2, Re>, cat: List<&2, Re>, q: Nat}

# Class scan: the unread tail, the last single char (a pending range low),
# whether a `-` follows it, the ranges so far; CDone once `]` is read
type Regex.Cls is Data:
  CScan{s: String, pend: Maybe<&2, U32>, dash: Bool, rs: List<&2, Sigma<&2, &2, U32, _ => U32>>}
  CDone{rs: List<&2, Sigma<&2, &2, U32, _ => U32>>, rest: String}

# Effects
# -------

# A handle is opaque, a law with no constructor and no field, so no
# program forges one, and linear (Type), so none copies or reuses one.
law File:
  Type

law Socket:
  Type

law Listener:
  Type

law Window:
  Type

law Audio:
  Type

# A channel is Data: the computations it links each hold a copy.
law Chan:
  for -A: Type
  Data

type IO.OP<-R: Type> is Type:
  Emit{value: R}
  Halt{code: U32, message: String}

law Pair:
  for -A: Type
  for -B: Type
  Type

law IO:
  for -A: Type
  Type

type App<-S: Type> is Type:
  App{view: S -> Pair(S, Image), tick: List<Event> -> S -> IO(Maybe<S>)}

# Defs
# ====

# Word
# ----

def Word(n):
  match n:
    case 0n:
      Word.Nil
    case 1n+p:
      Word.Con<p>

# Pair
# ----

def Pair(A, B):
  Sigma<&1, &1, A, _ => B>

def Exists(-A: Type, -B: @-x: A -> Type) -> Type:
  Sigma<&1, &1, A, B>

def Or(-A: Type, -B: Type) -> Type:
  Either<&1, &1, A, B>

def Pair.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def Pair.snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# Effects
# -------

def IO(A):
  @-R: Type ->
  @k: (A -> IO.OP<R>) ->
  IO.OP<R>

def IO.pure(-A: Type, x: A) -> IO(A):
  R => k => k(x)

def IO.bind(-A: Type, -B: Type, m: IO(A), f: A -> IO(B)) -> IO(B):
  R => k => m(R, x => f(x, R, k))

def IO.print(text: String) -> IO(Unit):
  import "./effs/print.c"
  import "./effs/print.js"

def IO.write(text: String) -> IO(Unit):
  import "./effs/write.c"
  import "./effs/write.js"

def IO.print_err(text: String) -> IO(Unit):
  import "./effs/print_err.c"
  import "./effs/print_err.js"

def IO.get_env(name: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./effs/get_env.c"
  import "./effs/get_env.js"

def IO.die(-A: Type, code: U32, msg: String) -> IO(A):
  R => k => Halt{code, msg}

def IO.pass(-A: Type, r: Result<&1, &1, U32 & String, A>) -> IO(A):
  match r:
    case Done{value}:
      IO.pure(A, value)
    case Fail{(code, message)}:
      IO.die(A, code, message)

def IO.try(-A: Type, act: IO(Result<&1, &1, U32 & String, A>)) -> IO(A):
  IO.bind(Result<&1, &1, U32 & String, A>, A, act, IO.pass(A))

def IO.spawn(-A: Type, act: IO(A)) -> IO(Unit):
  import "./effs/spawn.c"
  import "./effs/spawn.js"

def IO.sleep(ms: U32) -> IO(Unit):
  import "./effs/sleep.c"
  import "./effs/sleep.js"

def IO.now() -> IO(Nat):
  import "./effs/now.c"
  import "./effs/now.js"

def Chan.new(-A: Type, room: U32) -> IO(Chan(A)):
  import "./effs/chan_new.c"
  import "./effs/chan_new.js"

def Chan.send(-A: Type, chan: Chan(A), value: A) -> IO(Bool):
  import "./effs/chan_send.c"
  import "./effs/chan_send.js"

def Chan.recv(-A: Type, chan: Chan(A)) -> IO(Maybe<&1, A>):
  import "./effs/chan_recv.c"
  import "./effs/chan_recv.js"

def Chan.close(-A: Type, chan: Chan(A)) -> IO(Unit):
  import "./effs/chan_close.c"
  import "./effs/chan_close.js"

def IO.fork.go(-A: Type, act: IO(A), chan: Chan(A)) -> IO(Chan(A)):
  +c = chan
  sent = IO.bind(A, Bool, act, x => Chan.send(A, c, x))
  IO.bind(Unit, Chan(A), IO.spawn(Bool, sent), u => IO.pure(Chan(A), c))

def IO.fork(-A: Type, act: IO(A)) -> IO(Chan(A)):
  IO.bind(Chan(A), Chan(A), Chan.new(A, 1), IO.fork.go(A, act))

def IO.join.go(-A: Type, chan: Chan(A), got: Maybe<&1, A>) -> IO(A):
  match got:
    case None{}:
      IO.die(A, 1, "IO.join: the channel was closed")
    case Some{value}:
      IO.bind(Unit, A, Chan.close(A, chan), u => IO.pure(A, value))

def IO.join(-A: Type, +chan: Chan(A)) -> IO(A):
  IO.bind(Maybe<&1, A>, A, Chan.recv(A, chan), IO.join.go(A, chan))

def File.open(path: String, mode: String) ->
  IO(Result<&1, &1, U32 & String, File>):
  import "./effs/file_open.c"
  import "./effs/file_open.js"

def File.read(file: File, max: U32) ->
  IO(File & Result<&1, &1, U32 & String, String>):
  import "./effs/file_read.c"
  import "./effs/file_read.js"

def File.read_bytes(file: File, max: U32) ->
  IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  import "./effs/file_read_bytes.c"
  import "./effs/file_read_bytes.js"

def File.write(file: File, data: String) ->
  IO(File & Result<&1, &1, U32 & String, Unit>):
  import "./effs/file_write.c"
  import "./effs/file_write.js"

def File.close(file: File) -> IO(Unit):
  import "./effs/file_close.c"
  import "./effs/file_close.js"

def TCP.listen(port: U32) -> IO(Result<&1, &1, U32 & String, Listener>):
  import "./effs/tcp_listen.c"
  import "./effs/tcp_listen.js"

def TCP.accept(listener: Listener) ->
  IO(Listener & Result<&1, &1, U32 & String, Socket>):
  import "./effs/tcp_accept.c"
  import "./effs/tcp_accept.js"

def TCP.connect(host: String, port: U32) ->
  IO(Result<&1, &1, U32 & String, Socket>):
  import "./effs/tcp_connect.c"
  import "./effs/tcp_connect.js"

def TCP.send(sock: Socket, data: String) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  import "./effs/tcp_send.c"
  import "./effs/tcp_send.js"

def TCP.recv(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, String>):
  import "./effs/tcp_recv.c"
  import "./effs/tcp_recv.js"

def UDP.bind(port: U32) -> IO(Result<&1, &1, U32 & String, Socket>):
  import "./effs/udp_bind.c"
  import "./effs/udp_bind.js"

def UDP.send_to(sock: Socket, host: String, port: U32, data: String) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  import "./effs/udp_send_to.c"
  import "./effs/udp_send_to.js"

def UDP.recv_from(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, String & U32 & String>):
  import "./effs/udp_recv_from.c"
  import "./effs/udp_recv_from.js"

def UDP.poll(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, Maybe<&1, String & U32 & String>>):
  import "./effs/udp_poll.c"
  import "./effs/udp_poll.js"

def Socket.close(socket: Socket) -> IO(Unit):
  import "./effs/socket_close.c"
  import "./effs/socket_close.js"

def Listener.close(listener: Listener) -> IO(Unit):
  import "./effs/listener_close.c"
  import "./effs/listener_close.js"

def Window.open(title: String, width: U32, height: U32) ->
  IO(Result<&1, &1, U32 & String, Window>):
  import "./effs/window_open.c"
  import "./effs/window_open.js"

def Window.frame(window: Window, image: Image) ->
  IO(Window & Image & List<Event>):
  import "./effs/window_frame.c"
  import "./effs/window_frame.js"

def Window.set_title(window: Window, title: String) -> IO(Window):
  import "./effs/window_set_title.c"
  import "./effs/window_set_title.js"

def Window.close(window: Window) -> IO(Unit):
  import "./effs/window_close.c"
  import "./effs/window_close.js"

def Audio.open(rate: U32) -> IO(Result<&1, &1, U32 & String, Audio>):
  import "./effs/audio_open.c"
  import "./effs/audio_open.js"

def Audio.write(audio: Audio, samples: List<&2, F32>) -> IO(Audio & U32):
  import "./effs/audio_write.c"
  import "./effs/audio_write.js"

def Audio.close(audio: Audio) -> IO(Unit):
  import "./effs/audio_close.c"
  import "./effs/audio_close.js"

# Equal
# -----

law Equal.cong:
  for -A: Type
  for -B: Type
  for -f: A -> B
  for -a: A
  for -b: A
  for  e: {a == b : A}
  {f(a) == f(b) : B}

def Equal.cong(A, B, f, a, b, e):
  %e : {f(a) == f(_) : B}
  {==}

law Equal.sym:
  for -A: Type
  for -a: A
  for -b: A
  for  e: {a == b : A}
  {b == a : A}

def Equal.sym(A, a, b, e):
  %e : {_ == a : A}
  {==}

law Equal.trans:
  for -A : Type
  for -a : A
  for -b : A
  for -c : A
  for ab : {a == b : A}
  for bc : {b == c : A}
  {a == c : A}

def Equal.trans(A, a, b, c, ab, bc):
  %bc : {a == _ : A}
  ab

# Empty
# -----

def Empty.absurd(-A: Type, e: Empty) -> A:
  match e:

# Bool
# ----

def Bool.not(b: Bool) -> Bool:
  match b:
    case False{}:
      True{}
    case True{}:
      False{}

def Bool.and(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      False{}
    case True{}:
      b

def Bool.or(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      b
    case True{}:
      True{}

def Bool.xor(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      b
    case True{}:
      Bool.not(b)

def Bool.cmp(a: Bool, b: Bool) -> Cmp:
  match a b:
    case False{} False{}:
      EQ{}
    case False{} True{}:
      LT{}
    case True{} False{}:
      GT{}
    case True{} True{}:
      EQ{}

def Bool.full_add(a: Bool, b: Bool, c: Bool) -> Bool & Bool:
  match a b c:
    case False{} False{} False{}:
      (False{}, False{})
    case False{} False{} True{}:
      (True{}, False{})
    case False{} True{} False{}:
      (True{}, False{})
    case False{} True{} True{}:
      (False{}, True{})
    case True{} False{} False{}:
      (True{}, False{})
    case True{} False{} True{}:
      (False{}, True{})
    case True{} True{} False{}:
      (False{}, True{})
    case True{} True{} True{}:
      (True{}, True{})

def Bool.pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case False{}:
      b
    case True{}:
      a

def Bool.to_u32(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

# Cmp
# ---

def Cmp.is_lt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def Cmp.is_eq(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Cmp.is_gt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      False{}
    case GT{}:
      True{}

def Cmp.is_le(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Cmp.is_ge(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      True{}

# Nat
# ---

def Nat.double(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+Nat.double(p)

def Nat.add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+Nat.add(p, b)

def Nat.sub(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+bp:
      0n
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      Nat.sub(ap, bp)

def Nat.mul(a: Nat, +b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      Nat.add(b, Nat.mul(p, b))

def Nat.divmod.go(n: Nat, m: Nat, d: Nat, r: Nat) -> Nat & Nat:
  match n:
    case 0n:
      (d, r)
    case 1n+np:
      match m:
        case 0n:
          Nat.divmod.go(np, r, 1n+d, 0n)
        case 1n+mp:
          Nat.divmod.go(np, mp, d, 1n+r)

def Nat.divmod(a: Nat, b: Nat) -> Nat & Nat:
  match b:
    case 0n:
      (0n, a)
    case 1n+bp:
      Nat.divmod.go(a, bp, 0n, 0n)

def Nat.cmp(a: Nat, b: Nat) -> Cmp:
  match a b:
    case 0n 0n:
      EQ{}
    case 0n 1n+bp:
      LT{}
    case 1n+ap 0n:
      GT{}
    case 1n+ap 1n+bp:
      Nat.cmp(ap, bp)

def Nat.is_lt(a: Nat, b: Nat) -> Bool:
  Cmp.is_lt(Nat.cmp(a, b))

def Nat.is_eq(a: Nat, b: Nat) -> Bool:
  Cmp.is_eq(Nat.cmp(a, b))

def Nat.is_ne(a: Nat, b: Nat) -> Bool:
  Bool.not(Cmp.is_eq(Nat.cmp(a, b)))

def Nat.is_le(a: Nat, b: Nat) -> Bool:
  Cmp.is_le(Nat.cmp(a, b))

def Nat.is_gt(a: Nat, b: Nat) -> Bool:
  Cmp.is_gt(Nat.cmp(a, b))

def Nat.is_ge(a: Nat, b: Nat) -> Bool:
  Cmp.is_ge(Nat.cmp(a, b))

def Nat.min(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(a, b), a, b)

def Nat.max(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(a, b), b, a)

def Nat.div.fin(qr: Nat & Nat) -> Nat:
  (q, r) = qr
  q

def Nat.div(a: Nat, b: Nat) -> Nat:
  Nat.div.fin(Nat.divmod(a, b))

def Nat.mod.fin(qr: Nat & Nat) -> Nat:
  (q, r) = qr
  r

def Nat.mod(a: Nat, b: Nat) -> Nat:
  Nat.mod.fin(Nat.divmod(a, b))

def Nat.pow(+a: Nat, b: Nat) -> Nat:
  match b:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(a, Nat.pow(a, p))

# Maybe
# -----

def Maybe.pure(a, -A: Kind(a), x: A) -> Maybe<a, A>:
  Some{x}

def Maybe.bind(
  a, -A: Kind(a), -B: Kind(a), m: Maybe<a, A>, f: A -> Maybe<a, B>
) -> Maybe<a, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

def Maybe.default(a, -A: Kind(a), m: Maybe<a, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def Maybe.is_some(a, -A: Kind(a), m: Maybe<a, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def Maybe.is_none(a, -A: Kind(a), m: Maybe<a, A>) -> Bool:
  Bool.not(Maybe.is_some(a, A, m))

def Maybe.map(
  a, -A: Kind(a), -B: Kind(a), f: A -> B, m: Maybe<a, A>
) -> Maybe<a, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{f(x)}

def Maybe.or(a, -A: Kind(a), m: Maybe<a, A>, n: Maybe<a, A>) -> Maybe<a, A>:
  match m:
    case None{}:
      n
    case Some{x}:
      Some{x}

# Result
# ------

def Result.pure(a, b, -E: Kind(a), -A: Kind(b), x: A) -> Result<a, b, E, A>:
  Done{x}

def Result.bind(
  a, b, -E: Kind(a), -A: Kind(b), -B: Kind(b), r: Result<a, b, E, A>,
  f: A -> Result<a, b, E, B>
) -> Result<a, b, E, B>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      f(x)

def Result.default(
  a, b, -E: Kind(a), -A: Kind(b), r: Result<a, b, E, A>, d: A
) -> A:
  match r:
    case Fail{e}:
      d
    case Done{x}:
      x

def Result.is_done(
  a, b, -E: Kind(a), -A: Kind(b), r: Result<a, b, E, A>
) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

def Result.is_fail(
  a, b, -E: Kind(a), -A: Kind(b), r: Result<a, b, E, A>
) -> Bool:
  Bool.not(Result.is_done(a, b, E, A, r))

def Result.map(
  a, b, -E: Kind(a), -A: Kind(b), -B: Kind(b), f: A -> B,
  r: Result<a, b, E, A>
) -> Result<a, b, E, B>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{f(x)}

# List
# ----

def List.map(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>) -> List<B>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      f(h) <> List.map(~A, ~B, ~f, t)

def List.length(a, -A: Kind(a), xs: List<a, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+List.length(a, A, t)

def List.append(a, -A: Kind(a), xs: List<a, A>, ys: List<a, A>) -> List<a, A>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> List.append(a, A, t, ys)

def List.concat(a, -A: Kind(a), xss: List<a, List<a, A>>) -> List<a, A>:
  match xss:
    case Nil{}:
      Nil{}
    case h <> t:
      List.append(a, A, h, List.concat(a, A, t))

def List.reverse.go(a, -A: Kind(a), xs: List<a, A>, acc: List<a, A>) ->
  List<a, A>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      List.reverse.go(a, A, t, h <> acc)

def List.reverse(a, -A: Kind(a), xs: List<a, A>) -> List<a, A>:
  List.reverse.go(a, A, xs, Nil{})

def List.is_empty(a, -A: Kind(a), xs: List<a, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      False{}

def List.head(a, -A: Kind(a), xs: List<a, A>) -> Maybe<a, A>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{h}

def List.tail(a, -A: Kind(a), xs: List<a, A>) -> List<a, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def List.last.go(a, -A: Kind(a), xs: List<a, A>, last: A) -> A:
  match xs:
    case Nil{}:
      last
    case h <> t:
      List.last.go(a, A, t, h)

def List.last(a, -A: Kind(a), xs: List<a, A>) -> Maybe<a, A>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{List.last.go(a, A, t, h)}

def List.get(a, -A: Kind(a), xs: List<a, A>, n: Nat) -> Maybe<a, A>:
  match xs n:
    case Nil{} _:
      None{}
    case h <> t 0n:
      Some{h}
    case h <> t 1n+p:
      List.get(a, A, t, p)

def List.set(a, -A: Kind(a), xs: List<a, A>, n: Nat, x: A) -> List<a, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      x <> t
    case h <> t 1n+p:
      h <> List.set(a, A, t, p, x)

def List.take(a, -A: Kind(a), xs: List<a, A>, n: Nat) -> List<a, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      Nil{}
    case h <> t 1n+p:
      h <> List.take(a, A, t, p)

def List.drop(a, -A: Kind(a), xs: List<a, A>, n: Nat) -> List<a, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      List.drop(a, A, t, p)

def List.zip(
  a, -A: Kind(a), b, -B: Kind(b), xs: List<a, A>, ys: List<b, B>
) -> List<&1, A & B>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case h <> t Nil{}:
      Nil{}
    case x <> xt y <> yt:
      (x, y) <> List.zip(a, A, b, B, xt, yt)

def List.range.go(+n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      List.range.go(p, p <> acc)

def List.range(n: Nat) -> List<&2, Nat>:
  List.range.go(n, Nil{})

def List.replicate(-A: Data, n: Nat, +x: A) -> List<&2, A>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      x <> List.replicate(A, p, x)

def List.filter.put(-A: Data, h: A, r: List<&2, A>, keep: Bool) -> List<&2, A>:
  match keep:
    case False{}:
      r
    case True{}:
      h <> r

def List.filter(~A: Data, ~f: A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      List.filter.put(A, h, List.filter(~A, ~f, t), f(h))

def List.foldl(
  ~a: Quant, ~A: Kind(a), ~B: Type, ~f: B -> A -> B, xs: List<a, A>, acc: B
) -> B:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      List.foldl(~a, ~A, ~B, ~f, t, f(acc, h))

def List.foldr(
  ~a: Quant, ~A: Kind(a), ~B: Type, ~f: A -> B -> B, xs: List<a, A>, z: B
) -> B:
  match xs:
    case Nil{}:
      z
    case h <> t:
      f(h, List.foldr(~a, ~A, ~B, ~f, t, z))

def List.any(~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(f(h), List.any(~a, ~A, ~f, t))

def List.all(~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(f(h), List.all(~a, ~A, ~f, t))

def List.find.put(-A: Data, h: A, r: Maybe<&2, A>, hit: Bool) -> Maybe<&2, A>:
  match hit:
    case False{}:
      r
    case True{}:
      Some{h}

def List.find(~A: Data, ~f: A -> Bool, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case +h <> t:
      List.find.put(A, h, List.find(~A, ~f, t), f(h))

def List.contains(
  ~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A
) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(eq(h, x), List.contains(~A, ~eq, t, x))

def List.merge.step(
  -A: Data, acc: List<&2, A>, x: A, xt: List<&2, A>, y: A, yt: List<&2, A>,
  le: Bool
) -> List<&2, A> & List<&2, A> & List<&2, A>:
  match le:
    case False{}:
      (y <> acc, x <> xt, yt)
    case True{}:
      (x <> acc, xt, y <> yt)

# The fuel bounds the steps: a sort passes its length, enough for any merge.
def List.merge.go(
  ~A: Data, ~le: A -> A -> Bool, fuel: Nat,
  st: List<&2, A> & List<&2, A> & List<&2, A>
) -> List<&2, A>:
  match fuel:
    case 0n:
      (acc, xs, ys) = st
      List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys))
    case 1n+f:
      (acc, xs, ys) = st
      match xs ys:
        case Nil{} Nil{}:
          List.reverse.go(&2, A, acc, Nil{})
        case Nil{} y <> yt:
          List.reverse.go(&2, A, acc, y <> yt)
        case x <> xt Nil{}:
          List.reverse.go(&2, A, acc, x <> xt)
        case +x <> xt +y <> yt:
          List.merge.go(~A, ~le, f,
            List.merge.step(A, acc, x, xt, y, yt, le(x, y)))

def List.sort.runs(-A: Data, xs: List<&2, A>) -> List<&2, List<&2, A>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      [h] <> List.sort.runs(A, t)

def List.sort.pass(
  ~A: Data, ~le: A -> A -> Bool, +n: Nat, runs: List<&2, List<&2, A>>
) -> List<&2, List<&2, A>>:
  match runs:
    case Nil{}:
      Nil{}
    case r <> Nil{}:
      [r]
    case r1 <> r2 <> rest:
      List.merge.go(~A, ~le, n, (Nil{}, r1, r2))
        <> List.sort.pass(~A, ~le, n, rest)

def List.sort.go(
  ~A: Data, ~le: A -> A -> Bool, fuel: Nat, +n: Nat, runs: List<&2, List<&2, A>>
) -> List<&2, A>:
  match fuel:
    case 0n:
      List.concat(&2, A, runs)
    case 1n+f:
      match runs:
        case Nil{}:
          Nil{}
        case r <> Nil{}:
          r
        case r1 <> r2 <> rest:
          List.sort.go(~A, ~le, f, n,
            List.sort.pass(~A, ~le, n, r1 <> r2 <> rest))

def List.sort(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> List<&2, A>:
  +n = List.length(&2, A, xs)
  List.sort.go(~A, ~le, n, n, List.sort.runs(A, xs))

def List.for_each(
  ~a: Quant, ~A: Kind(a), ~f: A -> IO(Unit), xs: List<a, A>
) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case h <> t:
      IO.bind(Unit, Unit, f(h), u => List.for_each(~a, ~A, ~f, t))

# Word
# ----

def Word.zero(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, Word.zero(p)}

def Word.not(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{Bool.not(b), Word.not(p, t)}

def Word.and(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.and(ab, bb), Word.and(p, at, bt)}

def Word.or(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.or(ab, bb), Word.or(p, at, bt)}

def Word.xor(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.xor(ab, bb), Word.xor(p, at, bt)}

def Word.shl.put(n: Nat, c: Bool, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{c, Word.shl.put(p, b, t)}

def Word.shl(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{False{}, Word.shl.put(p, b, t)}

def Word.shl.out.con(-p: Nat, c: Bool, r: Bool & Word(p)) -> Bool & Word(1n+p):
  (hi, t2) = r
  (hi, WCon{c, t2})

def Word.shl.out(n: Nat, c: Bool, w: Word(n)) -> Bool & Word(n):
  match n:
    case 0n:
      (c, WNil{})
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shl.out.con(p, c, Word.shl.out(p, b, t))

def Word.shr.pad(n: Nat, w: Word(n)) -> Word(1n+n):
  match n:
    case 0n:
      WCon{False{}, w}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.shr.pad(p, t)}

def Word.shr(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shr.pad(p, t)

def Word.cmp.fin(ab: Bool, bb: Bool, t: Cmp) -> Cmp:
  match t:
    case LT{}:
      LT{}
    case EQ{}:
      Bool.cmp(ab, bb)
    case GT{}:
      GT{}

def Word.cmp(n: Nat, a: Word(n), b: Word(n)) -> Cmp:
  match n:
    case 0n:
      EQ{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))

def Word.inc(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          WCon{True{}, t}
        case WCon{True{}, t}:
          WCon{False{}, Word.inc(p, t)}

law Word.adc:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for f: Bool
  for c: Bool
  Word(n)

def Word.adc.con(p: Nat, at: Word(p), bt: Word(p), f: Bool, sk: Bool & Bool) ->
  Word(1n+p):
  (s, k) = sk
  WCon{s, Word.adc(p, at, bt, f, k)}

def Word.adc(n, a, b, f, c):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b f:
        case WCon{ab, at} WCon{bb, bt} False{}:
          Word.adc.con(p, at, bt, False{}, Bool.full_add(ab, bb, c))
        case WCon{ab, at} WCon{bb, bt} True{}:
          Word.adc.con(p, at, bt, True{}, Bool.full_add(ab, Bool.not(bb), c))

def Word.add(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.adc(n, a, b, False{}, False{})

def Word.sub(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.adc(n, a, b, True{}, True{})

law Word.add_comm.arm:
  for p  : Nat
  for -h : Bool
  for at : Word(p)
  for bt : Word(p)
  for k  : Bool
  {WCon{h, Word.adc(p, at, bt, False{}, k)}
    == WCon{h, Word.adc(p, bt, at, False{}, k)} : Word.Con<p>}

law Word.add_comm.go:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {Word.adc(n, a, b, False{}, c) == Word.adc(n, b, a, False{}, c) : Word(n)}

def Word.add_comm.arm(p, h, at, bt, k):
  Equal.cong(Word(p), Word(1n+p), w => WCon{h, w},
    Word.adc(p, at, bt, False{}, k), Word.adc(p, bt, at, False{}, k),
    Word.add_comm.go(p, at, bt, k))

def Word.add_comm.go(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          Word.add_comm.arm(p, False{}, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          Word.add_comm.arm(p, True{}, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          Word.add_comm.arm(p, True{}, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          Word.add_comm.arm(p, False{}, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          Word.add_comm.arm(p, True{}, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          Word.add_comm.arm(p, False{}, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          Word.add_comm.arm(p, False{}, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          Word.add_comm.arm(p, True{}, at, bt, True{})

law Word.add_comm:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.add(n, a, b) == Word.add(n, b, a) : Word(n)}

def Word.add_comm(n, a, b):
  Word.add_comm.go(n, a, b, False{})

def Word.to_nat(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Nat.double(Word.to_nat(p, t))
        case WCon{True{}, t}:
          1n+Nat.double(Word.to_nat(p, t))

def Word.mul.go(+n: Nat, m: Nat, a: Word(m), +b: Word(n), acc: Word(n)) ->
  Word(n):
  match m:
    case 0n:
      acc
    case 1n+mp:
      match a:
        case WCon{False{}, at}:
          Word.mul.go(n, mp, at, Word.shl(n, b), acc)
        case WCon{True{}, at}:
          Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))

def Word.mul(+n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.mul.go(n, n, a, b, Word.zero(n))

# U32
# ---

def U32.inc(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.inc(32n, x)}

def U32.add(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.add(32n, x, y)}

law U32.add_comm:
  for a: U32
  for b: U32
  {U32.add(a, b) == U32.add(b, a) : U32}

def U32.add_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, y),
        Word.add(32n, y, x), Word.add_comm(32n, x, y))

def U32.sub(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.sub(32n, x, y)}

def U32.mul(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.mul(32n, x, y)}

def U32.not(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.not(32n, x)}

def U32.and(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.and(32n, x, y)}

def U32.or(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.or(32n, x, y)}

def U32.xor(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.xor(32n, x, y)}

def U32.shl(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.shl(32n, x)}

def U32.shr(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.shr(32n, x)}

def U32.shln(a: U32, n: Nat) -> U32:
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shl(U32.shln(a, p))

def U32.shrn(a: U32, n: Nat) -> U32:
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shr(U32.shrn(a, p))

def U32.cmp(a: U32, b: U32) -> Cmp:
  match a b:
    case U32{x} U32{y}:
      Word.cmp(32n, x, y)

def U32.is_eq(a: U32, b: U32) -> Bool:
  Cmp.is_eq(U32.cmp(a, b))

def U32.is_ne(a: U32, b: U32) -> Bool:
  Bool.not(Cmp.is_eq(U32.cmp(a, b)))

def U32.is_lt(a: U32, b: U32) -> Bool:
  Cmp.is_lt(U32.cmp(a, b))

def U32.is_le(a: U32, b: U32) -> Bool:
  Cmp.is_le(U32.cmp(a, b))

def U32.is_gt(a: U32, b: U32) -> Bool:
  Cmp.is_gt(U32.cmp(a, b))

def U32.is_ge(a: U32, b: U32) -> Bool:
  Cmp.is_ge(U32.cmp(a, b))

def U32.is_zero(a: U32) -> Bool:
  U32.is_eq(a, 0)

def U32.to_nat(a: U32) -> Nat:
  match a:
    case U32{w}:
      Word.to_nat(32n, w)

def U32.from_nat(n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n+p:
      U32.inc(U32.from_nat(p))

def U32.divmod.go.fin(-p: Nat, q: Word(p), s: U32, b: U32, g: Bool) ->
  Word(1n+p) & U32:
  match g:
    case True{}:
      (WCon{True{}, q}, U32.sub(s, b))
    case False{}:
      (WCon{False{}, q}, s)

def U32.divmod.go.shl(-p: Nat, q: Word(p), +b: U32, ts: Bool & Word(32n)) ->
  Word(1n+p) & U32:
  (t, s) = ts
  +s2 = {U32{s} : U32}
  U32.divmod.go.fin(p, q, s2, b, Bool.or(t, U32.is_ge(s2, b)))

def U32.divmod.go.rec(-p: Nat, a0: Bool, +b: U32, qr: Word(p) & U32) ->
  Word(1n+p) & U32:
  (q, r) = qr
  U32{rw} = r
  U32.divmod.go.shl(p, q, b, Word.shl.out(32n, a0, rw))

def U32.divmod.go(m: Nat, a: Word(m), +b: U32) -> Word(m) & U32:
  match m a:
    case 0n WNil{}:
      (WNil{}, 0)
    case 1n+p WCon{a0, hi}:
      U32.divmod.go.rec(p, a0, b, U32.divmod.go(p, hi, b))

def U32.div.fin(qr: Word(32n) & U32) -> U32:
  (q, r) = qr
  U32{q}

def U32.div.if(aw: Word(32n), b: U32, z: Bool) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      U32.div.fin(U32.divmod.go(32n, aw, b))

def U32.div(a: U32, +b: U32) -> U32:
  U32{aw} = a
  U32.div.if(aw, b, U32.is_zero(b))

def U32.mod.fin(qr: Word(32n) & U32) -> U32:
  (q, r) = qr
  r

def U32.mod.if(aw: Word(32n), b: U32, z: Bool) -> U32:
  match z:
    case True{}:
      U32{aw}
    case False{}:
      U32.mod.fin(U32.divmod.go(32n, aw, b))

def U32.mod(a: U32, +b: U32) -> U32:
  U32{aw} = a
  U32.mod.if(aw, b, U32.is_zero(b))

def U32.min(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), a, b)

def U32.max(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), b, a)

def U32.clamp(x: U32, lo: U32, hi: U32) -> U32:
  U32.min(U32.max(x, lo), hi)

def U32.pow(+a: U32, n: Nat) -> U32:
  match n:
    case 0n:
      1
    case 1n+p:
      U32.mul(a, U32.pow(a, p))

def U32.is_even(a: U32) -> Bool:
  U32.is_zero(U32.and(a, 1))

# F32
# ---

law U32.to_f32:
  for a: U32
  F32

law U32.to_f64:
  for a: U32
  F64

law F32.to_u32:
  for a: F32
  U32

law F32.add:
  for a: F32
  for b: F32
  F32

law F32.sub:
  for a: F32
  for b: F32
  F32

law F32.mul:
  for a: F32
  for b: F32
  F32

law F32.div:
  for a: F32
  for b: F32
  F32

law F32.mod:
  for a: F32
  for b: F32
  F32

law F32.pow:
  for a: F32
  for b: F32
  F32

law F32.atan2:
  for a: F32
  for b: F32
  F32

law F32.neg:
  for a: F32
  F32

law F32.abs:
  for a: F32
  F32

law F32.sqrt:
  for a: F32
  F32

law F32.exp:
  for a: F32
  F32

law F32.log:
  for a: F32
  F32

law F32.log2:
  for a: F32
  F32

law F32.log10:
  for a: F32
  F32

law F32.sin:
  for a: F32
  F32

law F32.cos:
  for a: F32
  F32

law F32.tan:
  for a: F32
  F32

law F32.asin:
  for a: F32
  F32

law F32.acos:
  for a: F32
  F32

law F32.atan:
  for a: F32
  F32

law F32.sinh:
  for a: F32
  F32

law F32.cosh:
  for a: F32
  F32

law F32.tanh:
  for a: F32
  F32

law F32.floor:
  for a: F32
  F32

law F32.ceil:
  for a: F32
  F32

law F32.trunc:
  for a: F32
  F32

law F32.is_eq:
  for a: F32
  for b: F32
  Bool

law F32.is_ne:
  for a: F32
  for b: F32
  Bool

law F32.is_lt:
  for a: F32
  for b: F32
  Bool

law F32.is_le:
  for a: F32
  for b: F32
  Bool

law F32.is_gt:
  for a: F32
  for b: F32
  Bool

law F32.is_ge:
  for a: F32
  for b: F32
  Bool

law F32.show:
  for +a: F32
  String

law F32.bits:
  for a: F32
  U32

law F32.read:
  for s: String
  Maybe<&2, F32>

def F32.min(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, F32.is_lt(a, b), a, b)

def F32.max(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, F32.is_lt(a, b), b, a)

def F32.clamp(x: F32, lo: F32, hi: F32) -> F32:
  F32.min(F32.max(x, lo), hi)

def F32.lerp(+a: F32, b: F32, t: F32) -> F32:
  F32.add(a, F32.mul(F32.sub(b, a), t))

def F32.square(+a: F32) -> F32:
  F32.mul(a, a)

def F32.hypot(+x: F32, +y: F32) -> F32:
  F32.sqrt(F32.add(F32.mul(x, x), F32.mul(y, y)))

def F32.round(a: F32) -> F32:
  F32.floor(F32.add(a, 0.5))

def F32.pi() -> F32:
  3.14159265

def F32.from_nat(n: Nat) -> F32:
  U32.to_f32(U32.from_nat(n))

def F32.to_nat(a: F32) -> Nat:
  U32.to_nat(F32.to_u32(a))

# F64
# ---

law F32.to_f64:
  for a: F32
  F64

law F64.to_f32:
  for a: F64
  F32

law F64.to_u32:
  for a: F64
  U32

law F64.add:
  for a: F64
  for b: F64
  F64

law F64.sub:
  for a: F64
  for b: F64
  F64

law F64.mul:
  for a: F64
  for b: F64
  F64

law F64.div:
  for a: F64
  for b: F64
  F64

law F64.mod:
  for a: F64
  for b: F64
  F64

law F64.pow:
  for a: F64
  for b: F64
  F64

law F64.atan2:
  for a: F64
  for b: F64
  F64

law F64.neg:
  for a: F64
  F64

law F64.abs:
  for a: F64
  F64

law F64.sqrt:
  for a: F64
  F64

law F64.exp:
  for a: F64
  F64

law F64.log:
  for a: F64
  F64

law F64.log2:
  for a: F64
  F64

law F64.log10:
  for a: F64
  F64

law F64.sin:
  for a: F64
  F64

law F64.cos:
  for a: F64
  F64

law F64.tan:
  for a: F64
  F64

law F64.asin:
  for a: F64
  F64

law F64.acos:
  for a: F64
  F64

law F64.atan:
  for a: F64
  F64

law F64.sinh:
  for a: F64
  F64

law F64.cosh:
  for a: F64
  F64

law F64.tanh:
  for a: F64
  F64

law F64.floor:
  for a: F64
  F64

law F64.ceil:
  for a: F64
  F64

law F64.trunc:
  for a: F64
  F64

law F64.is_eq:
  for a: F64
  for b: F64
  Bool

law F64.is_ne:
  for a: F64
  for b: F64
  Bool

law F64.is_lt:
  for a: F64
  for b: F64
  Bool

law F64.is_le:
  for a: F64
  for b: F64
  Bool

law F64.is_gt:
  for a: F64
  for b: F64
  Bool

law F64.is_ge:
  for a: F64
  for b: F64
  Bool

law F64.show:
  for +a: F64
  String

law F64.bits:
  for a: F64
  Nat

law F64.read:
  for s: String
  Maybe<&2, F64>

def F64.min(+a: F64, +b: F64) -> F64:
  Bool.pick(F64, F64.is_lt(a, b), a, b)

def F64.max(+a: F64, +b: F64) -> F64:
  Bool.pick(F64, F64.is_lt(a, b), b, a)

def F64.clamp(x: F64, lo: F64, hi: F64) -> F64:
  F64.min(F64.max(x, lo), hi)

def F64.lerp(+a: F64, b: F64, t: F64) -> F64:
  F64.add(a, F64.mul(F64.sub(b, a), t))

def F64.square(+a: F64) -> F64:
  F64.mul(a, a)

def F64.hypot(+x: F64, +y: F64) -> F64:
  F64.sqrt(F64.add(F64.mul(x, x), F64.mul(y, y)))

def F64.round(a: F64) -> F64:
  F64.floor(F64.add(a, 0.5d))

def F64.pi() -> F64:
  3.141592653589793d

def F64.from_nat(n: Nat) -> F64:
  U32.to_f64(U32.from_nat(n))

def F64.to_nat(a: F64) -> Nat:
  U32.to_nat(F64.to_u32(a))

# Char
# ----

def Char.cmp(a: Char, b: Char) -> (Char & Char) & Cmp:
  match a b:
    case Chr{+x} Chr{+y}:
      ((Chr{x}, Chr{y}), U32.cmp(x, y))

def Char.to_u32(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

def Char.from_u32(x: U32) -> Char:
  Chr{x}

def Char.is_eq(a: Char, b: Char) -> Bool:
  match a b:
    case Chr{x} Chr{y}:
      U32.is_eq(x, y)

def Char.is_digit(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

def Char.is_upper(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90))

def Char.is_lower(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122))

def Char.is_alpha(+c: Char) -> Bool:
  Bool.or(Char.is_upper(c), Char.is_lower(c))

def Char.is_space(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_eq(x, 32), Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13)))

def Char.is_line_break(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 10), U32.is_le(x, 13)),
        Bool.or(Bool.and(U32.is_ge(x, 28), U32.is_le(x, 30)),
        Bool.or(U32.is_eq(x, 133),
        Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)))))

def Char.case_if(c: Char, x: U32, hit: Bool) -> Char:
  match hit:
    case False{}:
      c
    case True{}:
      Chr{x}

def Char.to_upper(+c: Char) -> Char:
  Char.case_if(c, U32.sub(Char.to_u32(c), 32), Char.is_lower(c))

def Char.to_lower(+c: Char) -> Char:
  Char.case_if(c, U32.add(Char.to_u32(c), 32), Char.is_upper(c))

# String
# ------

def String.append(a: String, b: String) -> String:
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}

law String.order:
  for a: String
  for b: String
  Cmp

def String.order.step(a: String, b: String, c: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      String.order(a, b)
    case GT{}:
      GT{}

def String.order(a, b):
  match a b:
    case SNil{} SNil{}:
      EQ{}
    case SNil{} SCon{h, t}:
      LT{}
    case SCon{h, t} SNil{}:
      GT{}
    case SCon{Chr{x}, xt} SCon{Chr{y}, yt}:
      String.order.step(xt, yt, U32.cmp(x, y))

law String.cmp:
  for a: String
  for b: String
  (String & String) & Cmp

def String.cmp(a, b):
  +x = a
  +y = b
  ((x, y), String.order(x, y))

def String.eq(a: String, b: String) -> Bool:
  Cmp.is_eq(String.order(a, b))

def String.length.go(s: String, n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{h, t}:
      String.length.go(t, 1n+n)

def String.length(s: String) -> Nat:
  String.length.go(s, 0n)

def String.is_empty(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      False{}

def String.reverse.go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      String.reverse.go(t, SCon{h, acc})

def String.reverse(s: String) -> String:
  String.reverse.go(s, SNil{})

def String.is_lt(a: String, b: String) -> Bool:
  Cmp.is_lt(String.order(a, b))

def String.is_le(a: String, b: String) -> Bool:
  Cmp.is_le(String.order(a, b))

def String.is_gt(a: String, b: String) -> Bool:
  Cmp.is_gt(String.order(a, b))

def String.is_ge(a: String, b: String) -> Bool:
  Cmp.is_ge(String.order(a, b))

law String.starts_with:
  for s: String
  for p: String
  Bool

def String.starts_with.if(t: String, pt: String, same: Bool) -> Bool:
  match same:
    case False{}:
      False{}
    case True{}:
      String.starts_with(t, pt)

def String.starts_with(s, p):
  match s p:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{h, t}:
      False{}
    case SCon{h, t} SNil{}:
      True{}
    case SCon{x, xt} SCon{y, yt}:
      String.starts_with.if(xt, yt, Char.is_eq(x, y))

law String.contains:
  for +s: String
  for +p: String
  Bool

def String.contains.if(t: String, p: String, here: Bool) -> Bool:
  match here:
    case False{}:
      String.contains(t, p)
    case True{}:
      True{}

def String.contains(s, p):
  match s:
    case SNil{}:
      String.is_empty(p)
    case SCon{h, t}:
      String.contains.if(t, p, String.starts_with(SCon{h, t}, p))

def String.take(s: String, n: Nat) -> String:
  match s n:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SNil{}
    case SCon{h, t} 1n+p:
      SCon{h, String.take(t, p)}

def String.drop(s: String, n: Nat) -> String:
  match s n:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SCon{h, t}
    case SCon{h, t} 1n+p:
      String.drop(t, p)

def String.ends_with(+s: String, +p: String) -> Bool:
  String.eq(String.drop(s, Nat.sub(String.length(s), String.length(p))), p)

def String.get(s: String, n: Nat) -> Maybe<&2, Char>:
  match s n:
    case SNil{} _:
      None{}
    case SCon{h, t} 0n:
      Some{h}
    case SCon{h, t} 1n+p:
      String.get(t, p)

def String.to_list(s: String) -> List<&2, Char>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{h, t}:
      h <> String.to_list(t)

def String.from_list(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case h <> t:
      SCon{h, String.from_list(t)}

def String.concat(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case h <> t:
      String.append(h, String.concat(t))

def String.join.go(xs: List<&2, String>, h: String, +sep: String) -> String:
  match xs:
    case Nil{}:
      h
    case h2 <> t:
      String.append(h, String.append(sep, String.join.go(t, h2, sep)))

def String.join(xs: List<&2, String>, +sep: String) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case h <> t:
      String.join.go(t, h, sep)

def String.split.push(c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case h <> t:
      SCon{c, h} <> t

def String.split.fin(c: Char, r: List<&2, String>, cut: Bool) ->
  List<&2, String>:
  match cut:
    case False{}:
      String.split.push(c, r)
    case True{}:
      SNil{} <> r

# Accumulators keep the reference split stack bounded on large input.
# The current field and completed fields are reversed independently.
law String.split.acc:
  for s: String
  for +sep: Char
  for +space: Bool
  for word: String
  for words: List<&2, String>
  List<&2, String>

def String.split.test(c: Char, sep: Char, space: Bool) -> Bool:
  match space:
    case False{}:
      Char.is_eq(c, sep)
    case True{}:
      Char.is_space(c)

def String.split.step(t: String, sep: Char, space: Bool, h: Char,
  word: String, words: List<&2, String>, cut: Bool) -> List<&2, String>:
  match cut:
    case False{}:
      String.split.acc(t, sep, space, SCon{h, word}, words)
    case True{}:
      String.split.acc(t, sep, space, "", String.reverse(word) <> words)

def String.split.acc(s, sep, space, word, words):
  match s:
    case SNil{}:
      List.reverse(&2, String, String.reverse(word) <> words)
    case SCon{+h, t}:
      String.split.step(t, sep, space, h, word, words,
        String.split.test(h, sep, space))

def String.split(s: String, +sep: Char) -> List<&2, String>:
  String.split.acc(s, sep, False{}, "", [])

def String.lines(s: String) -> List<&2, String>:
  String.split(s, '\n')

def String.repeat.go(n: Nat, +s: String) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      String.append(s, String.repeat.go(p, s))

def String.repeat(+s: String, n: Nat) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      String.repeat.go(n, SCon{h, t})

def String.to_upper(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{Char.to_upper(h), String.to_upper(t)}

def String.to_lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{Char.to_lower(h), String.to_lower(t)}

law String.trim_start:
  for s: String
  String

def String.trim_start.if(h: Char, t: String, space: Bool) -> String:
  match space:
    case False{}:
      SCon{h, t}
    case True{}:
      String.trim_start(t)

def String.trim_start(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      String.trim_start.if(h, t, Char.is_space(h))

def String.trim_end(s: String) -> String:
  String.reverse(String.trim_start(String.reverse(s)))

def String.trim(s: String) -> String:
  String.trim_end(String.trim_start(s))

def String.take_end(+s: String, k: Nat) -> String:
  String.drop(s, Nat.sub(String.length(s), k))

def String.drop_end(+s: String, k: Nat) -> String:
  String.take(s, Nat.sub(String.length(s), k))

def String.get_end.if(s: String, i: Nat, ok: Bool) -> Maybe<&2, Char>:
  match ok:
    case False{}:
      None{}
    case True{}:
      String.get(s, i)

# s[-k]: k = 0 or k > length is None
def String.get_end(+s: String, +k: Nat) -> Maybe<&2, Char>:
  +n = String.length(s)
  String.get_end.if(s, Nat.sub(n, k), Bool.and(Nat.is_ge(k, 1n), Nat.is_le(k, n)))

def String.slice(s: String, +i: Nat, j: Nat) -> String:
  String.take(String.drop(s, i), Nat.sub(j, i))

def String.cut(+s: String, +n: Nat) -> String & String:
  (String.take(s, n), String.drop(s, n))

def String.clone(+s: String) -> String & String:
  (s, s)

def String.copy(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{h, String.copy(t)}

law String.find.go:
  for +s: String
  for +p: String
  for i: Nat
  Maybe<&2, Nat>

def String.find.if(t: String, p: String, i: Nat, here: Bool) -> Maybe<&2, Nat>:
  match here:
    case False{}:
      String.find.go(t, p, 1n+i)
    case True{}:
      Some{i}

def String.find.go(s, p, i):
  match s:
    case SNil{}:
      Bool.pick(Maybe<&2, Nat>, String.is_empty(p), Some{i}, None{})
    case SCon{h, t}:
      String.find.if(t, p, i, String.starts_with(SCon{h, t}, p))

# first match start; the empty needle matches at 0
def String.find(s: String, p: String) -> Maybe<&2, Nat>:
  String.find.go(s, p, 0n)

law String.find_last.go:
  for +s: String
  for +p: String
  for i: Nat
  for best: Maybe<&2, Nat>
  Maybe<&2, Nat>

def String.find_last.if(
  t: String, p: String, +i: Nat, best: Maybe<&2, Nat>, here: Bool
) -> Maybe<&2, Nat>:
  match here:
    case False{}:
      String.find_last.go(t, p, 1n+i, best)
    case True{}:
      String.find_last.go(t, p, 1n+i, Some{i})

def String.find_last.go(s, p, i, best):
  match s:
    case SNil{}:
      Bool.pick(Maybe<&2, Nat>, String.is_empty(p), Some{i}, best)
    case SCon{h, t}:
      String.find_last.if(t, p, i, best, String.starts_with(SCon{h, t}, p))

# last match start (overlapping starts count); the empty needle matches at length
def String.find_last(s: String, p: String) -> Maybe<&2, Nat>:
  String.find_last.go(s, p, 0n, None{})

law String.count.go:
  for +s: String
  for +p: String
  for +n: Nat
  Nat

def String.count.if(t: String, +p: String, n: Nat, here: Bool) -> Nat:
  match here:
    case False{}:
      String.count.go(t, p, n)
    case True{}:
      String.count.go(String.drop(t, Nat.sub(String.length(p), 1n)), p, 1n+n)

def String.count.go(s, p, n):
  match s:
    case SNil{}:
      Bool.pick(Nat, String.is_empty(p), 1n+n, n)
    case SCon{h, t}:
      String.count.if(t, p, n, String.starts_with(SCon{h, t}, p))

# nonoverlapping matches; the empty needle counts length+1
def String.count(s: String, p: String) -> Nat:
  String.count.go(s, p, 0n)

law String.replace:
  for +s: String
  for +old: String
  for +new: String
  String

def String.replace.if(
  +h: Char, +t: String, +old: String, +new: String, here: Bool
) -> String:
  match here:
    case False{}:
      SCon{h, String.replace(t, old, new)}
    case True{}:
      +m = String.length(old)
      String.append(new, String.append(String.take(SCon{h, t}, Nat.sub(1n, m)),
        String.replace(String.drop(SCon{h, t}, Nat.max(m, 1n)), old, new)))

# nonoverlapping, left to right; empty old inserts new at every boundary
def String.replace(s, old, new):
  match s:
    case SNil{}:
      Bool.pick(String, String.is_empty(old), new, SNil{})
    case SCon{h, t}:
      String.replace.if(h, t, old, new, String.starts_with(SCon{h, t}, old))

law String.split_on.go:
  for +s: String
  for +sep: String
  List<&2, String>

def String.split_on.if(h: Char, t: String, +sep: String, here: Bool) ->
  List<&2, String>:
  match here:
    case False{}:
      String.split.push(h, String.split_on.go(t, sep))
    case True{}:
      SNil{} <> String.split_on.go(
        String.drop(t, Nat.sub(String.length(sep), 1n)), sep)

def String.split_on.go(s, sep):
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{h, t}:
      String.split_on.if(h, t, sep, String.starts_with(SCon{h, t}, sep))

def String.split_on.start(s: String, sep: String, empty: Bool) ->
  List<&2, String>:
  match empty:
    case False{}:
      String.split_on.go(s, sep)
    case True{}:
      [s]

# substring separator, empties kept; unlike Python the empty separator is
# total: it never matches, so the result is [s]
def String.split_on(s: String, +sep: String) -> List<&2, String>:
  String.split_on.start(s, sep, String.is_empty(sep))

def String.words.cut(s: String) -> List<&2, String>:
  String.split.acc(s, ' ', True{}, "", [])

def String.words.keep(w: String) -> Bool:
  Bool.not(String.is_empty(w))

# runs between ASCII whitespace (U+0020, U+0009..U+000D); no empties
def String.words(s: String) -> List<&2, String>:
  List.filter(~String, ~String.words.keep, String.words.cut(s))

def String.partition.at(+s: String, +sep: String, i: Maybe<&2, Nat>) ->
  String & (String & String):
  match i:
    case None{}:
      (s, (SNil{}, SNil{}))
    case Some{+k}:
      (String.take(s, k), (sep, String.drop(s, Nat.add(k, String.length(sep)))))

def String.partition.find(s: String, sep: String, empty: Bool) ->
  Maybe<&2, Nat>:
  match empty:
    case False{}:
      String.find(s, sep)
    case True{}:
      None{}

# (before, sep, after) at the first match; absent, or the empty separator
# (which Python rejects), gives (s, "", "")
def String.partition(+s: String, +sep: String) -> String & (String & String):
  String.partition.at(s, sep, String.partition.find(s, sep, String.is_empty(sep)))

law String.splitlines:
  for s: String
  List<&2, String>

def String.splitlines.lf(t: String) -> String:
  match t:
    case SNil{}:
      SNil{}
    case SCon{+h, +t2}:
      Bool.pick(String, Char.is_eq(h, '\n'), t2, SCon{h, t2})

def String.splitlines.cr(t: String, cr: Bool) -> String:
  match cr:
    case False{}:
      t
    case True{}:
      String.splitlines.lf(t)

def String.splitlines.if(h: Char, t: String, brk: Bool) -> List<&2, String>:
  match brk:
    case False{}:
      String.split.push(h, String.splitlines(t))
    case True{}:
      SNil{} <> String.splitlines(String.splitlines.cr(t, Char.is_eq(h, '\r')))

# Python's boundaries (LF CR CRLF VT FF FS GS RS NEL LS PS); no trailing empty
def String.splitlines(s):
  match s:
    case SNil{}:
      Nil{}
    case SCon{+h, t}:
      String.splitlines.if(h, t, Char.is_line_break(h))

def String.capitalize(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{Char.to_upper(h), String.to_lower(t)}

# width counts code points, not columns
def String.pad_start(+s: String, w: Nat, c: Char) -> String:
  String.append(
    String.from_list(List.replicate(Char, Nat.sub(w, String.length(s)), c)), s)

def String.pad_end(+s: String, w: Nat, c: Char) -> String:
  String.append(
    s, String.from_list(List.replicate(Char, Nat.sub(w, String.length(s)), c)))

def String.zfill.if(h: Char, t: String, w: Nat, sign: Bool) -> String:
  match sign:
    case False{}:
      String.pad_start(SCon{h, t}, w, '0')
    case True{}:
      SCon{h, String.pad_start(t, Nat.sub(w, 1n), '0')}

# zeros after a leading '+' or '-'
def String.zfill(s: String, w: Nat) -> String:
  match s:
    case SNil{}:
      String.pad_start(SNil{}, w, '0')
    case SCon{+h, t}:
      String.zfill.if(h, t, w, Bool.or(Char.is_eq(h, '+'), Char.is_eq(h, '-')))

def String.hash.byte(h: U32, b: U32) -> U32:
  U32.mul(U32.xor(h, b), 16777619)

def String.hash.cell(h: U32, +x: U32) -> U32:
  String.hash.byte(String.hash.byte(String.hash.byte(String.hash.byte(h,
    U32.and(x, 255)), U32.and(U32.shrn(x, 8n), 255)),
    U32.and(U32.shrn(x, 16n), 255)), U32.shrn(x, 24n))

def String.hash.go(s: String, h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{x}, t}:
      String.hash.go(t, String.hash.cell(h, x))

# FNV-1a (32-bit) over four little-endian bytes per code point; a stable
# Bend spec, not Python's hash
def String.hash(s: String) -> U32:
  String.hash.go(s, 2166136261)

# Regex
# -----

# CPython 3.11 `re.ASCII` is the pin: leftmost-first alternation, greedy and
# lazy repeats, a capture keeps its last value, `$` also matches before a
# final newline, `.` skips only newline. Offsets are code-point indices.
# An unbounded repeat of a nullable body is rejected at parse (NullableRepeat).
# Errors carry `pos`: the code-point offset where the parser gave up.

def Regex.max_rep() -> Nat:
  256n

def Regex.max_prog() -> Nat:
  4096n

def Regex.Range() -> Data:
  Sigma<&2, &2, U32, _ => U32>

def Regex.Ranges() -> Data:
  List<&2, Regex.Range()>

def Regex.Span() -> Data:
  Sigma<&2, &2, Nat, _ => Nat>

def Regex.digits() -> Regex.Ranges():
  [(48, 57)]

def Regex.words() -> Regex.Ranges():
  [(48, 57), (65, 90), (95, 95), (97, 122)]

def Regex.spaces() -> Regex.Ranges():
  [(9, 13), (32, 32)]

# Complement of an ascending, disjoint range list over the code points
def Regex.ranges.not(rs: Regex.Ranges(), lo: U32) -> Regex.Ranges():
  match rs:
    case Nil{}:
      [(lo, 1114111)]
    case (a, b) <> rest:
      (lo, U32.sub(a, 1)) <> Regex.ranges.not(rest, U32.add(b, 1))

def Regex.nullable(r: Re) -> Bool:
  match r:
    case RLit{c}:
      False{}
    case RAny{}:
      False{}
    case RSet{neg, rs}:
      False{}
    case RCat{a, b}:
      Bool.and(Regex.nullable(a), Regex.nullable(b))
    case RAlt{a, b}:
      Bool.or(Regex.nullable(a), Regex.nullable(b))
    case RRep{r, lo, hi, g}:
      Bool.or(Nat.is_eq(lo, 0n), Regex.nullable(r))
    case RCap{n, r}:
      Regex.nullable(r)
    case _:
      True{}

# Anchors take no quantifier
def Regex.parse.q(r: Re) -> Nat:
  match r:
    case RBol{}:
      0n
    case REol{}:
      0n
    case RWordB{neg}:
      0n
    case _:
      1n

# The parser is a stack machine over the pattern: every step reads one
# char, so the fuel is the pattern length. State = unread tail, groups
# opened so far, open frames (the root frame at the bottom). An error
# carries the unread length; `Regex.parse.run` turns it into an offset
def Regex.parse.Stack() -> Data:
  List<&2, Regex.Frame>

def Regex.parse.State() -> Data:
  Result<&2, &2, Regex.Error, Sigma<&2, &2, String, _ => Sigma<&2, &2, Nat, _ => Regex.parse.Stack()>>>

def Regex.parse.Item() -> Data:
  Result<&2, &2, Regex.Error, Sigma<&2, &2, Re, _ => String>>

def Regex.parse.Tree() -> Data:
  Result<&2, &2, Regex.Error, Sigma<&2, &2, Re, _ => Nat>>

def Regex.parse.Scan() -> Data:
  Result<&2, &2, Regex.Error, Regex.Cls>

def Regex.parse.Num() -> Data:
  Sigma<&2, &2, Nat, _ => Sigma<&2, &2, Nat, _ => String>>

def Regex.parse.Code() -> Data:
  Result<&2, &2, Regex.Error, Sigma<&2, &2, U32, _ => String>>

# Index of x in ks, from i; 0 when absent
def Regex.parse.index(+x: U32, ks: List<&2, U32>, +i: Nat) -> Nat:
  match ks:
    case Nil{}:
      0n
    case k <> rest:
      Bool.pick(Nat, U32.is_eq(x, k), i, Regex.parse.index(x, rest, 1n+i))

# Newest-first items fold into source order: [c, b, a] -> RCat{a, RCat{b, c}}
def Regex.parse.rcat(acc: Re, x: Re) -> Re:
  RCat{x, acc}

def Regex.parse.ralt(acc: Re, x: Re) -> Re:
  RAlt{x, acc}

def Regex.parse.cat(rs: List<&2, Re>) -> Re:
  match rs:
    case Nil{}:
      REmpty{}
    case x <> rest:
      List.foldl(~&2, ~Re, ~Re, ~Regex.parse.rcat, rest, x)

def Regex.parse.wrap(cap: Maybe<&2, Nat>, r: Re) -> Re:
  match cap:
    case None{}:
      r
    case Some{k}:
      RCap{k, r}

def Regex.parse.fin(fr: Regex.Frame) -> Re:
  match fr:
    case Frame{cap, alts, cat, q}:
      Regex.parse.wrap(cap, List.foldl(~&2, ~Re, ~Re, ~Regex.parse.ralt, alts, Regex.parse.cat(cat)))

def Regex.parse.push(t: String, n: Nat, stack: Regex.parse.Stack(), +r: Re) -> Regex.parse.State():
  match stack:
    case Frame{cap, alts, cat, q} <> rest:
      Done{(t, (n, Frame{cap, alts, r <> cat, Regex.parse.q(r)} <> rest))}
    case Nil{}:
      Fail{RErr{String.length(t), "unbalanced parenthesis"}}

def Regex.parse.atom(n: Nat, stack: Regex.parse.Stack(), r: Regex.parse.Item()) -> Regex.parse.State():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(re, t)}:
      Regex.parse.push(t, n, stack, re)

def Regex.parse.open.cap(t: String, +n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.State():
  Done{(t, (1n+n, Frame{Some{1n+n}, [], [], 0n} <> stack))}

# `(?:` opens a plain group; any other `(?` extension is out of scope
def Regex.parse.open.ext(+k: Nat, t: String, n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.State():
  match t:
    case SCon{Chr{+x}, t2}:
      Bool.pick(Regex.parse.State(), U32.is_eq(x, 58),
        Done{(t2, (n, Frame{None{}, [], [], 0n} <> stack))},
        Fail{RErr{k, "unsupported group extension"}})
    case SNil{}:
      Fail{RErr{k, "unsupported group extension"}}

def Regex.parse.open(t: String, +n: Nat, +stack: Regex.parse.Stack()) -> Regex.parse.State():
  match t:
    case SCon{Chr{+x}, +t2}:
      Bool.pick(Regex.parse.State(), U32.is_eq(x, 63),
        Regex.parse.open.ext(Nat.add(2n, String.length(t2)), t2, n, stack),
        Regex.parse.open.cap(SCon{Chr{x}, t2}, n, stack))
    case SNil{}:
      Regex.parse.open.cap(SNil{}, n, stack)

def Regex.parse.close(+t: String, n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.State():
  match stack:
    case fr <> Nil{}:
      Fail{RErr{1n+String.length(t), "unbalanced parenthesis"}}
    case fr <> rest:
      Regex.parse.push(t, n, rest, Regex.parse.fin(fr))
    case Nil{}:
      Fail{RErr{1n+String.length(t), "unbalanced parenthesis"}}

def Regex.parse.bar(t: String, n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.State():
  match stack:
    case Frame{cap, alts, cat, q} <> rest:
      Done{(t, (n, Frame{cap, Regex.parse.cat(cat) <> alts, [], 0n} <> rest))}
    case Nil{}:
      Fail{RErr{String.length(t), "unbalanced parenthesis"}}

def Regex.parse.rep.if(k: Nat, st: Regex.parse.State(), bad: Bool) -> Regex.parse.State():
  match bad:
    case True{}:
      Fail{RErr{k, "NullableRepeat"}}
    case False{}:
      st

# Repeat the last atom; an unbounded repeat needs a body that eats
def Regex.parse.rep(+t: String, n: Nat, stack: Regex.parse.Stack(), lo: Nat, +hi: Maybe<&2, Nat>) -> Regex.parse.State():
  match stack:
    case Frame{cap, alts, +r <> cat, 1n} <> rest:
      Regex.parse.rep.if(1n+String.length(t),
        Done{(t, (n, Frame{cap, alts, RRep{r, lo, hi, True{}} <> cat, 2n} <> rest))},
        Bool.and(Bool.not(Maybe.is_some(&2, Nat, hi)), Regex.nullable(r)))
    case Frame{cap, alts, cat, 2n} <> rest:
      Fail{RErr{1n+String.length(t), "multiple repeat"}}
    case _:
      Fail{RErr{1n+String.length(t), "nothing to repeat"}}

# `?` after a fresh repeat makes it lazy, else it is the {0,1} repeat
def Regex.parse.opt(t: String, n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.State():
  match stack:
    case Frame{cap, alts, RRep{r, lo, hi, g} <> cat, 2n} <> rest:
      Done{(t, (n, Frame{cap, alts, RRep{r, lo, hi, False{}} <> cat, 0n} <> rest))}
    case other:
      Regex.parse.rep(t, n, other, 0n, Some{1n})

def Regex.parse.Bounds() -> Data:
  Result<&2, &2, Regex.Error, Sigma<&2, &2, Sigma<&2, &2, Nat, _ => Maybe<&2, Nat>>, _ => String>>

# Decimal digits, capped at 1000 so a silly count costs nothing
def Regex.parse.num(t: String, +acc: Nat, +cnt: Nat) -> Regex.parse.Num():
  match t:
    case SNil{}:
      (acc, (cnt, SNil{}))
    case SCon{Chr{+x}, +t2}:
      Bool.pick(Regex.parse.Num(), Char.is_digit(Chr{x}),
        Regex.parse.num(t2, Nat.min(1000n, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(x, 48)))), 1n+cnt),
        (acc, (cnt, SCon{Chr{x}, t2})))

def Regex.parse.bounds.ok(+k: Nat, +lo: Nat, +hi: Maybe<&2, Nat>, t: String) -> Regex.parse.Bounds():
  Bool.pick(Regex.parse.Bounds(), Nat.is_gt(Nat.max(lo, Maybe.default(&2, Nat, hi, 0n)), Regex.max_rep()),
    Fail{RErr{k, "repeat count exceeds max_rep"}},
    Bool.pick(Regex.parse.Bounds(), Nat.is_gt(lo, Maybe.default(&2, Nat, hi, lo)),
      Fail{RErr{k, "min repeat greater than max repeat"}},
      Done{((lo, hi), t)}))

def Regex.parse.bounds.hi(+k: Nat, lo: Nat, r: Regex.parse.Num()) -> Regex.parse.Bounds():
  match r:
    case (hi, (cnt, SCon{Chr{+y}, t2})):
      Bool.pick(Regex.parse.Bounds(), U32.is_eq(y, 125),
        Regex.parse.bounds.ok(k, lo, Bool.pick(Maybe<&2, Nat>, Nat.is_eq(cnt, 0n), None{}, Some{hi}), t2),
        Fail{RErr{k, "bad repeat"}})
    case (hi, (cnt, SNil{})):
      Fail{RErr{k, "bad repeat"}}

def Regex.parse.bounds.lo(+k: Nat, r: Regex.parse.Num()) -> Regex.parse.Bounds():
  match r:
    case (lo, (0n, rest)):
      Fail{RErr{k, "bad repeat"}}
    case (+lo, (cnt, SCon{Chr{+y}, +t2})):
      Bool.pick(Regex.parse.Bounds(), U32.is_eq(y, 125),
        Regex.parse.bounds.ok(k, lo, Some{lo}, t2),
        Bool.pick(Regex.parse.Bounds(), U32.is_eq(y, 44),
          Regex.parse.bounds.hi(k, lo, Regex.parse.num(t2, 0n, 0n)),
          Fail{RErr{k, "bad repeat"}}))
    case (lo, (cnt, SNil{})):
      Fail{RErr{k, "bad repeat"}}

# `{m}` `{m,}` `{m,n}`; anything else (so `{,n}`) is a bad repeat
def Regex.parse.bounds(+t: String) -> Regex.parse.Bounds():
  Regex.parse.bounds.lo(1n+String.length(t), Regex.parse.num(t, 0n, 0n))

def Regex.parse.braces(n: Nat, stack: Regex.parse.Stack(), b: Regex.parse.Bounds()) -> Regex.parse.State():
  match b:
    case Fail{e}:
      Fail{e}
    case Done{((lo, hi), t)}:
      Regex.parse.rep(t, n, stack, lo, hi)

def Regex.parse.hexval(+x: U32) -> U32:
  Bool.pick(U32, Char.is_digit(Chr{x}), U32.sub(x, 48),
    Bool.pick(U32, Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)), U32.sub(x, 87),
      Bool.pick(U32, Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)), U32.sub(x, 55), 16)))

def Regex.parse.hex.if(k: Nat, v: U32, r: Regex.parse.Code()) -> Regex.parse.Code():
  Bool.pick(Regex.parse.Code(), U32.is_lt(v, 16), r, Fail{RErr{k, "bad escape"}})

# Exactly d hex digits
def Regex.parse.hex(+k: Nat, d: Nat, t: String, acc: U32) -> Regex.parse.Code():
  match d:
    case 0n:
      Done{(acc, t)}
    case 1n+e:
      match t:
        case SNil{}:
          Fail{RErr{k, "bad escape"}}
        case SCon{Chr{+x}, t2}:
          Regex.parse.hex.if(k, Regex.parse.hexval(x),
            Regex.parse.hex(k, e, t2, U32.add(U32.mul(acc, 16), Regex.parse.hexval(x))))

# A code point escape must be a scalar value
def Regex.parse.esc.code(k: Nat, r: Regex.parse.Code()) -> Regex.parse.Item():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+c, t)}:
      Bool.pick(Regex.parse.Item(),
        Bool.or(U32.is_gt(c, 1114111), Bool.and(U32.is_ge(c, 55296), U32.is_le(c, 57343))),
        Fail{RErr{k, "bad escape"}}, Done{(RLit{Chr{c}}, t)})

def Regex.parse.esc.table() -> List<&2, Sigma<&2, &2, U32, _ => Re>>:
  [(110, RLit{Chr{10}}), (114, RLit{Chr{13}}), (116, RLit{Chr{9}}), (102, RLit{Chr{12}}),
   (118, RLit{Chr{11}}), (48, RLit{Chr{0}}), (98, RWordB{False{}}), (66, RWordB{True{}}),
   (100, RSet{False{}, Regex.digits()}), (68, RSet{True{}, Regex.digits()}),
   (119, RSet{False{}, Regex.words()}), (87, RSet{True{}, Regex.words()}),
   (115, RSet{False{}, Regex.spaces()}), (83, RSet{True{}, Regex.spaces()})]

def Regex.parse.esc.find(+x: U32, tbl: List<&2, Sigma<&2, &2, U32, _ => Re>>) -> Maybe<&2, Re>:
  match tbl:
    case Nil{}:
      None{}
    case (c, r) <> rest:
      Bool.pick(Maybe<&2, Re>, U32.is_eq(x, c), Some{r}, Regex.parse.esc.find(x, rest))

# Off the table: \x \u \U take hex digits; a digit is a backreference, a
# letter is unknown, anything else is the char itself
def Regex.parse.esc.go(+k: Nat, hex: Nat, +x: U32, t: String, found: Maybe<&2, Re>) -> Regex.parse.Item():
  match hex found:
    case _ Some{r}:
      Done{(r, t)}
    case 0n None{}:
      Bool.pick(Regex.parse.Item(), Char.is_digit(Chr{x}), Fail{RErr{k, "backreferences are not supported"}},
        Bool.pick(Regex.parse.Item(), Char.is_alpha(Chr{x}), Fail{RErr{k, "bad escape"}},
          Done{(RLit{Chr{x}}, t)}))
    case 1n None{}:
      Regex.parse.esc.code(k, Regex.parse.hex(k, 2n, t, 0))
    case 2n None{}:
      Regex.parse.esc.code(k, Regex.parse.hex(k, 4n, t, 0))
    case 3n+_ None{}:
      Regex.parse.esc.code(k, Regex.parse.hex(k, 8n, t, 0))

# The tail after a backslash
def Regex.parse.esc(t: String) -> Regex.parse.Item():
  match t:
    case SNil{}:
      Fail{RErr{1n, "bad escape"}}
    case SCon{Chr{+x}, +t2}:
      Regex.parse.esc.go(Nat.add(2n, String.length(t2)), Regex.parse.index(x, [120, 117, 85], 1n), x, t2,
        Regex.parse.esc.find(x, Regex.parse.esc.table()))

def Regex.parse.cls.flush(pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges()) -> Regex.Ranges():
  match pend dash:
    case Some{+p} True{}:
      (45, 45) <> ((p, p) <> rs)
    case Some{+p} False{}:
      (p, p) <> rs
    case None{} _:
      rs

def Regex.parse.cls.range(+t: String, rs: Regex.Ranges(), +lo: U32, +c: U32) -> Regex.parse.Scan():
  Bool.pick(Regex.parse.Scan(), U32.is_le(lo, c),
    Done{CScan{t, None{}, False{}, (lo, c) <> rs}},
    Fail{RErr{String.length(t), "bad character range"}})

# One char joins the class: closes a pending range, or waits as the next low
def Regex.parse.cls.item(t: String, pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges(), +c: U32) -> Regex.parse.Scan():
  match pend dash:
    case Some{lo} True{}:
      Regex.parse.cls.range(t, rs, lo, c)
    case Some{+p} False{}:
      Done{CScan{t, Some{c}, False{}, (p, p) <> rs}}
    case None{} _:
      Done{CScan{t, Some{c}, False{}, rs}}

def Regex.parse.cls.union(+t: String, pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges(), rs2: Regex.Ranges()) -> Regex.parse.Scan():
  match dash:
    case True{}:
      Fail{RErr{String.length(t), "bad character range"}}
    case False{}:
      Done{CScan{t, None{}, False{}, List.append(&2, Regex.Range(), rs2, Regex.parse.cls.flush(pend, False{}, rs))}}

# An escape inside a class: a char, a set (`\D` as its complement), `\b` is backspace
def Regex.parse.cls.add(pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges(), r: Regex.parse.Item()) -> Regex.parse.Scan():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(RLit{Chr{c}}, t)}:
      Regex.parse.cls.item(t, pend, dash, rs, c)
    case Done{(RSet{False{}, rs2}, t)}:
      Regex.parse.cls.union(t, pend, dash, rs, rs2)
    case Done{(RSet{True{}, rs2}, t)}:
      Regex.parse.cls.union(t, pend, dash, rs, Regex.ranges.not(rs2, 0))
    case Done{(RWordB{False{}}, t)}:
      Regex.parse.cls.item(t, pend, dash, rs, 8)
    case Done{(re, +t)}:
      Fail{RErr{String.length(t), "bad escape"}}

def Regex.parse.cls.dash(t: String, pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges()) -> Regex.parse.Scan():
  match pend dash:
    case Some{lo} True{}:
      Regex.parse.cls.range(t, rs, lo, 45)
    case Some{p} False{}:
      Done{CScan{t, Some{p}, True{}, rs}}
    case None{} _:
      Done{CScan{t, Some{45}, False{}, rs}}

def Regex.parse.cls.char(kind: Nat, +x: U32, t: String, pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges()) -> Regex.parse.Scan():
  match kind:
    case 0n:
      Regex.parse.cls.item(t, pend, dash, rs, x)
    case 1n:
      Done{CDone{Regex.parse.cls.flush(pend, dash, rs), t}}
    case 2n:
      Regex.parse.cls.add(pend, dash, rs, Regex.parse.esc(t))
    case 3n+_:
      Regex.parse.cls.dash(t, pend, dash, rs)

def Regex.parse.cls.step(s: String, pend: Maybe<&2, U32>, dash: Bool, rs: Regex.Ranges()) -> Regex.parse.Scan():
  match s:
    case SNil{}:
      Fail{RErr{0n, "unterminated character set"}}
    case SCon{Chr{+x}, t}:
      Regex.parse.cls.char(Regex.parse.index(x, [93, 92, 45], 1n), x, t, pend, dash, rs)

def Regex.parse.cls(fuel: Nat, st: Regex.parse.Scan()) -> Regex.parse.Scan():
  match fuel st:
    case _ Fail{e}:
      Fail{e}
    case _ Done{CDone{rs, rest}}:
      Done{CDone{rs, rest}}
    case 0n Done{CScan{s, pend, dash, rs}}:
      Fail{RErr{0n, "unterminated character set"}}
    case 1n+f Done{CScan{s, pend, dash, rs}}:
      Regex.parse.cls(f, Regex.parse.cls.step(s, pend, dash, rs))

# A leading `]` is a member
def Regex.parse.set.lead(t: String) -> Regex.Cls:
  match t:
    case SCon{Chr{+x}, +t2}:
      Bool.pick(Regex.Cls, U32.is_eq(x, 93),
        CScan{t2, Some{93}, False{}, []}, CScan{SCon{Chr{x}, t2}, None{}, False{}, []})
    case SNil{}:
      CScan{SNil{}, None{}, False{}, []}

def Regex.parse.set.head(t: String) -> Sigma<&2, &2, Bool, _ => String>:
  match t:
    case SCon{Chr{+x}, +t2}:
      Bool.pick(Sigma<&2, &2, Bool, _ => String>, U32.is_eq(x, 94), (True{}, t2), (False{}, SCon{Chr{x}, t2}))
    case SNil{}:
      (False{}, SNil{})

def Regex.parse.set.fin(neg: Bool, r: Regex.parse.Scan()) -> Regex.parse.Item():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{CDone{rs, rest}}:
      Done{(RSet{neg, rs}, rest)}
    case Done{CScan{s, pend, dash, rs}}:
      Fail{RErr{0n, "unterminated character set"}}

def Regex.parse.set.go(fuel: Nat, h: Sigma<&2, &2, Bool, _ => String>) -> Regex.parse.Item():
  (neg, t) = h
  Regex.parse.set.fin(neg, Regex.parse.cls(fuel, Done{Regex.parse.set.lead(t)}))

# The tail after `[`
def Regex.parse.set(+t: String) -> Regex.parse.Item():
  Regex.parse.set.go(String.length(t), Regex.parse.set.head(t))

def Regex.parse.char(kind: Nat, +x: U32, t: String, n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.State():
  match kind:
    case 0n:
      Regex.parse.push(t, n, stack, RLit{Chr{x}})
    case 1n:
      Regex.parse.open(t, n, stack)
    case 2n:
      Regex.parse.close(t, n, stack)
    case 3n:
      Regex.parse.bar(t, n, stack)
    case 4n:
      Regex.parse.rep(t, n, stack, 0n, None{})
    case 5n:
      Regex.parse.rep(t, n, stack, 1n, None{})
    case 6n:
      Regex.parse.opt(t, n, stack)
    case 7n:
      Regex.parse.braces(n, stack, Regex.parse.bounds(t))
    case 8n:
      Regex.parse.atom(n, stack, Regex.parse.set(t))
    case 9n:
      Regex.parse.push(t, n, stack, RAny{})
    case 10n:
      Regex.parse.push(t, n, stack, RBol{})
    case 11n:
      Regex.parse.push(t, n, stack, REol{})
    case 12n+_:
      Regex.parse.atom(n, stack, Regex.parse.esc(t))

def Regex.parse.step(st: Regex.parse.State()) -> Regex.parse.State():
  match st:
    case Fail{e}:
      Fail{e}
    case Done{(SNil{}, (n, stack))}:
      Done{(SNil{}, (n, stack))}
    case Done{(SCon{Chr{+x}, t}, (n, stack))}:
      Regex.parse.char(Regex.parse.index(x, [40, 41, 124, 42, 43, 63, 123, 91, 46, 94, 36, 92], 1n), x, t, n, stack)

def Regex.parse.end.go(n: Nat, stack: Regex.parse.Stack()) -> Regex.parse.Tree():
  match stack:
    case fr <> Nil{}:
      Done{(Regex.parse.fin(fr), n)}
    case _:
      Fail{RErr{0n, "missing )"}}

def Regex.parse.end(st: Regex.parse.State()) -> Regex.parse.Tree():
  match st:
    case Fail{e}:
      Fail{e}
    case Done{(s, (n, stack))}:
      Regex.parse.end.go(n, stack)

def Regex.parse.go(fuel: Nat, st: Regex.parse.State()) -> Regex.parse.Tree():
  match fuel:
    case 0n:
      Regex.parse.end(st)
    case 1n+f:
      Regex.parse.go(f, Regex.parse.step(st))

def Regex.parse.pos(len: Nat, r: Regex.parse.Tree()) -> Regex.parse.Tree():
  match r:
    case Fail{RErr{k, msg}}:
      Fail{RErr{Nat.sub(len, k), msg}}
    case Done{v}:
      Done{v}

# The tree and its group count
def Regex.parse.run(+p: String) -> Regex.parse.Tree():
  +len = String.length(p)
  Regex.parse.pos(len, Regex.parse.go(len, Done{(p, (0n, [Frame{None{}, [], [], 0n}]))}))

def Regex.parse.re(r: Regex.parse.Tree()) -> Result<&2, &2, Regex.Error, Re>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(re, n)}:
      Done{re}

def Regex.parse(p: String) -> Result<&2, &2, Regex.Error, Re>:
  Regex.parse.re(Regex.parse.run(p))

# Flags: (i, (m, s))
def Regex.Flags() -> Data:
  Sigma<&2, &2, Bool, _ => Sigma<&2, &2, Bool, _ => Bool>>

def Regex.flags.kind(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{Chr{+x}, t}:
      Regex.parse.index(x, [105, 109, 115], 1n)

# `kind` classifies the head of `f`: 0 unknown, 1 i, 2 m, 3 s
def Regex.flags(f: String, kind: Nat, fl: Regex.Flags()) -> Result<&2, &2, Regex.Error, Regex.Flags()>:
  match f kind fl:
    case SNil{}, _, fl:
      Done{fl}
    case SCon{c, t}, 0n, _:
      Fail{RErr{0n, "unknown flag"}}
    case SCon{c, +t}, 1n, (False{}, r):
      Regex.flags(t, Regex.flags.kind(t), (True{}, r))
    case SCon{c, +t}, 2n, (i, (False{}, s)):
      Regex.flags(t, Regex.flags.kind(t), (i, (True{}, s)))
    case SCon{c, +t}, 3n+_, (i, (m, False{})):
      Regex.flags(t, Regex.flags.kind(t), (i, (m, True{})))
    case SCon{c, t}, _, _:
      Fail{RErr{0n, "duplicate flag"}}

# Program size of a tree, saturating just past max_prog
def Regex.size.rep(+s: Nat, +lo: Nat, hi: Maybe<&2, Nat>) -> Nat:
  match hi:
    case None{}:
      Nat.add(Nat.mul(lo, s), 2n+s)
    case Some{h}:
      Nat.add(Nat.mul(lo, s), Nat.mul(Nat.sub(h, lo), 1n+s))

def Regex.size(r: Re) -> Nat:
  match r:
    case RCat{a, b}:
      Nat.add(Regex.size(a), Regex.size(b))
    case RAlt{a, b}:
      2n+Nat.add(Regex.size(a), Regex.size(b))
    case RRep{r, lo, hi, g}:
      Nat.min(1n+Regex.max_prog(), Regex.size.rep(Regex.size(r), lo, hi))
    case RCap{n, r}:
      2n+Regex.size(r)
    case REmpty{}:
      0n
    case _:
      1n

# Bounded repeats unfold into copies: `x{2,4}` = `x x (x (x)?)?`, `x{2,}` =
# `x x x*`. After this only `x*` and `x?` remain (lo = 0)
def Regex.expand.opt(+e: Re, k: Nat, +g: Bool) -> Re:
  match k:
    case 0n:
      REmpty{}
    case 1n+p:
      RRep{RCat{e, Regex.expand.opt(e, p, g)}, 0n, Some{1n}, g}

def Regex.expand.times(n: Nat, +e: Re, acc: Re) -> Re:
  match n:
    case 0n:
      acc
    case 1n+p:
      Regex.expand.times(p, e, RCat{e, acc})

def Regex.expand.rep(+e: Re, +lo: Nat, hi: Maybe<&2, Nat>, +g: Bool) -> Re:
  match hi:
    case None{}:
      Regex.expand.times(lo, e, RRep{e, 0n, None{}, g})
    case Some{h}:
      Regex.expand.times(lo, e, Regex.expand.opt(e, Nat.sub(h, lo), g))

def Regex.expand(r: Re) -> Re:
  match r:
    case RCat{a, b}:
      RCat{Regex.expand(a), Regex.expand(b)}
    case RAlt{a, b}:
      RAlt{Regex.expand(a), Regex.expand(b)}
    case RRep{r, lo, hi, g}:
      Regex.expand.rep(Regex.expand(r), lo, hi, g)
    case RCap{n, r}:
      RCap{n, Regex.expand(r)}
    case other:
      other

# Case folding (flag i): add the ASCII letters of the other case
def Regex.emit.swap(+a: U32, +b: U32, lo: U32, hi: U32, acc: Regex.Ranges()) -> Regex.Ranges():
  +x = U32.max(a, lo)
  +y = U32.min(b, hi)
  List.filter.put(Regex.Range(), (U32.xor(x, 32), U32.xor(y, 32)), acc, U32.is_le(x, y))

def Regex.emit.fold(rs: Regex.Ranges()) -> Regex.Ranges():
  match rs:
    case Nil{}:
      []
    case (+a, +b) <> rest:
      (a, b) <> Regex.emit.swap(a, b, 65, 90, Regex.emit.swap(a, b, 97, 122, Regex.emit.fold(rest)))

def Regex.emit.ranges(fl: Regex.Flags(), rs: Regex.Ranges()) -> Regex.Ranges():
  (i, r) = fl
  match i:
    case True{}:
      Regex.emit.fold(rs)
    case False{}:
      rs

def Regex.emit.lit(fl: Regex.Flags(), +c: U32) -> Inst:
  (i, r) = fl
  match i:
    case True{}:
      ISet{False{}, Regex.emit.fold([(c, c)])}
    case False{}:
      IChr{c}

def Regex.emit.any(fl: Regex.Flags()) -> Inst:
  (i, (m, s)) = fl
  match s:
    case True{}:
      ISet{True{}, []}
    case False{}:
      IAny{}

def Regex.emit.multi(fl: Regex.Flags()) -> Bool:
  (i, (m, s)) = fl
  m

def Regex.emit.split(g: Bool, x: Nat, y: Nat) -> Inst:
  match g:
    case True{}:
      ISplit{x, y}
    case False{}:
      ISplit{y, x}

# Code for an expanded tree placed at address `pc`
def Regex.emit(r: Re, +fl: Regex.Flags(), +pc: Nat) -> List<&2, Inst>:
  match r:
    case RLit{Chr{c}}:
      [Regex.emit.lit(fl, c)]
    case RAny{}:
      [Regex.emit.any(fl)]
    case RSet{neg, rs}:
      [ISet{neg, Regex.emit.ranges(fl, rs)}]
    case RCat{+a, b}:
      List.append(&2, Inst, Regex.emit(a, fl, pc), Regex.emit(b, fl, Nat.add(pc, Regex.size(a))))
    case RAlt{+a, +b}:
      +q = Nat.add(2n+pc, Regex.size(a))
      ISplit{1n+pc, q} <> List.append(&2, Inst, Regex.emit(a, fl, 1n+pc), IJmp{Nat.add(q, Regex.size(b))} <> Regex.emit(b, fl, q))
    case RRep{+r, lo, None{}, g}:
      Regex.emit.split(g, 1n+pc, Nat.add(2n+pc, Regex.size(r))) <> List.append(&2, Inst, Regex.emit(r, fl, 1n+pc), [IJmp{pc}])
    case RRep{+r, lo, Some{h}, g}:
      Regex.emit.split(g, 1n+pc, Nat.add(1n+pc, Regex.size(r))) <> Regex.emit(r, fl, 1n+pc)
    case RCap{+n, r}:
      ISave{Nat.mul(2n, n)} <> List.append(&2, Inst, Regex.emit(r, fl, 1n+pc), [ISave{1n+Nat.mul(2n, n)}])
    case RBol{}:
      [IBol{Regex.emit.multi(fl)}]
    case REol{}:
      [IEol{Regex.emit.multi(fl)}]
    case RWordB{neg}:
      [IWordB{neg}]
    case REmpty{}:
      []

def Regex.compile.prog(fl: Regex.Flags(), re: Re, n: Nat, big: Bool) -> Result<&2, &2, Regex.Error, Regex>:
  match big:
    case True{}:
      Fail{RErr{0n, "program exceeds max_prog"}}
    case False{}:
      Done{Regex{ISave{0n} <> List.append(&2, Inst, Regex.emit(Regex.expand(re), fl, 1n), [ISave{1n}, IMatch{}]), n}}

def Regex.compile.tree(fr: Result<&2, &2, Regex.Error, Regex.Flags()>, t: Regex.parse.Tree()) -> Result<&2, &2, Regex.Error, Regex>:
  match fr t:
    case Fail{e} _:
      Fail{e}
    case Done{fl} Fail{e}:
      Fail{e}
    case Done{fl} Done{(+re, n)}:
      Regex.compile.prog(fl, re, n, Nat.is_gt(3n+Regex.size(re), Regex.max_prog()))

# Flags: any of `i` (ASCII case fold) `m` (multiline anchors) `s` (dot
# matches newline), each at most once
def Regex.compile(p: String, +f: String) -> Result<&2, &2, Regex.Error, Regex>:
  Regex.compile.tree(Regex.flags(f, Regex.flags.kind(f), (False{}, (False{}, False{}))), Regex.parse.run(p))

# Reference Pike VM. A thread is a pc and its capture slots; at each
# position the live threads are kept in priority order, so the first
# thread to reach IMatch is the leftmost-first answer and cuts every
# thread below it. Slow but total: O(n·m²) on every lane
def Regex.exec.Caps() -> Data:
  List<&2, Maybe<&2, Nat>>

def Regex.exec.Thread() -> Data:
  Sigma<&2, &2, Nat, _ => Regex.exec.Caps()>

def Regex.exec.Threads() -> Data:
  List<&2, Regex.exec.Thread()>

# Where the VM stands: (position, (previous char, subject from here))
def Regex.exec.Ctx() -> Data:
  Sigma<&2, &2, Nat, _ => Sigma<&2, &2, Maybe<&2, U32>, _ => String>>

# Closure state: (work stack, (pcs seen at this position, live threads reversed))
def Regex.exec.CState() -> Data:
  Sigma<&2, &2, Regex.exec.Threads(), _ => Sigma<&2, &2, List<&2, Nat>, _ => Regex.exec.Threads()>>

# Run state: (threads to close at the next position, best match so far)
def Regex.exec.State() -> Data:
  Sigma<&2, &2, Regex.exec.Threads(), _ => Maybe<&2, Regex.exec.Caps()>>

def Regex.exec.inset(+y: U32, rs: Regex.Ranges()) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case (a, b) <> rest:
      Bool.or(Bool.and(U32.is_le(a, y), U32.is_le(y, b)), Regex.exec.inset(y, rest))

def Regex.exec.peek(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{Chr{x}, t}:
      Some{x}

def Regex.exec.is_word(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Regex.exec.inset(x, Regex.words())

def Regex.exec.is_nl(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, 10)

def Regex.exec.bol(multi: Bool, ctx: Regex.exec.Ctx()) -> Bool:
  match ctx:
    case (0n, r):
      True{}
    case (i, (prev, tail)):
      Bool.and(multi, Regex.exec.is_nl(prev))

# `$`: at the end, before a final newline, or (multiline) before any newline
def Regex.exec.eol(multi: Bool, ctx: Regex.exec.Ctx()) -> Bool:
  match ctx:
    case (i, (prev, SNil{})):
      True{}
    case (i, (prev, SCon{Chr{x}, SNil{}})):
      U32.is_eq(x, 10)
    case (i, (prev, SCon{Chr{x}, t})):
      Bool.and(multi, U32.is_eq(x, 10))

def Regex.exec.wordb(neg: Bool, ctx: Regex.exec.Ctx()) -> Bool:
  (i, (prev, tail)) = ctx
  Bool.xor(neg, Bool.xor(Regex.exec.is_word(prev), Regex.exec.is_word(Regex.exec.peek(tail))))

def Regex.exec.pos(ctx: Regex.exec.Ctx()) -> Nat:
  (i, r) = ctx
  i

def Regex.exec.save(caps: Regex.exec.Caps(), slot: Nat, +i: Nat) -> Regex.exec.Caps():
  match caps slot:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      Some{i} <> t
    case h <> t 1n+p:
      h <> Regex.exec.save(t, p, i)

# One closure step at `pc`: `dup` = already seen here, `inst` = prog[pc]
def Regex.exec.step(ctx: Regex.exec.Ctx(), +pc: Nat, +caps: Regex.exec.Caps(), work: Regex.exec.Threads(), seen: List<&2, Nat>, acc: Regex.exec.Threads(), dup: Bool, inst: Maybe<&2, Inst>) -> Regex.exec.CState():
  match dup inst:
    case True{} _:
      (work, (seen, acc))
    case False{} Some{ISplit{x, y}}:
      ((x, caps) <> ((y, caps) <> work), (pc <> seen, acc))
    case False{} Some{IJmp{x}}:
      ((x, caps) <> work, (pc <> seen, acc))
    case False{} Some{ISave{+slot}}:
      (List.filter.put(Regex.exec.Thread(), (1n+pc, Regex.exec.save(caps, slot, Regex.exec.pos(ctx))), work, Nat.is_lt(slot, List.length(&2, Maybe<&2, Nat>, caps))), (pc <> seen, acc))
    case False{} Some{IBol{multi}}:
      (List.filter.put(Regex.exec.Thread(), (1n+pc, caps), work, Regex.exec.bol(multi, ctx)), (pc <> seen, acc))
    case False{} Some{IEol{multi}}:
      (List.filter.put(Regex.exec.Thread(), (1n+pc, caps), work, Regex.exec.eol(multi, ctx)), (pc <> seen, acc))
    case False{} Some{IWordB{neg}}:
      (List.filter.put(Regex.exec.Thread(), (1n+pc, caps), work, Regex.exec.wordb(neg, ctx)), (pc <> seen, acc))
    case False{} Some{i}:
      (work, (pc <> seen, (pc, caps) <> acc))
    case False{} None{}:
      (work, (pc <> seen, acc))

# ε-closure over a work stack; each pc is expanded at most once per
# position, so 3·(1+|prog|) steps always drain the stack
def Regex.exec.close(fuel: Nat, +prog: List<&2, Inst>, +ctx: Regex.exec.Ctx(), st: Regex.exec.CState()) -> Regex.exec.CState():
  match fuel st:
    case 0n, st:
      st
    case 1n+f, (Nil{}, r):
      (Nil{}, r)
    case 1n+f, ((+pc, caps) <> work, (+seen, acc)):
      Regex.exec.close(f, prog, ctx, Regex.exec.step(ctx, pc, caps, work, seen, acc, List.contains(~Nat, ~Nat.is_eq, seen, pc), List.get(&2, Inst, prog, pc)))

def Regex.exec.closed(st: Regex.exec.CState()) -> Regex.exec.Threads():
  (work, (seen, acc)) = st
  List.reverse(&2, Regex.exec.Thread(), acc)

# Threads alive at this position, in priority order: the closure of the
# survivors plus, while no match is known, a fresh thread at the bottom
def Regex.exec.alive(+prog: List<&2, Inst>, ctx: Regex.exec.Ctx(), work: Regex.exec.Threads(), start: Regex.exec.Threads(), best: Bool) -> Regex.exec.Threads():
  Regex.exec.closed(Regex.exec.close(Nat.mul(3n, 1n+List.length(&2, Inst, prog)), prog, ctx, (List.append(&2, Regex.exec.Thread(), work, Bool.pick(Regex.exec.Threads(), best, [], start)), ([], []))))

def Regex.exec.eat(inst: Inst, c: Maybe<&2, U32>) -> Bool:
  match inst c:
    case IChr{x} Some{y}:
      U32.is_eq(x, y)
    case IAny{} Some{y}:
      Bool.not(U32.is_eq(y, 10))
    case ISet{neg, rs} Some{+y}:
      Bool.xor(neg, Regex.exec.inset(y, rs))
    case _ _:
      False{}

def Regex.exec.fetch(+prog: List<&2, Inst>, ts: Regex.exec.Threads()) -> Maybe<&2, Inst>:
  match ts:
    case Nil{}:
      None{}
    case (pc, caps) <> rest:
      List.get(&2, Inst, prog, pc)

# Feed the char to the live threads in priority order. IMatch wins and cuts
# the rest, unless `cut` is off (fullmatch before the end); `inst` = prog[head pc]
def Regex.exec.adv(clist: Regex.exec.Threads(), +prog: List<&2, Inst>, cut: Bool, +c: Maybe<&2, U32>, inst: Maybe<&2, Inst>, work: Regex.exec.Threads()) -> Maybe<&2, Regex.exec.Caps()> & Regex.exec.Threads():
  match clist cut inst:
    case Nil{}, _, _:
      (None{}, work)
    case (pc, caps) <> +rest, False{}, Some{IMatch{}}:
      Regex.exec.adv(rest, prog, False{}, c, Regex.exec.fetch(prog, rest), work)
    case (pc, caps) <> rest, _, Some{IMatch{}}:
      (Some{caps}, work)
    case (pc, caps) <> +rest, k, Some{i}:
      Regex.exec.adv(rest, prog, k, c, Regex.exec.fetch(prog, rest), List.filter.put(Regex.exec.Thread(), (1n+pc, caps), work, Regex.exec.eat(i, c)))
    case (pc, caps) <> +rest, k, None{}:
      Regex.exec.adv(rest, prog, k, c, Regex.exec.fetch(prog, rest), work)

def Regex.exec.feed(+prog: List<&2, Inst>, full: Bool, +c: Maybe<&2, U32>, +clist: Regex.exec.Threads()) -> Maybe<&2, Regex.exec.Caps()> & Regex.exec.Threads():
  Regex.exec.adv(clist, prog, Bool.or(Bool.not(full), Maybe.is_none(&2, U32, c)), c, Regex.exec.fetch(prog, clist), [])

def Regex.exec.post(best: Maybe<&2, Regex.exec.Caps()>, r: Maybe<&2, Regex.exec.Caps()> & Regex.exec.Threads()) -> Regex.exec.State():
  (found, acc) = r
  (List.reverse(&2, Regex.exec.Thread(), acc), Maybe.or(&2, Regex.exec.Caps(), found, best))

def Regex.exec.groups(caps: Regex.exec.Caps()) -> List<&2, Maybe<&2, Regex.Span()>>:
  match caps:
    case Some{a} <> (Some{b} <> gs):
      Some{(a, b)} <> Regex.exec.groups(gs)
    case x <> (y <> gs):
      None{} <> Regex.exec.groups(gs)
    case _:
      []

def Regex.exec.match(caps: Regex.exec.Caps()) -> Maybe<&2, Match>:
  match caps:
    case Some{a} <> (Some{b} <> gs):
      Some{Match{a, b, Regex.exec.groups(gs)}}
    case _:
      None{}

def Regex.exec.fin(st: Regex.exec.State()) -> Maybe<&2, Match>:
  match st:
    case (work, Some{caps}):
      Regex.exec.match(caps)
    case (work, None{}):
      None{}

# Walks the subject; the first `at` chars are skipped (they still set
# `prev` for `^` `\b`). `anchored` drops the fresh thread after position `at`
def Regex.exec.run(s: String, at: Nat, +prog: List<&2, Inst>, +full: Bool, +anchored: Bool, +start: Regex.exec.Threads(), +i: Nat, prev: Maybe<&2, U32>, st: Regex.exec.State()) -> Maybe<&2, Match>:
  match s at st:
    case SCon{Chr{x}, t}, 1n+a, st:
      Regex.exec.run(t, a, prog, full, anchored, start, 1n+i, Some{x}, st)
    case SCon{Chr{+x}, +t}, 0n, (work, +best):
      Regex.exec.run(t, 0n, prog, full, anchored, Bool.pick(Regex.exec.Threads(), anchored, [], start), 1n+i, Some{x}, Regex.exec.post(best, Regex.exec.feed(prog, full, Some{x}, Regex.exec.alive(prog, (i, (prev, SCon{Chr{x}, t})), work, start, Maybe.is_some(&2, Regex.exec.Caps(), best)))))
    case SNil{}, _, (work, +best):
      Regex.exec.fin(Regex.exec.post(best, Regex.exec.feed(prog, full, None{}, Regex.exec.alive(prog, (i, (prev, SNil{})), work, start, Maybe.is_some(&2, Regex.exec.Caps(), best)))))

def Regex.exec.go(re: Regex, s: String, at: Nat, full: Bool, anchored: Bool) -> Maybe<&2, Match>:
  match re:
    case Regex{prog, n}:
      Regex.exec.run(s, at, prog, full, anchored, [(0n, List.replicate(Maybe<&2, Nat>, Nat.mul(2n, 1n+n), None{}))], 0n, None{}, ([], None{}))

# First match starting at or after `at` (code-point offset)
def Regex.exec(re: Regex, s: String, at: Nat) -> Maybe<&2, Match>:
  Regex.exec.go(re, s, at, False{}, False{})

# Match starting exactly at `at`
def Regex.match_at(re: Regex, s: String, at: Nat) -> Maybe<&2, Match>:
  Regex.exec.go(re, s, at, False{}, True{})

# Match covering the whole subject
def Regex.fullmatch(re: Regex, s: String) -> Maybe<&2, Match>:
  Regex.exec.go(re, s, 0n, True{}, True{})

# Text
# ----

def Nat.show.put(qr: Nat & Nat) -> Char & Nat:
  (q, r) = qr
  (Chr{U32.from_nat(Nat.add(48n, r))}, q)

law Nat.show.go:
  for f   : Nat
  for n   : Nat
  for acc : String
  String

def Nat.show.fin(g: Nat, acc: String, dq: Char & Nat) -> String:
  (d, q) = dq
  match q:
    case 0n:
      SCon{d, acc}
    case 1n+p:
      Nat.show.go(g, 1n+p, SCon{d, acc})

def Nat.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      Nat.show.fin(g, acc, Nat.show.put(Nat.divmod(n, 10n)))

def Nat.show(n: Nat) -> String:
  +m = n
  Nat.show.fin(m, SNil{}, Nat.show.put(Nat.divmod(m, 10n)))

law Nat.read.go:
  for s   : String
  for +acc : Nat
  Maybe<&2, Nat>

def Nat.read.max() -> Nat:
  Nat.mul(U32.to_nat(16777215), U32.to_nat(16777217))

def Nat.read.fit(acc: Nat, qr: Nat & Nat) -> Bool:
  (q, r) = qr
  Bool.not(Nat.is_lt(q, acc))

def Nat.read.if(t: String, acc: Nat, d: U32, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Nat.read.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(d)))
    case False{}:
      None{}

def Nat.read.go(s, acc):
  match s:
    case SNil{}:
      Some{acc}
    case SCon{Chr{x}, t}:
      +d = U32.sub(x, 48)
      Nat.read.if(t, acc, d, Bool.and(U32.is_lt(d, 10), Nat.read.fit(acc,
        Nat.divmod(Nat.sub(Nat.read.max(), U32.to_nat(d)), 10n))))

def Nat.read(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      Nat.read.go(SCon{h, t}, 0n)

law U32.show.go:
  for f   : Nat
  for +n  : U32
  for acc : String
  String

def U32.show.fin(g: Nat, acc: String, +n: U32, z: Bool) -> String:
  match z:
    case True{}:
      acc
    case False{}:
      U32.show.go(g, U32.div(n, 10),
        SCon{Chr{U32.add(48, U32.mod(n, 10))}, acc})

def U32.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      U32.show.fin(g, acc, n, U32.is_zero(n))

def U32.show.if(a: U32, z: Bool) -> String:
  match z:
    case True{}:
      SCon{Chr{48}, SNil{}}
    case False{}:
      U32.show.go(10n, a, SNil{})

def U32.show(a: U32) -> String:
  +b = a
  U32.show.if(b, U32.is_zero(b))

law U32.read.go:
  for s   : String
  for +acc : U32
  Maybe<&2, U32>

def U32.read.if(t: String, n: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      U32.read.go(t, n)
    case False{}:
      None{}

def U32.read.go(s, acc):
  match s:
    case SNil{}:
      Some{acc}
    case SCon{Chr{x}, t}:
      +n = U32.add(U32.mul(acc, 10), U32.sub(x, 48))
      U32.read.if(t, n, U32.is_eq(U32.div(n, 10), acc))

def U32.read(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      U32.read.go(SCon{h, t}, 0)

def Bool.show(b: Bool) -> String:
  match b:
    case False{}:
      "False"
    case True{}:
      "True"

def Char.show(c: Char) -> String:
  SCon{c, SNil{}}

def Maybe.show(~a: Quant, ~A: Kind(a), ~f: A -> String, m: Maybe<a, A>) ->
  String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      "Some(" ++ f(x) ++ ")"

def List.show.go(~a: Quant, ~A: Kind(a), ~f: A -> String, xs: List<a, A>) ->
  String:
  match xs:
    case Nil{}:
      "]"
    case h <> t:
      ", " ++ f(h) ++ List.show.go(~a, ~A, ~f, t)

def List.show(~a: Quant, ~A: Kind(a), ~f: A -> String, xs: List<a, A>) ->
  String:
  match xs:
    case Nil{}:
      "[]"
    case h <> t:
      "[" ++ f(h) ++ List.show.go(~a, ~A, ~f, t)

# Array
# -----

def Array.size.node(-T: Type, ys: Array<T>, r: Array<T> & U32) ->
  Array<T> & U32:
  (xs2, n) = r
  (ANode{xs2, ys}, U32.shl(n))

def Array.size(-T: Type, a: Array<T>) -> Array<T> & U32:
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1)
    case ANode{xs, ys}:
      Array.size.node(T, ys, Array.size(T, xs))

def Array.swap.lo(-T: Type, ys: Array<T>, r: Array<T> & T) -> Array<T> & T:
  (nxs, old) = r
  (ANode{nxs, ys}, old)

def Array.swap.hi(-T: Type, xs: Array<T>, r: Array<T> & T) -> Array<T> & T:
  (nys, old) = r
  (ANode{xs, nys}, old)

law Array.swap.go:
  for -T: Type
  for  a: Array<T>
  for  n: U32
  for +i: U32
  for  v: T
  Array<T> & T

def Array.swap.if(
  -T: Type, xs: Array<T>, ys: Array<T>, +h: U32, i: U32, v: T, z: Bool
) -> Array<T> & T:
  match z:
    case True{}:
      Array.swap.lo(T, ys, Array.swap.go(T, xs, h, i, v))
    case False{}:
      Array.swap.hi(T, xs, Array.swap.go(T, ys, h, U32.sub(i, h), v))

def Array.swap.go(T, a, n, i, v):
  match a:
    case ALeaf{x}:
      (ALeaf{v}, x)
    case ANode{xs, ys}:
      +h = U32.shr(n)
      Array.swap.if(T, xs, ys, h, i, v, U32.is_lt(i, h))

def Array.swap.at(-T: Type, i: U32, v: T, an: Array<T> & U32) -> Array<T> & T:
  (a, +n) = an
  Array.swap.go(T, a, n, U32.and(i, U32.sub(n, 1)), v)

def Array.swap(-T: Type, a: Array<T>, +i: U32, v: T) -> Array<T> & T:
  Array.swap.at(T, i, v, Array.size(T, a))

def Array.clone.node(
  -T: Data, cx: Array<T> & Array<T>, cy: Array<T> & Array<T>
) -> Array<T> & Array<T>:
  (xa, xb) = cx
  (ya, yb) = cy
  (ANode{xa, ya}, ANode{xb, yb})

def Array.clone(-T: Data, a: Array<T>) -> Array<T> & Array<T>:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, ALeaf{x})
    case ANode{xs, ys}:
      Array.clone.node(T, Array.clone(T, xs), Array.clone(T, ys))

def Array.new(-T: Data, +d: Nat, +v: T) -> Array<T>:
  match d:
    case 0n:
      ALeaf{v}
    case 1n+p:
      ANode{[v : T^p], [v : T^p]}

def Array.set.fin(-T: Type, r: Array<T> & T) -> Array<T>:
  (na, old) = r
  na

def Array.set(-T: Type, a: Array<T>, i: U32, v: T) -> Array<T>:
  Array.set.fin(T, Array.swap(T, a, i, v))

law Array.get.go:
  for -T: Data
  for  a: Array<T>
  for  n: U32
  for +i: U32
  Array<T> & T

def Array.get.if(
  -T: Data, xs: Array<T>, ys: Array<T>, +h: U32, i: U32, z: Bool
) -> Array<T> & T:
  match z:
    case True{}:
      Array.swap.lo(T, ys, Array.get.go(T, xs, h, i))
    case False{}:
      Array.swap.hi(T, xs, Array.get.go(T, ys, h, U32.sub(i, h)))

def Array.get.go(T, a, n, i):
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, x)
    case ANode{xs, ys}:
      +h = U32.shr(n)
      Array.get.if(T, xs, ys, h, i, U32.is_lt(i, h))

def Array.get.at(-T: Data, i: U32, an: Array<T> & U32) -> Array<T> & T:
  (a, +n) = an
  Array.get.go(T, a, n, U32.and(i, U32.sub(n, 1)))

def Array.get(-T: Data, a: Array<T>, +i: U32) -> Array<T> & T:
  Array.get.at(T, i, Array.size(T, a))

def Array.to_list.go(~T: Type, a: Array<T>, acc: List<T>) -> List<T>:
  match a:
    case ALeaf{x}:
      x <> acc
    case ANode{xs, ys}:
      Array.to_list.go(~T, xs, Array.to_list.go(~T, ys, acc))

def Array.to_list(~T: Type, a: Array<T>) -> List<T>:
  Array.to_list.go(~T, a, Nil{})

def Array.map(~T: Type, ~U: Type, ~f: T -> U, a: Array<T>) -> Array<U>:
  match a:
    case ALeaf{x}:
      ALeaf{f(x)}
    case ANode{xs, ys}:
      l r = Array.map(~T, ~U, ~f, xs) Array.map(~T, ~U, ~f, ys)
      ANode{l, r}

# Map
# ---

def Map.bit.u(x: U32, k: Nat) -> Bool:
  U32.is_ne(U32.and(U32.shrn(x, k), 1), 0)

def Map.bit.chr(c: Char, off: Nat) -> Char & Bool:
  match c off:
    case Chr{x} 0n:
      (Chr{x}, True{})
    case Chr{+x} 1n+b:
      (Chr{x}, Map.bit.u(x, Nat.sub(31n, b)))

def Map.bit.go.chr(t: String, r: Char & Bool) -> String & Bool:
  (c2, b) = r
  (SCon{c2, t}, b)

def Map.bit.go.rec(c: Char, r: String & Bool) -> String & Bool:
  (t2, b) = r
  (SCon{c, t2}, b)

def Map.bit.go(key: String, ci: Nat, off: Nat) -> String & Bool:
  match key:
    case SNil{}:
      (SNil{}, False{})
    case SCon{c, t}:
      match ci:
        case 0n:
          Map.bit.go.chr(t, Map.bit.chr(c, off))
        case 1n+j:
          Map.bit.go.rec(c, Map.bit.go(t, j, off))

def Map.bit.at(key: String, co: Nat & Nat) -> String & Bool:
  (ci, off) = co
  Map.bit.go(key, ci, off)

def Map.bit(key: String, pos: Nat) -> String & Bool:
  Map.bit.at(key, Nat.divmod(pos, 33n))

law Map.msb.u:
  for n: Nat
  for +x: U32
  Nat

def Map.msb.u.if(p: Nat, x2: U32, z: Bool) -> Nat:
  match z:
    case True{}:
      0n
    case False{}:
      Nat.add(1n, Map.msb.u(p, U32.shr(x2)))

def Map.msb.u(n, x):
  match n:
    case 0n:
      0n
    case 1n+p:
      Map.msb.u.if(p, x, U32.is_zero(x))

def Map.diff.chr(x: U32) -> Nat:
  Nat.sub(33n, Map.msb.u(32n, x))

def Map.diff.step(x: Char, y: Char) -> Nat & Bool:
  match x y:
    case Chr{+cx} Chr{+cy}:
      (Map.diff.chr(U32.xor(cx, cy)), U32.is_eq(cx, cy))

law Map.diff:
  for a: String
  for b: String
  Nat

def Map.diff.fin(xt: String, yt: String, rc: Nat & Bool) -> Nat:
  (r, c) = rc
  match c:
    case True{}:
      Nat.add(33n, Map.diff(xt, yt))
    case False{}:
      r

def Map.diff(a, b):
  match a b:
    case SNil{} SNil{}:
      0n
    case SNil{} SCon{h, t}:
      0n
    case SCon{h, t} SNil{}:
      0n
    case SCon{x, xt} SCon{y, yt}:
      Map.diff.fin(xt, yt, Map.diff.step(x, y))

def Map.new(a, -V: Kind(a)) -> Map<a, V>:
  MTip{}

law Map.put:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  for x   : V
  Map<a, V>

def Map.put.bit(
  a, -V: Kind(a), x: V, p2: Nat, lo: Map<a, V>, hi: Map<a, V>, kb: String & Bool
) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{p2, Map.put(a, V, lo, key2, x), hi}
    case True{}:
      MNode{p2, lo, Map.put(a, V, hi, key2, x)}

def Map.put(a, V, m, key, x):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      MLeaf{k, x}
    case MNode{+pos, lo, hi}:
      Map.put.bit(a, V, x, pos, lo, hi, Map.bit(key, pos))

def Map.ins.splice.bit(
  a, -V: Kind(a), x: V, rest: Map<a, V>, pb: Nat, kb: String & Bool
) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{pb, MLeaf{key2, x}, rest}
    case True{}:
      MNode{pb, rest, MLeaf{key2, x}}

def Map.ins.splice(
  a, -V: Kind(a), +p: Nat, key: String, x: V, rest: Map<a, V>
) -> Map<a, V>:
  Map.ins.splice.bit(a, V, x, rest, p, Map.bit(key, p))

law Map.ins:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  for x   : V
  for +p  : Nat
  Map<a, V>

def Map.ins.deep(
  a, -V: Kind(a), x: V, lo: Map<a, V>, hi: Map<a, V>, pb: Nat, qb: Nat,
  kb: String & Bool
) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{qb, Map.ins(a, V, lo, key2, x, pb), hi}
    case True{}:
      MNode{qb, lo, Map.ins(a, V, hi, key2, x, pb)}

def Map.ins.if(
  a, -V: Kind(a), key: String, x: V, lo: Map<a, V>, hi: Map<a, V>, +p2: Nat,
  pb: Nat, t: Bool
) -> Map<a, V>:
  match t:
    case False{}:
      Map.ins.splice(a, V, pb, key, x, MNode{p2, lo, hi})
    case True{}:
      Map.ins.deep(a, V, x, lo, hi, pb, p2, Map.bit(key, p2))

def Map.ins(a, V, m, key, x, p):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      Map.ins.splice(a, V, p, key, x, MLeaf{k, v})
    case MNode{+pos, lo, hi}:
      Map.ins.if(a, V, key, x, lo, hi, pos, p, Nat.is_lt(pos, p))

def Map.lo(
  a, -V: Kind(a), -R: Type, p2: Nat, hi: Map<a, V>, r0: Map<a, V> & R
) -> Map<a, V> & R:
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.hi(
  a, -V: Kind(a), -R: Type, p2: Nat, lo: Map<a, V>, r0: Map<a, V> & R
) -> Map<a, V> & R:
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

law Map.seek:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  Map<a, V> & String & Maybe<&2, String>

def Map.seek.bit(
  a, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool
) -> Map<a, V> & String & Maybe<&2, String>:
  (key2, b) = kb
  match b:
    case False{}:
      Map.lo(a, V, String & Maybe<&2, String>, p2, hi, Map.seek(a, V, lo, key2))
    case True{}:
      Map.hi(a, V, String & Maybe<&2, String>, p2, lo, Map.seek(a, V, hi, key2))

def Map.seek(a, V, m, key):
  match m:
    case MTip{}:
      (MTip{}, key, None{})
    case MLeaf{+k, v}:
      (MLeaf{k, v}, key, Some{k})
    case MNode{+pos, lo, hi}:
      Map.seek.bit(a, V, lo, hi, pos, Map.bit(key, pos))

def Map.set.fin.go(
  a, -V: Kind(a), m: Map<a, V>, key: String, x: V, r: (String & String) & Cmp
) -> Map<a, V>:
  ((keyb2, k2), c) = r
  match c:
    case LT{}:
      Map.ins(a, V, m, key, x, Map.diff(keyb2, k2))
    case EQ{}:
      Map.put(a, V, m, key, x)
    case GT{}:
      Map.ins(a, V, m, key, x, Map.diff(keyb2, k2))

def Map.set.fin(
  a, -V: Kind(a), m: Map<a, V>, key: String, x: V, keyb: String, k: String
) -> Map<a, V>:
  Map.set.fin.go(a, V, m, key, x, String.cmp(keyb, k))

def Map.set.go(
  a, -V: Kind(a), x: V, r: Map<a, V> & String & Maybe<&2, String>
) -> Map<a, V>:
  (m2, key2, found) = r
  match found:
    case None{}:
      MLeaf{key2, x}
    case Some{k}:
      +ka = {key2 : String}
      Map.set.fin(a, V, m2, ka, x, ka, k)

def Map.set(a, -V: Kind(a), m: Map<a, V>, key: String, x: V) -> Map<a, V>:
  Map.set.go(a, V, x, Map.seek(a, V, m, key))

def Map.has.leaf(a, -V: Kind(a), v: V, r: (String & String) & Cmp) ->
  Map<a, V> & Bool:
  ((key2, k2), c) = r
  (MLeaf{k2, v}, Cmp.is_eq(c))

law Map.has:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  Map<a, V> & Bool

def Map.has.bit(
  a, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool
) -> Map<a, V> & Bool:
  (key2, b) = kb
  match b:
    case False{}:
      Map.lo(a, V, Bool, p2, hi, Map.has(a, V, lo, key2))
    case True{}:
      Map.hi(a, V, Bool, p2, lo, Map.has(a, V, hi, key2))

def Map.has(a, V, m, key):
  match m:
    case MTip{}:
      (MTip{}, False{})
    case MLeaf{k, v}:
      Map.has.leaf(a, V, v, String.cmp(key, k))
    case MNode{+pos, lo, hi}:
      Map.has.bit(a, V, lo, hi, pos, Map.bit(key, pos))

def Map.get.leaf(-V: Data, d: V, +v: V, r: (String & String) & Cmp) ->
  Map<&2, V> & V:
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, d)
    case EQ{}:
      (MLeaf{k2, v}, v)
    case GT{}:
      (MLeaf{k2, v}, d)

law Map.get:
  for -V  : Data
  for d   : V
  for m   : Map<&2, V>
  for key : String
  Map<&2, V> & V

def Map.get.bit(
  -V: Data, d: V, lo: Map<&2, V>, hi: Map<&2, V>, p2: Nat, kb: String & Bool
) -> Map<&2, V> & V:
  (key2, b) = kb
  match b:
    case False{}:
      Map.lo(&2, V, V, p2, hi, Map.get(V, d, lo, key2))
    case True{}:
      Map.hi(&2, V, V, p2, lo, Map.get(V, d, hi, key2))

def Map.get(V, d, m, key):
  match m:
    case MTip{}:
      (MTip{}, d)
    case MLeaf{k, v}:
      Map.get.leaf(V, d, v, String.cmp(key, k))
    case MNode{+pos, lo, hi}:
      Map.get.bit(V, d, lo, hi, pos, Map.bit(key, pos))

def Map.pop.lo(
  a, -V: Kind(a), pos: Nat, hi: Map<a, V>, r0: Map<a, V> & Maybe<a, V>
) -> Map<a, V> & Maybe<a, V>:
  (lo, r) = r0
  match lo:
    case MTip{}:
      (hi, r)
    case lo2:
      (MNode{pos, lo2, hi}, r)

def Map.pop.hi(
  a, -V: Kind(a), pos: Nat, lo: Map<a, V>, r0: Map<a, V> & Maybe<a, V>
) -> Map<a, V> & Maybe<a, V>:
  (hi, r) = r0
  match hi:
    case MTip{}:
      (lo, r)
    case hi2:
      (MNode{pos, lo, hi2}, r)

def Map.pop.leaf(a, -V: Kind(a), v: V, r: (String & String) & Cmp) ->
  Map<a, V> & Maybe<a, V>:
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, None{})
    case EQ{}:
      (MTip{}, Some{v})
    case GT{}:
      (MLeaf{k2, v}, None{})

law Map.pop:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  Map<a, V> & Maybe<a, V>

def Map.pop.bit(
  a, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool
) -> Map<a, V> & Maybe<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      Map.pop.lo(a, V, p2, hi, Map.pop(a, V, lo, key2))
    case True{}:
      Map.pop.hi(a, V, p2, lo, Map.pop(a, V, hi, key2))

def Map.pop(a, V, m, key):
  match m:
    case MTip{}:
      (MTip{}, None{})
    case MLeaf{k, v}:
      Map.pop.leaf(a, V, v, String.cmp(key, k))
    case MNode{+pos, lo, hi}:
      Map.pop.bit(a, V, lo, hi, pos, Map.bit(key, pos))

def Map.del.fin(a, -V: Kind(a), r: Map<a, V> & Maybe<a, V>) -> Map<a, V>:
  (m2, x) = r
  m2

def Map.del(a, -V: Kind(a), m: Map<a, V>, key: String) -> Map<a, V>:
  Map.del.fin(a, V, Map.pop(a, V, m, key))

def Map.to_list.go(
  a, -V: Kind(a), m: Map<a, V>, acc: List<a, Sigma<&2, a, String, _ => V>>
) -> List<a, Sigma<&2, a, String, _ => V>>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      (k, v) <> acc
    case MNode{pos, lo, hi}:
      Map.to_list.go(a, V, lo, Map.to_list.go(a, V, hi, acc))

def Map.to_list(a, -V: Kind(a), m: Map<a, V>) ->
  List<a, Sigma<&2, a, String, _ => V>>:
  Map.to_list.go(a, V, m, Nil{})

def Map.keys.go(a, -V: Kind(a), m: Map<a, V>, acc: List<&2, String>) ->
  List<&2, String>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      k <> acc
    case MNode{pos, lo, hi}:
      Map.keys.go(a, V, lo, Map.keys.go(a, V, hi, acc))

def Map.keys(a, -V: Kind(a), m: Map<a, V>) -> List<&2, String>:
  Map.keys.go(a, V, m, Nil{})

def Map.from_list.go(
  a, -V: Kind(a), kvs: List<a, Sigma<&2, a, String, _ => V>>, m: Map<a, V>
) -> Map<a, V>:
  match kvs:
    case Nil{}:
      m
    case (k, v) <> t:
      Map.from_list.go(a, V, t, Map.set(a, V, m, k, v))

def Map.from_list(a, -V: Kind(a), kvs: List<a, Sigma<&2, a, String, _ => V>>) ->
  Map<a, V>:
  Map.from_list.go(a, V, kvs, MTip{})

def Map.union(a, -V: Kind(a), m: Map<a, V>, n: Map<a, V>) -> Map<a, V>:
  Map.from_list.go(a, V, Map.to_list(a, V, n), m)

def Map.size(a, -V: Kind(a), m: Map<a, V>) -> Nat:
  match m:
    case MTip{}:
      0n
    case MLeaf{k, v}:
      1n
    case MNode{pos, lo, hi}:
      Nat.add(Map.size(a, V, lo), Map.size(a, V, hi))

def Map.values.go(a, -V: Kind(a), m: Map<a, V>, acc: List<a, V>) -> List<a, V>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      v <> acc
    case MNode{pos, lo, hi}:
      Map.values.go(a, V, lo, Map.values.go(a, V, hi, acc))

def Map.values(a, -V: Kind(a), m: Map<a, V>) -> List<a, V>:
  Map.values.go(a, V, m, Nil{})

# Set
# ---

def Set() -> Data:
  Map<&2, Unit>

def Set.new() -> Set():
  Map.new(&2, Unit)

def Set.add(s: Set(), key: String) -> Set():
  Map.set(&2, Unit, s, key, Unit{})

def Set.has(s: Set(), key: String) -> Set() & Bool:
  Map.has(&2, Unit, s, key)

def Set.del(s: Set(), key: String) -> Set():
  Map.del(&2, Unit, s, key)

def Set.size(s: Set()) -> Nat:
  Map.size(&2, Unit, s)

def Set.to_list(s: Set()) -> List<&2, String>:
  Map.keys(&2, Unit, s)

def Set.from_list.go(keys: List<&2, String>, s: Set()) -> Set():
  match keys:
    case Nil{}:
      s
    case h <> t:
      Set.from_list.go(t, Set.add(s, h))

def Set.from_list(keys: List<&2, String>) -> Set():
  Set.from_list.go(keys, Set.new())

# Image
# -----

def Image.sink(img: Image) -> Unit:
  Unit{}

def Image.drop.join(a: Unit, b: Unit, c: Unit, d: Unit) -> Unit:
  match a b c d:
    case Unit{} Unit{} Unit{} Unit{}:
      Unit{}

# Forks k levels, then a dead parameter sinks the rest in one loop.
def Image.free(+k: Nat, img: Image) -> Unit:
  match k:
    case 0n:
      Image.sink(img)
    case 1n+e:
      match img:
        case Pix{c}:
          Unit{}
        case Qua{tl, tr, bl, br}:
          a b c d = Image.free(e, tl) Image.free(e, tr) Image.free(e, bl)
            Image.free(e, br)
          Image.drop.join(a, b, c, d)

def Image.drop(img: Image) -> Unit:
  Image.free(7n, img)

# App
# ---

def App.next(
  -S: Type, window: Window, rest: Window -> S -> IO(Unit), next: Maybe<S>
) -> IO(Unit):
  match next:
    case None{}:
      Window.close(window)
    case Some{state}:
      rest(window, state)

def App.turn(
  -S: Type, shown: Window & Image & List<Event>,
  tick: List<Event> -> S -> IO(Maybe<S>), state: S,
  rest: Window -> S -> IO(Unit)
) -> IO(Unit):
  (window, image, events) = shown
  do IO<Unit>:
    Unit <- IO.pure(Unit, Image.drop!(image))
    IO.bind(Maybe<S>, Unit, tick(events, state), App.next(S, window, rest))

def App.draw(
  -S: Type, window: Window, drawn: S & Image,
  tick: List<Event> -> S -> IO(Maybe<S>), rest: Window -> S -> IO(Unit)
) -> IO(Unit):
  (state, image) = drawn
  do IO<Unit>:
    shown : Window & Image & List<Event> <- Window.frame(window, image)
    App.turn(S, shown, tick, state, rest)

def App.step(
  -S: Type, app: App<S>, window: Window, state: S,
  rest: Window -> S -> IO(Unit)
) -> IO(Unit):
  App{view, tick} = app
  App.draw(S, window, view(state), tick, rest)

def App.loop(~S: Type, ~app: App<S>, fuel: Nat, window: Window, state: S) ->
  IO(Unit):
  match fuel:
    case 0n:
      Window.close(window)
    case 1n+f:
      App.step(S, app, window, state, w => s => App.loop(~S, ~app, f, w, s))

def App.run(
  ~S: Type, ~app: App<S>, title: String, width: U32, height: U32, state: S
) -> IO(Unit):
  do IO<Unit>:
    window : Window <- IO.try(Window, Window.open(title, width, height))
    App.loop(~S, ~app, U32.to_nat(4294967295), window, state)

def App.more(-S: Type, rest: S -> IO(Maybe<S>), next: Maybe<S>) ->
  IO(Maybe<S>):
  match next:
    case None{}:
      IO.pure(Maybe<S>, None{})
    case Some{state}:
      rest(state)

def App.fold(
  -S: Type, app: App<S>, events: List<Event>, state: S,
  rest: S -> IO(Maybe<S>)
) -> IO(Maybe<S>):
  App{view, tick} = app
  IO.bind(Maybe<S>, Maybe<S>, tick(events, state), App.more(S, rest))

def App.play(~S: Type, ~app: App<S>, frames: List<List<Event>>, state: S) ->
  IO(Maybe<S>):
  match frames:
    case Nil{}:
      IO.pure(Maybe<S>, Some{state})
    case events <> rest:
      App.fold(S, app, events, state, s => App.play(~S, ~app, rest, s))
