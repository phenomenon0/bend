# The laws of the RESP reader and server. The reader's are the HTTP
# engine's laws with the nouns changed, which is the point of writing
# this file at all: the reader shape carries its properties with it. The
# walk is the reader kit's (wire/reader.bend), and the laws every such
# walk has -- feed_split, bad_feeds and the block walk's -- are the
# kit's, proven once there and instantiated here for R.step.
import Base
import ../../wire/reader.bend as Wr
import ../../wire/loop.bend as L
import ../../wire/world.bend as WW
import ./resp.bend as R
import ./main.bend as S

# LAW: chunking does not change the read. Feeding a chunk and then
# another lands exactly where feeding the two joined would have, so a
# value split across however many recvs parses like one that arrived
# whole -- including a value split inside a nested array, since the
# stack is part of the state this is quantified over.
law feed_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +r: R.Rd
  {R.feed(List.append(&2, U32, a, b), r) == R.feed(b, R.feed(a, r)) : R.Rd}

# LAW: broken framing stays broken. No byte moves the reader out of
# Bad{}, so a peer cannot follow a refused value with one that is
# served -- the property that keeps a stream from being smuggled
# through after it has already been refused.
law bad_absorbs:
  for +c: U32
  for +up: List<&2, R.Fr>
  for +deep: U32
  for +out: List<&2, R.Val>
  {R.step(R.Rd{R.Bad{}, up, deep, out}, c) == R.Rd{R.Bad{}, Nil{}, 0, out} : R.Rd}

law bad_feeds:
  for +s: List<&2, U32>
  for +out: List<&2, R.Val>
  {R.feed(s, R.Rd{R.Bad{}, Nil{}, 0, out}) == R.Rd{R.Bad{}, Nil{}, 0, out} : R.Rd}

# LAW: the walk the server runs is the byte machine, and chunking does
# not change it either: a read however the socket cut it, and a stream
# however it was cut into reads, reads as the bytes whole.
law feed_buf_is_feed:
  for +b: Bytes()
  for +r: R.Rd
  {R.feed_buf(b, r) == R.feed(Bytes.to_list(b), r) : R.Rd}

law feed_buf_split:
  for +a: Bytes()
  for +b: Bytes()
  for +r: R.Rd
  {R.feed_buf(Bytes.append(a, b), r) == R.feed_buf(b, R.feed_buf(a, r)) : R.Rd}

law bad_feeds_buf:
  for +s: Bytes()
  for +out: List<&2, R.Val>
  {R.feed_buf(s, R.Rd{R.Bad{}, Nil{}, 0, out}) == R.Rd{R.Bad{}, Nil{}, 0, out} : R.Rd}

law reads_split:
  for +rs: List<&2, Bytes()>
  for +r: R.Rd
  {Wr.reads(~Unit, ~R.Rd, ~R.wstep, ~R.wadv, Unit{}, rs, r) ==
    R.feed_buf(Bytes.concat(rs), r) : R.Rd}

# LAW: what the five types read back as. These are the spec's own
# shapes, computed by the checker.
law reads_simple:
  {R.take(R.feed(Wr.bytes("+OK\r\n"), R.new())) ==
    (R.new(), [R.VStr{Wr.bytes("OK")}]) : R.Rd & List<&2, R.Val>}

law reads_error:
  {R.take(R.feed(Wr.bytes("-ERR unknown\r\n"), R.new())) ==
    (R.new(), [R.VErr{Wr.bytes("ERR unknown")}]) : R.Rd & List<&2, R.Val>}

law reads_int:
  {R.take(R.feed(Wr.bytes(":1000\r\n"), R.new())) ==
    (R.new(), [R.VInt{Wr.bytes("1000")}]) : R.Rd & List<&2, R.Val>}

law reads_bulk:
  {R.take(R.feed(Wr.bytes("$6\r\nfoobar\r\n"), R.new())) ==
    (R.new(), [R.VBulk{Wr.bytes("foobar")}]) : R.Rd & List<&2, R.Val>}

law reads_empty_bulk:
  {R.take(R.feed(Wr.bytes("$0\r\n\r\n"), R.new())) ==
    (R.new(), [R.VBulk{Nil{}}]) : R.Rd & List<&2, R.Val>}

law reads_null_bulk:
  {R.take(R.feed(Wr.bytes("$-1\r\n"), R.new())) ==
    (R.new(), [R.VNil{}]) : R.Rd & List<&2, R.Val>}

law reads_null_array:
  {R.take(R.feed(Wr.bytes("*-1\r\n"), R.new())) ==
    (R.new(), [R.VNil{}]) : R.Rd & List<&2, R.Val>}

law reads_empty_array:
  {R.take(R.feed(Wr.bytes("*0\r\n"), R.new())) ==
    (R.new(), [R.VArr{Nil{}}]) : R.Rd & List<&2, R.Val>}

# LAW: a command, which is what a client actually sends.
law reads_command:
  {R.take(R.feed(Wr.bytes("*2\r\n$4\r\nECHO\r\n$3\r\nhey\r\n"), R.new())) ==
    (R.new(), [R.VArr{[R.VBulk{Wr.bytes("ECHO")}, R.VBulk{Wr.bytes("hey")}]}]) :
    R.Rd & List<&2, R.Val>}

# LAW: an array inside an array. This is the one HTTP never had to
# answer, and it is why the reader carries a stack.
law reads_nested:
  {R.take(R.feed(Wr.bytes("*2\r\n*2\r\n:1\r\n:2\r\n+ok\r\n"), R.new())) ==
    (R.new(), [R.VArr{[R.VArr{[R.VInt{Wr.bytes("1")}, R.VInt{Wr.bytes("2")}]},
      R.VStr{Wr.bytes("ok")}]}]) : R.Rd & List<&2, R.Val>}

# LAW: two values in one chunk come out as two, in order, which is
# pipelining and costs the reader nothing.
law reads_two:
  {R.take(R.feed(Wr.bytes("+a\r\n+b\r\n"), R.new())) ==
    (R.new(), [R.VStr{Wr.bytes("a")}, R.VStr{Wr.bytes("b")}]) :
    R.Rd & List<&2, R.Val>}

# LAW: what is refused. A type byte no version of RESP has, a length
# that is not digits, and a bulk whose body does not end where it said.
law bad_type_byte:
  {R.dead(R.feed(Wr.bytes("?1\r\n"), R.new())) ==
    (R.Rd{R.Bad{}, Nil{}, 0, Nil{}}, True{}) : R.Rd & Bool}

law bad_length:
  {R.dead(R.feed(Wr.bytes("$x\r\n"), R.new())) ==
    (R.Rd{R.Bad{}, Nil{}, 0, Nil{}}, True{}) : R.Rd & Bool}

law bad_bulk_end:
  {R.dead(R.feed(Wr.bytes("$1\r\nabc\r\n"), R.new())) ==
    (R.Rd{R.Bad{}, Nil{}, 0, Nil{}}, True{}) : R.Rd & Bool}

# LAW: what the writer produces, which is what a client has to read.
law writes_simple:
  {R.simple("PONG") == Wr.bytes("+PONG\r\n") : List<&2, U32>}

law writes_bulk:
  {R.bulk(Wr.bytes("hey")) == Wr.bytes("$3\r\nhey\r\n") : List<&2, U32>}

law writes_empty_bulk:
  {R.bulk(Nil{}) == Wr.bytes("$0\r\n\r\n") : List<&2, U32>}

law writes_array:
  {R.array([R.bulk(Wr.bytes("a")), R.integer(7)]) ==
    Wr.bytes("*2\r\n$1\r\na\r\n:7\r\n") : List<&2, U32>}

# LAW: and the round trip -- what the writer writes, the reader reads
# back as what it was asked to write.
law round_trip_bulk:
  {R.take(R.feed(R.bulk(Wr.bytes("foobar")), R.new())) ==
    (R.new(), [R.VBulk{Wr.bytes("foobar")}]) : R.Rd & List<&2, R.Val>}

law round_trip_array:
  {R.take(R.feed(R.array([R.bulk(Wr.bytes("SET")), R.bulk(Wr.bytes("k"))]), R.new())) ==
    (R.new(), [R.VArr{[R.VBulk{Wr.bytes("SET")}, R.VBulk{Wr.bytes("k")}]}]) :
    R.Rd & List<&2, R.Val>}

# The server
# ==========
#
# The connection loop is bend-wire's, and its laws are proven once in
# wire/world.bend for every protocol's hooks. Here they are at RESP's:
# the loop in the model, then what it does.
def sim.conn(f: Nat, +srv: S.Cfg, sph: (WW.World & S.Plan()) & L.Hw, w: Nat) -> WW.World:
  WW.sim.conn(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, f, srv, sph, w)

def mute.conn(f: Nat, +srv: S.Cfg, sph: (WW.World & S.Plan()) & L.Hw, w: Nat) -> WW.World:
  WW.mute.conn(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, f, srv, sph, w)

def sim.segs(s: WW.World, xs: List<&2, L.Seg>, +ms: U32) -> L.Put(WW.World):
  WW.sim.segs(~L.no.shut, ~L.no.fhead, ~L.no.miss, ~L.no.lnote, ~L.no.lsize, s, xs, ms)

def sim.turn(+srv: S.Cfg, m: L.Put(WW.World), c: S.Conn, hw: L.Hw) ->
  (WW.World & S.Plan()) & L.Hw:
  WW.sim.turn(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.big(), srv, m, c, hw)

# LAW: a plan that ends the connection is its last act: its replies
# are written, and nothing is read; a Stop does nothing at all.
law end_is_last:
  for +srv: S.Cfg
  for w: WW.World
  for out: List<&2, L.Seg>
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {sim.conn(1n+g, srv, ((w, L.End{out}), hw), v) ==
    L.put.s(WW.World, sim.segs(w, out, S.idle(srv))) : WW.World}

law stop_is_last:
  for +srv: S.Cfg
  for w: WW.World
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {sim.conn(1n+g, srv, ((w, L.Stop{}), hw), v) == w : WW.World}

# LAW: replies go out before the next read.
law go_order:
  for +srv: S.Cfg
  for w: WW.World
  for out: List<&2, L.Seg>
  for +c: S.Conn
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {sim.conn(1n+g, srv, ((w, L.Go{out, c}), hw), v) ==
    sim.conn(g, srv, sim.turn(srv, sim.segs(w, out, S.idle(srv)), c,
      L.hw.next(L.no.mid(~S.Conn, c), L.NoHead{})), L.conn.waits()) : WW.World}

# LAW: nothing is done after a send fails.
law fail_go:
  for +srv: S.Cfg
  for g: Nat
  for v: Nat
  for m: L.Put(WW.World)
  for c: S.Conn
  for hw: L.Hw
  for e: {WW.put.done(m) == False{} : Bool}
  {sim.conn(g, srv, sim.turn(srv, m, c, hw), v) == L.put.s(WW.World, m) : WW.World}

# LAW: replies reach a peer that reads byte for byte, in order.
law segs_wire:
  for +xs: List<&2, L.Seg>
  for +ms: U32
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +e: {WW.raws(xs) == True{} : Bool}
  {sim.segs(WW.eager(rd, now, fs, out), xs, ms) ==
    WW.sent(rd, now, fs, Bytes.append(out, WW.wire(~L.no.shut, xs, False{}))) : L.Put(WW.World)}

# LAW: a peer that stops is let go within three turns, from any state.
law stall_ends:
  for +srv: S.Cfg
  for +w: WW.World
  for pl: S.Plan()
  for +hw: L.Hw
  for +g: Nat
  for +v: Nat
  {mute.conn(1n+1n+1n+g, srv, ((w, pl), hw), v) == mute.conn(1n+1n+1n, srv, ((w, pl), hw), v) :
    WW.World}

# LAW: RESP's own. A refused stream is answered with the replies its
# values earned before the refusal, then the error, and the connection
# ends there: whatever arrives after the refusal is never read, let
# alone answered.
law refuse_ends:
  for +cfg: S.Cfg
  for +buf: Bytes()
  for +out: List<&2, R.Val>
  for +kv: List<&2, S.Kv>
  {S.plan(cfg, buf, S.Conn{R.Rd{R.Bad{}, Nil{}, 0, out}, kv}) ==
    L.End{[L.Raw{Bytes.from_list(Wr.cat(S.ans.out(S.answer.all(kv, R.rev.vals(out))),
      R.error("ERR protocol error")))}]} : S.Plan()}
