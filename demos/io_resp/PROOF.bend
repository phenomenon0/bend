# The proofs. feed_split, bad_feeds and the block walk's laws are the
# reader kit's (wire/reader.bend), instantiated at R.step: RESP proves
# only its obligation, that a refused reader is a fixed point of the
# step (bad_absorbs, which computes). The server's laws are the loop's
# (wire/world.bend) at RESP's hooks. Everything else computes.
import Base
import ../../wire/reader.bend as Wr
import ../../wire/loop.bend as L
import ../../wire/world.bend as WW
import ./resp.bend as R
import ./main.bend as S
import ./LAWS.bend as Laws

def Laws.feed_split(a, b, r):
  Wr.feed_split(~Unit, ~R.Rd, ~R.wstep, Unit{}, a, b, r)

def Laws.bad_absorbs(c, up, deep, out):
  {==}

# the refused reader, and the kit's obligation for it
def bad(out: List<&2, R.Val>) -> R.Rd:
  R.Rd{R.Bad{}, Nil{}, 0, out}

def absorbs(+u: Unit, +out: List<&2, R.Val>, +c: U32) ->
  {R.wstep(u, bad(out), c) == bad(out) : R.Rd}:
  Laws.bad_absorbs(c, Nil{}, 0, out)

def Laws.bad_feeds(s, out):
  Wr.bad_feeds(~Unit, ~R.Rd, ~R.wstep, ~List<&2, R.Val>, ~bad, ~absorbs, Unit{}, s, out)

def Laws.feed_buf_is_feed(b, r):
  Wr.feed_buf_is_feed(~Unit, ~R.Rd, ~R.wstep, ~R.wadv,
    ~Wr.one.step_ok(~Unit, ~R.Rd, ~R.wstep), Unit{}, b, r)

def Laws.feed_buf_split(a, b, r):
  Wr.feed_buf_split(~Unit, ~R.Rd, ~R.wstep, ~R.wadv,
    ~Wr.one.step_ok(~Unit, ~R.Rd, ~R.wstep), Unit{}, a, b, r)

def Laws.bad_feeds_buf(s, out):
  Wr.bad_feeds_buf(~Unit, ~R.Rd, ~R.wstep, ~R.wadv, ~Wr.one.step_ok(~Unit, ~R.Rd, ~R.wstep),
    ~List<&2, R.Val>, ~bad, ~absorbs, Unit{}, s, out)

def Laws.reads_split(rs, r):
  Wr.reads_split(~Unit, ~R.Rd, ~R.wstep, ~R.wadv, ~Wr.one.step_ok(~Unit, ~R.Rd, ~R.wstep),
    Unit{}, rs, r)

def Laws.reads_simple():
  {==}

def Laws.reads_error():
  {==}

def Laws.reads_int():
  {==}

def Laws.reads_bulk():
  {==}

def Laws.reads_empty_bulk():
  {==}

def Laws.reads_null_bulk():
  {==}

def Laws.reads_null_array():
  {==}

def Laws.reads_empty_array():
  {==}

def Laws.reads_command():
  {==}

def Laws.reads_nested():
  {==}

def Laws.reads_two():
  {==}

def Laws.bad_type_byte():
  {==}

def Laws.bad_length():
  {==}

def Laws.bad_bulk_end():
  {==}

def Laws.writes_simple():
  {==}

def Laws.writes_bulk():
  {==}

def Laws.writes_empty_bulk():
  {==}

def Laws.writes_array():
  {==}

def Laws.round_trip_bulk():
  {==}

def Laws.round_trip_array():
  {==}

# The server: the loop's laws are wire/world.bend's, at RESP's hooks.
# The one obligation (stall_ends: an event is never empty) is the
# default event's, discharged in wire/world.bend (no.event_ok).
def Laws.end_is_last(srv, w, out, hw, g, v):
  WW.end_is_last(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, w, out, hw, g, v)

def Laws.stop_is_last(srv, w, hw, g, v):
  WW.stop_is_last(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, w, hw, g, v)

def Laws.go_order(srv, w, out, c, hw, g, v):
  WW.go_order(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, w, out, c, hw, g, v)

def Laws.fail_go(srv, g, v, m, c, hw, e):
  WW.fail_go(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, g, v, m, c, hw, e)

def Laws.segs_wire(xs, ms, rd, now, fs, out, e):
  WW.segs_wire(~L.no.shut, ~L.no.fhead, ~L.no.miss, ~L.no.lnote, ~L.no.lsize, xs, ms, rd, now, fs, out, e)

def Laws.stall_ends(srv, w, pl, hw, g, v):
  WW.stall_ends(~S.Cfg, ~S.Conn, ~Unit, ~S.idle, ~S.idle, ~S.plan, ~L.no.mid(~S.Conn), ~L.no.big(),
    ~L.no.uplan(~S.Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, ~WW.no.event_ok, srv, w, pl, hw, g, v)

# a refused reader takes nothing more (the kit's bad_feeds_buf), and
# the rest computes
def Laws.refuse_ends(cfg, buf, out, kv):
  %Equal.sym(R.Rd, R.feed_buf(buf, R.Rd{R.Bad{}, Nil{}, 0, out}), R.Rd{R.Bad{}, Nil{}, 0, out},
    Laws.bad_feeds_buf(buf, out)) :
    {S.plan.took(kv, R.take(_)) ==
      L.End{[L.Raw{Bytes.from_list(Wr.cat(S.ans.out(S.answer.all(kv, R.rev.vals(out))),
        R.error("ERR protocol error")))}]} : S.Plan()}
  {==}
