# The proofs of power/deflate_laws.bend.
import Base
import ../wire/reader.bend as Wr
import ./deflate.bend as D
import ./gzip.bend as Z
import ./deflate_laws.bend as Laws

# The reads
# =========
#
# The inflate machine and the gunzip machine are byte-step readers; the
# reader kit (wire/reader.bend) proves chunking once for every such
# reader, and a one-byte move needs no obligation but the kit's own.

def Laws.inflate_split(a, b, st):
  Wr.feed_split(~Unit, ~D.St, ~D.wstep, Unit{}, a, b, st)

def adv_ok(+e: Unit, +s: Bytes(), p: D.St) ->
  {Wr.feed_buf.last(~Unit, ~D.St, ~D.wstep, e, D.wadv(e, s, p)) ==
    Wr.feed_buf.slow(~Unit, ~D.St, ~D.wstep, e, s, p) : D.St}:
  Wr.one.step_ok(~Unit, ~D.St, ~D.wstep, e, s, p)

def Laws.inflate_buf(s, st):
  Wr.feed_buf_is_feed(~Unit, ~D.St, ~D.wstep, ~D.wadv, ~adv_ok, Unit{}, s, st)

def Laws.inflate_buf_split(a, b, st):
  Wr.feed_buf_split(~Unit, ~D.St, ~D.wstep, ~D.wadv, ~adv_ok, Unit{}, a, b, st)

def Laws.gunzip_split(a, b, g):
  Wr.feed_split(~Unit, ~Z.G, ~Z.wstep, Unit{}, a, b, g)

def gz_adv_ok(+e: Unit, +s: Bytes(), p: Z.G) ->
  {Wr.feed_buf.last(~Unit, ~Z.G, ~Z.wstep, e, Z.wadv(e, s, p)) ==
    Wr.feed_buf.slow(~Unit, ~Z.G, ~Z.wstep, e, s, p) : Z.G}:
  Wr.one.step_ok(~Unit, ~Z.G, ~Z.wstep, e, s, p)

def Laws.gunzip_buf(s, g):
  Wr.feed_buf_is_feed(~Unit, ~Z.G, ~Z.wstep, ~Z.wadv, ~gz_adv_ok, Unit{}, s, g)

# The fixed points
# ----------------
#
# A byte is eight steps and the bit offset goes round once: from any of
# the eight offsets a refused (or ended) machine is where it was.

type B8 is Data:
  O0{}
  O1{}
  O2{}
  O3{}
  O4{}
  O5{}
  O6{}
  O7{}

def b8n(k: B8) -> Nat:
  match k:
    case O0{}:
      0n
    case O1{}:
      1n
    case O2{}:
      2n
    case O3{}:
      3n
    case O4{}:
      4n
    case O5{}:
      5n
    case O6{}:
      6n
    case O7{}:
      7n

type Held is Data:
  HBad{why: D.Why, o: D.O, k: B8}
  HEnd{o: D.O, k: B8}

def held(x: Held) -> D.St:
  match x:
    case HBad{why, o, k}:
      D.St{D.Bad{why}, o, b8n(k)}
    case HEnd{o, k}:
      D.St{D.End{}, o, b8n(k)}

def held_fix(+e: Unit, +x: Held, +c: U32) -> {D.wstep(e, held(x), c) == held(x) : D.St}:
  match x:
    case HBad{why, o, k}:
      match k:
        case O0{}:
          {==}
        case O1{}:
          {==}
        case O2{}:
          {==}
        case O3{}:
          {==}
        case O4{}:
          {==}
        case O5{}:
          {==}
        case O6{}:
          {==}
        case O7{}:
          {==}
    case HEnd{o, k}:
      match k:
        case O0{}:
          {==}
        case O1{}:
          {==}
        case O2{}:
          {==}
        case O3{}:
          {==}
        case O4{}:
          {==}
        case O5{}:
          {==}
        case O6{}:
          {==}
        case O7{}:
          {==}

def held_feeds(+s: List<&2, U32>, +x: Held) ->
  {D.feed_list(s, held(x)) == held(x) : D.St}:
  Wr.bad_feeds(~Unit, ~D.St, ~D.wstep, ~Held, ~held, ~held_fix, Unit{}, s, x)

def bad_at(+s: List<&2, U32>, +why: D.Why, +o: D.O, +bp: Nat) ->
  {Nat.is_lt(bp, 8n) == True{} : Bool} -> {D.feed_list(s, D.St{D.Bad{why}, o, bp}) == D.St{D.Bad{why}, o, bp} : D.St}:
  match bp:
    case 0n:
      lt => held_feeds(s, HBad{why, o, O0{}})
    case 1n+p0:
      match p0:
        case 0n:
          lt => held_feeds(s, HBad{why, o, O1{}})
        case 1n+p1:
          match p1:
            case 0n:
              lt => held_feeds(s, HBad{why, o, O2{}})
            case 1n+p2:
              match p2:
                case 0n:
                  lt => held_feeds(s, HBad{why, o, O3{}})
                case 1n+p3:
                  match p3:
                    case 0n:
                      lt => held_feeds(s, HBad{why, o, O4{}})
                    case 1n+p4:
                      match p4:
                        case 0n:
                          lt => held_feeds(s, HBad{why, o, O5{}})
                        case 1n+p5:
                          match p5:
                            case 0n:
                              lt => held_feeds(s, HBad{why, o, O6{}})
                            case 1n+p6:
                              match p6:
                                case 0n:
                                  lt => held_feeds(s, HBad{why, o, O7{}})
                                case 1n+p7:
                                  lt => Nat.lt_zero({D.feed_list(s, D.St{D.Bad{why}, o, 8n+p7}) == D.St{D.Bad{why}, o, 8n+p7} : D.St}, p7, lt)

def end_at(+s: List<&2, U32>, +o: D.O, +bp: Nat) ->
  {Nat.is_lt(bp, 8n) == True{} : Bool} -> {D.feed_list(s, D.St{D.End{}, o, bp}) == D.St{D.End{}, o, bp} : D.St}:
  match bp:
    case 0n:
      lt => held_feeds(s, HEnd{o, O0{}})
    case 1n+p0:
      match p0:
        case 0n:
          lt => held_feeds(s, HEnd{o, O1{}})
        case 1n+p1:
          match p1:
            case 0n:
              lt => held_feeds(s, HEnd{o, O2{}})
            case 1n+p2:
              match p2:
                case 0n:
                  lt => held_feeds(s, HEnd{o, O3{}})
                case 1n+p3:
                  match p3:
                    case 0n:
                      lt => held_feeds(s, HEnd{o, O4{}})
                    case 1n+p4:
                      match p4:
                        case 0n:
                          lt => held_feeds(s, HEnd{o, O5{}})
                        case 1n+p5:
                          match p5:
                            case 0n:
                              lt => held_feeds(s, HEnd{o, O6{}})
                            case 1n+p6:
                              match p6:
                                case 0n:
                                  lt => held_feeds(s, HEnd{o, O7{}})
                                case 1n+p7:
                                  lt => Nat.lt_zero({D.feed_list(s, D.St{D.End{}, o, 8n+p7}) == D.St{D.End{}, o, 8n+p7} : D.St}, p7, lt)

def Laws.inflate_bad(s, why, o, bp, lt):
  bad_at(s, why, o, bp)(lt)

def Laws.inflate_end(s, o, bp, lt):
  end_at(s, o, bp)(lt)

type GB is Data:
  GB{at: Nat, why: Z.Why, done: Bytes(), crc: U32, cap: Nat, pos: Nat}

def gb(x: GB) -> Z.G:
  match x:
    case GB{at, why, done, crc, cap, pos}:
      Z.G{Z.Bad{at, why}, done, crc, cap, pos}

def gb_fix(+e: Unit, +x: GB, +c: U32) -> {Z.wstep(e, gb(x), c) == gb(x) : Z.G}:
  match x:
    case GB{at, why, done, crc, cap, pos}:
      {==}

def Laws.gunzip_bad(s, at, why, done, crc, cap, pos):
  Wr.bad_feeds(~Unit, ~Z.G, ~Z.wstep, ~GB, ~gb, ~gb_fix, Unit{}, s, GB{at, why, done, crc, cap, pos})

