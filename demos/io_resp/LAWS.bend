# The laws of the RESP reader. They are the HTTP engine's laws with the
# nouns changed, which is the point of writing this file at all: the
# reader shape carries its properties with it.
import Base
import ./resp.bend as R

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

# LAW: what the five types read back as. These are the spec's own
# shapes, computed by the checker.
law reads_simple:
  {R.take(R.feed(R.bytes("+OK\r\n"), R.new())) ==
    (R.new(), [R.VStr{R.bytes("OK")}]) : R.Rd & List<&2, R.Val>}

law reads_error:
  {R.take(R.feed(R.bytes("-ERR unknown\r\n"), R.new())) ==
    (R.new(), [R.VErr{R.bytes("ERR unknown")}]) : R.Rd & List<&2, R.Val>}

law reads_int:
  {R.take(R.feed(R.bytes(":1000\r\n"), R.new())) ==
    (R.new(), [R.VInt{R.bytes("1000")}]) : R.Rd & List<&2, R.Val>}

law reads_bulk:
  {R.take(R.feed(R.bytes("$6\r\nfoobar\r\n"), R.new())) ==
    (R.new(), [R.VBulk{R.bytes("foobar")}]) : R.Rd & List<&2, R.Val>}

law reads_empty_bulk:
  {R.take(R.feed(R.bytes("$0\r\n\r\n"), R.new())) ==
    (R.new(), [R.VBulk{Nil{}}]) : R.Rd & List<&2, R.Val>}

law reads_null_bulk:
  {R.take(R.feed(R.bytes("$-1\r\n"), R.new())) ==
    (R.new(), [R.VNil{}]) : R.Rd & List<&2, R.Val>}

law reads_null_array:
  {R.take(R.feed(R.bytes("*-1\r\n"), R.new())) ==
    (R.new(), [R.VNil{}]) : R.Rd & List<&2, R.Val>}

law reads_empty_array:
  {R.take(R.feed(R.bytes("*0\r\n"), R.new())) ==
    (R.new(), [R.VArr{Nil{}}]) : R.Rd & List<&2, R.Val>}

# LAW: a command, which is what a client actually sends.
law reads_command:
  {R.take(R.feed(R.bytes("*2\r\n$4\r\nECHO\r\n$3\r\nhey\r\n"), R.new())) ==
    (R.new(), [R.VArr{[R.VBulk{R.bytes("ECHO")}, R.VBulk{R.bytes("hey")}]}]) :
    R.Rd & List<&2, R.Val>}

# LAW: an array inside an array. This is the one HTTP never had to
# answer, and it is why the reader carries a stack.
law reads_nested:
  {R.take(R.feed(R.bytes("*2\r\n*2\r\n:1\r\n:2\r\n+ok\r\n"), R.new())) ==
    (R.new(), [R.VArr{[R.VArr{[R.VInt{R.bytes("1")}, R.VInt{R.bytes("2")}]},
      R.VStr{R.bytes("ok")}]}]) : R.Rd & List<&2, R.Val>}

# LAW: two values in one chunk come out as two, in order, which is
# pipelining and costs the reader nothing.
law reads_two:
  {R.take(R.feed(R.bytes("+a\r\n+b\r\n"), R.new())) ==
    (R.new(), [R.VStr{R.bytes("a")}, R.VStr{R.bytes("b")}]) :
    R.Rd & List<&2, R.Val>}

# LAW: what is refused. A type byte no version of RESP has, a length
# that is not digits, and a bulk whose body does not end where it said.
law bad_type_byte:
  {R.dead(R.feed(R.bytes("?1\r\n"), R.new())) ==
    (R.Rd{R.Bad{}, Nil{}, 0, Nil{}}, True{}) : R.Rd & Bool}

law bad_length:
  {R.dead(R.feed(R.bytes("$x\r\n"), R.new())) ==
    (R.Rd{R.Bad{}, Nil{}, 0, Nil{}}, True{}) : R.Rd & Bool}

law bad_bulk_end:
  {R.dead(R.feed(R.bytes("$1\r\nabc\r\n"), R.new())) ==
    (R.Rd{R.Bad{}, Nil{}, 0, Nil{}}, True{}) : R.Rd & Bool}

# LAW: what the writer produces, which is what a client has to read.
law writes_simple:
  {R.simple("PONG") == R.bytes("+PONG\r\n") : List<&2, U32>}

law writes_bulk:
  {R.bulk(R.bytes("hey")) == R.bytes("$3\r\nhey\r\n") : List<&2, U32>}

law writes_empty_bulk:
  {R.bulk(Nil{}) == R.bytes("$0\r\n\r\n") : List<&2, U32>}

law writes_array:
  {R.array([R.bulk(R.bytes("a")), R.integer(7)]) ==
    R.bytes("*2\r\n$1\r\na\r\n:7\r\n") : List<&2, U32>}

# LAW: and the round trip -- what the writer writes, the reader reads
# back as what it was asked to write.
law round_trip_bulk:
  {R.take(R.feed(R.bulk(R.bytes("foobar")), R.new())) ==
    (R.new(), [R.VBulk{R.bytes("foobar")}]) : R.Rd & List<&2, R.Val>}

law round_trip_array:
  {R.take(R.feed(R.array([R.bulk(R.bytes("SET")), R.bulk(R.bytes("k"))]), R.new())) ==
    (R.new(), [R.VArr{[R.VBulk{R.bytes("SET")}, R.VBulk{R.bytes("k")}]}]) :
    R.Rd & List<&2, R.Val>}
