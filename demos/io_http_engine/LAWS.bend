# The laws of the HTTP engine. The human states them; PROOF.bend must
# prove them. They pin the three things a byte-at-a-time protocol
# reader has to get right, and the one optimisation that would
# otherwise be a comment nobody checks.
import Base
import ./main.bend as Eng

# LAW: chunking does not change the parse. Feeding a chunk and then
# another one lands exactly where feeding the two joined would have.
# This is the property that makes the reader safe against however TCP
# decides to split a message: a head cut in the middle of a field name,
# a body cut mid-byte, or three requests arriving in one segment all
# parse the same as the whole stream. It is also what lets the engine
# keep no buffer of its own.
law feed_split:
  for +a: String
  for +b: String
  for +p: Eng.P
  {Eng.feed(a ++ b, p) == Eng.feed(b, Eng.feed(a, p)) : Eng.P}

# LAW: a broken grammar stays broken. No byte moves the reader out of
# Bad{}, so once a message has been refused nothing later in the stream
# can revive it. Without this a smuggled request could follow a refused
# one on the same connection and be served.
law bad_absorbs:
  for +c: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.step(Eng.P{Eng.Bad{}, pd, out}, c) ==
    Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: and it stays broken for a whole chunk, not just one byte.
law bad_feeds:
  for +s: String
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.feed(s, Eng.P{Eng.Bad{}, pd, out}) ==
    Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: the replies the engine keeps ready are the replies it would have
# built. Writing a fixed reply out by hand is worth roughly a third of
# the cost of serving a request, and it is exactly the kind of shortcut
# that rots: these five say the shortcut is the same bytes, so the
# checker refuses the engine if anyone edits one without the other.
law health_is_built:
  {Eng.resp.health() ==
    Eng.reply("200 OK", "application/json", "{\"ok\":true}") : String}

law root_is_built:
  {Eng.resp.root() ==
    Eng.reply("200 OK", "text/plain", "bend-http\n") : String}

law missing_is_built:
  {Eng.resp.missing() ==
    Eng.reply("404 Not Found", "text/plain", "no route\n") : String}

law method_is_built:
  {Eng.resp.method() ==
    Eng.reply("405 Method Not Allowed", "text/plain", "no method\n") : String}

law bad_is_built:
  {Eng.resp.bad() ==
    Eng.reply("400 Bad Request", "text/plain", "bad request\n") : String}
