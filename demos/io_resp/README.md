# io_resp

RESP, the Redis serialisation protocol, read and written in Bend. It
exists to test a claim rather than to serve Redis: that the reader
shape `demos/io_http_engine` found -- one structural walk over
whatever bytes arrive, the whole state in one node, never stopping --
is a shape other protocols fit, and that its laws come with it.

RESP is the harder case on purpose. HTTP framing is flat; RESP nests,
an array holding arrays holding bulk strings, so the reader carries a
stack and a finished value has to be handed to whatever was waiting
for it, which may itself finish.

## What works

`resp.bend` reads and writes all five RESP2 types with caps on a
bulk's length, an array's length and nesting depth, each refused at the
byte that announces it. `PROOF.bend` checks **24 laws**, first try:

- `feed_split` -- chunking does not change the read, the same
  four-line induction as the HTTP engine's, over a state that now
  includes the stack;
- `bad_absorbs` and `bad_feeds` -- broken framing stays broken;
- the five types read back as the spec says, empty and null included;
- a command, and an array inside an array;
- two values in one chunk, in order (pipelining, free);
- three refusals: an unknown type byte, a length that is not digits, a
  bulk whose body does not end where it said;
- what the writer writes, and the round trip through both.

    bend demos/io_resp/PROOF.bend

## What does not

`main.bend` is a Redis-protocol server -- PING, ECHO, SET, GET,
COMMAND, QUIT over the HTTP engine's connection loop -- and **it does
not check**: the checker runs for minutes rather than reporting. The
cause looks like the collision described below, and the file is here
because a half-finished honest thing is worth more than a deleted one.

## What this cost, which was the point of writing it

The reader and its laws were quick and went in clean. The server was
not, and every hour of it went to one thing: Bend's rules on shape.
Nothing here was a RESP problem.

- a `match` may not scrutinise a computed value, so every test becomes
  a parameter and a helper def;
- scrutinees must come in the order their binders were declared;
- mutual recursion is refused, so `find`, `drop` and the batch loop
  each had to be rewritten as one self-recursive def with the rest
  handed in as an argument -- which is how the base library writes
  `List.find`, and is a thing to know rather than to discover;
- a helper must precede its caller;
- a binder read twice needs `+`, and which ones do is found by trying.

**And twice, a name collision made the checker loop instead of
report.** A def namespace that shares a name with something in scope --
`tls.cert` called where a binder `tls` is live, `plan.close` where a
binder `close` is -- does not error, it runs for minutes. Every other
collision in this work reported at once and clearly. That is the one
thing here worth filing upstream.

## What it says about the library

The reader kit is real: the parser, its laws and its proofs took a
fraction of the time, and `feed_split` transferred without a change of
idea. The connection loop is not a protocol at all -- it is the same
two hundred lines of shape-fighting each time -- and that is exactly
what `bend-wire` should absorb, along with the byte helpers this file
had to re-type from the HTTP engine.
