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
byte that announces it. `PROOF.bend` checks **23 laws**, first try:

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

## The server

`main.bend` is a Redis-protocol server -- PING, ECHO, SET, GET,
COMMAND, QUIT -- on bend-wire (`wire/`, whose README takes it as the
worked example): the connection loop, its budgets, the accept loop with
a connection limit and SIGTERM, and their laws are the library's. What
is RESP's is the planner, from a read's bytes through the reader and
the commands to the replies, and the hooks. `bend main.bend -o respd
&& ./respd 6380`.

`PROOF.bend` now checks 34 laws: the reader's 23; the block walk's four
(`feed_buf_is_feed`, `feed_buf_split`, `bad_feeds_buf`, `reads_split`),
instances of the reader kit's; the loop's, at RESP's hooks
(`end_is_last`, `stop_is_last`, `go_order`, `fail_go`, `segs_wire`,
`stall_ends`), instances of `wire/world.bend`'s; and one of its own,
`refuse_ends`: a refused stream is answered with what its values
earned, then the error, and the connection ends.

## What it cost, before and after

Before bend-wire the server was 147 lines (121 of code), every one of
them the HTTP engine's connection-loop shape re-typed, with none of its
budgets and none of its laws; every hour of it went to Bend's rules on
shape (a `match` on parameters only, scrutinees in binder order, no
mutual recursion). On bend-wire it is 102 lines (69 of code), of which
the planner is 36 and the rest a configuration record and the hooks;
the byte helpers are the reader kit's. It gained the head and batch
budgets, the send deadline, a connection limit, graceful stopping and
the loop's laws.
