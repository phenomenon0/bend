# The proofs. feed_split and bad_feeds are inductions on the chunk, the
# same four lines as the HTTP engine's and for the same reason: feed
# walks a list structurally and ++ builds it the same way. Everything
# else computes.
import Base
import ./resp.bend as R
import ./LAWS.bend as Laws

def Laws.feed_split(a, b, r):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.feed_split(t, b, R.step(r, c))

def Laws.bad_absorbs(c, up, deep, out):
  {==}

def Laws.bad_feeds(s, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.bad_feeds(t, out)

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
