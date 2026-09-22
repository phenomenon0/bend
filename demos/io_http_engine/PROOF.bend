# The proofs of the HTTP engine laws.
#
# feed_split and bad_feeds are inductions on the chunk: feed walks the
# string structurally and ++ builds it the same way, so in the cons
# case both sides step the reader once and the induction hypothesis is
# already the goal. bad_absorbs and the five reply laws compute: the
# machine's last row sends Bad{} to Bad{} whatever the byte class is,
# and each written-out reply normalises to the same string the builder
# does.
import Base
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./LAWS.bend as Laws

def Laws.feed_split(a, b, p):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.feed_split(t, b, Eng.step(p, c))

def Laws.bad_absorbs(c, pd, out):
  {==}

def Laws.bad_feeds(s, pd, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.bad_feeds(t, pd, out)

def Laws.health_is_built():
  {==}

def Laws.root_is_built():
  {==}

def Laws.missing_is_built():
  {==}

def Laws.method_is_built():
  {==}

def Laws.bad_is_built():
  {==}

def Laws.head_of_health():
  {==}

def Laws.head_of_missing():
  {==}

def Laws.route_health():
  {==}

def Laws.route_root():
  {==}

def Laws.route_echo():
  {==}

def Laws.route_events():
  {==}

def Laws.route_missing():
  {==}

def Laws.route_files():
  {==}

def Laws.route_files_index():
  {==}

def Laws.route_files_fixed():
  {==}

def Laws.routes_distinct():
  {==}

def Laws.routes_distinct_root():
  {==}

def Laws.route_empty(path):
  {==}

def Laws.norm_climb():
  {==}

def Laws.norm_deep_climb():
  {==}

def Laws.norm_dots():
  {==}

def Laws.norm_flat():
  {==}

def Laws.sha1_empty():
  {==}

def Laws.sha1_abc():
  {==}

def Laws.sha1_two_blocks():
  {==}

def Laws.b64_empty():
  {==}

def Laws.b64_f():
  {==}

def Laws.b64_fo():
  {==}

def Laws.b64_foo():
  {==}

def Laws.b64_foob():
  {==}

def Laws.b64_fooba():
  {==}

def Laws.b64_foobar():
  {==}

def Laws.ws_accept():
  {==}
