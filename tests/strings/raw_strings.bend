# C and interpret preserve raw U32 cells through views, transforms, lists and
# Map keys (Map.bit reads the 33-bit protocol off the raw cells).
# JS rejects at construction with the pinned raw_strings.js-error diagnostic.
import Base

def raw() -> String:
  SCon{Chr{55296}, SCon{Chr{56320}, SCon{Chr{4294967295}, SNil{}}}}

def bit(+s: String, p: Nat) -> Bool:
  Pair.snd(String, Bool, Map.bit(s, p))

def main() -> List<&2, String> & (List<&2, Char> & (Maybe<&2, Char> & (Cmp & (List<&2, Bool> & Nat)))):
  +s = raw()
  ([s, String.reverse(s), String.slice(s, 1n, 3n),
    String.from_list(String.to_list(s)), String.copy(s), String.to_upper(s),
    String.pad_start("a", 3n, Chr{4294967295}),
    String.pad_end("a", 3n, Chr{55296}), String.capitalize(s)],
   (String.to_list(s), (String.get(s, 1n), (String.order(s, String.reverse(s)),
    ([bit(s, 0n), bit(s, 1n), bit(s, 67n), bit(s, 98n), bit(s, 99n)],
     Pair.snd(Map<&2, Nat>, Nat, Map.get(Nat, 0n,
       Map.set(&2, Nat, Map.new(&2, Nat), s, 7n), s)))))))

#|(["\u{d800}\u{dc00}\u{ffffffff}", "\u{ffffffff}\u{dc00}\u{d800}", "\u{dc00}\u{ffffffff}", "\u{d800}\u{dc00}\u{ffffffff}", "\u{d800}\u{dc00}\u{ffffffff}", "\u{d800}\u{dc00}\u{ffffffff}", "\u{ffffffff}\u{ffffffff}a", "a\u{d800}\u{d800}", "\u{d800}\u{dc00}\u{ffffffff}"], ['\u{d800}', '\u{dc00}', '\u{ffffffff}'], Some{'\u{dc00}'}, LT{}, [True{}, False{}, True{}, True{}, False{}], 7n)
