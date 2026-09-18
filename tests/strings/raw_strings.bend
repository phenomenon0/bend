# C and interpret preserve raw U32 cells through views, transforms and lists.
# JS rejects at construction with the pinned raw_strings.js-error diagnostic.
import Base

def raw() -> String:
  SCon{Chr{55296}, SCon{Chr{56320}, SCon{Chr{4294967295}, SNil{}}}}

def main() -> List<&2, String> & (List<&2, Char> & (Maybe<&2, Char> & Cmp)):
  +s = raw()
  ([s, String.reverse(s), String.slice(s, 1n, 3n),
    String.from_list(String.to_list(s)), String.copy(s), String.to_upper(s),
    String.pad_start("a", 3n, Chr{4294967295}),
    String.pad_end("a", 3n, Chr{55296}), String.capitalize(s)],
   (String.to_list(s), (String.get(s, 1n), String.order(s, String.reverse(s)))))

#|(["\u{d800}\u{dc00}\u{ffffffff}", "\u{ffffffff}\u{dc00}\u{d800}", "\u{dc00}\u{ffffffff}", "\u{d800}\u{dc00}\u{ffffffff}", "\u{d800}\u{dc00}\u{ffffffff}", "\u{d800}\u{dc00}\u{ffffffff}", "\u{ffffffff}\u{ffffffff}a", "a\u{d800}\u{d800}", "\u{d800}\u{dc00}\u{ffffffff}"], ['\u{d800}', '\u{dc00}', '\u{ffffffff}'], Some{'\u{dc00}'}, LT{})
