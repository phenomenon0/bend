# All U32 values round-trip at Char level on every lane, including JS.
import Base

def main() -> List<&2, Char> & (List<&2, U32> & (Cmp & Bool)):
  ([Chr{55296}, Chr{56320}, Chr{1114112}, Chr{4294967295},
    Char.to_upper(Chr{4294967295}), Char.to_lower(Chr{55296})],
   ([Char.to_u32(Char.from_u32(55296)), Char.to_u32(Chr{4294967295})],
    (U32.cmp(Char.to_u32(Chr{4294967295}), Char.to_u32('😀')),
     Char.is_space(Chr{55296}))))

#|(['\u{d800}', '\u{dc00}', '\u{110000}', '\u{ffffffff}', '\u{ffffffff}', '\u{d800}'], [55296, 4294967295], GT{}, False{})
