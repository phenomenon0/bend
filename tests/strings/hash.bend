# hash: FNV-1a 32 over four little-endian bytes per code point; vectors
# computed independently in Python (seed 2166136261, prime 16777619)
import Base

def main() -> U32 & (U32 & (U32 & (U32 & U32))):
  (String.hash(""), (String.hash("a"), (String.hash("abc"), (String.hash("hello world"), String.hash("é中😀")))))

#|(2166136261, 4125217764, 4070381781, 3112970261, 3781327616)
