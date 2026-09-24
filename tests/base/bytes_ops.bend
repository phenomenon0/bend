# bend3's Bytes module (encode/pack) has no bend surface: base's Bytes
# is a String of bytes (tests/base/bytes_buf.bend) and has no encode --
# the head call is an undefined name
import Base

law main:
  U32

def main():
  Bytes.encode("banana")

#|Error:
#|- expected : a defined name
#|- observed : Bytes.encode
#|Location: main
#| 9 | def main():
#|10>|   Bytes.encode("banana")
#|11 |
#|exit 1
