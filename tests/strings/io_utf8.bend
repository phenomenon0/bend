# Actual File.read -> native decoding -> code-point rendering -> IO output.
# The byte fixture includes BOM, NUL, supplementary text, invalid sequences,
# and a truncated multibyte sequence. It is decoded one replacement per byte.
import Base

def codes(cs: List<&2, Char>) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case h <> t:
      U32.show(Char.to_u32(h)) <> codes(t)

def finish(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    s : String <- IO.pass(String, result)
    File.close(f)
    IO.print(String.join(codes(String.to_list(s)), ","))

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("tests/strings/utf8.bin", "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 128)
    finish(read)

#|65279,65,0,128512,65533,65533,65533,65533,65533,65533,65533,65533,65533,65533,65533
