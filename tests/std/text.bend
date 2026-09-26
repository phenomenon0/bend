# std/text.bend: UTF-8 both ways (every length of character, U+FFFD for
# each ill-formed stretch WHATWG's decoder replaces, valid), numbers out of
# text, padding, split_on and replace, and the hash (this repo's
# String.hash values). Byte lists print as numbers, text as itself.
import Base
import ../../std/bytes.bend as By
import ../../std/text.bend as Text

def bytes.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ U32.show(x) ++ bytes.go(t)

def bytes(b: String) -> String:
  "[" ++ bytes.go(By.to_list(b)) ++ " ]"

def cps.go(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{c}, t}:
      " " ++ U32.show(c) ++ cps.go(t)

def cps(s: String) -> String:
  "<" ++ cps.go(s) ++ " >"

def flag(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def nat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{n}:
      Nat.show(n)

def u32(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{n}:
      U32.show(n)

def f32(m: Maybe<&2, F32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{x}:
      F32.show(x)

def list(xs: List<&2, String>) -> String:
  "[" ++ String.join(xs, "|") ++ "]"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(bytes(Text.encode("aé€\u{1d11e}")))
    IO.print(cps(Text.decode(By.from_list([97, 195, 169, 226, 130, 172, 240, 157, 132, 158]))))
    IO.print(Text.decode(By.from_list([99, 97, 102, 195, 169])))
    IO.print(cps(Text.decode(By.from_list([128, 97, 195, 40, 224, 128, 175, 237, 160, 128, 244, 144, 128, 128, 240, 159, 152]))))
    IO.print(flag(Text.valid(Text.encode("日本語"))) ++ " " ++ flag(Text.valid(By.from_list([192, 128]))) ++ " " ++
      flag(Text.valid(By.from_list([237, 159, 191]))) ++ " " ++ flag(Text.valid(By.from_list([237, 160, 128]))))
    IO.print(nat(Text.nat("12345")) ++ " " ++ nat(Text.nat("12a")) ++ " " ++ nat(Text.nat("")))
    IO.print(u32(Text.u32("4294967295")) ++ " " ++ u32(Text.u32("4294967296")))
    IO.print(f32(Text.f32("3.25")) ++ " " ++ f32(Text.f32("-1e3")) ++ " " ++ f32(Text.f32("x")))
    IO.print("[" ++ Text.pad_start("42", 5n, '0') ++ "][" ++ Text.pad_end("ab", 4n, '.') ++ "][" ++ Text.pad_start("toolong", 3n, ' ') ++ "]")
    IO.print(list(Text.split_on("a, b,, c", ", ")) ++ " " ++ list(Text.split_on("", ",")) ++ " " ++ list(Text.split_on(",x,", ",")))
    IO.print(Text.replace("the cat sat on the mat", "at", "og") ++ " " ++ Text.replace("aaa", "aa", "b") ++ " " ++ Text.replace("abc", "", "-"))
    IO.print(U32.show(Text.hash("")) ++ " " ++ U32.show(Text.hash("bend")) ++ " " ++ U32.show(Text.hash("é")))

#|[ 97 195 169 226 130 172 240 157 132 158 ]
#|< 97 233 8364 119070 >
#|café
#|< 65533 97 65533 40 65533 65533 65533 65533 65533 65533 65533 65533 65533 65533 65533 >
#|yes no yes no
#|12345 none none
#|4294967295 none
#|3.25 -1000 none
#|[00042][ab..][toolong]
#|[a|b,|c] [] [|x|]
#|the cog sog on the mog ba abc
#|2166136261 3905159256 1629766636
