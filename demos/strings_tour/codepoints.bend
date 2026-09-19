# Code points are the unit: length, index, reverse and order all count
# scalars, never UTF-16 halves or UTF-8 bytes. The last three rows are the
# honest ones: case and trim are ASCII-only, and a combining mark is its own
# code point (a grapheme is not the unit). run_tour.sh prints one measured
# footnote from Python or JS under each row.
import Base
import ../text/slices.bend as Slices

def main() -> IO(Unit):
  IO.print(String.join([
    Slices.row("length \"A😀é\"", Nat.show(String.length("A😀é"))),
    Slices.row("reverse \"A😀é\"", String.reverse("A😀é")),
    Slices.row("U+E000 < \"😀\"", Bool.show(String.is_lt("\u{e000}", "😀"))),
    Slices.row("to_upper \"éßıa\"", String.to_upper("éßıa")),
    Slices.row("length trim NBSP·x·NBSP", Nat.show(String.length(String.trim("\u{a0}x\u{a0}")))),
    Slices.row("reverse \"e\u{301}😀\"", String.reverse("e\u{301}😀"))], "\n"))
