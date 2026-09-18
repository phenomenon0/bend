# Shared string descriptors and overlapping payload views cross a ! transfer.
import Base

def work(+s: String) -> String:
  String.append(String.reverse(String.to_upper(s)), s)

def main() -> String & (String & String):
  +s = String.from_list(['a', 'b', '😀', 'c', 'd'])
  a b = work!(s) work!(String.slice(s, 1n, 4n))
  (a, (b, s))

#|("DC😀BAab😀cd", "C😀Bb😀c", "ab😀cd")
