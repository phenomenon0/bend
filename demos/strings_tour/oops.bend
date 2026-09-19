# This file does not compile, on purpose. A String is affine: a name is used
# once unless it is marked `+`. `line` below is consumed twice, so the checker
# rejects the def before anything runs; `+line: String` is the fix.
import Base

def shout(line: String) -> String:
  String.append(String.to_upper(line), line)

def main() -> String:
  shout("user=😀ana login ok")
