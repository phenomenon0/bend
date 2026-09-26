# F07: Base is the one library a file imports by name; anything else is
# `import <path>.bend as <Name>`, relative or from the hub. A second
# standard module (bend2/time.bend, say) could not be `import Time`
# without a change to bend.ts, so the whole standard library lives in
# base.bend, under one ttok cap (U15).
import Time

def main() -> U32:
  7
