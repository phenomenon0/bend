# F08 (the library self_prefix.bend imports): a def `at` and a def
# `self_prefix_lib.at`. Canon reads the second as the file's own `at` and
# refuses it as a duplicate declaration; power/deflate.bend had `at` and
# `deflate.at` side by side.
import Base

def at(x: U32) -> U32:
  x

def self_prefix_lib.at(x: U32) -> U32:
  U32.inc(x)
