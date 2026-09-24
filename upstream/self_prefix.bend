# F08: a def whose name starts with its own file's name is that file's
# name without it. self_prefix_lib.bend defines `at` and
# `self_prefix_lib.at`; canon refuses the second ("a fresh name (duplicate
# declaration: self_prefix_lib.at)"), where this repo's older checker
# keeps them apart.
import Base
import ./self_prefix_lib.bend as L

def main() -> U32:
  L.self_prefix_lib.at(1)

#|2
