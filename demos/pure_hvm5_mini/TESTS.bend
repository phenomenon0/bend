# HVM5 in Bend -- the numeric tests. Each case is a program this
# evaluator parses, normalizes and prints exactly as main.bend runs
# its own: the case's name, then the normal form and the interaction
# count. The `#|` block at the end is what the run must print, the
# repo's test convention; run.sh builds this file and diffs it.
#
# Every case has an hvm4 twin, eight of them files of its devs/test:
# docs/omen/lanes/hvm5-num.md tables the port's count beside the
# reference's. The one standing difference is the counter's floor:
# hvm4 charges nothing for a reference, this machine (hvm5.c's)
# charges one, so a case reads one higher per @ref it expands --
# two_ref expands two and reads two higher.

import Base
import ./main.bend as Hvm

# a program parsed and run, as Hvm.main runs its own
def one(src: String) -> IO(Unit):
  Hvm.prog()(Hvm.book_run, Hvm.st_new(src, Nil{}, 1, Hvm.Names{Map.new(&2, U32), 0}))

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- IO.print("== add")
    Unit <- one("@main = (((1 + 2) + 3) + 4);\n")
    Unit <- IO.print("== mul")
    Unit <- one("@main = ((2 * 3) + (4 * 5));\n")
    Unit <- IO.print("== divmod")
    Unit <- one("@main = ((20 / 4) + (17 % 5));\n")
    Unit <- IO.print("== xor")
    Unit <- one("@main = (12 ^ 10);\n")
    Unit <- IO.print("== shift")
    Unit <- one("@main = ((3 << 4) >> 2);\n")
    Unit <- IO.print("== cmp")
    Unit <- one("@main = ((2 + 3) == (1 * 5));\n")
    Unit <- IO.print("== andor")
    Unit <- one("@main = ((12 .&. 10) .|. 0);\n")
    Unit <- IO.print("== eql_num")
    Unit <- one("@main = (42 === 42);\n")
    Unit <- IO.print("== eql_pak")
    Unit <- one("@main = (#(1,2) === #(1,2));\n")
    Unit <- IO.print("== eql_lam")
    Unit <- one("@main = (λx.x === λy.y);\n")
    Unit <- IO.print("== eql_era")
    Unit <- one("@main = (1 === &{});\n")
    Unit <- IO.print("== op2_era")
    Unit <- one("@main = (&{} + 1);\n")
    Unit <- IO.print("== num_era")
    Unit <- one("@main = (1 + &{});\n")
    Unit <- IO.print("== op2_sup")
    Unit <- one("@main = (&A{1,2} + 10);\n")
    Unit <- IO.print("== num_sup")
    Unit <- one("@main = (10 + &A{1,2});\n")
    Unit <- IO.print("== op2_inc")
    Unit <- one("@main = (↑3 + 4);\n")
    Unit <- IO.print("== dup_num")
    Unit <- one("@main = ! &A{a,b} = 7; (a + b);\n")
    Unit <- IO.print("== dup_op2")
    Unit <- one("@main = ! &A{a,b} = (3 + 4); (a * b);\n")
    Unit <- IO.print("== dup_inc")
    Unit <- one("@main = ! &A{a,b} = ↑7; (a + b);\n")
    Unit <- IO.print("== two_ref")
    Unit <- one("@f = (1 + 2);\n@main = (@f * 10);\n")
    Unit <- IO.print("== show_lam")
    Unit <- one("@main = λx.x;\n")
    IO.pure(Unit, Unit{})
#|== add
#|10
#|- Itrs: 4 interactions
#|== mul
#|26
#|- Itrs: 4 interactions
#|== divmod
#|7
#|- Itrs: 4 interactions
#|== xor
#|6
#|- Itrs: 2 interactions
#|== shift
#|12
#|- Itrs: 3 interactions
#|== cmp
#|1
#|- Itrs: 4 interactions
#|== andor
#|1
#|- Itrs: 3 interactions
#|== eql_num
#|1
#|- Itrs: 2 interactions
#|== eql_pak
#|↑↑1
#|- Itrs: 5 interactions
#|== eql_lam
#|1
#|- Itrs: 3 interactions
#|== eql_era
#|&{}
#|- Itrs: 2 interactions
#|== op2_era
#|&{}
#|- Itrs: 2 interactions
#|== num_era
#|&{}
#|- Itrs: 2 interactions
#|== op2_sup
#|&A{11,12}
#|- Itrs: 5 interactions
#|== num_sup
#|&A{11,12}
#|- Itrs: 4 interactions
#|== op2_inc
#|↑7
#|- Itrs: 3 interactions
#|== dup_num
#|14
#|- Itrs: 3 interactions
#|== dup_op2
#|49
#|- Itrs: 4 interactions
#|== dup_inc
#|↑↑14
#|- Itrs: 6 interactions
#|== two_ref
#|30
#|- Itrs: 4 interactions
#|== show_lam
#|λa.a
#|- Itrs: 1 interactions
