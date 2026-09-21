# HVM5 in Bend -- the laws. Claims about the pure logic under the
# evaluator: the lexer (a word and the rest re-form the source, a
# blank skip only moves the cursor), the parser's cursor (drops
# compose, a read past a drop is a read at the sum), the printer (a
# pack of n constructors prints n more braces than its body), the
# closed facts about run words, name codes and the book's depth, and
# the numeric machine (the operator table mirrors the U32 primitive
# it names, the edges answer zero, OP2-NUM-SUP distributes for free,
# the codes split where hvm4 splits its nodes, the operator lexer
# takes neither a lone "&" nor a lone "!"). PROOF.bend proves them.

import Base
import ./main.bend as Hvm

# LAW: the lexer loses nothing: for any source and any head class,
# the word at the head and the rest re-form the source.
law word_joins:
  for +s: String
  for z: Bool
  {Hvm.word_cat(Hvm.str_word(s, z)) == s : String}

# LAW: skipping blanks and comments only moves the cursor forward:
# for any source and any head class, the skipped source is the source
# past some n characters (n is the witness).
law skip_is_drop:
  for +s: String
  for z: Hvm.Ws
  exs n: Nat
  {Hvm.str_skip(s, z) == Hvm.str_drop(s, n) : String}

# LAW: the printer's packs are balanced: the display of a pack of run
# p around x opens run_len(p) braces more than the display of x, for
# any run word and any term.
law pak_braces:
  for +p: U32
  for +x: Hvm.Term
  {Nat.add(Hvm.run_len(p), Hvm.opens(Hvm.term_show(x)))
    == Hvm.opens(Hvm.term_show(Hvm.Pak{p, x})) : Nat}

# LAW: the cursor composes: dropping m characters, then n, drops
# m + n.
law drop_drop:
  for s: String
  for m: Nat
  for n: Nat
  {Hvm.str_drop(Hvm.str_drop(s, m), n) == Hvm.str_drop(s, Nat.add(m, n)) : String}

# LAW: the code at k past a cursor moved by n is the code at n + k.
law at_drop:
  for s: String
  for n: Nat
  for k: Nat
  {Hvm.str_at(Hvm.str_drop(s, n), k) == Hvm.str_at(s, Nat.add(n, k)) : U32}

# LAW: a bit pushed outermost onto a run word is the bit bit0 reads
# back, and popping it restores the word (here the one-bit run #1{..},
# for either bit) (sanity).
law run_push_pop:
  for +b: Bool
  {(Hvm.bit0(Hvm.run_push(Hvm.run_word(1, 1), Hvm.pick(U32, b, 1, 0))),
    Hvm.run_pop(Hvm.run_push(Hvm.run_word(1, 1), Hvm.pick(U32, b, 1, 0))))
   == (Bool.not(b), Hvm.run_word(1, 1)) : Bool & U32}

# LAW: a name survives its code: the parser's six-bits-per-character
# code of a name prints back as the name (sanity).
law name_round_trip:
  {(Hvm.nam(Hvm.name_code("main", 0)), Hvm.nam(Hvm.name_code("F", 0)))
   == ("main", "F") : String & String}

# LAW: the book's depth is the least d with 2^d slots for n
# definitions (sanity).
law book_depth_fits:
  {(Hvm.book_depth(32n, 1, 0n), Hvm.book_depth(32n, 5, 0n), Hvm.book_depth(32n, 8, 0n),
    Hvm.book_depth(32n, 9, 0n))
   == (0n, 3n, 3n, 4n) : Nat & Nat & Nat & Nat}

# The numeric machine
# -------------------

# LAW: an operator code is the U32 primitive it names, so it carries
# the primitive's algebra: hvm4's code 0 is addition, and addition
# commutes.
law op_add_comm:
  for +a: U32
  for +b: U32
  {Hvm.op_u32(0, a, b) == Hvm.op_u32(0, b, a) : U32}

# LAW: the comparisons reflect U32's own order into hvm4's 1 and 0:
# code 11 is ==, code 13 is <. This pins the numbering -- move a code
# and the law stops holding.
law op_cmp_reflect:
  for +a: U32
  for +b: U32
  {(Hvm.op_u32(11, a, b), Hvm.op_u32(13, a, b))
   == (Hvm.pick(U32, U32.is_eq(a, b), 1, 0), Hvm.pick(U32, U32.is_lt(a, b), 1, 0))
   : U32 & U32}

# LAW: the edges answer zero, at the two places the C reference is
# undefined or platform-shaped: a zero divisor for / and for %, and a
# shift of 32 or wider (op_sh clamps the count).
law op_edges_zero:
  for +a: U32
  {(Hvm.op_u32(3, a, 0), Hvm.op_u32(4, a, 0),
    Hvm.op_u32(8, 1, 32), Hvm.op_u32(9, 1, 32))
   == (0, 0, 0, 0) : U32 & U32 & U32 & U32}

# LAW: OP2-NUM-SUP distributes for free. A word costs nothing to
# copy, so the rule writes it into both sides of the superposition
# and leaves the env, the free list and the fresh counter exactly as
# it found them -- no cell is taken -- for one interaction.
law op2_num_sup:
  for env: Array<Hvm.Cell>
  for book: Array<Hvm.Tpl>
  for k: Hvm.Kont
  for +c: U32
  for +fh: U32
  for +nx: U32
  for +o: U32
  for +x: U32
  for +l: U32
  for a: Hvm.Term
  for b: Hvm.Term
  {Hvm.opn(env, book, k, c, fh, nx, o, x, Hvm.Sup{l, a, b})
   == Hvm.S{env, book,
        Hvm.Kn{Hvm.Sup{l, Hvm.Op2{o, Hvm.Val{x}, a}, Hvm.Op2{o, Hvm.Val{x}, b}}},
        k, (c + 1 : U32), fh, nx} : Hvm.S}

# LAW: the four kinds split the codes where hvm4 splits its nodes:
# 0..16 read the right operand on as an OP2, 17 is ===, 18 is .&., 19
# is .|. (sanity).
law op_kind_splits:
  {(Hvm.op_kind(0), Hvm.op_kind(16), Hvm.op_kind(17), Hvm.op_kind(18),
    Hvm.op_kind(19))
   == (Hvm.Oar{}, Hvm.Oar{}, Hvm.Oeq{}, Hvm.Oan{}, Hvm.Oor{})
   : Hvm.Ok & Hvm.Ok & Hvm.Ok & Hvm.Ok & Hvm.Ok}

# LAW: the longest token wins, and the operator lexer takes neither a
# lone "&" nor a lone "!", so a superposition and a duplication still
# parse as themselves (sanity).
law op_tok_longest:
  {(Hvm.op_tok(Hvm.chr_code('&'), Hvm.chr_code('{'), Hvm.chr_code('1')),
    Hvm.op_tok(Hvm.chr_code('!'), Hvm.chr_code(' '), Hvm.chr_code('&')),
    Hvm.op_tok(Hvm.chr_code('='), Hvm.chr_code('='), Hvm.chr_code('=')),
    Hvm.op_tok(Hvm.chr_code('='), Hvm.chr_code('='), Hvm.chr_code(' ')),
    Hvm.op_tok(Hvm.chr_code('.'), Hvm.chr_code('&'), Hvm.chr_code('.')))
   == (0, 0, Hvm.op_w(3, 17), Hvm.op_w(2, 11), Hvm.op_w(3, 18))
   : U32 & U32 & U32 & U32 & U32}
