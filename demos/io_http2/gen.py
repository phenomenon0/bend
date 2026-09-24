#!/usr/bin/env python3
# Writes huff.bend, the Huffman code of RFC 7541 Appendix B as Bend: the
# decoding tree and the code of every byte. The table is transcribed
# below from the RFC (sym: code as bits, length); nothing else is read.
#
#   python3 demos/io_http2/gen.py
import os

HERE = os.path.dirname(os.path.abspath(__file__))

# RFC 7541 Appendix B: (code, bit length) for symbols 0..256 (256 = EOS)
CODES = [
  (0x1ff8, 13), (0x7fffd8, 23), (0xfffffe2, 28), (0xfffffe3, 28), (0xfffffe4, 28), (0xfffffe5, 28),
  (0xfffffe6, 28), (0xfffffe7, 28), (0xfffffe8, 28), (0xffffea, 24), (0x3ffffffc, 30), (0xfffffe9, 28),
  (0xfffffea, 28), (0x3ffffffd, 30), (0xfffffeb, 28), (0xfffffec, 28), (0xfffffed, 28), (0xfffffee, 28),
  (0xfffffef, 28), (0xffffff0, 28), (0xffffff1, 28), (0xffffff2, 28), (0x3ffffffe, 30), (0xffffff3, 28),
  (0xffffff4, 28), (0xffffff5, 28), (0xffffff6, 28), (0xffffff7, 28), (0xffffff8, 28), (0xffffff9, 28),
  (0xffffffa, 28), (0xffffffb, 28), (0x14, 6), (0x3f8, 10), (0x3f9, 10), (0xffa, 12), (0x1ff9, 13),
  (0x15, 6), (0xf8, 8), (0x7fa, 11), (0x3fa, 10), (0x3fb, 10), (0xf9, 8), (0x7fb, 11), (0xfa, 8),
  (0x16, 6), (0x17, 6), (0x18, 6), (0x0, 5), (0x1, 5), (0x2, 5), (0x19, 6), (0x1a, 6), (0x1b, 6),
  (0x1c, 6), (0x1d, 6), (0x1e, 6), (0x1f, 6), (0x5c, 7), (0xfb, 8), (0x7ffc, 15), (0x20, 6),
  (0xffb, 12), (0x3fc, 10), (0x1ffa, 13), (0x21, 6), (0x5d, 7), (0x5e, 7), (0x5f, 7), (0x60, 7),
  (0x61, 7), (0x62, 7), (0x63, 7), (0x64, 7), (0x65, 7), (0x66, 7), (0x67, 7), (0x68, 7), (0x69, 7),
  (0x6a, 7), (0x6b, 7), (0x6c, 7), (0x6d, 7), (0x6e, 7), (0x6f, 7), (0x70, 7), (0x71, 7), (0x72, 7),
  (0xfc, 8), (0x73, 7), (0xfd, 8), (0x1ffb, 13), (0x7fff0, 19), (0x1ffc, 13), (0x3ffc, 14), (0x22, 6),
  (0x7ffd, 15), (0x3, 5), (0x23, 6), (0x4, 5), (0x24, 6), (0x5, 5), (0x25, 6), (0x26, 6), (0x27, 6),
  (0x6, 5), (0x74, 7), (0x75, 7), (0x28, 6), (0x29, 6), (0x2a, 6), (0x7, 5), (0x2b, 6), (0x76, 7),
  (0x2c, 6), (0x8, 5), (0x9, 5), (0x2d, 6), (0x77, 7), (0x78, 7), (0x79, 7), (0x7a, 7), (0x7b, 7),
  (0x7ffe, 15), (0x7fc, 11), (0x3ffd, 14), (0x1ffd, 13), (0xffffffc, 28), (0xfffe6, 20), (0x3fffd2, 22),
  (0xfffe7, 20), (0xfffe8, 20), (0x3fffd3, 22), (0x3fffd4, 22), (0x3fffd5, 22), (0x7fffd9, 23),
  (0x3fffd6, 22), (0x7fffda, 23), (0x7fffdb, 23), (0x7fffdc, 23), (0x7fffdd, 23), (0x7fffde, 23),
  (0xffffeb, 24), (0x7fffdf, 23), (0xffffec, 24), (0xffffed, 24), (0x3fffd7, 22), (0x7fffe0, 23),
  (0xffffee, 24), (0x7fffe1, 23), (0x7fffe2, 23), (0x7fffe3, 23), (0x7fffe4, 23), (0x1fffdc, 21),
  (0x3fffd8, 22), (0x7fffe5, 23), (0x3fffd9, 22), (0x7fffe6, 23), (0x7fffe7, 23), (0xffffef, 24),
  (0x3fffda, 22), (0x1fffdd, 21), (0xfffe9, 20), (0x3fffdb, 22), (0x3fffdc, 22), (0x7fffe8, 23),
  (0x7fffe9, 23), (0x1fffde, 21), (0x7fffea, 23), (0x3fffdd, 22), (0x3fffde, 22), (0xfffff0, 24),
  (0x1fffdf, 21), (0x3fffdf, 22), (0x7fffeb, 23), (0x7fffec, 23), (0x1fffe0, 21), (0x1fffe1, 21),
  (0x3fffe0, 22), (0x1fffe2, 21), (0x7fffed, 23), (0x3fffe1, 22), (0x7fffee, 23), (0x7fffef, 23),
  (0xfffea, 20), (0x3fffe2, 22), (0x3fffe3, 22), (0x3fffe4, 22), (0x7ffff0, 23), (0x3fffe5, 22),
  (0x3fffe6, 22), (0x7ffff1, 23), (0x3ffffe0, 26), (0x3ffffe1, 26), (0xfffeb, 20), (0x7fff1, 19),
  (0x3fffe7, 22), (0x7ffff2, 23), (0x3fffe8, 22), (0x1ffffec, 25), (0x3ffffe2, 26), (0x3ffffe3, 26),
  (0x3ffffe4, 26), (0x7ffffde, 27), (0x7ffffdf, 27), (0x3ffffe5, 26), (0xfffff1, 24), (0x1ffffed, 25),
  (0x7fff2, 19), (0x1fffe3, 21), (0x3ffffe6, 26), (0x7ffffe0, 27), (0x7ffffe1, 27), (0x3ffffe7, 26),
  (0x7ffffe2, 27), (0xfffff2, 24), (0x1fffe4, 21), (0x1fffe5, 21), (0x3ffffe8, 26), (0x3ffffe9, 26),
  (0xffffffd, 28), (0x7ffffe3, 27), (0x7ffffe4, 27), (0x7ffffe5, 27), (0xfffec, 20), (0xfffff3, 24),
  (0xfffed, 20), (0x1fffe6, 21), (0x3fffe9, 22), (0x1fffe7, 21), (0x1fffe8, 21), (0x7ffff3, 23),
  (0x3fffea, 22), (0x3fffeb, 22), (0x1ffffee, 25), (0x1ffffef, 25), (0xfffff4, 24), (0xfffff5, 24),
  (0x3ffffea, 26), (0x7ffff4, 23), (0x3ffffeb, 26), (0x7ffffe6, 27), (0x3ffffec, 26), (0x3ffffed, 26),
  (0x7ffffe7, 27), (0x7ffffe8, 27), (0x7ffffe9, 27), (0x7ffffea, 27), (0x7ffffeb, 27), (0xffffffe, 28),
  (0x7ffffec, 27), (0x7ffffed, 27), (0x7ffffee, 27), (0x7ffffef, 27), (0x7fffff0, 27), (0x3ffffee, 26),
  (0x3fffffff, 30),
]
assert len(CODES) == 257

def bits(code, n):
  return [(code >> (n - 1 - i)) & 1 for i in range(n)]

# the tree, as nested dicts
def build():
  root = {}
  for sym, (code, n) in enumerate(CODES):
    node = root
    bs = bits(code, n)
    for b in bs[:-1]:
      node = node.setdefault(b, {})
      assert isinstance(node, dict)
    assert bs[-1] not in node
    node[bs[-1]] = sym
  return root

def emit_tree(node, path):
  if isinstance(node, int):
    return 'HLeaf{%d}' % node
  # a place a string may end: the root, or on the all-ones path (a prefix
  # of EOS) at most 7 bits deep
  end = len(path) <= 7 and all(b == 1 for b in path)
  return 'HNode{%s, %s, %s}' % ('True{}' if end else 'False{}',
    emit_tree(node[0], path + [0]), emit_tree(node[1], path + [1]))

def tf(b):
  return 'True{}' if b else 'False{}'

def main():
  tree = build()
  out = []
  out.append('''# The Huffman code of RFC 7541 Appendix B, written by gen.py from the
# RFC's table: do not edit by hand.
#
# tree() is the decoding tree: a leaf is a symbol (256 is EOS), and a
# node says whether a string may end there -- the root, or a node on the
# all-ones path at most 7 bits deep, since padding is at most 7 bits of
# EOS's most significant ones (RFC 7541 5.2).
#
# code8 is the code of a byte, given its eight bits from the most
# significant: its bits, most significant first.
import Base

type Ht is Data:
  HLeaf{sym: U32}
  HNode{end: Bool, zero: Ht, one: Ht}

def tree() -> Ht:
  %s
''' % emit_tree(tree, []))
  out.append('def code8(b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->')
  out.append('  List<&2, Bool>:')
  out.append('  match b7 b6 b5 b4 b3 b2 b1 b0:')
  for sym in range(256):
    bs = [(sym >> (7 - i)) & 1 for i in range(8)]
    code, n = CODES[sym]
    out.append('    case ' + ' '.join(tf(b) for b in bs) + ':')
    out.append('      [' + ', '.join(tf(b) for b in bits(code, n)) + ']')
  open(os.path.join(HERE, 'huff.bend'), 'w').write('\n'.join(out) + '\n')

def tfs(n):
  return [tf((n >> (7 - i)) & 1) for i in range(8)]

# The proof pieces that are a computation per byte: a packed byte walks
# its eight bits (hf_byte), and each byte's code walks the tree to its
# leaf (hf_sym). Each is 256 cases, every one {==}.
def proofs():
  out = []
  out.append('''# The Huffman proofs' two lemmas that hold byte by byte, one case per
# byte, each by computation; written by gen.py. PROOF.bend uses them.
import Base
import ./huff.bend as H
import ./hpack.bend as K
import ./LAWS.bend as Laws

# the decoder walked over bits, one at a time
def walk(+root: H.Ht, bs: List<&2, Bool>, h: K.Hf) -> K.Hf:
  match bs:
    case Nil{}:
      h
    case Con{b, t}:
      walk(root, t, K.hf.bit(root, h, b))

# a byte packed from eight bits is walked as those bits, most
# significant first
def hf_byte(+root: H.Ht, h: K.Hf, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool,
  b1: Bool, b0: Bool) ->
  {K.hf.byte(root, h, K.pack8(b7, b6, b5, b4, b3, b2, b1, b0)) ==
    walk(root, [b7, b6, b5, b4, b3, b2, b1, b0], h) : K.Hf}:
  match b7 b6 b5 b4 b3 b2 b1 b0:''')
  for n in range(256):
    out.append('    case ' + ' '.join(tfs(n)) + ':')
    out.append('      {==}')
  out.append('''
# every byte's code walks the tree from the root to that byte's leaf
def hf_sym(+acc: Bytes(), w: Word(8n)) ->
  {walk(H.tree(), K.code(Laws.byte(w)), K.HfAt{H.tree(), acc}) ==
    K.HfAt{H.tree(), Bytes.push(acc, Laws.byte(w))} : K.Hf}:
  match w:''')
  for n in range(256):
    lsb = [tf((n >> i) & 1) for i in range(8)]
    pat = 'WNil{}'
    for b in reversed(lsb):
      pat = 'WCon{%s, %s}' % (b, pat)
    out.append('    case ' + pat + ':')
    out.append('      {==}')
  open(os.path.join(HERE, 'huff_proof.bend'), 'w').write('\n'.join(out) + '\n')

main()
proofs()
