# The Huffman code of RFC 7541 Appendix B, written by gen.py from the
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
  HNode{True{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{48}, HLeaf{49}}, HNode{False{}, HLeaf{50}, HLeaf{97}}}, HNode{False{}, HNode{False{}, HLeaf{99}, HLeaf{101}}, HNode{False{}, HLeaf{105}, HLeaf{111}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{115}, HLeaf{116}}, HNode{False{}, HNode{False{}, HLeaf{32}, HLeaf{37}}, HNode{False{}, HLeaf{45}, HLeaf{46}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{47}, HLeaf{51}}, HNode{False{}, HLeaf{52}, HLeaf{53}}}, HNode{False{}, HNode{False{}, HLeaf{54}, HLeaf{55}}, HNode{False{}, HLeaf{56}, HLeaf{57}}}}}}, HNode{True{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{61}, HLeaf{65}}, HNode{False{}, HLeaf{95}, HLeaf{98}}}, HNode{False{}, HNode{False{}, HLeaf{100}, HLeaf{102}}, HNode{False{}, HLeaf{103}, HLeaf{104}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{108}, HLeaf{109}}, HNode{False{}, HLeaf{110}, HLeaf{112}}}, HNode{False{}, HNode{False{}, HLeaf{114}, HLeaf{117}}, HNode{False{}, HNode{False{}, HLeaf{58}, HLeaf{66}}, HNode{False{}, HLeaf{67}, HLeaf{68}}}}}}, HNode{True{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{69}, HLeaf{70}}, HNode{False{}, HLeaf{71}, HLeaf{72}}}, HNode{False{}, HNode{False{}, HLeaf{73}, HLeaf{74}}, HNode{False{}, HLeaf{75}, HLeaf{76}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{77}, HLeaf{78}}, HNode{False{}, HLeaf{79}, HLeaf{80}}}, HNode{False{}, HNode{False{}, HLeaf{81}, HLeaf{82}}, HNode{False{}, HLeaf{83}, HLeaf{84}}}}}, HNode{True{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{85}, HLeaf{86}}, HNode{False{}, HLeaf{87}, HLeaf{89}}}, HNode{False{}, HNode{False{}, HLeaf{106}, HLeaf{107}}, HNode{False{}, HLeaf{113}, HLeaf{118}}}}, HNode{True{}, HNode{False{}, HNode{False{}, HLeaf{119}, HLeaf{120}}, HNode{False{}, HLeaf{121}, HLeaf{122}}}, HNode{True{}, HNode{False{}, HNode{False{}, HLeaf{38}, HLeaf{42}}, HNode{False{}, HLeaf{44}, HLeaf{59}}}, HNode{True{}, HNode{False{}, HLeaf{88}, HLeaf{90}}, HNode{True{}, HNode{False{}, HNode{False{}, HLeaf{33}, HLeaf{34}}, HNode{False{}, HLeaf{40}, HLeaf{41}}}, HNode{False{}, HNode{False{}, HLeaf{63}, HNode{False{}, HLeaf{39}, HLeaf{43}}}, HNode{False{}, HNode{False{}, HLeaf{124}, HNode{False{}, HLeaf{35}, HLeaf{62}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{0}, HLeaf{36}}, HNode{False{}, HLeaf{64}, HLeaf{91}}}, HNode{False{}, HNode{False{}, HLeaf{93}, HLeaf{126}}, HNode{False{}, HNode{False{}, HLeaf{94}, HLeaf{125}}, HNode{False{}, HNode{False{}, HLeaf{60}, HLeaf{96}}, HNode{False{}, HLeaf{123}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{92}, HLeaf{195}}, HNode{False{}, HLeaf{208}, HNode{False{}, HLeaf{128}, HLeaf{130}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{131}, HLeaf{162}}, HNode{False{}, HLeaf{184}, HLeaf{194}}}, HNode{False{}, HNode{False{}, HLeaf{224}, HLeaf{226}}, HNode{False{}, HNode{False{}, HLeaf{153}, HLeaf{161}}, HNode{False{}, HLeaf{167}, HLeaf{172}}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{176}, HLeaf{177}}, HNode{False{}, HLeaf{179}, HLeaf{209}}}, HNode{False{}, HNode{False{}, HLeaf{216}, HLeaf{217}}, HNode{False{}, HLeaf{227}, HLeaf{229}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{230}, HNode{False{}, HLeaf{129}, HLeaf{132}}}, HNode{False{}, HNode{False{}, HLeaf{133}, HLeaf{134}}, HNode{False{}, HLeaf{136}, HLeaf{146}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{154}, HLeaf{156}}, HNode{False{}, HLeaf{160}, HLeaf{163}}}, HNode{False{}, HNode{False{}, HLeaf{164}, HLeaf{169}}, HNode{False{}, HLeaf{170}, HLeaf{173}}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{178}, HLeaf{181}}, HNode{False{}, HLeaf{185}, HLeaf{186}}}, HNode{False{}, HNode{False{}, HLeaf{187}, HLeaf{189}}, HNode{False{}, HLeaf{190}, HLeaf{196}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{198}, HLeaf{228}}, HNode{False{}, HLeaf{232}, HLeaf{233}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{1}, HLeaf{135}}, HNode{False{}, HLeaf{137}, HLeaf{138}}}, HNode{False{}, HNode{False{}, HLeaf{139}, HLeaf{140}}, HNode{False{}, HLeaf{141}, HLeaf{143}}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{147}, HLeaf{149}}, HNode{False{}, HLeaf{150}, HLeaf{151}}}, HNode{False{}, HNode{False{}, HLeaf{152}, HLeaf{155}}, HNode{False{}, HLeaf{157}, HLeaf{158}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{165}, HLeaf{166}}, HNode{False{}, HLeaf{168}, HLeaf{174}}}, HNode{False{}, HNode{False{}, HLeaf{175}, HLeaf{180}}, HNode{False{}, HLeaf{182}, HLeaf{183}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{188}, HLeaf{191}}, HNode{False{}, HLeaf{197}, HLeaf{231}}}, HNode{False{}, HNode{False{}, HLeaf{239}, HNode{False{}, HLeaf{9}, HLeaf{142}}}, HNode{False{}, HNode{False{}, HLeaf{144}, HLeaf{145}}, HNode{False{}, HLeaf{148}, HLeaf{159}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{171}, HLeaf{206}}, HNode{False{}, HLeaf{215}, HLeaf{225}}}, HNode{False{}, HNode{False{}, HLeaf{236}, HLeaf{237}}, HNode{False{}, HNode{False{}, HLeaf{199}, HLeaf{207}}, HNode{False{}, HLeaf{234}, HLeaf{235}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{192}, HLeaf{193}}, HNode{False{}, HLeaf{200}, HLeaf{201}}}, HNode{False{}, HNode{False{}, HLeaf{202}, HLeaf{205}}, HNode{False{}, HLeaf{210}, HLeaf{213}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{218}, HLeaf{219}}, HNode{False{}, HLeaf{238}, HLeaf{240}}}, HNode{False{}, HNode{False{}, HLeaf{242}, HLeaf{243}}, HNode{False{}, HLeaf{255}, HNode{False{}, HLeaf{203}, HLeaf{204}}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{211}, HLeaf{212}}, HNode{False{}, HLeaf{214}, HLeaf{221}}}, HNode{False{}, HNode{False{}, HLeaf{222}, HLeaf{223}}, HNode{False{}, HLeaf{241}, HLeaf{244}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{245}, HLeaf{246}}, HNode{False{}, HLeaf{247}, HLeaf{248}}}, HNode{False{}, HNode{False{}, HLeaf{250}, HLeaf{251}}, HNode{False{}, HLeaf{252}, HLeaf{253}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{254}, HNode{False{}, HLeaf{2}, HLeaf{3}}}, HNode{False{}, HNode{False{}, HLeaf{4}, HLeaf{5}}, HNode{False{}, HLeaf{6}, HLeaf{7}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{8}, HLeaf{11}}, HNode{False{}, HLeaf{12}, HLeaf{14}}}, HNode{False{}, HNode{False{}, HLeaf{15}, HLeaf{16}}, HNode{False{}, HLeaf{17}, HLeaf{18}}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{19}, HLeaf{20}}, HNode{False{}, HLeaf{21}, HLeaf{23}}}, HNode{False{}, HNode{False{}, HLeaf{24}, HLeaf{25}}, HNode{False{}, HLeaf{26}, HLeaf{27}}}}, HNode{False{}, HNode{False{}, HNode{False{}, HLeaf{28}, HLeaf{29}}, HNode{False{}, HLeaf{30}, HLeaf{31}}}, HNode{False{}, HNode{False{}, HLeaf{127}, HLeaf{220}}, HNode{False{}, HLeaf{249}, HNode{False{}, HNode{False{}, HLeaf{10}, HLeaf{13}}, HNode{False{}, HLeaf{22}, HLeaf{256}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def code8(b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) ->
  List<&2, Bool>:
  match b7 b6 b5 b4 b3 b2 b1 b0:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}]
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}]
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}]
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}]
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}]
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}]
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}]
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}]
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}]
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}]
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}]
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}]
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}]
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}]
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}]
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}]
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      [False{}, True{}, False{}, True{}, False{}, False{}]
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}]
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}]
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}]
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      [False{}, True{}, False{}, True{}, False{}, True{}]
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}]
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}]
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      [False{}, True{}, False{}, True{}, True{}, False{}]
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      [False{}, True{}, False{}, True{}, True{}, True{}]
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      [False{}, True{}, True{}, False{}, False{}, False{}]
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      [False{}, False{}, False{}, False{}, False{}]
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      [False{}, False{}, False{}, False{}, True{}]
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      [False{}, False{}, False{}, True{}, False{}]
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      [False{}, True{}, True{}, False{}, False{}, True{}]
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      [False{}, True{}, True{}, False{}, True{}, False{}]
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      [False{}, True{}, True{}, False{}, True{}, True{}]
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      [False{}, True{}, True{}, True{}, False{}, False{}]
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      [False{}, True{}, True{}, True{}, False{}, True{}]
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      [False{}, True{}, True{}, True{}, True{}, False{}]
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      [False{}, True{}, True{}, True{}, True{}, True{}]
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      [True{}, False{}, True{}, True{}, True{}, False{}, False{}]
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      [True{}, False{}, False{}, False{}, False{}, False{}]
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      [True{}, False{}, False{}, False{}, False{}, True{}]
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      [True{}, False{}, True{}, True{}, True{}, False{}, True{}]
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      [True{}, False{}, True{}, True{}, True{}, True{}, False{}]
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      [True{}, False{}, True{}, True{}, True{}, True{}, True{}]
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      [True{}, True{}, False{}, False{}, False{}, False{}, False{}]
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      [True{}, True{}, False{}, False{}, False{}, False{}, True{}]
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      [True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      [True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      [True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      [True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      [True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      [True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      [True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      [True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      [True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      [True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      [True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      [True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      [True{}, True{}, False{}, True{}, True{}, True{}, False{}]
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      [True{}, True{}, False{}, True{}, True{}, True{}, True{}]
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, False{}, False{}, False{}, False{}]
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, False{}, False{}, False{}, True{}]
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, False{}, False{}, True{}, False{}]
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, False{}, False{}, True{}, True{}]
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}]
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}]
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      [True{}, False{}, False{}, False{}, True{}, False{}]
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}]
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      [False{}, False{}, False{}, True{}, True{}]
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      [True{}, False{}, False{}, False{}, True{}, True{}]
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      [False{}, False{}, True{}, False{}, False{}]
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      [True{}, False{}, False{}, True{}, False{}, False{}]
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      [False{}, False{}, True{}, False{}, True{}]
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      [True{}, False{}, False{}, True{}, False{}, True{}]
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      [True{}, False{}, False{}, True{}, True{}, False{}]
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      [True{}, False{}, False{}, True{}, True{}, True{}]
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      [False{}, False{}, True{}, True{}, False{}]
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, False{}, True{}, False{}, False{}]
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, False{}, True{}, False{}, True{}]
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      [True{}, False{}, True{}, False{}, False{}, False{}]
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      [True{}, False{}, True{}, False{}, False{}, True{}]
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      [True{}, False{}, True{}, False{}, True{}, False{}]
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      [False{}, False{}, True{}, True{}, True{}]
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      [True{}, False{}, True{}, False{}, True{}, True{}]
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, False{}, True{}, True{}, False{}]
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      [True{}, False{}, True{}, True{}, False{}, False{}]
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      [False{}, True{}, False{}, False{}, False{}]
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      [False{}, True{}, False{}, False{}, True{}]
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      [True{}, False{}, True{}, True{}, False{}, True{}]
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, False{}, True{}, True{}, True{}]
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, False{}, False{}, False{}]
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, False{}, False{}, True{}]
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, False{}, True{}, False{}]
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, False{}, True{}, True{}]
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}]
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}]
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}]
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}]
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}, False{}]
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}, True{}]
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}, False{}]
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}, True{}]
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, True{}]
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}, False{}]
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}, False{}]
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}, True{}]
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}]
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}]
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, False{}]
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, True{}]
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}, True{}]
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}]
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}]
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}]
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}]
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}]
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, True{}]
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}]
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}, False{}]
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}]
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}, True{}]
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}]
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, False{}]
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}]
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, False{}]
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}]
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, True{}]
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, True{}]
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}]
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}]
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}]
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}]
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}]
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}]
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}]
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}]
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}]
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}]
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}]
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}]
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, False{}]
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}, True{}]
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}]
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}]
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}]
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}]
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}]
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}]
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}]
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}]
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}]
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}]
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}]
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}]
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}]
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}]
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}]
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}]
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}]
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}]
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}]
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}]
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}]
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}]
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}]
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}]
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}]
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}]
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}]
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}]
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}]
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}]
