# RFC 8439 section 2.4.2: 114 bytes (a full block and a short tail).
import Base
import ../../demos/kernels/chacha20.bend as C

def key() -> C.ChaKey:
  C.ChaKey{50462976, 117835012, 185207048, 252579084,
    319951120, 387323156, 454695192, 522067228}

def nonce() -> C.Nonce:
  C.Nonce{0, 1241513984, 0}

def shown(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "counter exhausted"
    case Some{bs}:
      C.hex(bs)

def octets(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      []
    case SCon{Chr{x}, t}:
      x <> octets(t)

def main() -> String:
  shown(C.crypt(key(), 1, nonce(), octets("Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.")))

#|"6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"
