# RFC 8439 appendix A.1, vector 1: zero key, nonce and counter.
import Base
import ../../demos/kernels/chacha20.bend as C

def main() -> String:
  C.hex(C.block(C.ChaKey{0, 0, 0, 0, 0, 0, 0, 0}, 0, C.Nonce{0, 0, 0}))

#|"76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586"
