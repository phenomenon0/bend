# The view-count limit. A view counts a reference on its string and the count
# is 24 bits: 16,777,215 live views of one string. `words` of $N copies of
# "a " holds $N views at once: under the limit it counts them, over it the
# runtime fail-stops (`bend: runtime fail-stop`, exit 1), never a wrong count.
#   N=16000000 ./viewcap --gpu off ; N=17000000 ./viewcap --gpu off
import Base
import ../text/slices.bend as Slices

def main() -> IO(Unit):
  do IO<Unit>:
    env : Result<&1, &1, U32 & String, String> <- IO.get_env("N")
    IO.print(String.append(Nat.show(List.length(&2, String,
      String.words(String.repeat("a ", U32.to_nat(Slices.visits(env)))))), " live views of one string"))
