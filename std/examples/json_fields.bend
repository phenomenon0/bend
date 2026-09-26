# Parse a JSON file and get fields out of it.
#   bend std/examples/json_fields.bend [FILE]    (from the directory holding std/)
import Base
import ../bytes.bend as By
import ../json_value.bend as Json
import ../text.bend as Text

# a string field as text (Json strings are UTF-8 bytes)
def str(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      Text.decode(s)
    case None{}:
      "(no such string)"

def num(m: Maybe<&2, Nat>) -> String:
  match m:
    case Some{n}:
      Nat.show(n)
    case None{}:
      "(no such number)"

def fields(+j: Json.Json) -> String:
  "name: " ++ str(Json.string(Json.get(j, "name"))) ++
  "\nowner: " ++ str(Json.string(Json.path(j, ["owner", "login"]))) ++
  " in " ++ str(Json.string(Json.path(j, ["owner", "city"]))) ++
  "\nstars: " ++ num(Json.nat(Json.get(j, "stars"))) ++
  "\nsecond tag: " ++ str(Json.string(Json.index(Json.get(j, "tags"), 1n))) ++
  "\nlicense: " ++ str(Json.string(Json.get(j, "license")))

def parsed(r: Json.Out()) -> String:
  match r:
    case Done{+j}:
      fields(j) ++ "\ncanonical: " ++ Text.decode(Json.show(j))
    case Fail{why}:
      "not JSON"

def show(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{+doc}:
      # lim(n): at most 64 containers deep, n bytes of budget
      parsed(Json.parse(doc, Json.lim(U32.from_nat(By.len(doc)))))
    case Fail{(code, msg)}:
      "cannot read the file: " ++ msg

def path(args: List<String>) -> String:
  match args:
    case Nil{}:
      "std/examples/data/project.json"
    case Con{p, t}:
      p

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    r : Result<&1, &1, U32 & String, String> <- By.read_file(path(args))
    IO.print(show(r))

#|name: bend
#|owner: HigherOrderCO in São Paulo
#|stars: 18000
#|second tag: parallel
#|license: (no such string)
#|canonical: {"name":"bend","version":"2.0.27","tags":["fast","parallel","typed"],"owner":{"login":"HigherOrderCO","id":42,"city":"São Paulo"},"stars":18000,"private":false}
