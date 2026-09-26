# Read a CSV file into rows, the first as its header, and print them.
#   bend std/examples/csv_rows.bend [FILE]    (from the directory holding std/)
import Base
import ../csv.bend as Csv
import ../text.bend as Text

# a row's fields, each decoded from UTF-8, between bars
def row(r: List<&2, String>) -> String:
  match r:
    case Nil{}:
      ""
    case Con{f, t}:
      " | " ++ Text.decode(f) ++ row(t)

def rows(rs: List<&2, List<&2, String>>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{+r, t}:
      "\n" ++ Nat.show(Csv.width(r)) ++ " fields" ++ row(r) ++ rows(t)

def head(h: Maybe<&2, List<&2, String>>) -> String:
  match h:
    case None{}:
      "no header"
    case Some{r}:
      "header" ++ row(r)

def table(o: Csv.Out) -> String:
  match o:
    case Csv.Read{h, rs}:
      head(h) ++ rows(rs)
    case Csv.Refused{at, why}:
      "refused at byte " ++ Nat.show(at) ++ ": " ++ Csv.why.show(why)

def show(r: Result<&1, &1, U32 & String, Csv.Out>) -> String:
  match r:
    case Done{o}:
      table(o)
    case Fail{(code, msg)}:
      "cannot read the file: " ++ msg

def path(args: List<String>) -> String:
  match args:
    case Nil{}:
      "std/examples/data/people.csv"
    case Con{p, t}:
      p

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    # excel(): RFC 4180 as CPython reads it; with_header: the first row is the header
    r : Result<&1, &1, U32 & String, Csv.Out> <- Csv.read_file(path(args), Csv.with_header(Csv.excel()))
    IO.print(show(r))

#|header | name | city | joined | note
#|4 fields | Ada | London | 1843-07-01 | first program, on paper
#|4 fields | Zoë | Zürich | 2024-02-29 | said "hi"
#|4 fields | Lin | New
#|York | 2000-01-01 |
