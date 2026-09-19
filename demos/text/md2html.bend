# md2html: render the Markdown file $FILE as HTML on stdout.
#   FILE=README.md ./md2html --gpu off > README.html
# Subset: # ## ### headings, **bold**, *italic*, `code`, [text](url),
# "- " bullet lists, blank-line paragraphs, ``` fences as <pre> (no inline
# markup inside); < > & are escaped everywhere, so raw HTML shows as text.
# An unclosed marker stays literal. md2html.py is the same spec in Python.
import Base

type Line is Data:
  Fence{}
  Blank{}
  Head{level: U32}
  Item{}
  Text{}

# the open block: nothing, a paragraph, a list, a fence
type Open is Data:
  Idle{}
  Para{}
  Items{}
  Pre{}

def same(s: String) -> String:
  s

# Inline
# ------

# parts of a line split at a marker alternate outside / inside the span;
# an inside part with nothing after it was never closed: its marker is text
def span(~out: String -> String, ~in: String -> String, p: String, last: Bool,
  mark: String, open: String, close: String) -> String:
  match last:
    case True{}:
      String.append(mark, out(p))
    case False{}:
      String.concat([open, in(p), close])

def spans(~out: String -> String, ~in: String -> String,
  parts: List<&2, String>, inside: Bool, +mark: String, +open: String,
  +close: String) -> List<&2, String>:
  match parts inside:
    case Nil{} _:
      []
    case Con{p, t} False{}:
      out(p) <> spans(~out, ~in, t, True{}, mark, open, close)
    case Con{p, +t} True{}:
      span(~out, ~in, p, List.is_empty(&2, String, t), mark, open, close)
        <> spans(~out, ~in, t, False{}, mark, open, close)

def italic(t: String) -> String:
  String.concat(spans(~same, ~same, String.split_on(t, "*"), False{},
    "*", "<i>", "</i>"))

# a part after "[" is a link when it reads text](url)rest
def link.make(part: String, txt: String, url: String, rest: String,
  open: Bool) -> String:
  match open:
    case True{}:
      String.append("[", italic(part))
    case False{}:
      String.concat(["<a href=\"", url, "\">", italic(txt), "</a>", italic(rest)])

def link.url(part: String, txt: String, r: String & (String & String)) -> String:
  (url, (sep, rest)) = r
  link.make(part, txt, url, rest, String.is_empty(sep))

def link.txt(part: String, r: String & (String & String)) -> String:
  (txt, (sep, rest)) = r
  link.url(part, txt, String.partition(rest, ")"))

def link(+part: String) -> String:
  link.txt(part, String.partition(part, "]("))

def links.go(parts: List<&2, String>) -> List<&2, String>:
  match parts:
    case Nil{}:
      []
    case p <> t:
      link(p) <> links.go(t)

def links.all(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      ""
    case p <> t:
      String.append(italic(p), String.concat(links.go(t)))

def links(t: String) -> String:
  links.all(String.split_on(t, "["))

def bold(t: String) -> String:
  String.concat(spans(~links, ~links, String.split_on(t, "**"), False{},
    "**", "<b>", "</b>"))

def inline(t: String) -> String:
  String.concat(spans(~bold, ~same, String.split_on(t, "`"), False{},
    "`", "<code>", "</code>"))

# Blocks
# ------

def line(+l: String) -> Line:
  Bool.pick(Line, String.starts_with(l, "```"), Fence{},
  Bool.pick(Line, String.is_empty(String.trim(l)), Blank{},
  Bool.pick(Line, String.starts_with(l, "### "), Head{3},
  Bool.pick(Line, String.starts_with(l, "## "), Head{2},
  Bool.pick(Line, String.starts_with(l, "# "), Head{1},
  Bool.pick(Line, String.starts_with(l, "- "), Item{}, Text{}))))))

def shut(o: Open, acc: List<&2, String>) -> List<&2, String>:
  match o:
    case Idle{}:
      acc
    case Para{}:
      "</p>" <> acc
    case Items{}:
      "</ul>" <> acc
    case Pre{}:
      "</pre>" <> acc

def head(+n: U32, l: String) -> String:
  String.concat(["<h", U32.show(n), ">",
    inline(String.drop(l, U32.to_nat(U32.add(n, 1)))), "</h", U32.show(n), ">"])

def item(l: String) -> String:
  String.concat(["<li>", inline(String.drop(l, 2n)), "</li>"])

# one line: the block left open after it, and the output so far (newest first)
def step(o: Open, k: Line, l: String, acc: List<&2, String>) ->
  Open & List<&2, String>:
  match o k:
    case Pre{} Fence{}:
      (Idle{}, "</pre>" <> acc)
    case Pre{} _:
      (Pre{}, l <> acc)
    case o Fence{}:
      (Pre{}, "<pre>" <> shut(o, acc))
    case o Blank{}:
      (Idle{}, shut(o, acc))
    case o Head{n}:
      (Idle{}, head(n, l) <> shut(o, acc))
    case Items{} Item{}:
      (Items{}, item(l) <> acc)
    case o Item{}:
      (Items{}, item(l) <> "<ul>" <> shut(o, acc))
    case Para{} Text{}:
      (Para{}, inline(l) <> acc)
    case o Text{}:
      (Para{}, inline(l) <> "<p>" <> shut(o, acc))

def render(ls: List<&2, String>, st: Open & List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      (o, acc) = st
      List.reverse(&2, String, shut(o, acc))
    case Con{+l, t}:
      (o, acc) = st
      render(t, step(o, line(l), l, acc))

def escape(s: String) -> String:
  String.replace(String.replace(String.replace(s, "&", "&amp;"), "<", "&lt;"),
    ">", "&gt;")

def html(s: String) -> String:
  String.join(render(String.splitlines(escape(s)), (Idle{}, [])), "\n")

def run(read: File & Result<&1, &1, U32 & String, String>, t0: Nat) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    s : String <- IO.pass(String, result)
    File.close(f)
    +t1 : Nat <- IO.now()
    IO.print(html(s))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["read ", Nat.show(Nat.sub(t1, t0)),
      " ms, render+print ", Nat.show(Nat.sub(t2, t1)), " ms"]))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    run(read, t0)
