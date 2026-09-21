# cas (http): the daemon without its socket. serve() takes a request's text
# and gives back the store and the response, so every route and both framing
# rules are a value here, not a connection.
#
# The framing rule worth reading twice is the last one. Content-Length counts
# BYTES; TCP.recv hands back a UTF-8 decode, so String.length counts
# CHARACTERS; for a body with any byte above 0x7f the two never meet and a
# reader that waits for them parks forever on a socket that is done talking.
# req.done calls such a request whole on purpose -- it cannot be served, so
# it is answered, with a 400.
import Base
import ../../power/blake3.bend as B3
import ../../demos/io_cas_store/cas.bend as Cas
import ../../demos/io_cas_store/serve.bend as Srv

def first(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      h

def line1(s: String) -> String:
  first(String.split_on(s, "\r\n"))

# the response body is plain text: its lines end in one newline, not two bytes
def nline1(s: String) -> String:
  first(String.split_on(s, "\n"))

def body.on(r: String & String) -> String:
  (sep, b) = r
  b

def body.go(r: String & (String & String)) -> String:
  (h, rest) = r
  body.on(rest)

def body(+s: String) -> String:
  body.go(String.partition(s, "\r\n\r\n"))

def yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def put.req(+txt: String) -> String:
  String.concat(["PUT /blob HTTP/1.1\r\nHost: x\r\nContent-Length: ",
    U32.show(U32.from_nat(String.length(txt))), "\r\n\r\n", txt])

def get.req(+a: String, +off: U32, +len: U32) -> String:
  String.concat(["GET /blob/", a, "/", U32.show(off), "/", U32.show(len),
    " HTTP/1.1\r\nHost: x\r\n\r\n"])

def payload() -> String:
  String.repeat("the quick brown fox ", 4n)

# a body whose bytes outnumber its characters: one U+00E9 is two bytes on the
# wire, so the Content-Length a real client sends can never be reached
def latin() -> String:
  SCon{Char.from_u32(233), "clair"}

def addr(+resp: String) -> String:
  String.take(String.drop(nline1(body(resp)), 7n), 64n)

def status(r: Cas.Store & String) -> String:
  (st, s) = r
  line1(s)

def get.said(+txt: String) -> String:
  String.concat([line1(txt), " | ", first(String.split_on(body(txt), "\n")),
    " | verified ", Nat.show(String.count(body(txt), "verified"))])

def get.on(r: Cas.Store & String) -> String:
  (st, s) = r
  get.said(s)

def go(st: Cas.Store, +resp: String) -> IO(Unit):
  do IO<Unit>:
    u : Unit <- IO.print("put " ++ line1(resp))
    v : Unit <- IO.print("put body " ++ nline1(body(resp)))
    IO.print("get " ++ get.on(Srv.serve(st, get.req(addr(resp), 20, 8))))

def run(r: Cas.Store & String) -> IO(Unit):
  (st, s) = r
  go(st, s)

def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- IO.print("clen " ++ U32.show(Srv.clen("Host: x\r\nContent-Length: 42\r\n")))
    b : Unit <- IO.print("done head only " ++ yn(Srv.req.done("PUT /blob HTTP/1.1\r\nContent-Length: 4\r\n")))
    c : Unit <- IO.print("done short body " ++ yn(Srv.req.done("PUT /blob HTTP/1.1\r\nContent-Length: 4\r\n\r\nab")))
    d : Unit <- IO.print("done full body " ++ yn(Srv.req.done("PUT /blob HTTP/1.1\r\nContent-Length: 4\r\n\r\nabcd")))
    e : Unit <- IO.print("done latin body " ++ yn(Srv.req.done(put.req(latin()))))
    f : Unit <- IO.print("latin " ++ status(Srv.serve(Cas.new(), put.req(latin()))))
    g : Unit <- IO.print("no route " ++ status(Srv.serve(Cas.new(), "GET / HTTP/1.1\r\n\r\n")))
    h : Unit <- IO.print("short path " ++ status(Srv.serve(Cas.new(), "GET /blob/aa/0 HTTP/1.1\r\n\r\n")))
    i : Unit <- IO.print("bad offset " ++ status(Srv.serve(Cas.new(), "GET /blob/aa/x/1 HTTP/1.1\r\n\r\n")))
    run(Srv.serve(Cas.new(), put.req(payload())))
#|clen 42
#|done head only no
#|done short body no
#|done full body yes
#|done latin body yes
#|latin HTTP/1.1 400 Bad Request
#|no route HTTP/1.1 404 Not Found
#|short path HTTP/1.1 400 Bad Request
#|bad offset HTTP/1.1 400 Bad Request
#|put HTTP/1.1 201 Created
#|put body stored f2c8dfc36091e80caafc35d952365a579a73396cd8dfd95a361c4094a0fabce9
#|get HTTP/1.1 200 OK | blob f2c8dfc36091e80caafc35d952365a579a73396cd8dfd95a361c4094a0fabce9 | verified 1
