# A command-line client: fetch a URL and print the status, the fields
# and the body, or the typed error and exit 1.
#
#   bend net/examples/fetch.bend -o fetch
#   ./fetch https://example.com/
#   ./fetch http://127.0.0.1:8080/items -X POST -d '{"n":1}' -H 'content-type: application/json'
#
# Flags: -X METHOD, -d BODY, -H 'name: value' (repeatable), --ca FILE
# (trust only these CAs), --timeout MS, --connect MS, --max-body N,
# --max-redirects N, --no-gzip, -i (print the status and fields too),
# --twice (the same request again on the session: the second goes over
# the pooled connection).
import Base
import ../http.bend as Http
import ../client.bend as Client

type Cli is Data:
  Cli{url: Bytes(), method: Bytes(), body: Bytes(), hs: List<&2, Http.Header>, o: Client.Opts, show: Bool,
    twice: Bool, prev: Bytes()}

def num(+s: Bytes(), d: U32) -> U32:
  Maybe.default(&2, U32, U32.read(s), d)

def header.of(+s: Bytes()) -> Http.Header:
  +i = Bytes.find_byte(s, 0n, 58)
  Http.Header{String.take(s, i), String.trim(String.drop(s, 1n+i))}

def flag(+p: Bytes(), +a: Bytes(), +c: Cli) -> Cli:
  match c:
    case Cli{u, m, b, hs, o, sh, tw, prev}:
      Cli{Bool.pick(Bytes(), String.is_empty(p) && Bool.not(String.starts_with(a, "-")), a, u),
        Bool.pick(Bytes(), String.eq(p, "-X"), a, m), Bool.pick(Bytes(), String.eq(p, "-d"), a, b),
        Bool.pick(List<&2, Http.Header>, String.eq(p, "-H"), List.append(&2, Http.Header, hs, [header.of(a)]), hs),
        Bool.pick(Client.Opts, String.eq(p, "--ca"), Client.with.ca(o, a),
        Bool.pick(Client.Opts, String.eq(p, "--timeout"), Client.with.timeout(o, num(a, 30000)),
        Bool.pick(Client.Opts, String.eq(p, "--connect"), Client.with.connect(o, num(a, 10000)),
        Bool.pick(Client.Opts, String.eq(p, "--max-body"), Client.with.max_body(o, num(a, 10485760)),
        Bool.pick(Client.Opts, String.eq(p, "--max-redirects"), Client.with.redirects(o, U32.to_nat(num(a, 10))),
        Bool.pick(Client.Opts, String.eq(a, "--no-gzip"), Client.with.gzip(o, False{}), o)))))),
        sh || String.eq(a, "-i"), tw || String.eq(a, "--twice"),
        Bool.pick(Bytes(), String.is_empty(p) && (String.eq(a, "-X") || String.eq(a, "-d") || String.eq(a, "-H")
          || String.eq(a, "--ca") || String.eq(a, "--timeout") || String.eq(a, "--connect")
          || String.eq(a, "--max-body") || String.eq(a, "--max-redirects")), a, "")}

def cli.one(+x: Bytes(), c: Cli) -> Cli:
  match c:
    case Cli{u, m, b, hs, o, sh, tw, +prev}:
      flag(prev, x, Cli{u, m, b, hs, o, sh, tw, prev})

def cli(xs: List<String>, c: Cli) -> Cli:
  match xs:
    case Nil{}:
      c
    case Con{+x, t}:
      cli(t, cli.one(x, c))

def fields.show(hs: List<&2, Http.Header>) -> Bytes():
  match hs:
    case Nil{}:
      ""
    case Con{h, t}:
      match h:
        case Http.Header{n, v}:
          Bytes.concat([n, ": ", v, "\n", fields.show(t)])

def shown(+show: Bool, r: Http.Response) -> IO(Unit):
  match r:
    case Http.Response{+st, hs, b}:
      do IO<Unit>:
        IO.write(Bool.pick(Bytes(), show, Bytes.concat([U32.show(st), " ", Http.reason(st), "\n", fields.show(hs), "\n"]), ""))
        IO.write(Http.resp.body(Http.Response{st, Nil{}, b}))

def answered(+show: Bool, r: Client.Res()) -> IO(Unit):
  match r:
    case Done{resp}:
      shown(show, resp)
    case Fail{e}:
      IO.die(Unit, 1, Bytes.append("fetch: ", Client.error.show(e)))

def again(tw: Bool, +ss: Client.Session, +rq: Client.Req, +show: Bool) -> IO(Unit):
  match tw:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        r : Client.Res() <- Client.fetch(ss, rq)
        answered(show, r)

def run(c: Cli) -> IO(Unit):
  match c:
    case Cli{u, m, b, hs, o, +sh, tw, prev}:
      +rq : Client.Req = Client.Req{m, u, hs, b}
      do IO<Unit>:
        +ss : Client.Session <- Client.session(o)
        r : Client.Res() <- Client.fetch(ss, rq)
        answered(sh, r)
        again(tw, ss, rq, sh)
        Client.close(ss)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    run(cli(xs, Cli{"", "GET", "", Nil{}, Client.opts(), False{}, False{}, ""}))
