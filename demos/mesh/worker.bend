# A bend-mesh worker: `worker --port P [--slow MS]`. POST /leaf with a body
# "job a lo n d" answers the leaf's summary as words (job.bend), computed by
# the same fork tree the single-process program runs, on every core of this
# machine. --slow waits MS before each answer: a straggler, for the
# coordinator's hedging to route around. GET /health answers "ok".
import Base
import ../../net/http.bend as Http
import ../../net/server.bend as Server
import ./job.bend as J

def answer(+j: J.Job) -> IO(Http.Response):
  Http.reply(Http.text(200, J.words.show(J.run(j))))

def leaf(+slow: U32, r: Http.Request) -> IO(Http.Response):
  +j = J.parse(Http.body(r))
  do IO<Http.Response>:
    IO.sleep(slow)
    answer(j)

def health(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "ok"))

def routes(+slow: U32) -> List<Server.Route>:
  [Server.get("/health", health), Server.post("/leaf", r => leaf(slow, r))]

def app(+slow: U32, r: Http.Request) -> IO(Http.Response):
  Server.route(routes(slow), r)

def main() -> IO(Unit):
  do IO<Unit>:
    a1 : List<String> <- IO.args()
    xs : List<String> <- IO.args()
    +slow : U32 = Maybe.default(&2, U32, U32.read(Server.flag(a1, "--slow", "0")), 0)
    Server.serve.with(~U32, ~app, slow, Server.set.send(Server.args(xs, Server.config(9001)), 120000))
