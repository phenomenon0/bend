# A client for json_api.bend: post a note as JSON, read its id from the
# JSON answer, get it back, then delete it. Each failure is matched by
# kind and exits with its own code.
#
#   ./notes --port 8080 &
#   bend net/examples/notes_client.bend -o notes_client && ./notes_client http://127.0.0.1:8080
import Base
import ../http.bend as Http
import ../client.bend as Client
import ../json.bend as Json
import ../../power/json_value.bend as J

# a NetError, by kind: the exit code says which
def failed(e: Client.NetError) -> IO(Unit):
  match e:
    case Client.Refused{}:
      IO.die(Unit, 3, "notes: nothing is listening there")
    case Client.Timeout{}:
      IO.die(Unit, 4, "notes: no answer in time")
    case _:
      IO.die(Unit, 1, "notes: " ++ Client.error.show(e))

def shown(+what: Bytes(), r: Client.Res()) -> IO(Unit):
  match r:
    case Done{+resp}:
      IO.print(Bytes.concat([what, " ", U32.show(Http.status(resp)), " ", Http.resp.body(resp)]))
    case Fail{e}:
      failed(e)

# GET the note, then DELETE it with a request of our own: a method, a
# field and a deadline of 2 s
def got(+base: Bytes(), id: Json.Got(Bytes())) -> IO(Unit):
  match id:
    case Fail{why}:
      IO.die(Unit, 1, "notes: the answer's " ++ why)
    case Done{+i}:
      +url = Bytes.concat([base, "/notes/", i])
      do IO<Unit>:
        g : Client.Res() <- Client.get(url)
        shown("GET", g)
        d : Client.Res() <- Client.request(Client.req.header(Client.req("DELETE", url), "x-request-id", "notes-1"),
          Client.with.timeout(Client.opts(), 2000))
        shown("DELETE", d)

def parsed(+base: Bytes(), r: Result<&2, &2, J.Why, J.Json>) -> IO(Unit):
  match r:
    case Done{j}:
      got(base, Json.get.str(j, "id"))
    case Fail{w}:
      IO.die(Unit, 1, "notes: the answer is not JSON: " ++ Json.why.show(w))

def created(+base: Bytes(), r: Client.Res()) -> IO(Unit):
  match r:
    case Done{+resp}:
      do IO<Unit>:
        IO.print(Bytes.concat(["POST ", U32.show(Http.status(resp)), " ", Http.resp.body(resp)]))
        parsed(base, Json.of(resp, 65536))
    case Fail{e}:
      failed(e)

def run(+base: Bytes()) -> IO(Unit):
  +note = Json.text(Json.obj([Json.kv("text", Json.str("written by notes_client"))]))
  do IO<Unit>:
    r : Client.Res() <- Client.post(Bytes.append(base, "/notes"), "application/json", note)
    created(base, r)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    run(Maybe.default(&1, String, List.head(&1, String, xs), "http://127.0.0.1:8080"))
