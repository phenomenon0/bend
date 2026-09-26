# The Client

`net/client.bend`: requests, their options, sessions, errors and redirects.
The tour is `bend guide networking`.

## One Request

```python
def run(+base: Bytes()) -> IO(Unit):
  +note = Json.text(Json.obj([Json.kv("text", Json.str("written by notes_client"))]))
  do IO<Unit>:
    r : Client.Res() <- Client.post(Bytes.append(base, "/notes"), "application/json", note)
    created(base, r)
```

`Client.get(url)` and `Client.post(url, ctype, body)` answer
`IO(Client.Res())`, which is `Result<&2, &2, Client.NetError, Http.Response>`:
in `net/`, an error and a `Data` value are reusable (`&2`), and only a value
holding a handle, like a WebSocket connection, is affine.
Read a response with `Http.status(resp)`, `Http.resp.header(resp, "name")` and
`Http.resp.body(resp)`. A status like 404 or 500 is not an error: it is a
`Done` with that status.

## Options

`Client.request(req, opts)` takes a request you build and options.
`Client.req(method, url)` is a request with no fields and no body;
`Client.req.header` sets a field and `Client.req.body` the body. `Client.opts()` is the
defaults, and `Client.with.connect`, `timeout`, `max_body`, `redirects` (each
a `U32`), `ca` and `gzip` change one each:

```python
        g : Client.Res() <- Client.get(url)
        shown("GET", g)
        d : Client.Res() <- Client.request(Client.req.header(Client.req("DELETE", url), "x-request-id", "notes-1"),
          Client.with.timeout(Client.opts(), 2000))
        shown("DELETE", d)
```

`Client.with.ca(o, file)` trusts only the CAs in that PEM file instead of the
system's store. TLS is always verified, and the name is checked against the
certificate. There is no option to turn that off.

## Sessions

`Client.get`, `post` and `request` each open a session and close it after.
To keep connections between requests, make a session, `Client.fetch` on it,
and `Client.close` it at the end:

```python
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
```

A session is `Data`, so a server can hand one to every handler through
`serve.with`, and requests from all of them share its connections:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv(["--upstream URL"])
    +s : Client.Session <- Client.session(Client.with.timeout(Client.opts(), 5000))
    +env : Env = Env{s, Server.flag(xs, "--upstream", "http://127.0.0.1:9000")}
    Server.serve.with(~Env, ~app, env, Server.args(xs, Server.config(8080)))
```

A session keeps at most 8 idle connections an origin and 32 origins. A
connection is checked before it is used again. The client sends a request
again only when a pooled connection turned out stale before anything came
back, and only for an idempotent method.

`Client.fetch.with(ss, req, o => ...)` is one request on the session's
connections with options of its own, made from the session's: its connect,
timeout, max_body, redirects and gzip (its `ca` stays the session's, whose
pooled connections were verified under it). A monitor that probes many URLs,
each with its own deadline, keeps one session:

```python
    res : Client.Res() <- Client.fetch.with(env.s(env), Client.req("GET", url), o => Client.with.timeout(o, 2000))
```

## Errors

```python
type NetError is Data:
  Timeout{}
  Refused{}
  Dns{msg: Bytes()}
  Tls{msg: Bytes()}
  Protocol{msg: Bytes()}
  TooLarge{}
  Closed{}
  BadUrl{msg: Bytes()}
  TooManyRedirects{}
  Io{code: U32, msg: Bytes()}
```

`Client.error.show(e)` says one in words. Match on the kinds you handle and
let `_` catch the rest:

```python
# a timeout is the upstream being slow: 504; anything else, 502
def fetched(+id: Bytes(), +up: Bytes(), r: Client.Res()) -> IO(Http.Response):
  match r:
    case Done{resp}:
      Http.reply(answered(id, up, resp))
    case Fail{e}:
      match e:
        case Client.Timeout{}:
          Http.reply(failed(504, "the upstream did not answer in time"))
        case _:
          Http.reply(failed(502, Client.error.show(e)))
```

## Redirects

The client follows 301, 302, 303, 307 and 308, at most 10 by default. 303, and
301 or 302 after a POST, go on as GET without the body. 307 and 308 keep the
method and the body. Authorization, Cookie and Proxy-Authorization go only to
the first request's origin. Past the cap, the answer is `TooManyRedirects`.

## Addresses and IPv6

A host is a name, a dotted address, or an IPv6 address in brackets:
`http://[::1]:8080/`. The URL is written back with the address as RFC 5952
writes it (`[0:0::1]` is `[::1]`), the `Host` field is `[::1]:8080`, and the
pool keys the origin by it, so every spelling of one address is one origin. A
zone ID (`[fe80::1%25eth0]`) is refused. A name is resolved to every address it
has, IPv6 and IPv4, and they are tried one after another in the resolver's
order (RFC 6724), each with an equal share of what is left of the connect
deadline; the first that connects is used. An address with no route fails at
once. Over TLS, a certificate for an IP address is checked against its IP
SANs, and no SNI is sent for one (RFC 6066).
