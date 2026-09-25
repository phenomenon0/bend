# A Map of the Repo

Where things are, for someone new. `AGENTS.md` has the short list for agents;
this file says the same in more words, and maps the networking stack in full.

## The Language

    bend2/              the language and its compiler
      bend.ts           the parser, the theory and the checker (human-written)
      comp.ts           the compiler and the runtimes: C (CPU), Metal, CUDA, JS
      main.ts           the `bend` command
      base.bend         the base library (`bend base` prints it)
      time.bend         dates in UTC: Time.iso, Time.http (imported by path)
      effs/             the IO effects, a .c and a .js per effect
      bend.lean         the core, mechanized in Lean
    kernel/             a second, independent checker in Rust; it re-checks a
                        proof's exported core (`bend F --export F.core`)
    guide/              GUIDE.md (`bend guide`), and the extras: SHADERS.md,
                        EFFECTS.md, NETWORKING.md (`bend guide networking`),
                        the tour of net/ whose pages are guide/net/*.md
                        (`bend guide net/serving`)
    power/              libraries in Bend: JSON, gzip and deflate, CSV, hashes,
                        search, numerics; some carry their own laws and proofs
    tests/<ns>/         the tests; each ends in the `#|` lines its run prints
    bench/              the runtime and checker benchmarks; bench/proxy is a
                        framing harness that compares a Bend proxy with nginx
                        and HAProxy; bench/net counts what a request costs the
                        engine, net/ and bend-h2 (instructions, syscalls)
    demos/              one program per directory
    gates/              the repo's own checks (tests, perf, the file allow list)
    paper/, media/      the papers and the charts
    docs/omen/          working notes: plans, reviews, house style

## Networking

The stack has three layers. Only the top one is meant to be imported by an
ordinary program.

    net/                           the library you import (the front door)
      http.bend                    Http: requests, responses, headers, percent-encoding
      server.bend                  Server: serve, the configuration, the router, middleware
      client.bend                  Client: get, post, request, sessions, NetError
      url.bend                     URLs: parse, resolve, origin
      addr.bend                    IPv6 text (RFC 4291/5952), IP-literals, connect to a name's addresses
      json.bend                    Json: JSON bodies
      stream.bend                  Stream: request bodies as streams (uploads), stream routes,
                                   response bodies written as they are made (exports, events)
      ws.bend                      Ws: the WebSocket client
      ws_net.bend                  a Ws.Err as a NetError
      ws_frame.bend, ws_hs.bend    the WebSocket client's frames and handshake
      ws_cli.bend                  a WebSocket command-line client (used by CI)
      examples/                    small programs, one per task (below)
      README.md                    the API in one page, the defaults, the laws

    wire/                          bend-wire: the substrate net/ is built on
      reader.bend                  the reader kit: a protocol's byte machine, fed any cut
      loop.bend                    the connection loop, the writer, the accept loop
      effects.bend                 the loops over real IO: a connection limit, SIGTERM
      world.bend                   a pure model of sockets, and the loops' laws in it
      client.bend                  one client exchange under budgets; when to reuse
      pool.bend                    idle connections, bounded, probed before reuse
      stream.bend                  a body as a stream, under a window
      http1/                       the HTTP/1.1 response reader and its RFC 9112 spec
      conform.bend, conform.c      the real effects checked against the model's contracts

    demos/io_http_engine/          the HTTP/1.1 engine: the request reader (held to
                                   RFC 9112 by frame_sim), files, WebSocket echo, SSE;
                                   net/'s server reads requests through it
    demos/io_proxy/                bend-proxy: a reverse proxy that cannot be
                                   desynchronised; net/ writes responses its way
    demos/io_http2/                bend-h2: an HTTP/2 server with HPACK, on bend-wire
    demos/io_http_client/          a command-line HTTP/1.1 client on bend-wire
    demos/io_sink/                 uploads streamed in bounded memory (wire/stream.bend)
    demos/io_resp/                 a Redis-protocol server, to test bend-wire on another protocol

The older demos `io_http_server`, `io_http_fetch` and `io_tcp_echos` use raw
TCP from Base and are not built on bend-wire.

If you want to serve or fetch HTTP, read `guide/NETWORKING.md` and use `net/`.
Read `wire/` and the demos when you want to change how the bytes are framed,
or to write a server for another protocol.

### The Examples

    net/examples/hello.bend         one handler
    net/examples/greet.bend         a query string, a handler that can fail, middleware
    net/examples/json_api.bend      a JSON API over a router, a channel as its store
    net/examples/notes_client.bend  a client for json_api: post, get, delete, errors by kind
    net/examples/file_server.bend   files under a root, with the browser's headers
    net/examples/tls_server.bend    a server over TLS
    net/examples/fetch.bend         a command-line client, like a small curl
    net/examples/relay.bend         fetch JSON upstream, keep some fields, serve them
    net/examples/ws_chat.bend       a WebSocket chat client
    net/examples/upload.bend        uploads of any size to files, in bounded memory
    net/examples/export.bend        exports of any size (CSV, NDJSON, bytes), written as they are made
    net/examples/events.bend        server-sent events with keepalives
    net/examples/relay_stream.bend  a relay that streams an upstream body end to end

Each builds with `bend net/examples/NAME.bend -o NAME`. Its header says how to
run it.

### The Apps

`apps/` holds whole programs built on `net/` the way a user would, without
touching the library. `apps/uptime/` is an uptime monitor: probes on their own
loops, a JSON API, a dashboard, live results over a WebSocket, webhooks, a
log it replays on start. Its `check.py` runs it against fake targets, and its
`FRICTION.md` ranks what the library and the language cost it to write.

### Laws, Proofs and Mutants

Each part states its promises in a `LAWS.bend` (or a `*_laws.bend`) and proves
them in a `PROOF.bend` (or a `*_proof.bend`). A proof passes when
`bend FILE` prints exactly `All terms check.`. A mutants script then breaks the
code on purpose, one bug at a time, and the proof must refuse every one. That
shows the laws are not empty.

| part | laws | proof | mutants |
| --- | --- | --- | --- |
| net/ (server, client) | net/LAWS.bend | net/PROOF.bend | python3 net/mutants.py |
| net/ (WebSocket client) | net/ws_laws.bend | net/ws_proof.bend | python3 net/ws_mutants.py |
| HTTP/1.1 engine | demos/io_http_engine/LAWS.bend | demos/io_http_engine/PROOF.bend | python3 demos/io_http_engine/mutants.py |
| HTTP/1.1 responses | wire/http1/LAWS.bend | wire/http1/PROOF.bend | python3 wire/http1/mutants.py |
| client, pool, stream | in the files | wire/client.bend, wire/pool.bend, wire/world.bend | python3 wire/client_mutants.py |
| proxy | demos/io_proxy/LAWS.bend | demos/io_proxy/PROOF.bend | python3 demos/io_proxy/mutants.py |
| HTTP/2 | demos/io_http2/LAWS.bend | demos/io_http2/PROOF.bend | python3 demos/io_http2/mutants.py |
| RESP | demos/io_resp/LAWS.bend | demos/io_resp/PROOF.bend | |

Run them from the repo root. With no `bend` installed, `bun bend2/main.ts` is
the same command. The second kernel re-checks a proof:

```bash
bun bend2/main.ts net/PROOF.bend                        # All terms check.
python3 net/mutants.py                                  # every mutant refused
cargo build --release --manifest-path kernel/Cargo.toml
bun bend2/main.ts net/PROOF.bend --export proof.core
kernel/target/release/bend-kernel -q proof.core
```

What the proofs do not cover: the IO loops that call the proven functions, and
the deadlines and limits. Those are checked from outside by running the
programs: `python3 net/check.py` for net/'s examples and defaults, and
`python3 net/ws_check.py ./wsc ./httpd PORT` for the WebSocket client.

### How CI Gates It

`.github/workflows/http.yml` runs on a push to its branches and on a pull
request, when `net/`, `wire/`, the networking demos, `power/` JSON, gzip,
deflate or CSV, `bend2/`, `kernel/` or the workflow itself changes. On
Ubuntu, it:

1. checks every proof above and requires the exact line `All terms check.`
   (a proof that leans on `@unsafe` or a foreign def prints more, and fails);
2. builds the Rust kernel, runs its own tests, and re-checks every proof's
   exported core with it;
3. runs every mutants script;
4. builds the HTTP engine and runs its C checks in every mode, its budgets
   (memory, slow peers, `ulimit -n 64`, SIGTERM under load), and the same
   checks over TLS;
5. checks the real effects against the model's contracts (`wire/conform`);
6. runs the client against the engine and nginx, and the proxy's smuggling
   vectors beside nginx;
7. runs the WebSocket client against the engine's echo, a raw server and the
   Python websockets library;
8. runs `python3 net/check.py`: net/'s examples against every default;
9. runs the RESP server, the upload sink, 500 random streams through the
   engine and a C control that must agree, two copies on a shared port, and
   bend-h2 through h2spec;
10. keeps the `httpd` and `h2d` binaries as build artifacts.

`net/check.py` builds every example in `net/examples/`, so a snippet the docs
quote cannot rot, and runs `hello`, `json_api`, `file_server`, `greet` and
`fetch`.

### The Allow List

`gates/repo.ts` lists every file the repo may hold, each with a size cap. A
new file needs a line there, or the repo gate fails.
