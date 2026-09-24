# bench/proxy -- a differential HTTP framing harness

An independent, second-opinion harness for the head-to-head between a Bend
reverse proxy / HTTP server and nginx and HAProxy. It does not trust the Bend
spec: it frames every byte stream with its own strict RFC 9112 parser
(`refparse.py`) and asks, of each front, whether what reached the backend is
what the RFC frames on the client's bytes. Where they disagree, a request has
been smuggled.

Python 3 standard library only, plus the `h2` package for the HTTP/2 vectors.
No Bend sources are touched. Everything uses ports 20400-20499 and every
process it starts is killed on the way out.

## Pieces

    refparse.py   a strict RFC 9112 request framer, written from the RFC as a
                  second opinion; frame(bytes) -> (requests, status, error)
    upstream.py   the echo-record upstream: records the raw bytes a front
                  forwards on each connection, frames them with refparse,
                  answers each request naming its index and byte range, and
                  logs a JSON event per request / error / close
    corpus.py     generates corpus/ -- the smuggling and desync families as
                  raw byte streams (.raw) and HTTP/2 scripts (.h2json), plus
                  index.json with each entry's RFC-expected disposition
    fronts.py     how to configure and run each front (nginx, HAProxy, the
                  Bend httpd as a server, an nginx h2c front)
    driver.py     the HTTP/1 differential: every corpus entry x every front,
                  classified against the reference -> results/
    h2driver.py   the HTTP/2 downgrade vectors via the h2 package
    perf.py       wrk against a fast upstream (the Bend httpd /health), pinned

## Corpus

`corpus/` holds a few hundred entries across the known families: CL.TE, TE.CL,
TE.TE obfuscations (case, whitespace, `chunked ` trailing space, `xchunked`,
`chunked, identity`, duplicate TE, TE in 1.0), duplicate/conflicting
Content-Length, CL with signs/spaces/commas/leading zeros/overflow, obs-fold,
bare LF/CR, NUL and control bytes in names/values/targets, space before colon,
absolute-form and odd targets, very long lines, pipelines, 1.0 keep-alive,
Expect: 100-continue, chunk-size overflow / extensions / trailers, upgrade with
trailing bytes, h2c upgrade, and the HTTP/2 downgrade vectors (H2.CL / H2.TE,
transfer-encoding in h2, CRLF injection, pseudo-header abuse). Each entry
carries a family and the RFC-expected disposition (`reject`, or `accept:N`),
computed by the reference for the raw entries so the corpus and the oracle can
never drift apart.

Regenerate it with `python3 corpus.py` (it is committed so the harness runs
without a generation step, and so a reviewer can read the bytes).

## Classification

For a **proxy** front (nginx, HAProxy, later `proxyd`), each entry is:

    clean           forwarded the same request count and body boundaries the
                    reference frames (targets may be legitimately rewritten)
    front_stricter  the front refused what the reference accepts (safe)
    reject          the reference rejects and the front forwarded nothing (good)
    desync          the backend saw a different number of requests or a
                    different body boundary than the reference frames
    fwd_reject      the front forwarded >=1 request the reference rejects

For the **Bend httpd** as a direct server (no upstream, a direct-parse rival):

    match_accept    both accept, same request count
    match_reject    both reject
    httpd_stricter  reference accepts, httpd refuses (conservative, safe)
    httpd_looser    reference rejects, httpd accepts (the dangerous direction)

A 404/405/426 counts as "framed and accepted": it is an application answer to a
request the server did parse, not a framing refusal. Only 400/413/414/431/501/
505 (and a bare connection close) count as a refusal.

## Run it

    python3 bench/proxy/corpus.py                       # (re)generate the corpus
    bun bend2/main.ts demos/io_http_engine/main.bend -o /tmp/httpd

    # HTTP/1 differential: nginx, HAProxy, Bend httpd as a server
    python3 bench/proxy/driver.py \
        --fronts nginx,haproxy,bend_httpd --httpd /tmp/httpd --out bench/proxy/results

    # HTTP/2 downgrade vectors (nginx h2c front)
    python3 bench/proxy/h2driver.py --out bench/proxy/results

    # performance, pinned (front core 0, upstream core 1, client cores 2-3)
    python3 bench/proxy/perf.py --httpd /tmp/httpd --out bench/proxy/results

Results land in `results/`: `matrix.md` / `matrix.json` and `detail_<front>.json`
for the HTTP/1 differential, `matrix_h2.md` for the h2 vectors, and `perf.md` /
`perf.json` for the load runs.

## The Bend reverse proxy (`proxyd`, demos/io_proxy)

    bun bend2/main.ts demos/io_proxy/main.bend -o /tmp/proxyd
    python3 bench/proxy/driver.py --fronts proxyd --proxyd /tmp/proxyd --out /tmp/res
    python3 bench/proxy/perf.py --fronts proxyd --proxyd /tmp/proxyd --httpd /tmp/httpd --out /tmp/res

scores it on the same corpus, by the same reference, as nginx and HAProxy.
