"""Generate the corpus of request byte streams into bench/proxy/corpus/.

Each HTTP/1 entry is a raw byte stream written to <nnn>_<family>_<name>.raw;
each HTTP/2 entry is an h2 script written to <nnn>_<family>_<name>.h2json (a
list of frame ops the driver replays through the `h2` package). An index.json
lists every entry with its family and its RFC-expected disposition:
  reject      the RFC reference refuses to frame it (400/431/414);
  accept:N    the reference frames exactly N requests.

The families are the known HTTP/1 smuggling and desync classes -- CL.TE, TE.CL,
TE.TE obfuscations, conflicting Content-Length, obs-fold, bare LF/CR, control
bytes, odd targets, pipelines, keep-alive, Expect, chunk tricks, upgrades -- and
the HTTP/2 downgrade vectors (H2.CL / H2.TE, TE in h2, CRLF injection, pseudo
abuse). The expected disposition is computed by the reference where the entry is
a raw stream, so the corpus and the oracle can never drift apart; h2 entries
carry a hand-written expectation since the reference is HTTP/1 only.
"""

import base64
import json
import os

import refparse

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "corpus")

_entries = []
_seq = 0


def _slug(s):
    return "".join(c if (c.isalnum()) else "_" for c in s.lower()).strip("_")[:48]


def add(family, name, data, expect=None):
    """A raw HTTP/1 stream. If expect is None it is computed by the reference."""
    global _seq
    if expect is None:
        expect, _reqs, _err = refparse.disposition(data)
    _seq += 1
    fn = "%03d_%s_%s.raw" % (_seq, _slug(family), _slug(name))
    _entries.append({
        "seq": _seq, "file": fn, "kind": "raw", "family": family,
        "name": name, "expect": expect, "nbytes": len(data),
        "bytes_b64": base64.b64encode(data).decode(),
    })
    with open(os.path.join(OUT, fn), "wb") as f:
        f.write(data)


def add_h2(family, name, script, expect):
    """An HTTP/2 script: a list of ops the driver replays via `h2`."""
    global _seq
    _seq += 1
    fn = "%03d_%s_%s.h2json" % (_seq, _slug(family), _slug(name))
    _entries.append({
        "seq": _seq, "file": fn, "kind": "h2", "family": family,
        "name": name, "expect": expect, "nbytes": None,
    })
    with open(os.path.join(OUT, fn), "w") as f:
        json.dump(script, f, indent=1)


CRLF = b"\r\n"


def req(line, headers, body=b""):
    out = line + CRLF
    for k, v in headers:
        out += k + b": " + v + CRLF
    out += CRLF + body
    return out


def build():
    # -- baseline good traffic (accept) -----------------------------------
    add("baseline", "simple get",
        b"GET / HTTP/1.1\r\nHost: a\r\n\r\n")
    add("baseline", "get with query",
        b"GET /p?x=1&y=2 HTTP/1.1\r\nHost: a\r\n\r\n")
    add("baseline", "post content-length",
        b"POST /e HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n\r\nhello")
    add("baseline", "chunked ok",
        b"POST /e HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"4\r\nWiki\r\n5\r\npedia\r\n0\r\n\r\n")
    add("baseline", "chunked with trailer",
        b"POST /e HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"3\r\nabc\r\n0\r\nX-Trace: 1\r\n\r\n")
    add("baseline", "head request",
        b"HEAD / HTTP/1.1\r\nHost: a\r\n\r\n")

    # -- pipelines (accept:N) ---------------------------------------------
    add("pipeline", "two gets",
        b"GET /a HTTP/1.1\r\nHost: a\r\n\r\nGET /b HTTP/1.1\r\nHost: a\r\n\r\n")
    add("pipeline", "three gets",
        b"".join(b"GET /%d HTTP/1.1\r\nHost: a\r\n\r\n" % i for i in range(3)))
    add("pipeline", "post then get",
        b"POST /e HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\n\r\nabc"
        b"GET /b HTTP/1.1\r\nHost: a\r\n\r\n")
    add("pipeline", "chunked then get",
        b"POST /e HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"3\r\nabc\r\n0\r\n\r\nGET /b HTTP/1.1\r\nHost: a\r\n\r\n")

    # -- CL.TE : Content-Length present with Transfer-Encoding ------------
    for name, te in [("plain", b"chunked"), ("upper", b"Chunked"),
                     ("mixed", b"cHuNkEd")]:
        add("cl_te", "cl then te " + name,
            b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\n"
            b"Transfer-Encoding: " + te + b"\r\n\r\n0\r\n\r\n")
    add("cl_te", "te then cl",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n"
        b"Content-Length: 6\r\n\r\n0\r\n\r\n")
    add("cl_te", "cl zero te chunked",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 0\r\n"
        b"Transfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")

    # -- TE.CL : the classic desync body ----------------------------------
    add("te_cl", "te chunked cl 4",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n"
        b"Content-Length: 4\r\n\r\n5c\r\nGPOST / HTTP/1.1\r\n\r\n0\r\n\r\n")

    # -- TE.TE : transfer-encoding obfuscation ----------------------------
    add("te_te", "trailing space value",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked \r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "leading space value",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding:  chunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "tab before value",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding:\tchunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "xchunked",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: xchunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "chunked space suffix token",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunkedx\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "chunked identity",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, identity\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "identity chunked",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: identity, chunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "double chunked one header",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, chunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "two te headers",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n"
        b"Transfer-Encoding: chunked\r\n\r\n0\r\n\r\n")
    add("te_te", "te gzip chunked two headers",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip\r\n"
        b"Transfer-Encoding: chunked\r\n\r\n0\r\n\r\n")
    add("te_te", "name with trailing space",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding : chunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "te in http 1.0",
        b"POST / HTTP/1.0\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"0\r\n\r\n")
    add("te_te", "vertical tab obfuscation",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\x0b\r\n\r\n"
        b"0\r\n\r\n")

    # -- Content-Length obfuscation ---------------------------------------
    add("cl_bad", "two conflicting cl",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n"
        b"Content-Length: 6\r\n\r\nhello")
    add("cl_bad", "two equal cl",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n"
        b"Content-Length: 5\r\n\r\nhello")
    add("cl_bad", "cl list conflict",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5, 6\r\n\r\nhello")
    add("cl_bad", "cl list equal",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5, 5\r\n\r\nhello")
    add("cl_bad", "cl plus sign",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: +5\r\n\r\nhello")
    add("cl_bad", "cl minus sign",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: -5\r\n\r\nhello")
    add("cl_bad", "cl leading space in value",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length:  5 \r\n\r\nhello")
    add("cl_bad", "cl trailing junk",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5x\r\n\r\nhello")
    add("cl_bad", "cl hex",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 0x5\r\n\r\nhello")
    add("cl_bad", "cl leading zeros",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 005\r\n\r\nhello")
    add("cl_bad", "cl overflow",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 18446744073709551616\r\n\r\n")
    add("cl_bad", "cl huge over cap",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 99999999\r\n\r\n")
    add("cl_bad", "cl tab padded",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length:\t5\r\n\r\nhello")

    # -- obs-fold ----------------------------------------------------------
    add("obs_fold", "folded value space",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Foo: bar\r\n baz\r\n\r\n")
    add("obs_fold", "folded value tab",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Foo: bar\r\n\tbaz\r\n\r\n")
    add("obs_fold", "folded host",
        b"GET / HTTP/1.1\r\nHost: a\r\n evil\r\n\r\n")

    # -- bare LF / CR ------------------------------------------------------
    add("bare_eol", "bare lf request line",
        b"GET / HTTP/1.1\nHost: a\r\n\r\n")
    add("bare_eol", "bare lf all",
        b"GET / HTTP/1.1\nHost: a\n\n")
    add("bare_eol", "bare lf header",
        b"GET / HTTP/1.1\r\nHost: a\nX-Y: z\r\n\r\n")
    add("bare_eol", "bare cr in value",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: a\rb\r\n\r\n")
    add("bare_eol", "bare lf then chunk",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"3\r\nabc\n0\r\n\r\n")
    add("bare_eol", "lf lf terminator",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\n\nabc")

    # -- NUL and control bytes --------------------------------------------
    add("ctrl", "nul in value",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: a\x00b\r\n\r\n")
    add("ctrl", "nul in name",
        b"GET / HTTP/1.1\r\nHost: a\r\nX\x00Y: z\r\n\r\n")
    add("ctrl", "control in value",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: a\x07b\r\n\r\n")
    add("ctrl", "nul in target",
        b"GET /a\x00b HTTP/1.1\r\nHost: a\r\n\r\n")
    add("ctrl", "control in target",
        b"GET /a\x1fb HTTP/1.1\r\nHost: a\r\n\r\n")
    add("ctrl", "del in value",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: a\x7fb\r\n\r\n")
    add("ctrl", "tab in value ok",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: a\tb\r\n\r\n")

    # -- header name / colon games ----------------------------------------
    add("name", "space before colon",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y : z\r\n\r\n")
    add("name", "empty name",
        b"GET / HTTP/1.1\r\nHost: a\r\n: z\r\n\r\n")
    add("name", "no colon",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y z\r\n\r\n")
    add("name", "space in name",
        b"GET / HTTP/1.1\r\nHost: a\r\nX Y: z\r\n\r\n")
    add("name", "unicode in name",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-\xc3\xa9: z\r\n\r\n")

    # -- request-line and target games ------------------------------------
    add("target", "absolute form",
        b"GET http://a/x HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "absolute form other host",
        b"GET http://evil/x HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "double space in line",
        b"GET  / HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "tab in request line",
        b"GET /\tx HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "missing version",
        b"GET /\r\nHost: a\r\n\r\n")
    add("target", "http 0.9 style",
        b"GET /\r\n\r\n")
    add("target", "bad version",
        b"GET / HTTP/3.0\r\nHost: a\r\n\r\n")
    add("target", "lowercase method",
        b"get / HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "asterisk form",
        b"OPTIONS * HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "very long target",
        b"GET /" + b"a" * 9000 + b" HTTP/1.1\r\nHost: a\r\n\r\n")
    add("target", "very long header line",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: " + b"a" * 20000 + b"\r\n\r\n")

    # -- Host games --------------------------------------------------------
    add("host", "no host 1.1",
        b"GET / HTTP/1.1\r\n\r\n")
    add("host", "two host",
        b"GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n")
    add("host", "no host 1.0 ok",
        b"GET / HTTP/1.0\r\n\r\n")

    # -- HTTP/1.0 keep-alive ----------------------------------------------
    add("keepalive", "1.0 keep-alive two",
        b"GET /a HTTP/1.0\r\nHost: a\r\nConnection: keep-alive\r\n\r\n"
        b"GET /b HTTP/1.0\r\nHost: a\r\nConnection: keep-alive\r\n\r\n")
    add("keepalive", "1.1 close",
        b"GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n")

    # -- Expect: 100-continue ---------------------------------------------
    add("expect", "expect 100 continue",
        b"POST /e HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\n"
        b"Content-Length: 3\r\n\r\nabc")
    add("expect", "expect unknown",
        b"POST /e HTTP/1.1\r\nHost: a\r\nExpect: 200-ok\r\n"
        b"Content-Length: 3\r\n\r\nabc")

    # -- chunk-size / extension / trailer games ---------------------------
    add("chunk", "chunk size overflow",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"ffffffffffffffff\r\nx\r\n0\r\n\r\n")
    add("chunk", "chunk size non hex",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"3g\r\nabc\r\n0\r\n\r\n")
    add("chunk", "chunk extension",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"3;name=val\r\nabc\r\n0\r\n\r\n")
    add("chunk", "chunk quoted extension",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b'3;n="a;b"\r\nabc\r\n0\r\n\r\n')
    add("chunk", "chunk leading zeros",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"003\r\nabc\r\n0\r\n\r\n")
    add("chunk", "chunk missing crlf after data",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"3\r\nabcX0\r\n\r\n")
    add("chunk", "chunk trailer smuggle",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"0\r\nGET /x HTTP/1.1\r\n\r\n")
    add("chunk", "chunk negative size",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
        b"-1\r\nabc\r\n0\r\n\r\n")

    # -- upgrade + trailing bytes -----------------------------------------
    add("upgrade", "websocket upgrade",
        b"GET /ws HTTP/1.1\r\nHost: a\r\nConnection: Upgrade\r\n"
        b"Upgrade: websocket\r\nSec-WebSocket-Key: x\r\n"
        b"Sec-WebSocket-Version: 13\r\n\r\n")
    add("upgrade", "upgrade trailing bytes",
        b"GET /ws HTTP/1.1\r\nHost: a\r\nConnection: Upgrade\r\n"
        b"Upgrade: websocket\r\n\r\nEXTRA-SMUGGLED-BYTES")
    add("upgrade", "h2c upgrade",
        b"GET / HTTP/1.1\r\nHost: a\r\nConnection: Upgrade, HTTP2-Settings\r\n"
        b"Upgrade: h2c\r\nHTTP2-Settings: AAMAAABkAARAAAAAAAIAAAAA\r\n\r\n")
    add("upgrade", "upgrade in 1.0",
        b"GET / HTTP/1.0\r\nHost: a\r\nConnection: Upgrade\r\n"
        b"Upgrade: websocket\r\n\r\n")

    # -- misc smuggling framings ------------------------------------------
    add("smuggle", "cl te space name",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\n"
        b"Transfer-Encoding : chunked\r\n\r\n0\r\n\r\nGPOST")
    add("smuggle", "double content length body",
        b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 44\r\n"
        b"Content-Length: 0\r\n\r\nGET /admin HTTP/1.1\r\nHost: a\r\n"
        b"Content-Length: 10\r\n\r\nx=")
    add("smuggle", "underscore te header",
        b"POST / HTTP/1.1\r\nHost: a\r\nTransfer_Encoding: chunked\r\n"
        b"Content-Length: 3\r\n\r\nabc")

    # -- systematic sweeps, to cover each byte position and each variant ---
    # every control byte in a header value (HTAB excepted; the reference
    # accepts it and refuses the rest).
    for b in list(range(0x01, 0x20)) + [0x7f]:
        add("ctrl_sweep", "value byte %02x" % b,
            b"GET / HTTP/1.1\r\nHost: a\r\nX-Y: a" + bytes([b]) + b"b\r\n\r\n")
    # every control byte in the request-target.
    for b in list(range(0x00, 0x21)) + [0x7f]:
        add("ctrl_sweep", "target byte %02x" % b,
            b"GET /a" + bytes([b]) + b"b HTTP/1.1\r\nHost: a\r\n\r\n")
    # Content-Length obfuscation matrix.
    for nm, v in [("space inside", b"5 5"), ("comma space", b"5, 6"),
                  ("comma tight", b"5,6"), ("comma equal", b"5,5"),
                  ("trailing comma", b"5,"), ("leading comma", b",5"),
                  ("dot", b"5.0"), ("hex prefix", b"0x5"),
                  ("plus", b"+5"), ("space plus", b" +5"), ("tab", b"\t5"),
                  ("newline pad", b"5 "), ("unicode digit", b"\xef\xbc\x95"),
                  ("empty", b""), ("just spaces", b"   "),
                  ("neg zero", b"-0"), ("big", b"99999999"),
                  ("overflow64", b"18446744073709551616")]:
        add("cl_sweep", nm,
            b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: " + v +
            b"\r\n\r\nhello")
    # Transfer-Encoding value obfuscation matrix.
    for nm, v in [("chunked", b"chunked"), ("CHUNKED", b"CHUNKED"),
                  ("Chunked", b"Chunked"), ("chunked sp", b"chunked "),
                  ("sp chunked", b" chunked"), ("chunkedx", b"chunkedx"),
                  ("xchunked", b"xchunked"), ("chunk", b"chunk"),
                  ("chunked comma", b"chunked,"), ("comma chunked", b",chunked"),
                  ("chunked id", b"chunked, identity"),
                  ("id chunked", b"identity, chunked"),
                  ("gzip chunked", b"gzip, chunked"),
                  ("chunked gzip", b"chunked, gzip"),
                  ("chunked cr", b"chunked\x0d"), ("chunked tab", b"chunked\t"),
                  ("chunked null", b"chunked\x00"), ("double", b"chunked, chunked"),
                  ("quoted", b'"chunked"'), ("chunked semi", b"chunked;")]:
        add("te_sweep", nm,
            b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: " + v +
            b"\r\n\r\n0\r\n\r\n")
    # pipelined mixes of varying depth.
    for d in (2, 4, 8):
        add("pipe_sweep", "depth %d" % d,
            b"".join(b"GET /%d HTTP/1.1\r\nHost: a\r\n\r\n" % i for i in range(d)))
    add("pipe_sweep", "get post get",
        b"GET /a HTTP/1.1\r\nHost: a\r\n\r\n"
        b"POST /e HTTP/1.1\r\nHost: a\r\nContent-Length: 2\r\n\r\nhi"
        b"GET /b HTTP/1.1\r\nHost: a\r\n\r\n")
    add("pipe_sweep", "good then bad",
        b"GET /a HTTP/1.1\r\nHost: a\r\n\r\n"
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y : z\r\n\r\n")
    add("pipe_sweep", "bad then good",
        b"GET / HTTP/1.1\r\nHost: a\r\nX-Y : z\r\n\r\n"
        b"GET /a HTTP/1.1\r\nHost: a\r\n\r\n")
    # absolute / authority-form target variants.
    for nm, t in [("http scheme", b"http://a/x"), ("https scheme", b"https://a/x"),
                  ("other host", b"http://evil.example/x"),
                  ("with port", b"http://a:80/x"),
                  ("authority form", b"a:443"),
                  ("scheme only", b"http:"), ("no scheme slashes", b"//a/x"),
                  ("backslash", b"/a\\b"), ("double slash path", b"//x"),
                  ("dotdot", b"/../x"), ("encoded dotdot", b"/%2e%2e/x"),
                  ("fragment", b"/x#y"), ("at sign", b"/x@y")]:
        add("target_sweep", nm,
            b"GET " + t + b" HTTP/1.1\r\nHost: a\r\n\r\n")

    # -- HTTP/2 downgrade vectors (scripts replayed via `h2`) -------------
    # Each op: {"send_headers":[[name,value],...], optional "body":"...",
    # "end":bool}. `expect` is the RFC/spec disposition at the h2 front.
    add_h2("h2", "plain get",
           [{"headers": [[":method", "GET"], [":path", "/"],
                         [":scheme", "http"], [":authority", "a"]],
             "end_stream": True}],
           "accept:1")
    add_h2("h2", "post with data",
           [{"headers": [[":method", "POST"], [":path", "/e"],
                         [":scheme", "http"], [":authority", "a"]],
             "body": "hello", "end_stream": True}],
           "accept:1")
    add_h2("h2_cl", "content-length disagrees short",
           [{"headers": [[":method", "POST"], [":path", "/e"],
                         [":scheme", "http"], [":authority", "a"],
                         ["content-length", "100"]],
             "body": "hello", "end_stream": True}],
           "reject")
    add_h2("h2_cl", "content-length disagrees long",
           [{"headers": [[":method", "POST"], [":path", "/e"],
                         [":scheme", "http"], [":authority", "a"],
                         ["content-length", "2"]],
             "body": "hello", "end_stream": True}],
           "reject")
    add_h2("h2_te", "transfer-encoding in h2",
           [{"headers": [[":method", "POST"], [":path", "/e"],
                         [":scheme", "http"], [":authority", "a"],
                         ["transfer-encoding", "chunked"]],
             "body": "0\r\n\r\n", "end_stream": True}],
           "reject")
    add_h2("h2_crlf", "crlf injection in value",
           [{"headers": [[":method", "GET"], [":path", "/"],
                         [":scheme", "http"], [":authority", "a"],
                         ["x-smuggle", "a\r\nGET /admin HTTP/1.1\r\nHost: a"]],
             "end_stream": True}],
           "reject")
    add_h2("h2_crlf", "crlf in path",
           [{"headers": [[":method", "GET"],
                         [":path", "/a HTTP/1.1\r\nHost: evil\r\n\r\nGET /b"],
                         [":scheme", "http"], [":authority", "a"]],
             "end_stream": True}],
           "reject")
    add_h2("h2_pseudo", "duplicate method pseudo",
           [{"headers": [[":method", "GET"], [":method", "POST"],
                         [":path", "/"], [":scheme", "http"],
                         [":authority", "a"]],
             "end_stream": True}],
           "reject")
    add_h2("h2_pseudo", "pseudo after regular",
           [{"headers": [[":method", "GET"], ["x-a", "1"],
                         [":path", "/"], [":scheme", "http"],
                         [":authority", "a"]],
             "end_stream": True}],
           "reject")
    add_h2("h2_pseudo", "unknown pseudo header",
           [{"headers": [[":method", "GET"], [":path", "/"],
                         [":scheme", "http"], [":authority", "a"],
                         [":protocol", "websocket"]],
             "end_stream": True}],
           "reject")
    add_h2("h2_pseudo", "connection header in h2",
           [{"headers": [[":method", "GET"], [":path", "/"],
                         [":scheme", "http"], [":authority", "a"],
                         ["connection", "keep-alive"]],
             "end_stream": True}],
           "reject")
    add_h2("h2_pseudo", "uppercase header name",
           [{"headers": [[":method", "GET"], [":path", "/"],
                         [":scheme", "http"], [":authority", "a"],
                         ["X-Upper", "1"]],
             "end_stream": True}],
           "reject")

    with open(os.path.join(OUT, "index.json"), "w") as f:
        json.dump({"count": len(_entries), "entries": _entries}, f, indent=1)

    fam = {}
    for e in _entries:
        fam[e["family"]] = fam.get(e["family"], 0) + 1
    return len(_entries), fam


if __name__ == "__main__":
    n, fam = build()
    print("corpus: %d entries" % n)
    for k in sorted(fam):
        print("  %-12s %d" % (k, fam[k]))
