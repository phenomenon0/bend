"""A strict RFC 9112 request framer, written from the RFC, not from the Bend
spec: a second, independent opinion on where one byte stream ends one request
and begins the next. It is deliberately conservative -- it refuses anything a
message-framing rule leaves ambiguous, because an ambiguity is exactly how a
request gets smuggled past one hop and re-read by the next.

frame(data) walks a buffer and returns (requests, status, error):
  requests  a list of framed Req, each with its method/target/headers, its
            body length, and the byte offsets [start, end) it framed;
  status    'complete' (every byte consumed into requests), 'partial' (a
            well-formed prefix, more bytes needed) or 'error';
  error     None, or a ParseErr with an RFC-shaped code and the byte offset.

The reference is used two ways: as the oracle disposition on a corpus entry's
original bytes, and, inside the echo-record upstream, to frame whatever a front
actually forwarded. A front desyncs when those two framings disagree.
"""

TCHAR = set(b"!#$%&'*+-.^_`|~0123456789"
            b"abcdefghijklmnopqrstuvwxyz"
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZ")
HEXDIG = set(b"0123456789abcdefABCDEF")
DIGIT = set(b"0123456789")
BODY_CAP = 1 << 20  # 1 MiB, the cap the Bend httpd enforces; noted, not fatal


class ParseErr(Exception):
    def __init__(self, code, off, why):
        super().__init__("%d @%d: %s" % (code, off, why))
        self.code = code
        self.off = off
        self.why = why


class Req:
    def __init__(self):
        self.method = b""
        self.target = b""
        self.version = b""
        self.headers = []      # list of (lower_name_bytes, value_bytes)
        self.raw_names = []     # original-case names, for reporting
        self.body_len = 0
        self.framing = ""      # 'none' | 'length' | 'chunked'
        self.start = 0
        self.end = 0
        self.notes = []        # non-fatal remarks (e.g. body-cap exceeded)

    def as_dict(self):
        return {
            "method": self.method.decode("latin1"),
            "target": self.target.decode("latin1"),
            "version": self.version.decode("latin1"),
            "headers": [[n.decode("latin1"), v.decode("latin1")]
                        for n, v in zip(self.raw_names,
                                        [v for _, v in self.headers])],
            "body_len": self.body_len,
            "framing": self.framing,
            "start": self.start,
            "end": self.end,
            "notes": self.notes,
        }


def _line(data, p):
    """Return (line_without_crlf, next_p) requiring a CRLF terminator.
    A bare LF or a lone CR is a framing error, not a line end."""
    i = p
    n = len(data)
    while i < n:
        c = data[i]
        if c == 0x0A:                       # LF not preceded by CR
            raise ParseErr(400, i, "bare LF line ending")
        if c == 0x0D:                       # CR: must be CRLF
            if i + 1 >= n:
                return None, p              # need more bytes
            if data[i + 1] != 0x0A:
                raise ParseErr(400, i, "bare CR in line")
            return data[p:i], i + 2
        i += 1
    return None, p                          # no terminator yet


def _one(data, p):
    """Frame exactly one request beginning at or after p. Returns
    (Req, next_p) or (None, p) if more bytes are needed."""
    n = len(data)

    # RFC 9112 2.2: ignore empty lines received prior to the request-line.
    start = p
    while True:
        line, q = _line(data, p)
        if line is None:
            return None, p
        if line == b"":
            p = q
            start = p
            continue
        break

    # request-line: method SP request-target SP HTTP-version
    if len(line) > 8 * 1024:
        raise ParseErr(414, start, "request-line over 8 KiB")
    parts = line.split(b" ")
    if len(parts) != 3:
        raise ParseErr(400, start, "request-line is not method SP target SP version")
    method, target, version = parts
    if not method or any(b not in TCHAR for b in method):
        raise ParseErr(400, start, "method is not a token")
    if not target:
        raise ParseErr(400, start, "empty request-target")
    for b in target:
        if b < 0x21 or b == 0x7F:
            raise ParseErr(400, start, "control or space byte in target")
    if version not in (b"HTTP/1.0", b"HTTP/1.1"):
        raise ParseErr(400, start, "unrecognised HTTP-version %r" % version)

    req = Req()
    req.method = method
    req.target = target
    req.version = version
    req.start = start
    p = q

    # header fields
    total = len(line)
    while True:
        hline, q = _line(data, p)
        if hline is None:
            return None, req.start
        if hline == b"":
            p = q
            break
        total += len(hline)
        if total > 16 * 1024:
            raise ParseErr(431, p, "header section over 16 KiB")
        if hline[0] in (0x20, 0x09):
            raise ParseErr(400, p, "obs-fold (leading space/tab)")
        ci = hline.find(b":")
        if ci < 0:
            raise ParseErr(400, p, "header line without a colon")
        name = hline[:ci]
        if not name or any(b not in TCHAR for b in name):
            raise ParseErr(400, p, "field-name is not a token (space before colon?)")
        val = hline[ci + 1:]
        # strip OWS
        val = val.strip(b" \t")
        for b in val:
            if b == 0x00 or (b < 0x20 and b != 0x09) or b == 0x7F:
                raise ParseErr(400, p, "control byte in field-value")
        req.headers.append((name.lower(), val))
        req.raw_names.append(name)
        p = q

    # Host: exactly one for 1.1, at most one for 1.0
    hosts = [v for k, v in req.headers if k == b"host"]
    if req.version == b"HTTP/1.1" and len(hosts) != 1:
        raise ParseErr(400, req.start, "HTTP/1.1 needs exactly one Host")
    if len(hosts) > 1:
        raise ParseErr(400, req.start, "multiple Host")

    # body framing: TE wins over CL, both together is invalid framing
    tes = [v for k, v in req.headers if k == b"transfer-encoding"]
    cls = [v for k, v in req.headers if k == b"content-length"]

    if tes:
        if req.version == b"HTTP/1.0":
            raise ParseErr(400, req.start, "Transfer-Encoding in HTTP/1.0")
        if len(tes) != 1:
            raise ParseErr(400, req.start, "multiple Transfer-Encoding")
        if tes[0].lower() != b"chunked":
            raise ParseErr(400, req.start,
                           "Transfer-Encoding is not exactly chunked: %r" % tes[0])
        if cls:
            raise ParseErr(400, req.start, "both Transfer-Encoding and Content-Length")
        req.framing = "chunked"
        end = _chunked(data, p, req)
        if end is None:
            return None, req.start
        req.end = end
        return req, end

    if cls:
        vals = []
        for v in cls:
            for tok in v.split(b","):
                vals.append(tok.strip(b" \t"))
        if any(not t or any(b not in DIGIT for b in t) for t in vals):
            raise ParseErr(400, req.start, "Content-Length is not 1*DIGIT")
        nums = set(int(t) for t in vals)
        if len(nums) != 1:
            raise ParseErr(400, req.start, "conflicting Content-Length: %r" % sorted(nums))
        clen = nums.pop()
        req.framing = "length"
        req.body_len = clen
        if clen > BODY_CAP:
            req.notes.append("content-length %d over 1 MiB cap" % clen)
        if p + clen > n:
            return None, req.start           # body not fully here yet
        req.end = p + clen
        return req, req.end

    # no framed body
    req.framing = "none"
    req.end = p
    return req, p


def _chunked(data, p, req):
    """Decode a chunked body from p; return end offset or None for more."""
    n = len(data)
    decoded = 0
    while True:
        line, q = _line(data, p)
        if line is None:
            return None
        # chunk-size [ chunk-ext ]
        semi = line.find(b";")
        size_field = line if semi < 0 else line[:semi]
        size_field = size_field.strip(b" \t")   # BWS the grammar allows
        if not size_field or any(b not in HEXDIG for b in size_field):
            raise ParseErr(400, p, "chunk-size is not 1*HEXDIG: %r" % size_field)
        size = int(size_field, 16)
        p = q
        if size == 0:
            # trailer section: field lines until an empty line
            while True:
                tline, q = _line(data, p)
                if tline is None:
                    return None
                if tline == b"":
                    return q
                if tline[0] in (0x20, 0x09):
                    raise ParseErr(400, p, "obs-fold in trailer")
                if tline.find(b":") < 0:
                    raise ParseErr(400, p, "trailer line without a colon")
                p = q
        decoded += size
        if decoded > BODY_CAP:
            req.notes.append("chunked body over 1 MiB cap")
        if p + size + 2 > n:
            return None
        # data then CRLF
        if data[p + size] != 0x0D or data[p + size + 1] != 0x0A:
            raise ParseErr(400, p + size, "chunk data not followed by CRLF")
        p = p + size + 2
        req.body_len = decoded


def frame(data):
    """Frame a whole buffer into as many requests as it holds.
    Returns (requests, status, error)."""
    reqs = []
    p = 0
    n = len(data)
    while p < n:
        try:
            req, q = _one(data, p)
        except ParseErr as e:
            return reqs, "error", e
        if req is None:
            return reqs, "partial", None
        reqs.append(req)
        p = q
    return reqs, "complete", None


def disposition(data):
    """The RFC-expected disposition of a raw byte stream: 'reject' (the
    reference refuses to frame it) or 'accept:N' (it frames N requests)."""
    reqs, status, err = frame(data)
    if status == "error":
        return "reject", reqs, err
    if status == "partial":
        # a well-formed but incomplete stream: whatever completed, plus a
        # dangling partial. Treated as reject at the framing level (the peer
        # never finished a message it began).
        return "reject", reqs, ParseErr(400, len(data), "incomplete trailing request")
    return "accept:%d" % len(reqs), reqs, None


if __name__ == "__main__":
    import sys
    raw = sys.stdin.buffer.read()
    d, reqs, err = disposition(raw)
    print("disposition:", d)
    for i, r in enumerate(reqs):
        print("  [%d] %s %s -> %s body=%d [%d,%d)" % (
            i, r.method.decode("latin1"), r.target.decode("latin1"),
            r.framing, r.body_len, r.start, r.end))
    if err:
        print("  error:", err)
