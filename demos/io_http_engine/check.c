// Behavioural checks for demos/io_http_engine, over a raw socket. The
// same binary checks the Bend engine and control.c, so "the same
// checks" is a claim the two are measured against rather than a
// sentence in a README. Given the server's pid, the last case also
// reads its CPU.
//
//   cc -std=c11 -O3 check.c -o check && ./check 8080 [pid] [--files] [--idle=MS]
//   ./check 8080 [pid] [--conns=N] [--term] [--ws] [--log=FILE] [--root=DIR]
#define _GNU_SOURCE
#include <errno.h>
#include <netinet/in.h>
#include <signal.h>
#include <netinet/tcp.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

static int PORT = 8080, pass = 0, fail = 0;

static int dial(void) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(PORT),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  struct timeval tv = { .tv_sec = 2, .tv_usec = 0 };
  if (connect(fd, (struct sockaddr*)&a, sizeof(a))) { close(fd); return -1; }
  setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
  return fd;
}

// The transport. Built plain, these are the socket calls themselves;
// built with -DCHECK_TLS they are a TLS session over the same socket,
// and every case below runs unchanged over it. One suite, two wires.
#ifdef CHECK_TLS
#include <openssl/ssl.h>
static SSL_CTX* tls_ctx;
static SSL*     tls_at[65536];

// A descriptor a case failed to open is -1, and every call here has to
// survive being handed one: plain, that is a write to -1 and an EBADF;
// here it would be a read from outside the table.
static SSL* tls_look(int fd) {
  return fd >= 0 && fd < 65536 ? tls_at[fd] : NULL;
}

static int wire_open(void) {
  if (tls_ctx == NULL) {
    tls_ctx = SSL_CTX_new(TLS_client_method());
    SSL_CTX_set_verify(tls_ctx, SSL_VERIFY_NONE, NULL);
  }
  int fd = dial();
  if (fd < 0) {
    return -1;
  }
  SSL* ssl = SSL_new(tls_ctx);
  SSL_set_fd(ssl, fd);
  if (SSL_connect(ssl) != 1) {
    SSL_free(ssl);
    close(fd);
    return -1;
  }
  tls_at[fd] = ssl;
  return fd;
}

static ssize_t wire_write(int fd, const void* b, size_t n) {
  SSL* ssl = tls_look(fd);
  if (ssl == NULL) {
    return write(fd, b, n);
  }
  int k = SSL_write(ssl, b, (int)n);
  return k > 0 ? (ssize_t)k : -1;
}

// A server that ends a connection sends its close_notify first, so a
// clean end reads as zero here as it does on a plain socket; anything
// else is the error it is.
static ssize_t wire_read(int fd, void* b, size_t n, int flags) {
  SSL* ssl = tls_look(fd);
  if (ssl == NULL) {
    return recv(fd, b, n, flags);
  }
  if ((flags & MSG_DONTWAIT) != 0 && SSL_pending(ssl) == 0) {
    char peek;
    if (recv(fd, &peek, 1, MSG_PEEK | MSG_DONTWAIT) < 0) {
      return -1;
    }
  }
  int k = SSL_read(ssl, b, (int)n);
  if (k > 0) {
    return k;
  }
  return SSL_get_error(ssl, k) == SSL_ERROR_ZERO_RETURN ? 0 : -1;
}

static void wire_close(int fd) {
  SSL* ssl = tls_look(fd);
  if (ssl != NULL) {
    SSL_free(ssl);
    tls_at[fd] = NULL;
  }
  if (fd >= 0) {
    close(fd);
  }
}
#else
#define wire_open()                dial()
#define wire_write(fd, b, n)       write((fd), (b), (n))
#define wire_read(fd, b, n, flags) recv((fd), (b), (n), (flags))
#define wire_close(fd)             close(fd)
#endif

// send the parts in order, then read until the peer stops or want bytes
// have arrived; returns what came back
static int ask(const char** parts, const int* lens, int n, char* out, int cap,
               int want) {
  int fd = wire_open();
  if (fd < 0) return -1;
  for (int i = 0; i < n; i++) {
    if (i) { struct timespec t = { 0, 120000000 }; nanosleep(&t, NULL); }
    if (wire_write(fd, parts[i], (size_t)lens[i]) != lens[i]) { wire_close(fd); return -1; }
  }
  int got = 0;
  while (got < cap) {
    ssize_t k = wire_read(fd, out + got, (size_t)(cap - got), 0);
    if (k <= 0) break;
    got += (int)k;
    if (want > 0 && got >= want) break;
  }
  wire_close(fd);
  return got;
}

static int one(const char* req, int len, char* out, int cap, int want) {
  const char* p[1] = { req };
  int l[1] = { len };
  return ask(p, l, 1, out, cap, want);
}

static void check(const char* name, int ok, const char* got, int n) {
  printf("%s  %s\n", ok ? "PASS" : "FAIL", name);
  if (!ok) {
    printf("   got %d bytes: %.*s\n", n, n > 200 ? 200 : n, got);
    fail += 1;
  } else {
    pass += 1;
  }
}

// does the reply hold this text
static int has(const char* b, int n, const char* s) {
  return memmem(b, (size_t)n, s, strlen(s)) != NULL;
}

// The server's CPU seconds, for the case that needs them.
static double cpu_of(long pid) {
  char path[64], buf[4096];
  snprintf(path, sizeof(path), "/proc/%ld/stat", pid);
  FILE* f = fopen(path, "r");
  if (f == NULL) return -1;
  size_t n = fread(buf, 1, sizeof(buf) - 1, f);
  fclose(f);
  buf[n] = 0;
  char* p = strrchr(buf, ')');
  if (p == NULL) return -1;
  long ut = 0, st = 0;
  // fields 3..15 after the comm; utime is the 14th field, stime the 15th
  if (sscanf(p + 2, "%*c %*d %*d %*d %*d %*d %*u %*u %*u %*u %*u %ld %ld",
    &ut, &st) != 2) return -1;
  return (double)(ut + st) / (double)sysconf(_SC_CLK_TCK);
}


// WebSocket, for the --ws cases: the handshake with RFC 6455's own key,
// whose accept value the RFC gives; masked client frames built here;
// the server's unmasked frames read back.
static int ws_open(void) {
  static const char up[] = "GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\n"
    "Connection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n"
    "Sec-WebSocket-Version: 13\r\n\r\n";
  int fd = wire_open();
  if (wire_write(fd, up, sizeof(up) - 1) != (ssize_t)(sizeof(up) - 1)) perror("write");
  char b[1024];
  int n = (int)wire_read(fd, b, sizeof(b), 0);
  if (n <= 0 || !has(b, n, "101 Switching Protocols")
      || !has(b, n, "sec-websocket-accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=")) { wire_close(fd); return -1; }
  return fd;
}

// a client frame: FIN, the opcode, the mask bit, the length, a mask, the
// payload masked; returns the bytes written into out
static int ws_frame(char* out, int op, const char* body, int n, int masked) {
  int k = 0;
  out[k++] = (char)(0x80 | op);
  if (n < 126) out[k++] = (char)((masked ? 0x80 : 0) | n);
  else { out[k++] = (char)((masked ? 0x80 : 0) | 126); out[k++] = (char)(n >> 8); out[k++] = (char)(n & 255); }
  const char m[4] = { 0x11, 0x22, 0x33, 0x44 };
  if (masked) { memcpy(out + k, m, 4); k += 4; }
  for (int i = 0; i < n; i++) out[k++] = masked ? (char)(body[i] ^ m[i % 4]) : body[i];
  return k;
}

// read until want bytes have arrived, the peer closed, or the socket's
// two-second timeout passed
static int ws_read(int fd, char* b, int cap, int want, int* closed) {
  int n = 0;
  while (n < want && n < cap) {
    int got = (int)wire_read(fd, b + n, (size_t)(cap - n), 0);
    if (got == 0) { *closed = 1; break; }
    if (got < 0) break;
    n += got;
  }
  return n;
}

// Static files under a root the check writes itself (--root=DIR, the
// directory the server was given): a file's bytes are a pattern of
// their offset, so any byte out of place is seen; a stream reads
// replies of one known length, head then body, and says whether every
// one arrived whole and byte for byte.
static uint8_t pat(uint32_t i) { return (uint8_t)((i * 2654435761u) >> 24); }

static int put_file(const char* dir, const char* name, uint32_t n) {
  char p[1024];
  static uint8_t buf[65536];
  snprintf(p, sizeof(p), "%s/%s", dir, name);
  FILE* f = fopen(p, "wb");
  if (f == NULL) return -1;
  for (uint32_t i = 0; i < n;) {
    uint32_t k = n - i < sizeof(buf) ? n - i : (uint32_t)sizeof(buf);
    for (uint32_t j = 0; j < k; j++) buf[j] = pat(i + j);
    if (fwrite(buf, 1, k, f) != k) { fclose(f); return -1; }
    i += k;
  }
  return fclose(f);
}

// the server's peak resident set, in kB, from /proc
static long hwm_of(long pid) {
  char path[64], line[256];
  long kb = -1;
  snprintf(path, sizeof(path), "/proc/%ld/status", pid);
  FILE* f = fopen(path, "r");
  if (f == NULL) return -1;
  while (fgets(line, sizeof(line), f)) if (sscanf(line, "VmHWM: %ld", &kb) == 1) break;
  fclose(f);
  return kb;
}

typedef struct {
  int fd, done, bad, body, hn, replies;
  long left, len, got;
  uint32_t off;
  char h[512];
} Stream;

static void stream_feed(Stream* s, const char* b, long n) {
  for (long i = 0; i < n;) {
    if (!s->body) {
      if (s->hn >= 511) { s->bad = 1; return; }
      s->h[s->hn++] = b[i++];
      s->h[s->hn] = 0;
      if (s->hn < 4 || memcmp(s->h + s->hn - 4, "\r\n\r\n", 4) != 0) continue;
      char* cl = strstr(s->h, "content-length: ");
      if (!has(s->h, s->hn, "200 OK") || cl == NULL || atol(cl + 16) != s->len) s->bad = 1;
      s->left = s->len; s->off = 0; s->hn = 0; s->body = 1;
    } else {
      long k = n - i < s->left ? n - i : s->left;
      for (long j = 0; j < k; j++) s->bad |= (uint8_t)b[i + j] != pat(s->off + (uint32_t)j);
      s->off += (uint32_t)k; s->left -= k; s->got += k; i += k;
    }
    if (s->body && s->left == 0) { s->body = 0; s->replies += 1; }
  }
}

// read every stream until its peer closes, or 30 s have passed
static void stream_all(Stream* ss, int m) {
  static char buf[65536];
  time_t t0 = time(NULL);
  int open_ = m;
  while (open_ > 0 && time(NULL) - t0 < 30) {
    int moved = 0;
    for (int i = 0; i < m; i++) {
      if (ss[i].done) continue;
      ssize_t k = wire_read(ss[i].fd, buf, sizeof(buf), MSG_DONTWAIT);
      if (k > 0) { stream_feed(&ss[i], buf, k); moved = 1; continue; }
      if (k < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) continue;
      ss[i].done = 1; open_ -= 1; wire_close(ss[i].fd);
    }
    if (!moved) usleep(500);
  }
}

// m connections, each asking for the file reps times in one write
static int stream_ask(const char* path, long len, int m, int reps) {
  static Stream ss[64];
  static char req[16384];
  int n = 0, ok = 1;
  for (int r = 0; r < reps; r++) n += snprintf(req + n, sizeof(req) - (size_t)n,
    "GET %s HTTP/1.1\r\nHost: x\r\n%s\r\n", path, r == reps - 1 ? "connection: close\r\n" : "");
  for (int i = 0; i < m; i++) {
    memset(&ss[i], 0, sizeof(ss[i]));
    ss[i].len = len;
    ss[i].fd = wire_open();
    if (ss[i].fd < 0 || wire_write(ss[i].fd, req, (size_t)n) != n) ss[i].bad = 1;
  }
  stream_all(ss, m);
  for (int i = 0; i < m; i++) ok = ok && !ss[i].bad && ss[i].replies == reps;
  return ok;
}

#define TEXT(s) s, (int)(sizeof(s) - 1)

int main(int argc, char** argv) {
  if (argc > 1) PORT = atoi(argv[1]);
  static char b[262144];
  int n;
  const char* logf = NULL;
  // --root=DIR: the server's --root, where the check writes fixtures
  const char* root = NULL;
  // flags after the pid: --files when the server has --root on the
  // fixture directory; --idle=MS when it was started with --idle-ms MS
  // --conns=N when it was started with --max-conns N; --term to end by
  // sending it SIGTERM (last, since the server is gone afterwards)
  int files = 0, idle = 0, conns = 0, term = 0, ws = 0;
  // --log=PATH: the file the server's stderr was sent to, when it was
  // started with --log
  for (int i = 3; i < argc; i++) {
    if (strcmp(argv[i], "--files") == 0) files = 1;
    else if (strcmp(argv[i], "--ws") == 0) ws = 1;
    else if (strncmp(argv[i], "--idle=", 7) == 0) idle = atoi(argv[i] + 7);
    else if (strncmp(argv[i], "--conns=", 8) == 0) conns = atoi(argv[i] + 8);
    else if (strcmp(argv[i], "--term") == 0) term = 1;
    else if (strncmp(argv[i], "--log=", 6) == 0) logf = argv[i] + 6;
    else if (strncmp(argv[i], "--root=", 7) == 0) root = argv[i] + 7;
  }
  // under --root, "/" is index.html rather than the banner
  const char* root_body = files ? "<h1>hi</h1>" : "bend-http";

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
  check("GET /health", has(b, n, "200 OK") && has(b, n, "{\"ok\":true}"), b, n);

  n = one(TEXT("GET / HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
  check("GET / root", has(b, n, "200 OK") && has(b, n, root_body), b, n);

  n = one(TEXT("GET /nope HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 96);
  check("unknown route is 404", has(b, n, "404 Not Found"), b, n);

  n = one(TEXT("POST /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 5\r\n\r\nhello"),
    b, sizeof(b), 104);
  check("an unimplemented method is 405", has(b, n, "405 Method Not Allowed"), b, n);

  n = one(TEXT("GET /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 5\r\n\r\nhello"),
    b, sizeof(b), 110);
  check("a body comes back from /echo", has(b, n, "200 OK") && has(b, n, "hello"),
    b, n);

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n"),
    b, sizeof(b), 204);
  check("two pipelined requests, two replies",
    has(b, n, "{\"ok\":true}") && has(b, n, root_body), b, n);

  n = one(TEXT("GET /echo HTTP/1.1\r\nHOST: x\r\nCoNtEnT-LeNgTh: 3\r\n\r\nabc"),
    b, sizeof(b), 108);
  check("a field name is case-insensitive",
    has(b, n, "200 OK") && has(b, n, "abc"), b, n);

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\ntransfer-encoding: chunked"
    "\r\n\r\n0\r\n\r\n"), b, sizeof(b), 0);
  check("Transfer-Encoding is refused", has(b, n, "400 Bad Request"), b, n);

  n = one(TEXT("GET /health HTTP/1.0\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
  check("HTTP/1.0 is refused", has(b, n, "400 Bad Request"), b, n);

  n = one(TEXT("GET /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 5x\r\n\r\n"),
    b, sizeof(b), 0);
  check("a non-digit Content-Length is refused", has(b, n, "400 Bad Request"), b, n);

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\nconnection: close\r\n\r\n"),
    b, sizeof(b), 0);
  check("Connection: close is answered then closed", has(b, n, "200 OK"), b, n);

  {
    const char* p[3] = { "GET /hea", "lth HTTP/1.1\r\nHo", "st: x\r\n\r\n" };
    int l[3] = { 8, 16, 9 };
    n = ask(p, l, 3, b, sizeof(b), 106);
    check("a head split across three writes still parses",
      has(b, n, "200 OK") && has(b, n, "{\"ok\":true}"), b, n);
  }

  // Every byte value, through a body and back. A reader that decodes
  // the wire as text fails here and nowhere else: the reply is longer
  // than the Content-Length it announced, which desynchronises a
  // keep-alive connection rather than merely corrupting one body.
  {
    char req[512 + 256];
    int  h = snprintf(req, sizeof(req),
      "GET /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 256\r\n\r\n");
    for (int i = 0; i < 256; i++) req[h + i] = (char)i;
    n = one(req, h + 256, b, sizeof(b), 0);
    char* body = memmem(b, (size_t)n, "\r\n\r\n", 4);
    int   ok   = body != NULL && (n - (int)(body + 4 - b)) == 256;
    if (ok) for (int i = 0; i < 256; i++)
      ok = ok && (uint8_t)body[4 + i] == (uint8_t)i;
    check("all 256 byte values survive a body round trip", ok, b, n);
  }

  n = one(TEXT("HEAD /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
  check("HEAD is GET's head and no body",
    has(b, n, "content-length: 11") && memmem(b, (size_t)n, "\r\n\r\n", 4) != NULL
    && n == (int)(memmem(b, (size_t)n, "\r\n\r\n", 4) - (void*)b) + 4, b, n);

  n = one(TEXT("POST /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
  check("405 names the methods that work", has(b, n, "allow: GET, HEAD"), b, n);

  // Framing. Each of these is how a request gets smuggled past a proxy
  // that reads it another way; each is a 400 that says it closes.
  static const char* smuggled[][2] = {
    { "a space before a colon", "GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length : 5\r\n\r\nhello" },
    { "a Transfer-Encoding with a space before its colon",
      "GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding : chunked\r\nContent-Length: 5\r\n\r\nhello" },
    { "two Content-Lengths that disagree",
      "GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nContent-Length: 5\r\n\r\nabcde" },
    { "a Content-Length past 2^32", "GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 4294967301\r\n\r\nhello" },
    { "a Content-Length list", "GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5, 5\r\n\r\nhello" },
    { "a folded line", "GET /echo HTTP/1.1\r\nHost: x\r\nX: a\r\n Content-Length: 5\r\n\r\nhello" },
    { "a bare LF", "GET /echo HTTP/1.1\r\nHost: x\r\nX: a\nContent-Length: 5\r\n\r\nhello" },
    { "a line without a colon", "GET /echo HTTP/1.1\r\nHost: x\r\nFoo\r\nContent-Length: 5\r\n\r\nhello" },
    { "a CR in the target", "GET /a\rb HTTP/1.1\r\nHost: x\r\n\r\n" },
    { "no Host", "GET /health HTTP/1.1\r\n\r\n" },
    { "two Hosts", "GET /health HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n" } };
  for (int i = 0; i < (int)(sizeof(smuggled) / sizeof(smuggled[0])); i++) {
    char what[96];
    snprintf(what, sizeof(what), "%s is refused", smuggled[i][0]);
    n = one(smuggled[i][1], (int)strlen(smuggled[i][1]), b, sizeof(b), 0);
    check(what, has(b, n, "400 Bad Request") && has(b, n, "connection: close")
      && !has(b, n, "200 OK"), b, n);
  }

  n = one(TEXT("GET /echo HTTP/1.1\r\nHost: x\r\nx-v5fged: 5\r\n\r\nhelloGET /health HTTP/1.1\r\nHost: x\r\n\r\n"),
    b, sizeof(b), 0);
  check("a name whose hash is Content-Length's is not one",
    has(b, n, "content-length: 0") && has(b, n, "405 Method Not Allowed"), b, n);

  n = one(TEXT("GET /health?x=1 HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
  check("a query is no part of the path", has(b, n, "200 OK"), b, n);

  n = one(TEXT("\r\nGET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
  check("an empty line before a request is skipped", has(b, n, "200 OK"), b, n);

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\nConnection: keep-alive, close\r\n\r\n"
    "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
  check("close anywhere in Connection closes, and nothing after it is served",
    has(b, n, "200 OK") && has(b, n, "connection: close") && !has(b, n, "404"), b, n);

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\nGET /health HTTP/1.1\r\nHost: x\r\nX : y\r\n\r\n"),
    b, sizeof(b), 0);
  check("a bad request after a good one: the good one's reply, then the 400",
    has(b, n, "200 OK") && has(b, n, "400 Bad Request")
    && (char*)memmem(b, (size_t)n, "200 OK", 6) < (char*)memmem(b, (size_t)n, "400 Bad", 7), b, n);

  // Static files, when the server was started with --root on the
  // fixture directory the harness writes: index.html "<h1>hi</h1>\n",
  // a.txt "alpha\n", img.png the 256 byte values, sub/b.css "b{}\n".
  if (files) {
    n = one(TEXT("GET /a.txt HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a file is served with its type",
      has(b, n, "200 OK") && has(b, n, "text/plain") && has(b, n, "alpha\n"), b, n);

    n = one(TEXT("HEAD /a.txt HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("HEAD of a file is its head",
      has(b, n, "content-length: 6") && !has(b, n, "alpha"), b, n);

    n = one(TEXT("GET / HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("/ is index.html under a root",
      has(b, n, "text/html") && has(b, n, "<h1>hi</h1>"), b, n);

    n = one(TEXT("GET /sub/b.css HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a nested file, typed by extension",
      has(b, n, "text/css") && has(b, n, "b{}"), b, n);

    n = one(TEXT("GET /img.png HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    {
      char* body = memmem(b, (size_t)n, "\r\n\r\n", 4);
      int   ok   = body != NULL && has(b, n, "image/png")
        && (n - (int)(body + 4 - b)) == 256;
      if (ok) for (int i = 0; i < 256; i++) ok = ok && (uint8_t)body[4 + i] == (uint8_t)i;
      check("a binary file arrives byte for byte", ok, b, n);
    }

    n = one(TEXT("GET /nope.txt HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a missing file is 404", has(b, n, "404 Not Found"), b, n);

    n = one(TEXT("GET /../etc/passwd HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a climb out of the root is refused", has(b, n, "404 Not Found"), b, n);

    n = one(TEXT("GET /sub/../a.txt HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a climb that stays under the root resolves",
      has(b, n, "200 OK") && has(b, n, "alpha\n"), b, n);

    n = one(TEXT("GET /sub HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a directory is not a file", has(b, n, "404 Not Found"), b, n);
  }

  // Static files that must not escape the root or the memory: with
  // --root=DIR the check writes its own fixtures there -- a symbolic
  // link to /etc/passwd, one to /etc, a dotfile, and files whose bytes
  // are a pattern of their offset. Given the pid, the peak resident set
  // is read after the two cases that would once have loaded every file
  // they asked for.
  if (root != NULL) {
    char p[1024];
    const char* made[] = { "pw", "etcl", ".env", "big.bin", "mid.bin", "shrink.bin" };
    for (int i = 0; i < 6; i++) { snprintf(p, sizeof(p), "%s/%s", root, made[i]); unlink(p); }
    snprintf(p, sizeof(p), "%s/pw", root);
    int fx = symlink("/etc/passwd", p);
    snprintf(p, sizeof(p), "%s/etcl", root);
    fx |= symlink("/etc", p);
    fx |= put_file(root, ".env", 9) | put_file(root, "big.bin", 4194304)
      | put_file(root, "mid.bin", 1048576) | put_file(root, "shrink.bin", 16777216);
    check("the fixtures are written", fx == 0, "", 0);

    n = one(TEXT("GET /pw HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a symbolic link to /etc/passwd is 404", has(b, n, "404 Not Found") && !has(b, n, "root:"), b, n);

    n = one(TEXT("GET /etcl/passwd HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a symbolic link to a directory is 404", has(b, n, "404 Not Found") && !has(b, n, "root:"), b, n);

    n = one(TEXT("GET /.env HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("a dotfile is 404", has(b, n, "404 Not Found"), b, n);

    check("a 4 MiB file arrives whole, byte for byte, at its length",
      stream_ask("/big.bin", 4194304, 1, 1), "", 0);

    long pid = argc > 2 ? atol(argv[2]) : 0;
    char why[96];
    int ok = stream_ask("/big.bin", 4194304, 32, 1);
    long kb = pid > 0 ? hwm_of(pid) : 0;
    snprintf(why, sizeof(why), "VmHWM %ld kB", kb);
    check("32 clients at once get the 4 MiB file, and memory stays under 20 MB",
      ok && kb < 20480, why, (int)strlen(why));

    ok = stream_ask("/mid.bin", 1048576, 1, 100);
    kb = pid > 0 ? hwm_of(pid) : 0;
    snprintf(why, sizeof(why), "VmHWM %ld kB", kb);
    check("100 pipelined GETs of a 1 MiB file, and memory stays under 20 MB",
      ok && kb < 20480, why, (int)strlen(why));

    // A file that shrinks while it is written: its head promised the
    // length, so the connection must end rather than hang or pad, and
    // what did arrive is the file's own bytes.
    Stream s1;
    memset(&s1, 0, sizeof(s1));
    s1.len = 16777216;
    s1.fd = wire_open();
    static const char sreq[] = "GET /shrink.bin HTTP/1.1\r\nHost: x\r\n\r\n";
    if (wire_write(s1.fd, sreq, sizeof(sreq) - 1) != (ssize_t)(sizeof(sreq) - 1)) perror("write");
    while (s1.got < 65536) {
      ssize_t k = wire_read(s1.fd, b, 4096, 0);
      if (k <= 0) break;
      stream_feed(&s1, b, k);
    }
    snprintf(p, sizeof(p), "%s/shrink.bin", root);
    if (truncate(p, 0) != 0) perror("truncate");
    stream_all(&s1, 1);
    snprintf(why, sizeof(why), "got %ld of 16777216", s1.got);
    n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
    check("a file that shrinks mid-reply ends the connection, and the server serves on",
      !s1.bad && s1.replies == 0 && s1.got < 16777216 && s1.done && has(b, n, "200 OK"),
      why, (int)strlen(why));
  }

  // Time and size, when the idle time is known. A peer that goes quiet,
  // mid-head or between requests, is dropped once the idle time has
  // passed; one that pauses for less keeps its connection; a head that
  // announces a body past the cap is refused before a byte of it is
  // sent; a head dribbled a byte at a time is dropped after the wait
  // budget, well inside the idle time.
  if (idle > 0) {
    static const char req[] = "GET /health HTTP/1.1\r\nHost: x\r\n\r\n";
    const int reqn = (int)(sizeof(req) - 1);
    // a peer that is dropped reads EOF (0); a 2 s read timeout is -1
    int fd = wire_open();
    if (wire_write(fd, "GET /hea", 8) != 8) perror("write");
    usleep((useconds_t)(idle + 300) * 1000);
    n = (int)wire_read(fd, b, sizeof(b), 0);
    check("a head that stalls is dropped after the idle time", n == 0, b, n > 0 ? n : 0);
    wire_close(fd);

    fd = wire_open();
    if (wire_write(fd, req, (size_t)reqn) != reqn) perror("write");
    n = (int)wire_read(fd, b, sizeof(b), 0);
    usleep((useconds_t)(idle + 300) * 1000);
    n = (int)wire_read(fd, b, sizeof(b), 0);
    check("an idle keep-alive connection is dropped after the idle time", n == 0, b, n > 0 ? n : 0);
    wire_close(fd);

    fd = wire_open();
    if (wire_write(fd, req, (size_t)reqn) != reqn) perror("write");
    n = (int)wire_read(fd, b, sizeof(b), 0);
    usleep((useconds_t)(idle / 2) * 1000);
    if (wire_write(fd, req, (size_t)reqn) != reqn) perror("write");
    n = (int)wire_read(fd, b, sizeof(b), 0);
    check("a pause shorter than the idle time keeps the connection", n > 0 && has(b, n, "200 OK"), b, n > 0 ? n : 0);
    wire_close(fd);

    n = one(TEXT("GET /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 2000000\r\n\r\n"), b, sizeof(b), 0);
    check("a body past the cap is refused before it is sent", has(b, n, "400 Bad Request"), b, n);

    fd = wire_open();
    const char* slow = "GET /health HTTP/1.1\r\nHost: x\r\nx-a: 0123456789012345678901234567890123456789012345678901234567890123456789\r\n\r\n";
    int dropped = 0, sl = (int)strlen(slow);
    for (int i = 0; i < sl && !dropped; i++) {
      if (wire_write(fd, slow + i, 1) != 1) dropped = 1;
      usleep(3000);
      n = (int)wire_read(fd, b, sizeof(b), MSG_DONTWAIT);
      if (n == 0 || (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK)) dropped = 1;
    }
    check("a head dribbled a byte at a time is dropped after the wait budget", dropped, b, 0);
    wire_close(fd);
  }

  // A peer that connects and closes without sending a byte. The engine
  // as first written read again on the empty recv, and one such peer
  // cost most of a core in passes until its fuel ran out. Given the
  // server's pid (./check 8080 <pid>) this measures it: twenty silent
  // closes, one second, and the server's CPU must not have moved.
  if (argc > 2) {
    long   pid = atol(argv[2]);
    double c0  = cpu_of(pid);
    for (int i = 0; i < 20; i++) { int fd = wire_open(); if (fd >= 0) wire_close(fd); }
    usleep(1000000);
    double c1 = cpu_of(pid);
    n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
    char why[96];
    snprintf(why, sizeof(why), "cpu moved %.3fs", c1 - c0);
    check("twenty silent closes cost no CPU",
      c0 >= 0 && c1 - c0 < 0.05 && has(b, n, "200 OK"), why, (int)strlen(why));
  }

  // WebSocket. The handshake earns the RFC's accept value; text comes
  // back as text, a ping as a pong, a 300-byte binary with its two-byte
  // length, a frame split across two writes whole; an unmasked client
  // frame ends the connection with 1002; a close is answered and ends
  // it; a plain GET of /ws is a 426.
  if (ws) {
    char f[1024], r[1024];
    int fd = ws_open(), k, closed;
    check("the handshake answers RFC 6455's accept key", fd >= 0, "", 0);

    k = ws_frame(f, 1, "hello", 5, 1); if (wire_write(fd, f, (size_t)k) != k) perror("write");
    closed = 0; n = ws_read(fd, r, sizeof(r), 7, &closed);
    check("a masked text frame comes back as text",
      n == 7 && (uint8_t)r[0] == 0x81 && r[1] == 5 && !memcmp(r + 2, "hello", 5), r, n);

    k = ws_frame(f, 9, "p", 1, 1); if (wire_write(fd, f, (size_t)k) != k) perror("write");
    n = ws_read(fd, r, sizeof(r), 3, &closed);
    check("a ping is answered with a pong", n == 3 && (uint8_t)r[0] == 0x8A && r[1] == 1 && r[2] == 'p', r, n);

    {
      char big[300]; for (int i = 0; i < 300; i++) big[i] = (char)(i * 7);
      k = ws_frame(f, 2, big, 300, 1); if (wire_write(fd, f, (size_t)k) != k) perror("write");
      n = ws_read(fd, r, sizeof(r), 304, &closed);
      int ok = n == 304 && (uint8_t)r[0] == 0x82 && (uint8_t)r[1] == 126 && r[2] == 1 && (uint8_t)r[3] == 44
        && !memcmp(r + 4, big, 300);
      check("a 300-byte binary frame comes back with its two-byte length", ok, r, n > 40 ? 40 : n);
    }

    k = ws_frame(f, 1, "split", 5, 1);
    if (wire_write(fd, f, 4) != 4) perror("write");
    usleep(20000);
    if (wire_write(fd, f + 4, (size_t)(k - 4)) != k - 4) perror("write");
    n = ws_read(fd, r, sizeof(r), 7, &closed);
    check("a frame split across two writes still parses",
      n == 7 && (uint8_t)r[0] == 0x81 && r[1] == 5 && !memcmp(r + 2, "split", 5), r, n);

    k = ws_frame(f, 8, "\x03\xe8", 2, 1); if (wire_write(fd, f, (size_t)k) != k) perror("write");
    n = ws_read(fd, r, sizeof(r), 4, &closed);
    int gone = closed; if (!gone) { char x[8]; gone = wire_read(fd, x, sizeof(x), 0) == 0; }
    check("a close is answered with a close and the connection ends",
      n == 4 && (uint8_t)r[0] == 0x88 && r[1] == 2 && r[2] == 3 && (uint8_t)r[3] == 0xe8 && gone, r, n);
    wire_close(fd);

    fd = ws_open();
    k = ws_frame(f, 1, "bare", 4, 0); if (wire_write(fd, f, (size_t)k) != k) perror("write");
    closed = 0; n = ws_read(fd, r, sizeof(r), 4, &closed);
    gone = closed; if (!gone) { char x[8]; gone = wire_read(fd, x, sizeof(x), 0) == 0; }
    check("an unmasked client frame ends the connection with 1002",
      n == 4 && (uint8_t)r[0] == 0x88 && r[1] == 2 && r[2] == 3 && (uint8_t)r[3] == 0xea && gone, r, n);
    wire_close(fd);

    n = one(TEXT("GET /ws HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("GET /ws without an upgrade is 426", has(b, n, "426 Upgrade Required"), b, n);

    // what follows an upgrade in the same write is frames, not requests;
    // Connection is a list, as a browser sends it
    static const char up2[] = "GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\n"
      "Connection: keep-alive, Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\n";
    memcpy(r, up2, sizeof(up2) - 1);
    k = (int)sizeof(up2) - 1 + ws_frame(r + sizeof(up2) - 1, 1, "abc", 3, 1);
    fd = wire_open();
    if (wire_write(fd, r, (size_t)k) != k) perror("write");
    closed = 0; n = ws_read(fd, b, sizeof(b), 134, &closed);
    check("a frame sent with the upgrade is answered after the 101",
      has(b, n, "101 Switching") && n >= 5 && !memcmp(b + n - 5, "\x81\x03" "abc", 5), b, n);
    wire_close(fd);

    n = one(TEXT("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
      "Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\nGET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("nothing after a 101 is answered as HTTP", has(b, n, "101") && !has(b, n, "200 OK"), b, n);

    n = one(TEXT("HEAD /events HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    check("HEAD /events is the head and no stream",
      has(b, n, "text/event-stream") && !has(b, n, "event: tick"), b, n);
  }

  // The access log: one line per request, what was asked, the status
  // and the bytes back, in the order the requests came. A pipelined
  // pair is two lines; a HEAD reports the head it sent.
  if (logf != NULL) {
    n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\nGET /nope HTTP/1.1\r\nHost: x\r\n\r\n"),
      b, sizeof(b), 0);
    n = one(TEXT("HEAD /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 0);
    usleep(200000);
    FILE* f = fopen(logf, "r");
    char lg[8192];
    size_t got = f != NULL ? fread(lg, 1, sizeof(lg) - 1, f) : 0;
    if (f != NULL) fclose(f);
    lg[got] = 0;
    char* a = strstr(lg, "GET /health 200 106");
    char* c = strstr(lg, "GET /nope 404 104");
    char* d = strstr(lg, "HEAD /health 200 95");
    check("the log has a line per request, in order",
      a != NULL && c != NULL && d != NULL && a < c && c < d, lg, (int)got);
  }

  // The connection limit. With N connections held open and idle, one
  // more is accepted by the kernel but not served until a slot frees;
  // closing one of the N is what frees it.
  if (conns > 0) {
    static const char req[] = "GET /health HTTP/1.1\r\nHost: x\r\n\r\n";
    const int reqn = (int)(sizeof(req) - 1);
    int held[64];
    int m = conns < 64 ? conns : 64;
    for (int i = 0; i < m; i++) held[i] = dial();
    usleep(200000);
    // The kernel finishes the handshake of the one over the limit, so
    // it connects; the server has not taken a slot for it, so nothing
    // answers. Over TLS the waiting shows one step earlier, because a
    // session cannot come up against a socket nobody is reading -- an
    // open that does not finish is the same evidence. Either way the
    // slot freed below is what lets it through.
    int extra = wire_open(), waited = 0;
    if (extra < 0) {
      waited = 1;
    } else {
      if (wire_write(extra, req, (size_t)reqn) != reqn) perror("write");
      n = (int)wire_read(extra, b, sizeof(b), 0);
      waited = n < 0;
    }
    close(held[0]);
    if (extra < 0) {
      extra = wire_open();
      if (extra >= 0 && wire_write(extra, req, (size_t)reqn) != reqn) perror("write");
    }
    n = extra >= 0 ? (int)wire_read(extra, b, sizeof(b), 0) : -1;
    check("past the connection limit a request waits for a slot",
      waited && n > 0 && has(b, n, "200 OK"), b, n > 0 ? n : 0);
    wire_close(extra);
    for (int i = 1; i < m; i++) close(held[i]);
  }

  // Stopping. After SIGTERM the port refuses new connections within a
  // tick, a connection already open still gets its request answered,
  // and the process is gone once the open ones have ended.
  if (term && argc > 2) {
    static const char req[] = "GET /health HTTP/1.1\r\nHost: x\r\n\r\n";
    const int reqn = (int)(sizeof(req) - 1);
    long pid = atol(argv[2]);
    int open_ = wire_open();
    kill((pid_t)pid, SIGTERM);
    usleep(600000);
    int fresh = wire_open();
    int refused = fresh < 0;
    if (fresh >= 0) wire_close(fresh);
    if (wire_write(open_, req, (size_t)reqn) != reqn) perror("write");
    n = (int)wire_read(open_, b, sizeof(b), 0);
    int served = n > 0 && has(b, n, "200 OK");
    wire_close(open_);
    int gone = 0;
    for (int i = 0; i < 100 && !gone; i++) {
      usleep(50000);
      gone = kill((pid_t)pid, 0) != 0;
    }
    check("SIGTERM: new connections refused, open ones served, then gone",
      refused && served && gone, b, n > 0 ? n : 0);
  }

  printf("\n%d/%d pass\n", pass, pass + fail);
  return fail == 0 ? 0 : 1;
}
