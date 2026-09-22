// Behavioural checks for demos/io_http_engine, over a raw socket. The
// same binary checks the Bend engine and control.c, so "the same
// checks" is a claim the two are measured against rather than a
// sentence in a README. Given the server's pid, the last case also
// reads its CPU.
//
//   cc -std=c11 -O3 check.c -o check && ./check 8080 [pid] [--files] [--idle=MS]
//   ./check 8080 [pid] [--conns=N] [--term]
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

// send the parts in order, then read until the peer stops or want bytes
// have arrived; returns what came back
static int ask(const char** parts, const int* lens, int n, char* out, int cap,
               int want) {
  int fd = dial();
  if (fd < 0) return -1;
  for (int i = 0; i < n; i++) {
    if (i) { struct timespec t = { 0, 120000000 }; nanosleep(&t, NULL); }
    if (write(fd, parts[i], (size_t)lens[i]) != lens[i]) { close(fd); return -1; }
  }
  int got = 0;
  while (got < cap) {
    ssize_t k = recv(fd, out + got, (size_t)(cap - got), 0);
    if (k <= 0) break;
    got += (int)k;
    if (want > 0 && got >= want) break;
  }
  close(fd);
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

#define TEXT(s) s, (int)(sizeof(s) - 1)

int main(int argc, char** argv) {
  if (argc > 1) PORT = atoi(argv[1]);
  static char b[262144];
  int n;
  // flags after the pid: --files when the server has --root on the
  // fixture directory; --idle=MS when it was started with --idle-ms MS
  // --conns=N when it was started with --max-conns N; --term to end by
  // sending it SIGTERM (last, since the server is gone afterwards)
  int files = 0, idle = 0, conns = 0, term = 0;
  for (int i = 3; i < argc; i++) {
    if (strcmp(argv[i], "--files") == 0) files = 1;
    else if (strncmp(argv[i], "--idle=", 7) == 0) idle = atoi(argv[i] + 7);
    else if (strncmp(argv[i], "--conns=", 8) == 0) conns = atoi(argv[i] + 8);
    else if (strcmp(argv[i], "--term") == 0) term = 1;
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
  check("a non-digit Content-Length is not a length",
    has(b, n, "200 OK") && has(b, n, "content-length: 0"), b, n);

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
    int fd = dial();
    if (write(fd, "GET /hea", 8) != 8) perror("write");
    usleep((useconds_t)(idle + 300) * 1000);
    n = (int)recv(fd, b, sizeof(b), 0);
    check("a head that stalls is dropped after the idle time", n == 0, b, n > 0 ? n : 0);
    close(fd);

    fd = dial();
    if (write(fd, req, (size_t)reqn) != reqn) perror("write");
    n = (int)recv(fd, b, sizeof(b), 0);
    usleep((useconds_t)(idle + 300) * 1000);
    n = (int)recv(fd, b, sizeof(b), 0);
    check("an idle keep-alive connection is dropped after the idle time", n == 0, b, n > 0 ? n : 0);
    close(fd);

    fd = dial();
    if (write(fd, req, (size_t)reqn) != reqn) perror("write");
    n = (int)recv(fd, b, sizeof(b), 0);
    usleep((useconds_t)(idle / 2) * 1000);
    if (write(fd, req, (size_t)reqn) != reqn) perror("write");
    n = (int)recv(fd, b, sizeof(b), 0);
    check("a pause shorter than the idle time keeps the connection", n > 0 && has(b, n, "200 OK"), b, n > 0 ? n : 0);
    close(fd);

    n = one(TEXT("GET /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 2000000\r\n\r\n"), b, sizeof(b), 0);
    check("a body past the cap is refused before it is sent", has(b, n, "400 Bad Request"), b, n);

    fd = dial();
    const char* slow = "GET /health HTTP/1.1\r\nHost: x\r\nx-a: 0123456789012345678901234567890123456789012345678901234567890123456789\r\n\r\n";
    int dropped = 0, sl = (int)strlen(slow);
    for (int i = 0; i < sl && !dropped; i++) {
      if (write(fd, slow + i, 1) != 1) dropped = 1;
      usleep(3000);
      n = (int)recv(fd, b, sizeof(b), MSG_DONTWAIT);
      if (n == 0 || (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK)) dropped = 1;
    }
    check("a head dribbled a byte at a time is dropped after the wait budget", dropped, b, 0);
    close(fd);
  }

  // A peer that connects and closes without sending a byte. The engine
  // as first written read again on the empty recv, and one such peer
  // cost most of a core in passes until its fuel ran out. Given the
  // server's pid (./check 8080 <pid>) this measures it: twenty silent
  // closes, one second, and the server's CPU must not have moved.
  if (argc > 2) {
    long   pid = atol(argv[2]);
    double c0  = cpu_of(pid);
    for (int i = 0; i < 20; i++) { int fd = dial(); if (fd >= 0) close(fd); }
    usleep(1000000);
    double c1 = cpu_of(pid);
    n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
    char why[96];
    snprintf(why, sizeof(why), "cpu moved %.3fs", c1 - c0);
    check("twenty silent closes cost no CPU",
      c0 >= 0 && c1 - c0 < 0.05 && has(b, n, "200 OK"), why, (int)strlen(why));
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
    int extra = dial();
    if (write(extra, req, (size_t)reqn) != reqn) perror("write");
    n = (int)recv(extra, b, sizeof(b), 0);
    int waited = n < 0;
    close(held[0]);
    n = (int)recv(extra, b, sizeof(b), 0);
    check("past the connection limit a request waits for a slot",
      waited && n > 0 && has(b, n, "200 OK"), b, n > 0 ? n : 0);
    close(extra);
    for (int i = 1; i < m; i++) close(held[i]);
  }

  // Stopping. After SIGTERM the port refuses new connections within a
  // tick, a connection already open still gets its request answered,
  // and the process is gone once the open ones have ended.
  if (term && argc > 2) {
    static const char req[] = "GET /health HTTP/1.1\r\nHost: x\r\n\r\n";
    const int reqn = (int)(sizeof(req) - 1);
    long pid = atol(argv[2]);
    int open_ = dial();
    kill((pid_t)pid, SIGTERM);
    usleep(600000);
    int fresh = dial();
    int refused = fresh < 0;
    if (fresh >= 0) close(fresh);
    if (write(open_, req, (size_t)reqn) != reqn) perror("write");
    n = (int)recv(open_, b, sizeof(b), 0);
    int served = n > 0 && has(b, n, "200 OK");
    close(open_);
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
