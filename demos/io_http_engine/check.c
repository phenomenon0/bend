// Behavioural checks for demos/io_http_engine, over a raw socket. The
// same binary checks the Bend engine and control.c, so "the same
// twelve checks" is a claim the two are measured against rather than a
// sentence in a README.
//
//   cc -std=c11 -O3 check.c -o check && ./check 8080
#define _GNU_SOURCE
#include <netinet/in.h>
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

#define TEXT(s) s, (int)(sizeof(s) - 1)

int main(int argc, char** argv) {
  if (argc > 1) PORT = atoi(argv[1]);
  static char b[262144];
  int n;

  n = one(TEXT("GET /health HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 106);
  check("GET /health", has(b, n, "200 OK") && has(b, n, "{\"ok\":true}"), b, n);

  n = one(TEXT("GET / HTTP/1.1\r\nHost: x\r\n\r\n"), b, sizeof(b), 98);
  check("GET / root", has(b, n, "200 OK") && has(b, n, "bend-http"), b, n);

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
    has(b, n, "{\"ok\":true}") && has(b, n, "bend-http"), b, n);

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

  printf("\n%d/%d pass\n", pass, pass + fail);
  return fail == 0 ? 0 : 1;
}
