// Differential fuzzing for demos/io_http_engine: the same bytes, split
// the same way, go to the Bend engine and to control.c, and what comes
// back has to be identical, byte for byte, closes included. Each round
// draws one to four messages -- valid, or mutated in the ways a
// protocol reader has to survive: a truncation, a byte flipped, a
// version that is not 1.1, a Transfer-Encoding, a length that is not
// all digits, a length past the cap, fields in odd case, bodies of
// arbitrary bytes, and the framing ambiguities requests are smuggled
// through (a space before a colon, a folded line, a bare LF, two
// lengths, a length list, a missing or repeated Host) -- then cuts the stream at random points and sends
// each cut to both servers with a pause between, so the splits are
// real recvs on the other side. A mismatch prints the round's seed,
// the stream, the cuts and both answers. Neither server serves
// /events here, since a stream never ends.
//
//   cc -std=c11 -O2 fuzz.c -o fuzz && ./fuzz 8080 8081 2000 [seed]
#define _GNU_SOURCE
#include <errno.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define MAXS 65536

static uint32_t rng;
static uint32_t rnd(void) {
  rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
  return rng;
}
static int pick(int n) { return (int)(rnd() % (uint32_t)n); }

static int dial(int port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons((uint16_t)port),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  if (connect(fd, (struct sockaddr*)&a, sizeof(a))) { perror("connect"); exit(2); }
  int on = 1;
  setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &on, sizeof(on));
  return fd;
}

// One message into s, returns its length. Valid most of the time, then
// one of the mutations a reader has to get right.
static const char* PATHS[] = { "/health", "/", "/echo", "/nope", "/health/", "/a/../health", "//" };
static const char* METHS[] = { "GET", "HEAD", "POST", "PUT", "DELETE", "OPTIONS", "get" };
// fields a smuggler sends; each is refused, except an agreeing repeat
// and trailing whitespace, which are a length
static const char* SMUGGLE[] = {
  "Content-Length : 5\r\n", "Transfer-Encoding : chunked\r\n", "content-length: 5, 5\r\n",
  "Content-Length: 3\r\nContent-Length: 5\r\n", "Content-Length: 3\r\ncontent-length: 3\r\n",
  "X-A: a\r\n b\r\n", "X-A: a\nContent-Length: 3\r\n", "content-length: +3\r\n",
  "Content-Length: 4294967299\r\n", "Content-Length: 3 \r\n", "TRANSFER-encoding: chunked\r\n",
  "X-A\r\n", "content-length:\t3\r\n", "X-\x01: y\r\n" };
static const char* CONNS[] = { "close", "keep-alive", "keep-alive, close", "Close", "x,close ,y" };

static int message(char* s, int cap) {
  int n = 0;
  const char* meth = pick(4) ? (pick(3) ? "GET" : "HEAD") : METHS[pick(7)];
  const char* path = PATHS[pick(7)];
  const char* ver  = pick(12) ? "HTTP/1.1" : (pick(2) ? "HTTP/1.0" : "HTTP/2.0");
  if (pick(16) == 0) n += snprintf(s + n, (size_t)(cap - n), "\r\n");
  n += snprintf(s + n, (size_t)(cap - n), "%s %s %s\r\n", meth, path, ver);
  int hosts = pick(16) ? 1 : pick(2) * 2;               // mostly one, sometimes none or two
  for (int i = 0; i < hosts; i++) n += snprintf(s + n, (size_t)(cap - n), "%s: x\r\n", pick(2) ? "Host" : "host");
  int body = 0, announce = -1;
  int kind = pick(11);
  if (kind < 5) {                                       // a body, announced right
    body = pick(40);
    announce = body;
  } else if (kind == 5) {                               // a length that is not all digits
    n += snprintf(s + n, (size_t)(cap - n), "content-length: 5x\r\n");
  } else if (kind == 6) {                               // past the cap
    n += snprintf(s + n, (size_t)(cap - n), "content-length: 2000000\r\n");
  } else if (kind == 7) {                               // transfer-encoding
    n += snprintf(s + n, (size_t)(cap - n), "Transfer-Encoding: chunked\r\n");
  } else if (kind == 8) {                               // announced more than sent (later bytes are body)
    body = pick(10);
    announce = body + 1 + pick(5);
  } else if (kind == 9) {                               // a smuggling vector
    n += snprintf(s + n, (size_t)(cap - n), "%s", SMUGGLE[pick(14)]);
    body = 3;
  }
  if (announce >= 0) {
    static const char* NAMES[] = { "content-length", "Content-Length", "CONTENT-LENGTH", "cOnTeNt-LeNgTh" };
    n += snprintf(s + n, (size_t)(cap - n), "%s:%s%d\r\n", NAMES[pick(4)], pick(2) ? " " : "", announce);
  }
  if (pick(5) == 0) n += snprintf(s + n, (size_t)(cap - n), "Connection: %s\r\n", CONNS[pick(5)]);
  if (pick(6) == 0) n += snprintf(s + n, (size_t)(cap - n), "X-Junk: %d\r\n", pick(100000));
  n += snprintf(s + n, (size_t)(cap - n), "\r\n");
  for (int i = 0; i < body && n < cap; i++) s[n++] = (char)pick(256);
  return n;
}

static int stream(char* s, int cap) {
  int n = 0, k = 1 + pick(4);
  for (int i = 0; i < k && n < cap - 4096; i++) n += message(s + n, cap - n);
  // a mutation over the whole stream, sometimes
  int m = pick(8);
  if (m == 0 && n > 1) n = 1 + pick(n - 1);            // truncated
  else if (m == 1 && n > 0) s[pick(n)] = (char)pick(256); // a byte flipped
  else if (m == 2 && n > 0) { int at = pick(n); s[at] = (char)(pick(2) ? '\r' : '\n'); }
  return n;
}

// read from both until both are quiet for a while or closed
static int drain(int fd, char* out, int cap, int* closed, int ms) {
  int n = 0;
  for (;;) {
    struct pollfd p = { .fd = fd, .events = POLLIN };
    int r = poll(&p, 1, ms);
    if (r <= 0) return n;
    int got = (int)recv(fd, out + n, (size_t)(cap - n), 0);
    if (got <= 0) { *closed = 1; return n; }
    n += got;
    if (n >= cap) return n;
  }
}

static void show(const char* tag, const char* s, int n) {
  printf("%s (%d bytes): ", tag, n);
  for (int i = 0; i < n && i < 400; i++) {
    unsigned char c = (unsigned char)s[i];
    if (c == '\r') printf("\\r"); else if (c == '\n') printf("\\n");
    else if (c >= 32 && c < 127) putchar(c); else printf("\\x%02x", c);
  }
  printf(n > 400 ? "...\n" : "\n");
}

int main(int argc, char** argv) {
  int pa = argc > 1 ? atoi(argv[1]) : 8080;
  int pb = argc > 2 ? atoi(argv[2]) : 8081;
  int rounds = argc > 3 ? atoi(argv[3]) : 500;
  uint32_t seed = argc > 4 ? (uint32_t)strtoul(argv[4], NULL, 10) : (uint32_t)time(NULL);
  static char s[MAXS], oa[MAXS], ob[MAXS];
  int bad = 0;
  // a server that closed first must not kill the fuzzer with SIGPIPE
  signal(SIGPIPE, SIG_IGN);
  setvbuf(stdout, NULL, _IOLBF, 0);
  printf("seed %u, %d rounds, %d vs %d\n", seed, rounds, pa, pb);
  for (int r = 0; r < rounds; r++) {
    rng = seed * 2654435761u + (uint32_t)r * 40503u + 1u;
    int n = stream(s, MAXS - 8192);
    int cuts[17], nc = 1 + pick(n > 16 ? 8 : 2);
    for (int i = 0; i < nc - 1; i++) cuts[i] = n > 0 ? pick(n) : 0;
    cuts[nc - 1] = n;
    // sort the cuts
    for (int i = 0; i < nc; i++) for (int j = i + 1; j < nc; j++)
      if (cuts[j] < cuts[i]) { int t = cuts[i]; cuts[i] = cuts[j]; cuts[j] = t; }
    int fa = dial(pa), fb = dial(pb);
    int at = 0;
    for (int i = 0; i < nc; i++) {
      int to = cuts[i];
      if (to > at) {
        if (send(fa, s + at, (size_t)(to - at), MSG_NOSIGNAL) < 0) { /* a closed peer is an answer too */ }
        if (send(fb, s + at, (size_t)(to - at), MSG_NOSIGNAL) < 0) { }
        at = to;
      }
      usleep(3000);
    }
    int ca = 0, cb = 0;
    int na = drain(fa, oa, MAXS, &ca, 200);
    int nb = drain(fb, ob, MAXS, &cb, 200);
    // an idle keep-alive on one side and a close on the other must agree
    if (!ca) { shutdown(fa, SHUT_WR); na += drain(fa, oa + na, MAXS - na, &ca, 300); }
    if (!cb) { shutdown(fb, SHUT_WR); nb += drain(fb, ob + nb, MAXS - nb, &cb, 300); }
    close(fa); close(fb);
    if (na != nb || memcmp(oa, ob, (size_t)na) != 0 || ca != cb) {
      bad++;
      int d = 0; while (d < na && d < nb && oa[d] == ob[d]) d++;
      printf("\nMISMATCH round %d (seed %u): %d cuts, first difference at %d, closed %d/%d\n", r, seed, nc, d, ca, cb);
      show("  stream", s, n);
      printf("  cuts:"); for (int i = 0; i < nc; i++) printf(" %d", cuts[i]); printf("\n");
      show("  engine ", oa, na);
      show("  control", ob, nb);
      if (bad >= 10) { printf("stopping after 10 mismatches\n"); break; }
    }
  }
  printf("\n%d rounds, %d mismatches\n", rounds, bad);
  return bad == 0 ? 0 : 1;
}
