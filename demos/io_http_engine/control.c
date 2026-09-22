// C control for main.bend: the same engine, written the way a C server
// is written. One epoll loop, one parser state per connection, the same
// states and the same byte-at-a-time transitions, the same routes and
// byte-identical replies, the same policy (HTTP/1.1 only, one Host,
// Content-Length only, all digits, agreeing when repeated, no
// Transfer-Encoding, names compared as bytes).
// It is the control for demos/io_http_engine: whatever it measures is
// what the Bend engine is measured against.
//
//   cc -std=c11 -O3 control.c -o control && ./control 8081
#define _GNU_SOURCE
#include <errno.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <unistd.h>

// the byte classes and states of main.bend's step.at, one for one
enum { K_SP, K_HT, K_CR, K_LF, K_CO, K_CM, K_DG, K_TK, K_VC, K_CT };
enum { PRE, PRE_LF, IN_M, IN_T, IN_V, CR_M, LIN, IN_N, IN_L0, IN_L, IN_LT,
  IN_LC, IN_LX, CR_L, BOD, BAD };
enum { M_OTHER, M_GET, M_HEAD };
enum { F_OTHER, F_TE, F_CL, F_CONN };

#define CHUNK 16384
#define MAXPATH 512
#define MAXBODY 65536
#define MAXTOK 32

typedef struct {
  int fd, st, used;
  uint32_t v, clen, bodn;
  int meth, hascl, close, hosts, plen, tn;
  int shut;                       // a served message asked to close
  char tok[MAXTOK + 1];           // the method, version, name or list member
  char path[MAXPATH], body[MAXBODY];
  char out[CHUNK * 4];
  int outn;
} Conn;

static int cls(uint8_t c) {
  if (c == 32) return K_SP;
  if (c == 9) return K_HT;
  if (c == 13) return K_CR;
  if (c == 10) return K_LF;
  if (c < 32 || c == 127) return K_CT;
  if (c > 127) return K_VC;
  if (c == 58) return K_CO;
  if (c == 44) return K_CM;
  if (c >= 48 && c <= 57) return K_DG;
  if ((c | 32) >= 97 && (c | 32) <= 122) return K_TK;
  return strchr("-._!#$%&'*+^`|~", c) ? K_TK : K_VC;
}
static int token(int t) { return t == K_TK || t == K_DG; }
static uint32_t lower(uint32_t c) { return c >= 65 && c <= 90 ? c + 32 : c; }
// a token is kept up to MAXTOK bytes; a longer one names nothing known
static void keep(Conn* k, uint8_t c) { if (k->tn <= MAXTOK) k->tok[k->tn++] = (char)c; }
static int is(Conn* k, const char* s) {
  return k->tn == (int)strlen(s) && !memcmp(k->tok, s, (size_t)k->tn);
}

static void put(Conn* k, const char* s, int n) {
  if (k->outn + n <= (int)sizeof(k->out)) { memcpy(k->out + k->outn, s, n); k->outn += n; }
}
// HEAD gets GET's head and no body; the 405 names the methods that
// work; the reply that ends its connection says so
static void reply(Conn* k, const char* status, const char* ctype,
                  const char* body, int bn) {
  char h[256];
  int n = snprintf(h, sizeof(h),
    "HTTP/1.1 %s\r\ncontent-type: %s\r\ncontent-length: %d%s"
    "\r\nconnection: %s\r\n\r\n", status, ctype, bn,
    !strncmp(status, "405", 3) ? "\r\nallow: GET, HEAD" : "",
    k->close || !strncmp(status, "400", 3) ? "close" : "keep-alive");
  put(k, h, n);
  if (k->meth != M_HEAD) put(k, body, bn);
}

// the same routes as main.bend, in the same order
static void serve(Conn* k) {
  if (k->meth == M_OTHER) {
    reply(k, "405 Method Not Allowed", "text/plain", "no method\n", 10);
  } else if (k->plen == 7 && !memcmp(k->path, "/health", 7)) {
    reply(k, "200 OK", "application/json", "{\"ok\":true}", 11);
  } else if (k->plen == 5 && !memcmp(k->path, "/echo", 5)) {
    reply(k, "200 OK", "application/octet-stream", k->body, (int)k->bodn);
  } else if (k->plen == 1 && k->path[0] == '/') {
    reply(k, "200 OK", "text/plain", "bend-http\n", 10);
  } else {
    reply(k, "404 Not Found", "text/plain", "no route\n", 9);
  }
  if (k->close) k->shut = 1;
  k->st = PRE;
}

// the same body cap as main.bend's body.cap(): a length past it is
// refused at the digit that crosses it
#define BODY_CAP 1048576u

static void head_done(Conn* k) {
  if (k->hosts != 1) { k->st = BAD; return; }
  k->bodn = 0;
  if (k->clen == 0) serve(k); else k->st = BOD;
}

// a name closes at its colon, compared by its bytes; a
// Transfer-Encoding is refused there
static void name_done(Conn* k) {
  int f = is(k, "transfer-encoding") ? F_TE : is(k, "content-length") ? F_CL
    : is(k, "connection") ? F_CONN : F_OTHER;
  if (is(k, "host")) k->hosts++;
  k->st = f == F_TE ? BAD : f == F_CL ? IN_L0 : f == F_CONN ? IN_LC : IN_LX;
  k->tn = 0;
}

// a Content-Length value closes: a second one must agree with the first
static void clen_done(Conn* k) {
  if (k->hascl && k->clen != k->v) { k->st = BAD; return; }
  k->hascl = 1; k->clen = k->v; k->st = CR_M;
}

// a member of a Connection list closes
static void member(Conn* k) { if (is(k, "close")) k->close = 1; k->tn = 0; }

// one byte, the same transition table as main.bend's step.at
static void step(Conn* k, uint8_t c) {
  int t = cls(c);
  switch (k->st) {
    case PRE:
      if (t == K_CR) k->st = PRE_LF;
      else if (token(t)) { k->tn = 0; keep(k, c); k->st = IN_M; }
      else k->st = BAD;
      break;
    case PRE_LF: k->st = t == K_LF ? PRE : BAD; break;
    case IN_M:
      if (t == K_SP) {
        k->meth = is(k, "GET") ? M_GET : is(k, "HEAD") ? M_HEAD : M_OTHER;
        k->plen = 0; k->clen = 0; k->hascl = 0; k->close = 0; k->hosts = 0;
        k->st = IN_T;
      } else if (token(t)) keep(k, c);
      else k->st = BAD;
      break;
    case IN_T:
      if (t == K_SP) { k->tn = 0; k->st = k->plen ? IN_V : BAD; }
      else if (t == K_HT || t == K_CR || t == K_LF || t == K_CT) k->st = BAD;
      else if (k->plen < MAXPATH) k->path[k->plen++] = (char)c;
      break;
    case IN_V:
      if (t == K_CR) k->st = is(k, "HTTP/1.1") ? CR_M : BAD;
      else if (token(t) || t == K_VC) keep(k, c);
      else k->st = BAD;
      break;
    case CR_M: k->st = (t == K_LF) ? LIN : BAD; break;
    case LIN:
      if (t == K_CR) k->st = CR_L;
      else if (token(t)) { k->tn = 0; keep(k, (uint8_t)lower(c)); k->st = IN_N; }
      else k->st = BAD;
      break;
    case IN_N:
      if (t == K_CO) name_done(k);
      else if (token(t)) keep(k, (uint8_t)lower(c));
      else k->st = BAD;
      break;
    case IN_L0:
      if (t == K_DG) { k->v = c - 48; k->st = IN_L; }
      else if (t != K_SP && t != K_HT) k->st = BAD;
      break;
    case IN_L:
      if (t == K_DG) { k->v = k->v * 10 + (c - 48); if (k->v > BODY_CAP) k->st = BAD; }
      else if (t == K_SP || t == K_HT) k->st = IN_LT;
      else if (t == K_CR) clen_done(k);
      else k->st = BAD;
      break;
    case IN_LT:
      if (t == K_CR) clen_done(k);
      else if (t != K_SP && t != K_HT) k->st = BAD;
      break;
    case IN_LC:
      if (t == K_CR) { member(k); k->st = CR_M; }
      else if (t == K_SP || t == K_HT || t == K_CM) member(k);
      else if (t == K_LF || t == K_CT) k->st = BAD;
      else keep(k, (uint8_t)lower(c));
      break;
    case IN_LX:
      if (t == K_CR) k->st = CR_M;
      else if (t == K_LF || t == K_CT) k->st = BAD;
      break;
    case CR_L: if (t == K_LF) head_done(k); else k->st = BAD; break;
    case BOD:
      if (k->bodn < MAXBODY) k->body[k->bodn] = (char)c;
      k->bodn += 1;
      if (k->bodn >= k->clen) serve(k);
      break;
    default: break;
  }
}

static void reset(Conn* k, int fd) {
  memset(k, 0, sizeof(*k));
  k->fd = fd; k->used = 1; k->st = PRE;
}

int main(int argc, char** argv) {
  int port = argc > 1 ? atoi(argv[1]) : 8081;
  // "shared": SO_REUSEPORT, so N copies split one port between them
  int shared = argc > 2 && strcmp(argv[2], "shared") == 0;
  int ln = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0);
  int on = 1;
  setsockopt(ln, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));
  if (shared) setsockopt(ln, SOL_SOCKET, SO_REUSEPORT, &on, sizeof(on));
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  if (bind(ln, (struct sockaddr*)&a, sizeof(a)) || listen(ln, 1024)) {
    perror("bind"); return 1;
  }
  int ep = epoll_create1(0);
  struct epoll_event ev = { .events = EPOLLIN, .data.fd = ln };
  epoll_ctl(ep, EPOLL_CTL_ADD, ln, &ev);
  static Conn conns[65536];
  struct epoll_event es[256];
  char buf[CHUNK];
  printf("control on http://127.0.0.1:%d\n", port);
  fflush(stdout);
  for (;;) {
    int n = epoll_wait(ep, es, 256, -1);
    for (int i = 0; i < n; i++) {
      int fd = es[i].data.fd;
      if (fd == ln) {
        for (;;) {
          int c = accept4(ln, NULL, NULL, SOCK_NONBLOCK);
          if (c < 0) break;
          if (c >= 65536) { close(c); continue; }
          setsockopt(c, IPPROTO_TCP, TCP_NODELAY, &on, sizeof(on));
          reset(&conns[c], c);
          struct epoll_event e2 = { .events = EPOLLIN, .data.fd = c };
          epoll_ctl(ep, EPOLL_CTL_ADD, c, &e2);
        }
        continue;
      }
      Conn* k = &conns[fd];
      ssize_t got = recv(fd, buf, sizeof(buf), 0);
      if (got <= 0) {
        if (got < 0 && errno == EAGAIN) continue;
        epoll_ctl(ep, EPOLL_CTL_DEL, fd, NULL); close(fd); k->used = 0; continue;
      }
      k->outn = 0;
      // nothing after a message that asked to close is served; a broken
      // grammar is answered with a 400 after the replies owed before it
      for (ssize_t j = 0; j < got && !k->shut && k->st != BAD; j++) step(k, (uint8_t)buf[j]);
      if (k->st == BAD) {
        k->meth = M_GET;
        reply(k, "400 Bad Request", "text/plain", "bad request\n", 12);
      }
      for (int off = 0; off < k->outn;) {
        ssize_t w = send(fd, k->out + off, (size_t)(k->outn - off), MSG_NOSIGNAL);
        if (w <= 0) break;
        off += (int)w;
      }
      if (k->st == BAD || k->shut) {
        epoll_ctl(ep, EPOLL_CTL_DEL, fd, NULL); close(fd); k->used = 0;
      }
    }
  }
}
