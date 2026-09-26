// C control for main.bend: the same engine, written the way a C server
// is written. One epoll loop, one parser state per connection, the same
// states and the same byte-at-a-time transitions, the same routes and
// byte-identical replies, the same policy (HTTP/1.1 with one Host, or
// HTTP/1.0 with at most one, closed unless it asks to keep alive; a
// Content-Length, all digits, agreeing when repeated, or a
// Transfer-Encoding that is chunked exactly and once, never both; a
// chunked body by RFC 9112 7.1 under one budget; names compared as
// bytes).
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
  IN_LC, IN_LX, IN_LE0, IN_LE, CR_L, BOD, CHK, CHD, BAD };
enum { M_OTHER, M_GET, M_HEAD };
enum { F_OTHER, F_TE, F_CL, F_CONN };
// a chunked body's places (main.bend's ChPos) and what a byte is there
// (its XK)
enum { C_SIZE0, C_SIZE, C_BWS, C_NAME0, C_NAME, C_NAMEWS, C_VAL0, C_TOKEN, C_QUOTED,
  C_ESCAPE, C_CLOSED, C_LF, C_DATACR, C_DATALF, C_TRAIL, C_TNAME, C_TVAL, C_TLF, C_END };
enum { X_HEX, X_TOK, X_WS, X_SEMI, X_EQ, X_QUOTE, X_BACK, X_COLON, X_CR, X_LF, X_VIS, X_CTL };

#define CHUNK 16384
#define MAXPATH 512
#define MAXBODY 65536
#define MAXTOK 32

typedef struct {
  int fd, st, used;
  uint32_t v, clen, bodn;
  int meth, hascl, close, hosts, plen, tn;
  int v10, ka, te;                // HTTP/1.0; keep-alive named; chunked named
  int pos;                        // where in a chunked body's framing
  uint32_t csz, left;             // the chunk's size, the budget left
  uint32_t crem;                  // a chunk's data still to come
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
  char* q = memchr(k->path, '?', (size_t)k->plen);   // a query is no part of the path
  if (q != NULL) k->plen = (int)(q - k->path);
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
// refused where the head ends, as main.bend's body.fit refuses it, before
// a byte of the body; a digit only guards the length from wrapping
// (main.bend's len.top(): a length whose value before the digit is past
// 429496728 is refused there)
#define BODY_CAP 1048576u
#define LEN_TOP 429496728u

// the head's end: HTTP/1.1 carries one Host and HTTP/1.0 at most one; a
// Transfer-Encoding with a length, or in HTTP/1.0, is refused; chunked
// is a chunked body under the budget; a length is that many bytes
static void head_done(Conn* k) {
  if (k->v10 ? k->hosts > 1 : k->hosts != 1) { k->st = BAD; return; }
  if (k->v10 && !k->ka) k->close = 1;
  k->bodn = 0;
  if (!k->te && k->clen > BODY_CAP) { k->st = BAD; return; }
  if (k->te) {
    if (k->hascl || k->v10) { k->st = BAD; return; }
    k->st = CHK; k->pos = C_SIZE0; k->csz = 0; k->left = BODY_CAP;
    return;
  }
  if (k->clen == 0) serve(k); else k->st = BOD;
}

// a name closes at its colon, compared by its bytes
static void name_done(Conn* k) {
  int f = is(k, "transfer-encoding") ? F_TE : is(k, "content-length") ? F_CL
    : is(k, "connection") ? F_CONN : F_OTHER;
  if (is(k, "host")) k->hosts++;
  k->st = f == F_TE ? IN_LE0 : f == F_CL ? IN_L0 : f == F_CONN ? IN_LC : IN_LX;
  k->tn = 0;
}

// a Transfer-Encoding closes: chunked, exactly and once
static void te_done(Conn* k) {
  if (is(k, "chunked") && !k->te) { k->te = 1; k->st = CR_M; } else k->st = BAD;
}

// a byte's kind in a chunked body's framing, as main.bend's xk.of says
static int xk(uint8_t c, uint32_t* d) {
  int t = cls(c);
  if (t == K_SP || t == K_HT) return X_WS;
  if (t == K_CR) return X_CR;
  if (t == K_LF) return X_LF;
  if (t == K_CO) return X_COLON;
  if (t == K_CM) return X_VIS;
  if (t == K_CT) return X_CTL;
  if (t == K_DG || t == K_TK) {
    uint32_t l = lower(c);
    if (l >= 48 && l <= 57) { *d = l - 48; return X_HEX; }
    if (l >= 97 && l <= 102) { *d = l - 87; return X_HEX; }
    return X_TOK;
  }
  return c == ';' ? X_SEMI : c == '=' ? X_EQ : c == '"' ? X_QUOTE : c == '\\' ? X_BACK : X_VIS;
}

// one byte of a chunked body's framing: RFC 9112 7.1's table, row by
// row as main.bend's chk.next has it. A move to a place is paid from the
// budget when the byte is part of a chunk line; a digit grows the size;
// a line's LF starts its data or the trailer; the last LF ends the body.
enum { MV_BAD, MV_TO, MV_DIGIT, MV_LINE, MV_DONE };
static int chk_next(int pos, int x, int* to, int* paid) {
  int tch = x == X_HEX || x == X_TOK;
  *paid = 1;
#define TO(p) do { *to = (p); return MV_TO; } while (0)
#define FREE(p) do { *paid = 0; *to = (p); return MV_TO; } while (0)
  switch (pos) {
    case C_SIZE0: return x == X_HEX ? MV_DIGIT : MV_BAD;
    case C_SIZE:
      if (x == X_HEX) return MV_DIGIT;
      if (x == X_SEMI) TO(C_NAME0);
      if (x == X_WS) TO(C_BWS);
      if (x == X_CR) FREE(C_LF);
      return MV_BAD;
    case C_BWS:
      if (x == X_WS) TO(C_BWS);
      if (x == X_SEMI) TO(C_NAME0);
      return MV_BAD;
    case C_NAME0:
      if (x == X_WS) TO(C_NAME0);
      if (tch) TO(C_NAME);
      return MV_BAD;
    case C_NAME:
      if (x == X_WS) TO(C_NAMEWS);
      if (x == X_EQ) TO(C_VAL0);
      if (x == X_SEMI) TO(C_NAME0);
      if (x == X_CR) FREE(C_LF);
      if (tch) TO(C_NAME);
      return MV_BAD;
    case C_NAMEWS:
      if (x == X_WS) TO(C_NAMEWS);
      if (x == X_EQ) TO(C_VAL0);
      if (x == X_SEMI) TO(C_NAME0);
      return MV_BAD;
    case C_VAL0:
      if (x == X_WS) TO(C_VAL0);
      if (x == X_QUOTE) TO(C_QUOTED);
      if (tch) TO(C_TOKEN);
      return MV_BAD;
    case C_TOKEN:
      if (x == X_SEMI) TO(C_NAME0);
      if (x == X_WS) TO(C_BWS);
      if (x == X_CR) FREE(C_LF);
      if (tch) TO(C_TOKEN);
      return MV_BAD;
    case C_QUOTED:
      if (x == X_BACK) TO(C_ESCAPE);
      if (x == X_QUOTE) TO(C_CLOSED);
      if (x == X_CR || x == X_LF || x == X_CTL) return MV_BAD;
      TO(C_QUOTED);
    case C_ESCAPE:
      if (x == X_CR || x == X_LF || x == X_CTL) return MV_BAD;
      TO(C_QUOTED);
    case C_CLOSED:
      if (x == X_SEMI) TO(C_NAME0);
      if (x == X_WS) TO(C_BWS);
      if (x == X_CR) FREE(C_LF);
      return MV_BAD;
    case C_LF: return x == X_LF ? MV_LINE : MV_BAD;
    case C_DATACR: if (x == X_CR) FREE(C_DATALF); return MV_BAD;
    case C_DATALF: if (x == X_LF) FREE(C_SIZE0); return MV_BAD;
    case C_TRAIL:
      if (x == X_CR) FREE(C_END);
      if (tch) FREE(C_TNAME);
      return MV_BAD;
    case C_TNAME:
      if (x == X_COLON) FREE(C_TVAL);
      if (tch) FREE(C_TNAME);
      return MV_BAD;
    case C_TVAL:
      if (x == X_CR) FREE(C_TLF);
      if (x == X_LF || x == X_CTL) return MV_BAD;
      FREE(C_TVAL);
    case C_TLF: if (x == X_LF) FREE(C_TRAIL); return MV_BAD;
    case C_END: return x == X_LF ? MV_DONE : MV_BAD;
  }
#undef TO
#undef FREE
  return MV_BAD;
}

// the budget: a paid byte, and a digit that grows the size, are refused
// where what is left could no longer hold them and the chunk's data
static void chk_step(Conn* k, uint8_t c) {
  uint32_t d = 0;
  int to = 0, paid = 0;
  int x = xk(c, &d);
  switch (chk_next(k->pos, x, &to, &paid)) {
    case MV_BAD: k->st = BAD; return;
    case MV_TO:
      if (paid) {
        if (k->left <= k->csz) { k->st = BAD; return; }
        k->left -= 1;
      }
      k->pos = to;
      return;
    case MV_DIGIT: {
      uint32_t n2 = k->csz * 16 + d;
      if (k->left <= n2) { k->st = BAD; return; }
      k->left -= 1; k->csz = n2; k->pos = C_SIZE;
      return;
    }
    case MV_LINE:
      if (k->csz == 0) { k->pos = C_TRAIL; return; }
      k->left -= k->csz; k->crem = k->csz; k->csz = 0; k->st = CHD;
      return;
    case MV_DONE: serve(k); return;
  }
}

// a Content-Length value closes: a second one must agree with the first
static void clen_done(Conn* k) {
  if (k->hascl && k->clen != k->v) { k->st = BAD; return; }
  k->hascl = 1; k->clen = k->v; k->st = CR_M;
}

// a member of a Connection list closes
static void member(Conn* k) {
  if (is(k, "close")) k->close = 1;
  if (is(k, "keep-alive")) k->ka = 1;
  k->tn = 0;
}

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
        k->v10 = 0; k->ka = 0; k->te = 0;
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
      if (t == K_CR) {
        if (is(k, "HTTP/1.1")) k->st = CR_M;
        else if (is(k, "HTTP/1.0")) { k->v10 = 1; k->st = CR_M; }
        else k->st = BAD;
      }
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
      if (t == K_DG) { if (k->v > LEN_TOP) k->st = BAD; else k->v = k->v * 10 + (c - 48); }
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
    case IN_LE0:
      if (t == K_SP || t == K_HT) break;
      if (t == K_CR || t == K_LF || t == K_CT) { k->st = BAD; break; }
      k->tn = 0; keep(k, (uint8_t)lower(c)); k->st = IN_LE;
      break;
    case IN_LE:
      if (t == K_CR) te_done(k);
      else if (t == K_LF || t == K_CT) k->st = BAD;
      else keep(k, (uint8_t)lower(c));
      break;
    case CR_L: if (t == K_LF) head_done(k); else k->st = BAD; break;
    case BOD:
      if (k->bodn < MAXBODY) k->body[k->bodn] = (char)c;
      k->bodn += 1;
      if (k->bodn >= k->clen) serve(k);
      break;
    case CHK: chk_step(k, c); break;
    case CHD:
      if (k->bodn < MAXBODY) k->body[k->bodn] = (char)c;
      k->bodn += 1;
      if (--k->crem == 0) { k->st = CHK; k->pos = C_DATACR; }
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
