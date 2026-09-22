// C control for main.bend: the same engine, written the way a C server
// is written. One epoll loop, one parser state per connection, the same
// ten modes and the same byte-at-a-time transitions, the same routes
// and byte-identical replies, the same policy (HTTP/1.1 only,
// Content-Length only, that length all digits, no Transfer-Encoding).
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

enum { K_SP, K_CR, K_LF, K_CO, K_CH };
enum { IN_M, IN_T, IN_V, CR_M, LIN, IN_N, OWS, IN_L, CR_L, BOD, BAD };

#define FNV 2166136261u
#define H_VERSION 4120326248u
#define H_CLEN 1308181789u
#define H_TE 3719590988u
#define H_CONN 951688921u
#define H_CLOSE 667630371u
#define M_GET 2531704439u
#define M_HEAD 811237315u

#define CHUNK 16384
#define MAXPATH 512
#define MAXBODY 65536

typedef struct {
  int fd, st, used;
  uint32_t h, n, v, g, meth, clen, bodn;
  int digit, close, te, plen;
  char path[MAXPATH], body[MAXBODY];
  char out[CHUNK * 4];
  int outn;
} Conn;

static uint32_t fnv1(uint32_t h, uint32_t c) { return (h ^ c) * 16777619u; }
static int cls(uint8_t c) {
  return c == 32 ? K_SP : c == 13 ? K_CR : c == 10 ? K_LF
    : c == 58 ? K_CO : K_CH;
}
static uint32_t lower(uint32_t c) { return c >= 65 && c <= 90 ? c + 32 : c; }

static void put(Conn* k, const char* s, int n) {
  if (k->outn + n <= (int)sizeof(k->out)) { memcpy(k->out + k->outn, s, n); k->outn += n; }
}
static void reply(Conn* k, const char* status, const char* ctype,
                  const char* body, int bn) {
  char h[256];
  int n = snprintf(h, sizeof(h),
    "HTTP/1.1 %s\r\ncontent-type: %s\r\ncontent-length: %d"
    "\r\nconnection: keep-alive\r\n\r\n", status, ctype, bn);
  put(k, h, n);
  put(k, body, bn);
}

// the same routes as main.bend, in the same order
static void serve(Conn* k) {
  if (k->meth != M_GET && k->meth != M_HEAD) {
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
}

static void head_done(Conn* k) {
  if (k->te) { k->st = BAD; return; }
  if (k->clen == 0) { k->bodn = 0; serve(k); k->st = IN_M; k->h = FNV; k->meth = 0;
    k->plen = 0; k->clen = 0; k->close = 0; k->te = 0; }
  else { k->bodn = 0; k->st = BOD; }
}

static void field(Conn* k) {
  if (k->n == H_CLEN && k->digit) k->clen = k->v;
  else if (k->n == H_TE) k->te = 1;
  else if (k->n == H_CONN) k->close = (k->g == H_CLOSE);
}

// one byte, the same transition table as main.bend's step.at
static void step(Conn* k, uint8_t b) {
  uint32_t c = b;
  int t = cls(b);
  switch (k->st) {
    case IN_M:
      if (t == K_SP) { k->meth = k->h; k->plen = 0; k->clen = 0; k->close = 0;
        k->te = 0; k->st = IN_T; }
      else k->h = fnv1(k->h, c);
      break;
    case IN_T:
      if (t == K_SP) { k->h = FNV; k->st = IN_V; }
      else if (k->plen < MAXPATH) k->path[k->plen++] = (char)c;
      break;
    case IN_V:
      if (t == K_CR) k->st = (k->h == H_VERSION) ? CR_M : BAD;
      else k->h = fnv1(k->h, c);
      break;
    case CR_M: k->st = (t == K_LF) ? LIN : BAD; break;
    case LIN:
      if (t == K_CR) k->st = CR_L;
      else { k->h = fnv1(FNV, lower(c)); k->st = IN_N; }
      break;
    case IN_N:
      if (t == K_CO) { k->n = k->h; k->st = OWS; }
      else k->h = fnv1(k->h, lower(c));
      break;
    case OWS:
      if (t == K_SP) break;
      if (t == K_CR) { k->v = 0; k->g = FNV; k->digit = 0; field(k); k->st = CR_M; break; }
      k->v = c - 48; k->g = fnv1(FNV, lower(c)); k->digit = (c >= 48 && c <= 57);
      k->st = IN_L;
      break;
    case IN_L:
      if (t == K_CR) { field(k); k->st = CR_M; }
      else { k->v = k->v * 10 + (c - 48); k->g = fnv1(k->g, lower(c));
        k->digit = k->digit && (c >= 48 && c <= 57); }
      break;
    case CR_L: if (t == K_LF) head_done(k); else k->st = BAD; break;
    case BOD:
      if (k->bodn < MAXBODY) k->body[k->bodn] = (char)c;
      k->bodn += 1;
      if (k->bodn >= k->clen) { serve(k); k->st = IN_M; k->h = FNV; k->meth = 0;
        k->plen = 0; k->clen = 0; k->close = 0; k->te = 0; }
      break;
    default: break;
  }
}

static void reset(Conn* k, int fd) {
  memset(k, 0, sizeof(*k));
  k->fd = fd; k->used = 1; k->st = IN_M; k->h = FNV;
}

int main(int argc, char** argv) {
  int port = argc > 1 ? atoi(argv[1]) : 8081;
  int ln = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0);
  int on = 1;
  setsockopt(ln, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));
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
      for (ssize_t j = 0; j < got; j++) step(k, (uint8_t)buf[j]);
      if (k->st == BAD) {
        k->outn = 0;
        reply(k, "400 Bad Request", "text/plain", "bad request\n", 12);
      }
      for (int off = 0; off < k->outn;) {
        ssize_t w = send(fd, k->out + off, (size_t)(k->outn - off), MSG_NOSIGNAL);
        if (w <= 0) break;
        off += (int)w;
      }
      if (k->st == BAD || k->close) {
        epoll_ctl(ep, EPOLL_CTL_DEL, fd, NULL); close(fd); k->used = 0;
      }
    }
  }
}
