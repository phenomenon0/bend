// Load generator for demos/io_http_engine. One epoll loop drives C
// keep-alive connections, each holding P requests in flight, for S
// seconds. It counts bytes and divides by the reply size it measured on
// the first connection, so it counts replies the server actually wrote
// rather than replies it hoped for. The same binary drives the Bend
// engine and the C control.
//
//   cc -std=c11 -O3 load.c -o load && ./load 8080 64 5 8 /health
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
#include <time.h>
#include <unistd.h>

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

static int dial(int port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  if (connect(fd, (struct sockaddr*)&a, sizeof(a))) { close(fd); return -1; }
  int on = 1;
  setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &on, sizeof(on));
  return fd;
}

int main(int argc, char** argv) {
  int port  = argc > 1 ? atoi(argv[1]) : 8080;
  int conns = argc > 2 ? atoi(argv[2]) : 32;
  double secs = argc > 3 ? atof(argv[3]) : 5.0;
  int pipe_ = argc > 4 ? atoi(argv[4]) : 1;
  const char* path = argc > 5 ? argv[5] : "/health";
  // LOAD_SPIN=1: never sleep, so no reply has to wake this process; the
  // server's send then costs what a send costs and not a wake-up too
  int spin = getenv("LOAD_SPIN") != NULL;

  char one[512];
  int onen = snprintf(one, sizeof(one),
    "GET %s HTTP/1.1\r\nHost: bench.local\r\nUser-Agent: bend-load/1.0"
    "\r\nAccept: */*\r\n\r\n", path);
  char* batch = malloc((size_t)onen * (size_t)pipe_ + 1);
  for (int i = 0; i < pipe_; i++) memcpy(batch + (size_t)onen * i, one, (size_t)onen);
  int batchn = onen * pipe_;

  // one round trip on its own, to learn the reply size
  int probe = dial(port);
  if (probe < 0) { perror("connect (probe)"); return 1; }
  if (write(probe, one, (size_t)onen) != onen) { fprintf(stderr, "write\n"); return 1; }
  char pb[65536];
  ssize_t pn = read(probe, pb, sizeof(pb));
  close(probe);
  if (pn <= 0) { fprintf(stderr, "no reply\n"); return 1; }
  int rsize = (int)pn;

  int ep = epoll_create1(0);
  int* fds = calloc((size_t)conns, sizeof(int));
  for (int i = 0; i < conns; i++) {
    fds[i] = dial(port);
    if (fds[i] < 0) { fprintf(stderr, "connect %d: ", i); perror(""); return 1; }
    if (write(fds[i], batch, (size_t)batchn) != batchn) { fprintf(stderr, "write\n"); return 1; }
    struct epoll_event e = { .events = EPOLLIN, .data.fd = fds[i] };
    epoll_ctl(ep, EPOLL_CTL_ADD, fds[i], &e);
  }

  static char buf[262144];
  int64_t bytes = 0, errs = 0;
  // bytes still owed on each fd before its next batch goes out
  static int owed[65536];
  for (int i = 0; i < conns; i++) owed[fds[i]] = rsize * pipe_;

  double t0 = now(), t1 = t0 + secs;
  struct epoll_event es[256];
  while (now() < t1) {
    int n = epoll_wait(ep, es, 256, spin ? 0 : 200);
    for (int i = 0; i < n; i++) {
      int fd = es[i].data.fd;
      ssize_t got = recv(fd, buf, sizeof(buf), 0);
      if (got <= 0) {
        if (got < 0 && errno == EAGAIN) continue;
        // the server closed: drop this fd and dial a replacement, so a
        // server that cannot hold the connection is counted honestly
        epoll_ctl(ep, EPOLL_CTL_DEL, fd, NULL);
        close(fd);
        errs++;
        int nf = dial(port);
        if (nf >= 0) {
          owed[nf] = rsize * pipe_;
          if (write(nf, batch, (size_t)batchn) == batchn) {
            struct epoll_event e2 = { .events = EPOLLIN, .data.fd = nf };
            epoll_ctl(ep, EPOLL_CTL_ADD, nf, &e2);
          } else { close(nf); }
        }
        continue;
      }
      bytes += got;
      owed[fd] -= (int)got;
      while (owed[fd] <= 0) {
        if (write(fd, batch, (size_t)batchn) != batchn) { errs++; break; }
        owed[fd] += rsize * pipe_;
      }
    }
  }
  double dt = now() - t0;
  double reqs = (double)bytes / (double)rsize;
  printf("%.0f req in %.2fs  %.0f req/s  %.1f MB/s  reply=%dB conns=%d pipeline=%d errs=%lld\n",
    reqs, dt, reqs / dt, (double)bytes / dt / 1e6, rsize, conns, pipe_,
    (long long)errs);
  return 0;
}
