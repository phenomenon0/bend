// The two halves of bend2/comp.ts's io_wait, measured against what
// would replace them. io_wait does work proportional to every parked
// computation on each pass: it mallocs a pollfd array at the live
// count, walks the park list to fill it and to find the soonest
// deadline, polls, then walks the list again to dispatch. Accepting a
// connection needs a pass, so accepting n of them costs O(n^2).
//
// readiness: the pollfd rebuild and poll(), against epoll with the fds
//   registered once.
// deadlines: the linear scan for the soonest, against a binary min-heap.
//
// Both hold the ready/due count fixed and grow the waiting set, which
// is the shape that matters: the cost should follow what is ready, not
// what is waiting.
//
//   cc -std=c11 -O2 sched.c -o sched && ./sched
#define _GNU_SOURCE
#include <errno.h>
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

// Readiness
// =========

static int rd[20000], wr[20000];
static char junk[64];

static void ready(int n, int k, int round) {
  for (int j = 0; j < k; j++) {
    int i = (round * 7919 + j * 104729) % n;
    if (write(wr[i], "x", 1) != 1) { /* a full pipe is still ready */ }
  }
}

static void drain(int n) {
  for (int i = 0; i < n; i++) {
    (void)recv(rd[i], junk, sizeof junk, MSG_DONTWAIT);
  }
}

// what io_wait does now: build the array over every waiter, poll, rescan
static double by_poll(int n, int k, int rounds) {
  double spent = 0;
  for (int r = 0; r < rounds; r++) {
    ready(n, k, r);
    double t0 = now();
    struct pollfd* fds = malloc((size_t)(n + 1) * sizeof *fds);
    for (int i = 0; i < n; i++) {
      fds[i].fd = rd[i];
      fds[i].events = POLLIN;
      fds[i].revents = 0;
    }
    while (poll(fds, (nfds_t)n, -1) < 0 && errno == EINTR) { }
    int due = 0;
    for (int i = 0; i < n; i++) {
      due += fds[i].revents != 0;
    }
    free(fds);
    spent += now() - t0;
    drain(n);
    (void)due;
  }
  return spent / rounds;
}

// registered once; only the ready ones come back
static double by_epoll(int n, int k, int rounds) {
  int ep = epoll_create1(0);
  for (int i = 0; i < n; i++) {
    struct epoll_event e = { .events = EPOLLIN, .data.fd = rd[i] };
    epoll_ctl(ep, EPOLL_CTL_ADD, rd[i], &e);
  }
  struct epoll_event* es = malloc((size_t)n * sizeof *es);
  double spent = 0;
  for (int r = 0; r < rounds; r++) {
    ready(n, k, r);
    double t0 = now();
    int m = epoll_wait(ep, es, n, -1);
    for (int i = 0; i < m; i++) {
      (void)es[i].data.fd;
    }
    spent += now() - t0;
    drain(n);
  }
  free(es);
  close(ep);
  return spent / rounds;
}

// Deadlines
// =========

typedef struct { unsigned long long t; int id; } Ent;
static Ent list[200000], heap[200000];
static int hn;

static void hpush(Ent e) {
  int i = hn++;
  heap[i] = e;
  while (i > 0) {
    int p = (i - 1) / 2;
    if (heap[p].t <= heap[i].t) break;
    Ent x = heap[p]; heap[p] = heap[i]; heap[i] = x; i = p;
  }
}

static Ent hpop(void) {
  Ent top = heap[0];
  heap[0] = heap[--hn];
  for (int i = 0;;) {
    int l = 2 * i + 1, r = l + 1, m = i;
    if (l < hn && heap[l].t < heap[m].t) m = l;
    if (r < hn && heap[r].t < heap[m].t) m = r;
    if (m == i) break;
    Ent x = heap[m]; heap[m] = heap[i]; heap[i] = x; i = m;
  }
  return top;
}

int main(int argc, char** argv) {
  int rounds = argc > 1 ? atoi(argv[1]) : 300;

  printf("readiness: %d ready per pass, the waiting set grows\n", 10);
  printf("%9s %15s %15s %9s\n", "waiting", "poll us/pass", "epoll us/pass", "ratio");
  int fdsz[] = { 500, 1000, 2000, 4000, 8000 };
  for (unsigned s = 0; s < sizeof fdsz / sizeof *fdsz; s++) {
    int n = fdsz[s];
    for (int i = 0; i < n; i++) {
      int sv[2];
      if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv)) { perror("socketpair"); return 1; }
      rd[i] = sv[0];
      wr[i] = sv[1];
    }
    double a = by_poll(n, 10, rounds), b = by_epoll(n, 10, rounds);
    printf("%9d %15.1f %15.1f %8.1fx\n", n, a * 1e6, b * 1e6, a / b);
    for (int i = 0; i < n; i++) { close(rd[i]); close(wr[i]); }
  }

  printf("\ndeadlines: %d due per pass, the sleeping set grows\n", 10);
  printf("%9s %15s %15s %9s\n", "sleeping", "scan us/pass", "heap us/pass", "ratio");
  int tsz[] = { 1000, 5000, 10000, 50000, 100000 };
  for (unsigned s = 0; s < sizeof tsz / sizeof *tsz; s++) {
    int n = tsz[s], due = 10;
    unsigned long long base = 1000000;
    volatile unsigned long long sink = 0;
    for (int i = 0; i < n; i++) {
      list[i].t = base + (unsigned long long)(i * 13 % n);
      list[i].id = i;
    }
    double t0 = now();
    for (int r = 0; r < rounds * 4; r++) {
      unsigned long long soon = 0;
      for (int i = 0; i < n; i++) {
        if (soon == 0 || list[i].t < soon) soon = list[i].t;
      }
      unsigned long long lim = soon + (unsigned long long)due;
      for (int i = 0; i < n; i++) {
        if (list[i].t <= lim) list[i].t += (unsigned long long)n;
      }
      sink += soon;
    }
    double a = (now() - t0) / (rounds * 4);
    hn = 0;
    for (int i = 0; i < n; i++) {
      hpush((Ent){ base + (unsigned long long)(i * 13 % n), i });
    }
    t0 = now();
    for (int r = 0; r < rounds * 4; r++) {
      unsigned long long soon = heap[0].t;
      unsigned long long lim = soon + (unsigned long long)due;
      while (hn > 0 && heap[0].t <= lim) {
        Ent e = hpop();
        e.t += (unsigned long long)n;
        hpush(e);
      }
      sink += soon;
    }
    double b = (now() - t0) / (rounds * 4);
    printf("%9d %15.2f %15.2f %8.1fx\n", n, a * 1e6, b * 1e6, a / b);
  }
  return 0;
}
