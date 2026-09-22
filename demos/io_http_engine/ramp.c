// How the cost of accepting a connection grows with the number already
// held. Connections are opened in blocks and never closed, so each
// block is timed against a larger live set than the last. Against the
// Bend engine this is the measurement that finds io_wait's O(live) pass:
// holding is nearly free, arriving is not.
//
//   cc -std=c11 -O2 ramp.c -o ramp
//   ./ramp 8080 /events        # against a running engine
//   ./ramp 8081 /events        # against control.c, for the shape C has
#define _GNU_SOURCE
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define CAP 20000

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

static int held[CAP];

int main(int argc, char** argv) {
  int port = argc > 1 ? atoi(argv[1]) : 8080;
  const char* path = argc > 2 ? argv[2] : "/events";
  char req[256];
  int reqn = snprintf(req, sizeof req,
    "GET %s HTTP/1.1\r\nHost: ramp\r\n\r\n", path);

  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  int marks[] = { 500, 1000, 2000, 4000, 8000 };
  int live = 0;

  printf("%10s %12s %16s\n", "live after", "block wall s", "us per connection");
  for (unsigned m = 0; m < sizeof marks / sizeof *marks; m++) {
    int want = marks[m];
    if (want > CAP) break;
    double t0 = now();
    for (; live < want; live++) {
      int fd = socket(AF_INET, SOCK_STREAM, 0);
      if (fd < 0) { perror("socket"); return 1; }
      if (connect(fd, (struct sockaddr*)&a, sizeof a)) { perror("connect"); return 1; }
      int on = 1;
      setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &on, sizeof on);
      if (write(fd, req, (size_t)reqn) != reqn) { perror("write"); return 1; }
      held[live] = fd;
    }
    double dt = now() - t0;
    int added = want - marks[m == 0 ? 0 : m - 1];
    if (m == 0) added = want;
    printf("%10d %12.2f %16.1f\n", want, dt, dt / added * 1e6);
    fflush(stdout);
  }
  for (int i = 0; i < live; i++) close(held[i]);
  return 0;
}
