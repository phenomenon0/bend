// The peer for conform.bend: the bridge between the proofs and C.
//
// world.bend states what the model of the socket world assumes of each
// effect (a relation per effect) and proves the model keeps it,
// and conform.bend judges the real effects by those same relations. This
// program plays the other end: it lays out the files, starts conform
// under a descriptor limit low enough to run out, and for each case, in
// the order conform takes them, connects, waits for conform's "A", and
// behaves as the case says -- silent, late, too much, a FIN, a reset, a
// reader through a 16 KiB window, a reader that stops, a flood of
// connections. It checks what it sees from its side too (the bytes a
// crawling send delivered, that the flood was shed rather than
// refused), echoes conform's verdicts, and exits 0 only when both
// sides passed.
//
//   bend wire/conform.bend -o conform
//   cc -std=c11 -O2 -Wall wire/conform.c -o conform-peer
//   ./conform-peer ./conform 19120 /tmp/conform-root
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static int PORT, pass = 0, fail = 0;

static void ok(int c, const char* what) {
  printf("%s  peer: %s\n", c ? "PASS" : "FAIL", what);
  fflush(stdout);
  if (c) pass++; else fail++;
}

static double now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec * 1e3 + (double)t.tv_nsec / 1e6;
}

static void nap(int ms) {
  struct timespec t = { ms / 1000, (long)(ms % 1000) * 1000000L };
  nanosleep(&t, NULL);
}

static int dial(int rcvbuf) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (rcvbuf > 0) setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &rcvbuf, sizeof(rcvbuf));
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(PORT),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  if (connect(fd, (struct sockaddr*)&a, sizeof(a)) != 0) { close(fd); return -1; }
  int on = 1;
  setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &on, sizeof(on));
  return fd;
}

// read with a deadline: bytes, 0 at EOF, -1 on error, -2 on timeout
static ssize_t read_for(int fd, char* b, size_t n, int ms) {
  struct pollfd p = { fd, POLLIN, 0 };
  int r = poll(&p, 1, ms);
  if (r == 0) return -2;
  if (r < 0) return -1;
  return recv(fd, b, n, 0);
}

// connect for the next case and wait for conform's "A"
static int take(int rcvbuf) {
  for (int i = 0; i < 50; i++) {
    int fd = dial(rcvbuf);
    if (fd >= 0) {
      char c;
      ssize_t n = read_for(fd, &c, 1, 10000);
      if (n == 1 && c == 'A') return fd;
      close(fd);
      return -1;
    }
    nap(100);
  }
  return -1;
}

// read until conform closes the connection; the bytes that came
static long drain(int fd, int ms) {
  char b[65536];
  long got = 0;
  for (;;) {
    ssize_t n = read_for(fd, b, sizeof(b), ms);
    if (n <= 0) break;
    got += n;
  }
  close(fd);
  return got;
}

static void reset(int fd) {
  struct linger l = { 1, 0 };
  setsockopt(fd, SOL_SOCKET, SO_LINGER, &l, sizeof(l));
  close(fd);
}

static void files(const char* root) {
  char p[4096], q[4096];
  snprintf(p, sizeof(p), "%s", root);
  for (char* c = p + 1; *c; c++) {
    if (*c == '/') { *c = 0; mkdir(p, 0755); *c = '/'; }
  }
  mkdir(root, 0755);
  snprintf(p, sizeof(p), "%s/a.txt", root);
  FILE* f = fopen(p, "w"); fputs("alpha\n", f); fclose(f);
  snprintf(p, sizeof(p), "%s/link", root);
  unlink(p);
  if (symlink("a.txt", p) != 0) perror("symlink");
  snprintf(p, sizeof(p), "%s/sub", root);
  mkdir(p, 0755);
  snprintf(q, sizeof(q), "%s/../conform-outside.txt", root);
  f = fopen(q, "w"); fputs("out\n", f); fclose(f);
}

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: conform-peer BIN PORT ROOT\n"); return 2; }
  PORT = atoi(argv[2]);
  signal(SIGPIPE, SIG_IGN);
  files(argv[3]);

  int out[2];
  if (pipe(out) != 0) { perror("pipe"); return 1; }
  pid_t pid = fork();
  if (pid == 0) {
    // few enough descriptors that a flood of connections runs them out
    struct rlimit lim = { 48, 48 };
    setrlimit(RLIMIT_NOFILE, &lim);
    dup2(out[1], 1);
    close(out[0]); close(out[1]);
    execl(argv[1], argv[1], argv[2], argv[3], "--threads", "1", (char*)NULL);
    perror("exec");
    _exit(127);
  }
  close(out[1]);
  FILE* from = fdopen(out[0], "r");
  char line[4096];
  if (fgets(line, sizeof(line), from) == NULL || strncmp(line, "ready", 5) != 0) {
    fprintf(stderr, "conform never became ready\n");
    kill(pid, SIGKILL);
    return 1;
  }

  // rx.silent: say nothing; conform's read waits out 300 ms
  int fd = take(0);
  ok(fd >= 0, "rx.silent connected");
  if (fd >= 0) drain(fd, 5000);

  // rx.wakes: 100 ms late, ten bytes; the read parks, then wakes
  fd = take(0);
  if (fd >= 0) { nap(100); send(fd, "0123456789", 10, 0); drain(fd, 5000); }

  // rx.max: ten bytes at once to a read of four
  fd = take(0);
  if (fd >= 0) { send(fd, "0123456789", 10, 0); drain(fd, 5000); }

  // rx.fin: close at once
  fd = take(0);
  if (fd >= 0) close(fd);

  // rx.reset: reset at once
  fd = take(0);
  if (fd >= 0) reset(fd);

  // tx.crawl: a 16 KiB window, read every 2 ms; 16 MiB must all arrive
  // though it takes far longer than the send's 300 ms deadline
  fd = take(16384);
  if (fd >= 0) {
    char* b = malloc(65536);
    long got = 0;
    double t0 = now_ms();
    for (;;) {
      ssize_t n = read_for(fd, b, 65536, 5000);
      if (n <= 0) break;
      got += n;
      nap(2);
    }
    free(b);
    close(fd);
    char what[128];
    snprintf(what, sizeof(what), "tx.crawl delivered %ld of %d bytes in %.0f ms", got, 16 << 20,
      now_ms() - t0);
    ok(got == 16L << 20, what);
  }

  // tx.stall: read nothing; conform's send must give up after 300 ms
  fd = take(4096);
  if (fd >= 0) {
    nap(1500);
    long got = drain(fd, 5000);
    char what[128];
    snprintf(what, sizeof(what), "tx.stall delivered %ld of %d bytes before it gave up", got,
      16 << 20);
    ok(got < 16L << 20, what);
  }

  // tx.reset: reset before conform sends
  fd = take(0);
  if (fd >= 0) reset(fd);

  // lsn.emfile: 80 connections at once against 48 descriptors. Those it
  // cannot hold are shed (closed at once), not left to wake it forever;
  // then, once it lets the rest go, a last connection is served.
  int fds[80], shed = 0;
  for (int i = 0; i < 80; i++) fds[i] = dial(0);
  nap(1500);
  for (int i = 0; i < 80; i++) {
    if (fds[i] < 0) continue;
    char c;
    ssize_t n = read_for(fds[i], &c, 1, 0);
    if (n == 0 || (n < 0 && n != -2)) shed++;
  }
  for (int i = 0; i < 80; i++) if (fds[i] >= 0) close(fds[i]);
  char what[128];
  snprintf(what, sizeof(what), "lsn.emfile shed %d of 80 connections", shed);
  ok(shed > 0, what);
  int served = 0;
  for (int i = 0; i < 20 && !served; i++) {
    int l = dial(0);
    if (l < 0) { nap(200); continue; }
    send(l, "x", 1, 0);
    char b[8];
    ssize_t n = read_for(l, b, sizeof(b), 1500);
    served = n == 2 && memcmp(b, "ok", 2) == 0;
    close(l);
    if (!served) nap(100);
  }
  ok(served, "lsn.emfile the last connection was served");

  // conform's verdicts
  int theirs_pass = 0, theirs_fail = 0;
  while (fgets(line, sizeof(line), from) != NULL) {
    fputs(line, stdout);
    if (strncmp(line, "PASS", 4) == 0) theirs_pass++;
    if (strncmp(line, "FAIL", 4) == 0) theirs_fail++;
  }
  int st = 0;
  waitpid(pid, &st, 0);
  int clean = WIFEXITED(st) && WEXITSTATUS(st) == 0;
  printf("conform: %d / %d on the effects' side, %d / %d on the peer's, exit %s\n",
    theirs_pass, theirs_pass + theirs_fail, pass, pass + fail, clean ? "clean" : "unclean");
  return clean && fail == 0 && theirs_fail == 0 && theirs_pass > 0 ? 0 : 1;
}
