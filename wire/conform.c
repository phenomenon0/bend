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
// crawling send delivered, the very bytes of the file each sendfile
// put on the wire, that the flood was shed rather than refused),
// echoes conform's verdicts, and exits 0 only when both sides passed.
//
//   bend wire/conform.bend -o conform
//   cc -std=c11 -O2 -Wall wire/conform.c -o conform-peer -lssl -lcrypto
//   ./conform-peer ./conform 19120 /tmp/conform-root
//
// For the connects conform makes out, it serves before conform starts:
// port + 1 accepts, port + 2 is left closed, port + 3's backlog is full
// (its SYNs go unanswered), port + 4 is TLS with a certificate for
// localhost that is its own CA (made here with the openssl command,
// passed to conform as the pin) and answers "ping" with "pong", and
// port + 5 answers in plain HTTP and closes; port + 6 is told what to do
// by conform's first byte: nothing, send a byte, or close (TCP.idle).
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
#include <openssl/err.h>
#include <openssl/ssl.h>

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

// read until conform closes the connection, keeping up to cap bytes
static long slurp(int fd, char* b, long cap, int ms) {
  long got = 0;
  for (;;) {
    ssize_t n = read_for(fd, b + got, cap - got > 65536 ? 65536 : cap - got, ms);
    if (n <= 0) break;
    got += n;
    if (got == cap) break;
  }
  close(fd);
  return got;
}

// big.bin's byte at i: no two blocks of it alike, so a block sent from
// the wrong offset shows
static unsigned char big_at(long i) {
  return (unsigned char)(i * 7 + (i >> 16));
}

#define BIG (16L << 20)

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
  snprintf(p, sizeof(p), "%s/big.bin", root);
  f = fopen(p, "w");
  for (long i = 0; i < BIG; i++) fputc(big_at(i), f);
  fclose(f);
}

static int alpn_h11(SSL* ssl, const unsigned char** out, unsigned char* outn,
  const unsigned char* in, unsigned int inn, void* arg) {
  static const unsigned char h11[] = { 8, 'h', 't', 't', 'p', '/', '1', '.', '1' };
  return SSL_select_next_proto((unsigned char**)out, outn, h11, sizeof(h11), in, inn)
    == OPENSSL_NPN_NEGOTIATED ? SSL_TLSEXT_ERR_OK : SSL_TLSEXT_ERR_NOACK;
}

static int listen_on(int port, int backlog) {
  int fd = socket(AF_INET, SOCK_STREAM, 0), one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port),
    .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
  if (bind(fd, (struct sockaddr*)&a, sizeof(a)) != 0 || listen(fd, backlog) != 0) {
    perror("listen");
    exit(1);
  }
  return fd;
}

// the connects' servers, in a child of their own until killed
static pid_t servers(const char* cert, const char* key) {
  int acc = listen_on(PORT + 1, 16), tls = listen_on(PORT + 4, 16), plain = listen_on(PORT + 5, 16),
    idle = listen_on(PORT + 6, 16);
  pid_t pid = fork();
  if (pid != 0) {
    close(acc); close(tls); close(plain); close(idle);
    return pid;
  }
  SSL_CTX* ctx = SSL_CTX_new(TLS_server_method());
  if (SSL_CTX_use_certificate_chain_file(ctx, cert) != 1
    || SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) != 1) {
    fprintf(stderr, "the connects' certificate did not load\n");
    _exit(1);
  }
  SSL_CTX_set_alpn_select_cb(ctx, alpn_h11, NULL);
  for (;;) {
    struct pollfd p[4] = { { acc, POLLIN, 0 }, { tls, POLLIN, 0 }, { plain, POLLIN, 0 },
      { idle, POLLIN, 0 } };
    if (poll(p, 4, -1) < 0) continue;
    // port + 6: one byte says what to do -- q nothing, b a byte, f close --
    // and then the connection is held until conform closes it
    if (p[3].revents) {
      int c = accept(idle, NULL, NULL);
      char cmd = 0, b[64];
      if (c >= 0 && read_for(c, &cmd, 1, 3000) == 1) {
        if (cmd == 'b') send(c, "x", 1, 0);
        if (cmd != 'f') while (read_for(c, b, sizeof(b), 3000) > 0) {}
      }
      if (c >= 0) close(c);
    }
    if (p[0].revents) {
      int c = accept(acc, NULL, NULL);
      if (c >= 0) close(c);
    }
    if (p[2].revents) {
      int c = accept(plain, NULL, NULL);
      if (c >= 0) {
        const char* r = "HTTP/1.1 400 Bad Request\r\nContent-Length: 0\r\n\r\n";
        send(c, r, strlen(r), 0);
        close(c);
      }
    }
    if (p[1].revents) {
      int c = accept(tls, NULL, NULL);
      if (c < 0) continue;
      struct timeval tv = { 3, 0 };
      setsockopt(c, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
      SSL* ssl = SSL_new(ctx);
      SSL_set_fd(ssl, c);
      if (SSL_accept(ssl) == 1) {
        char b[8];
        if (SSL_read(ssl, b, 4) == 4 && memcmp(b, "ping", 4) == 0) {
          SSL_write(ssl, "pong", 4);
        }
        SSL_shutdown(ssl);
      }
      SSL_free(ssl);
      ERR_clear_error();
      close(c);
    }
  }
}

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: conform-peer BIN PORT ROOT\n"); return 2; }
  PORT = atoi(argv[2]);
  signal(SIGPIPE, SIG_IGN);
  files(argv[3]);

  // the connects: a certificate for localhost, its own CA; a full
  // backlog on port + 3 (one queued connection fills a backlog of 0,
  // and the kernel drops the SYNs after it); the servers
  char cert[4096], key[4096], cmd[12288];
  snprintf(cert, sizeof(cert), "%s/../conform-cert.pem", argv[3]);
  snprintf(key, sizeof(key), "%s/../conform-key.pem", argv[3]);
  snprintf(cmd, sizeof(cmd), "openssl req -x509 -newkey rsa:2048 -keyout '%s' -out '%s' -days 2"
    " -nodes -subj /CN=localhost -addext subjectAltName=DNS:localhost 2>/dev/null", key, cert);
  if (system(cmd) != 0) { fprintf(stderr, "openssl req failed\n"); return 1; }
  int full = listen_on(PORT + 3, 0), queued[3];
  for (int i = 0; i < 3; i++) {
    queued[i] = socket(AF_INET, SOCK_STREAM, 0);
    fcntl(queued[i], F_SETFL, O_NONBLOCK);
    struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(PORT + 3),
      .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
    connect(queued[i], (struct sockaddr*)&a, sizeof(a));
  }
  pid_t srv = servers(cert, key);

  int out[2];
  if (pipe(out) != 0) { perror("pipe"); return 1; }
  pid_t pid = fork();
  if (pid == 0) {
    // few enough descriptors that a flood of connections runs them out
    struct rlimit lim = { 48, 48 };
    setrlimit(RLIMIT_NOFILE, &lim);
    dup2(out[1], 1);
    close(out[0]); close(out[1]);
    execl(argv[1], argv[1], argv[2], argv[3], cert, "--threads", "1", (char*)NULL);
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

  // fsend.crawl: big.bin by sendfile through a 16 KiB window read every
  // 2 ms, far longer than the send's 300 ms deadline; every byte must
  // arrive, and be the file's
  fd = take(16384);
  if (fd >= 0) {
    char* b = malloc(BIG + 1);
    long got = 0;
    for (;;) {
      ssize_t n = read_for(fd, b + got, BIG + 1 - got > 65536 ? 65536 : BIG + 1 - got, 5000);
      if (n <= 0) break;
      got += n;
      nap(2);
    }
    close(fd);
    long bad = got == BIG ? 0 : 1;
    for (long i = 0; i < got && i < BIG && bad == 0; i++) bad = (unsigned char)b[i] != big_at(i);
    free(b);
    char what[128];
    snprintf(what, sizeof(what), "fsend.crawl delivered %ld of %ld bytes, %s", got, BIG,
      bad ? "not the file's" : "the file's");
    ok(bad == 0, what);
  }

  // fsend.part: a.txt from 1, 3 bytes: "lph", and nothing else
  fd = take(0);
  if (fd >= 0) {
    char b[64];
    long got = slurp(fd, b, sizeof(b), 5000);
    ok(got == 3 && memcmp(b, "lph", 3) == 0, "fsend.part delivered the file's bytes 1 to 3");
  }

  // fsend.short: a.txt from 3, 100 bytes asked: the 3 it has, "ha\n"
  fd = take(0);
  if (fd >= 0) {
    char b[256];
    long got = slurp(fd, b, sizeof(b), 5000);
    ok(got == 3 && memcmp(b, "ha\n", 3) == 0, "fsend.short delivered what the file had");
  }

  // fsend.stall: read nothing; conform's sendfile must give up after
  // 300 ms, and what did arrive is the file's head
  fd = take(4096);
  if (fd >= 0) {
    nap(1500);
    char* b = malloc(BIG);
    long got = slurp(fd, b, BIG, 5000);
    long bad = 0;
    for (long i = 0; i < got && bad == 0; i++) bad = (unsigned char)b[i] != big_at(i);
    free(b);
    char what[128];
    snprintf(what, sizeof(what), "fsend.stall delivered %ld of %ld bytes before it gave up", got,
      BIG);
    ok(got < BIG && bad == 0, what);
  }

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
  kill(srv, SIGKILL);
  waitpid(srv, NULL, 0);
  for (int i = 0; i < 3; i++) close(queued[i]);
  close(full);
  int clean = WIFEXITED(st) && WEXITSTATUS(st) == 0;
  printf("conform: %d / %d on the effects' side, %d / %d on the peer's, exit %s\n",
    theirs_pass, theirs_pass + theirs_fail, pass, pass + fail, clean ? "clean" : "unclean");
  return clean && fail == 0 && theirs_fail == 0 && theirs_pass > 0 ? 0 : 1;
}
