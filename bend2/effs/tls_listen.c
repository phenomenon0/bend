// TLS
// ===

// TLS.listen(port, cert, key) is TCP.listen with a TLS session under
// every socket it accepts. It installs an IoWire, so nothing else
// changes: TCP.accept, TCP.recv_bytes, TCP.send_bytes, TCP.poll_bytes
// and Socket.close go through the wire already and do not know whether
// what they are carrying is encrypted. A program that never imports
// this never includes <openssl/ssl.h>, and the build links libssl only
// for the ones that do.
//
// The handshake is not done at accept: it runs inside the first read or
// write, driven by the same park the rest of the loop uses. That is why
// a slow or hostile handshake costs a parked computation and not a
// blocked server, and why the connection's idle deadline covers it.
#include <openssl/err.h>
#include <openssl/ssl.h>

// Which listeners are TLS, and which sockets have a session. Both are
// arrays over the descriptor, grown as descriptors get larger, because
// a descriptor is a small dense integer and anything cleverer would be
// a map that is never looked at twice.
static SSL_CTX** tls_ctx;
static u32       tls_ctx_cap;
static SSL**     tls_ssl;
static u32       tls_ssl_cap;
static u8*       tls_up;
static u32       tls_up_cap;

// What tls_up says of a socket: its session is not up yet, is up, has
// failed (so no close_notify is owed or sent), or never existed because
// SSL_new failed (so the socket is refused, never read in the clear).
enum { TLS_NEW = 0, TLS_UP = 1, TLS_BROKE = 2, TLS_NONE = 3 };

#define TLS_SLOT(tab, cap, fd, type)                                       \
  do {                                                                     \
    if ((u32)(fd) >= (cap)) {                                              \
      u32 was = (cap);                                                     \
      (cap) = (cap) != 0 ? (cap) : 256;                                    \
      while ((u32)(fd) >= (cap)) {                                         \
        (cap) *= 2;                                                        \
      }                                                                    \
      (tab) = io_mem(realloc((tab), (cap) * sizeof(type)));                \
      memset((tab) + was, 0, ((cap) - was) * sizeof(type));                \
    }                                                                      \
  } while (0)

static SSL* tls_of(int fd) {
  return fd >= 0 && (u32)fd < tls_ssl_cap ? tls_ssl[fd] : NULL;
}

static u8 tls_state(int fd) {
  return fd >= 0 && (u32)fd < tls_up_cap ? tls_up[fd] : TLS_NEW;
}

// Before every SSL_* call: what SSL_get_error reads is the error queue
// and errno, so a stale entry from another socket, or a stale EAGAIN,
// would be read as this call's answer.
static void tls_pre(void) {
  errno = 0;
  ERR_clear_error();
}

// What OpenSSL is waiting for, said the way the rest of the runtime
// says it: a short read that has to be tried again sets errno to EAGAIN
// and dir to the direction the socket must become ready in, which for a
// read is not always POLLIN.
static ssize_t tls_again(int fd, SSL* ssl, int n, short* dir) {
  int why = SSL_get_error(ssl, n);
  if (why == SSL_ERROR_WANT_READ) {
    *dir  = POLLIN;
    errno = EAGAIN;
    return -1;
  }
  if (why == SSL_ERROR_WANT_WRITE) {
    *dir  = POLLOUT;
    errno = EAGAIN;
    return -1;
  }
  if (why == SSL_ERROR_ZERO_RETURN) {
    return 0;
  }
  tls_up[fd] = TLS_BROKE;
  if (why == SSL_ERROR_SYSCALL) {
    if (errno == 0) {
      errno = ECONNRESET;
    }
    return -1;
  }
  ERR_clear_error();
  errno = EPROTO;
  return -1;
}

// The handshake, run wherever the first byte is wanted. It answers 1
// when the session is up, 0 when it needs the socket to become ready in
// dir, and -1 when it will never come up.
static int tls_hand(int fd, SSL* ssl, short* dir) {
  if (tls_state(fd) == TLS_UP) {
    return 1;
  }
  if (tls_state(fd) == TLS_BROKE) {
    errno = EPROTO;
    return -1;
  }
  tls_pre();
  int n = SSL_accept(ssl);
  if (n == 1) {
    tls_up[fd] = TLS_UP;
    return 1;
  }
  return tls_again(fd, ssl, n, dir) < 0 && errno == EAGAIN ? 0 : -1;
}

// A socket from a TLS listener that has no session is refused rather
// than read or written in the clear.
static bool tls_none(int fd) {
  if (tls_state(fd) != TLS_NONE) {
    return false;
  }
  errno = EPROTO;
  return true;
}

static ssize_t tls_read(int fd, void* buf, size_t len, short* dir) {
  SSL* ssl = tls_of(fd);
  if (ssl == NULL) {
    return tls_none(fd) ? -1 : recv(fd, buf, len, 0);
  }
  int up = tls_hand(fd, ssl, dir);
  if (up != 1) {
    return up == 0 ? (errno = EAGAIN, -1) : -1;
  }
  tls_pre();
  int n = SSL_read(ssl, buf, len > INT_MAX ? INT_MAX : (int)len);
  return n > 0 ? (ssize_t)n : tls_again(fd, ssl, n, dir);
}

static ssize_t tls_write(int fd, const void* buf, size_t len, short* dir) {
  SSL* ssl = tls_of(fd);
  if (ssl == NULL) {
    return tls_none(fd) ? -1 : send(fd, buf, len, 0);
  }
  int up = tls_hand(fd, ssl, dir);
  if (up != 1) {
    return up == 0 ? (errno = EAGAIN, -1) : -1;
  }
  tls_pre();
  int n = SSL_write(ssl, buf, len > INT_MAX ? INT_MAX : (int)len);
  return n > 0 ? (ssize_t)n : tls_again(fd, ssl, n, dir);
}

// A socket that closes without a close_notify leaves the peer unable to
// tell an orderly end from a cut connection, which is the truncation a
// peer is supposed to refuse to guess at. Ours goes out first, once and
// without waiting for theirs: the connection is ending either way, and
// a server that waited would be one a peer could hold open. After a
// fatal error there is no session to end, and none is attempted.
static void tls_shut(int fd) {
  SSL* ssl = tls_of(fd);
  if (ssl != NULL) {
    if (tls_state(fd) == TLS_UP) {
      tls_pre();
      SSL_shutdown(ssl);
      ERR_clear_error();
    }
    SSL_free(ssl);
    tls_ssl[fd] = NULL;
  }
  if (fd >= 0 && (u32)fd < tls_up_cap) {
    tls_up[fd] = TLS_NEW;
  }
  if (fd >= 0 && (u32)fd < tls_ctx_cap && tls_ctx[fd] != NULL) {
    SSL_CTX_free(tls_ctx[fd]);
    tls_ctx[fd] = NULL;
  }
}

// A socket accepted from a TLS listener gets that listener's session
// waiting to be handshaken; one from a plain listener gets nothing and
// stays a plain socket, so a program may serve both.
static void tls_join(int lfd, int fd) {
  SSL_CTX* ctx = lfd >= 0 && (u32)lfd < tls_ctx_cap ? tls_ctx[lfd] : NULL;
  if (ctx == NULL) {
    return;
  }
  TLS_SLOT(tls_up, tls_up_cap, fd, u8);
  tls_pre();
  SSL* ssl = SSL_new(ctx);
  if (ssl == NULL || SSL_set_fd(ssl, fd) != 1) {
    SSL_free(ssl);
    ERR_clear_error();
    shutdown(fd, SHUT_RDWR);
    tls_up[fd] = TLS_NONE;
    return;
  }
  SSL_set_accept_state(ssl);
  TLS_SLOT(tls_ssl, tls_ssl_cap, fd, SSL*);
  tls_ssl[fd] = ssl;
  tls_up[fd]  = TLS_NEW;
}

static IoWire tls_wire = { tls_read, tls_write, tls_join, tls_shut };

// http/1.1 is what this engine speaks, so it is what it agrees to. h2
// goes here, before http/1.1, when there is an h2 to agree to.
static const unsigned char tls_alpn[] = { 8, 'h', 't', 't', 'p', '/', '1', '.', '1' };

static int tls_pick(SSL* ssl, const unsigned char** out, unsigned char* outn,
  const unsigned char* in, unsigned int inn, void* arg) {
  return SSL_select_next_proto((unsigned char**)out, outn, tls_alpn,
    sizeof(tls_alpn), in, inn) == OPENSSL_NPN_NEGOTIATED
    ? SSL_TLSEXT_ERR_OK : SSL_TLSEXT_ERR_NOACK;
}

static SSL_CTX* tls_make(const char* cert, const char* key, uint32_t* err) {
  SSL_CTX* ctx = SSL_CTX_new(TLS_server_method());
  if (ctx == NULL) {
    *err = ENOMEM;
    return NULL;
  }
  // no renegotiation (a CPU lever for the peer); a close without a
  // close_notify is an end rather than an error; buffers go back while
  // a connection idles; TLS 1.2 only with ephemeral keys and AEAD (TLS
  // 1.3's suites are all of that already)
  SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION);
  SSL_CTX_set_options(ctx, SSL_OP_NO_RENEGOTIATION
#ifdef SSL_OP_IGNORE_UNEXPECTED_EOF
    | SSL_OP_IGNORE_UNEXPECTED_EOF
#endif
    );
  SSL_CTX_set_mode(ctx, SSL_MODE_ENABLE_PARTIAL_WRITE
    | SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER | SSL_MODE_RELEASE_BUFFERS);
  SSL_CTX_set_alpn_select_cb(ctx, tls_pick, NULL);
  if (SSL_CTX_set_cipher_list(ctx, "ECDHE+AESGCM:ECDHE+CHACHA20:!aNULL") != 1
    || SSL_CTX_use_certificate_chain_file(ctx, cert) != 1
    || SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) != 1
    || SSL_CTX_check_private_key(ctx) != 1) {
    ERR_clear_error();
    SSL_CTX_free(ctx);
    *err = EINVAL;
    return NULL;
  }
  return ctx;
}

// The same socket TCP.listen opens, opened here rather than borrowed:
// an effect is only compiled into a program that uses it, so one that
// leans on another's C is one that does not build.
static uint32_t tls_bind(uint32_t port, int* out) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    return (uint32_t)errno;
  }
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  struct sockaddr_in at;
  if (io_sys_addr("0.0.0.0", port, &at) < 0) {
    close(fd);
    return EINVAL;
  }
  if (bind(fd, (struct sockaddr*)&at, sizeof(at)) < 0
    || listen(fd, SOMAXCONN) < 0
    || fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK) < 0) {
    uint32_t code = (uint32_t)errno;
    close(fd);
    return code;
  }
  *out = fd;
  return 0;
}

Term tls_listen_run(Env e, Term* f, IoWork* w) {
  u64   cn = 0, kn = 0;
  char* cert = io_cstr(e, f[1], &cn);
  char* key  = io_cstr(e, f[2], &kn);
  if (io_nul(cert, cn) || io_nul(key, kn)) {
    free(cert);
    free(key);
    return io_fail(e, EINVAL, NULL);
  }
  uint32_t err = 0;
  SSL_CTX* ctx = tls_make(cert, key, &err);
  free(cert);
  free(key);
  if (ctx == NULL) {
    return io_fail(e, err, NULL);
  }
  int out = -1;
  uint32_t q = tls_bind((uint32_t)f[0], &out);
  if (q != 0) {
    SSL_CTX_free(ctx);
    return io_fail(e, q, NULL);
  }
  TLS_SLOT(tls_ctx, tls_ctx_cap, out, SSL_CTX*);
  tls_ctx[out] = ctx;
  io_wire      = &tls_wire;
  return io_done(e, io_hand(out));
}

static void __attribute__((constructor)) tls_listen_use(void) {
  io_eff(CID_TLS_LISTEN, tls_listen_run, 0);
}
