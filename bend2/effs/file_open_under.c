// File
// ====

#include <sys/stat.h>
#include <sys/uio.h>
#if defined(__linux__)
#include <sys/syscall.h>
#endif

// path, opened for reading one component at a time below root: every
// step is an openat with O_NOFOLLOW, so a symbolic link anywhere under
// root, to a file or to a directory, fails (ELOOP) rather than being
// followed out of it. A component that is empty, "." or ".." fails with
// EACCES, and so does an end that is not a regular file (EISDIR for a
// directory); O_NONBLOCK keeps a FIFO from parking the helper thread.
// root itself is opened as given: it is the operator's, not the peer's.
static int file_open_under_walk(const char* root, char* at) {
  int dir = open(root, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  while (dir >= 0) {
    char* cut  = strchr(at, '/');
    int   last = cut == NULL;
    if (!last) {
      *cut = 0;
    }
    if (*at == 0 || strcmp(at, ".") == 0 || strcmp(at, "..") == 0) {
      close(dir);
      errno = EACCES;
      return -1;
    }
    int fd = openat(dir, at, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NOCTTY
      | (last ? O_NONBLOCK : O_DIRECTORY));
    int no = errno;
    close(dir);
    errno = no;
    if (fd < 0 || !last) {
      dir = fd;
      at  = cut + 1;
      continue;
    }
    return fd;
  }
  return -1;
}

// Linux 5.6 and later resolve the whole path in one openat2 under
// RESOLVE_BENEATH | RESOLVE_NO_SYMLINKS: no symbolic link anywhere, no
// escape from root. The walk's refusals by shape (an empty, "." or ".."
// component: EACCES) are made first, so both ways refuse the same names
// with the same codes. A kernel or a sandbox without it (ENOSYS, EPERM)
// falls back to the walk, for good.
#if defined(__linux__) && defined(SYS_openat2)
static int file_open_under_no2;

static bool file_open_under_shape(const char* p) {
  for (;;) {
    const char* c = strchr(p, '/');
    size_t      n = c ? (size_t)(c - p) : strlen(p);
    if (n == 0 || (p[0] == '.' && (n == 1 || (n == 2 && p[1] == '.')))) {
      return false;
    }
    if (!c) {
      return true;
    }
    p = c + 1;
  }
}

static int file_open_under_two(const char* root, const char* at) {
  if (!file_open_under_shape(at)) {
    errno = EACCES;
    return -1;
  }
  int dir = open(root, O_PATH | O_DIRECTORY | O_CLOEXEC);
  if (dir < 0) {
    return -1;
  }
  struct { u64 flags, mode, resolve; } how = {
    O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NOCTTY | O_NONBLOCK, 0,
    0x08 | 0x04 | 0x02 };  // RESOLVE_BENEATH, NO_SYMLINKS, NO_MAGICLINKS
  int fd = (int)syscall(SYS_openat2, dir, at, &how, sizeof how);
  int no = errno;
  close(dir);
  errno = no;
  return fd;
}
#endif

// the end, opened, must be a regular file; st is its fstat
static int file_open_under_end(int fd, struct stat* st) {
  if (fd >= 0 && (fstat(fd, st) != 0 || !S_ISREG(st->st_mode))) {
    int no = S_ISDIR(st->st_mode) ? EISDIR : EACCES;
    close(fd);
    errno = no;
    return -1;
  }
  return fd;
}

static int file_open_under_stat(const char* root, char* at, struct stat* st) {
#if defined(__linux__) && defined(SYS_openat2)
  if (!file_open_under_no2) {
    int fd = file_open_under_two(root, at);
    if (fd >= 0 || (errno != ENOSYS && errno != EPERM)) {
      return file_open_under_end(fd, st);
    }
    file_open_under_no2 = 1;
  }
#endif
  return file_open_under_end(file_open_under_walk(root, at), st);
}

static int file_open_under_fd(const char* root, char* at) {
  struct stat st;
  int fd = file_open_under_stat(root, at, &st);
  if (fd >= 0) {
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) & ~O_NONBLOCK);
  }
  return fd;
}

#ifdef CID_FILE_OPEN_UNDER

static void file_open_under_call(IoWork* w) {
  w->made = (intptr_t)io_sys_end(w, file_open_under_fd(w->text, w->data));
}

static Term file_open_under_pack(Env e, IoWork* w) {
  free(w->data);
  free(w->text);
  return w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, io_hand(w->made));
}

Term file_open_under_run(Env e, Term* f, IoWork* w) {
  uint64_t rn = 0;
  w->text = io_cstr(e, f[0], &rn);
  w->data = io_cstr(e, f[1], &w->size);
  w->code = 0;
  if (io_nul(w->text, rn) || io_nul(w->data, w->size)) {
    w->code = EILSEQ;
    return file_open_under_pack(e, w);
  }
  // on the loop: a walk of openat and one fstat, which the dentry cache
  // answers, costs less than a helper's round trip
  return io_now(e, w, file_open_under_call, file_open_under_pack);
}

static void __attribute__((constructor)) file_open_under_use(void) {
  io_eff(CID_FILE_OPEN_UNDER, file_open_under_run, 0);
}

#endif

#ifdef CID_FILE_GET_UNDER

// File.get_under(root, path, small): File.open_under and its fstat in
// one effect, and, for a file under small bytes, its read and close too:
// Done{(size, (mtime, (None, body)))}, or Done{(size, (mtime, (Some{file},
// "")))} with the file open at 0 for a larger one -- or a small one whose
// bytes the page cache does not hold, which is then read as any other.
// The body is read straight into the block the Bytes will be; a file
// that shrank since its fstat comes back shorter than its size.
static Term file_get_under_body(Env e, int fd, u64 n, bool* held) {
  StrParts p = str_alloc(e, n, 2);
  *held = true;
  if (!n || !p.data || err_seen(e.mem)) {
    return str_view_owned(e, p);
  }
  u8* at  = (u8*)(e.mem + term_peek(e, p.data));
  u64 got = 0;
  while (got < n) {
    struct iovec v = { at + got, n - got };
#if defined(__linux__) && defined(RWF_NOWAIT)
    ssize_t k = preadv2(fd, &v, 1, (off_t)got, got == 0 ? RWF_NOWAIT : 0);
#else
    ssize_t k = preadv(fd, &v, 1, (off_t)got);
#endif
    if (k < 0 && errno == EINTR) {
      continue;
    }
    if (k < 0 && got == 0) {
      *held = false;
      p.len = 0;
      break;
    }
    if (k <= 0) {
      break;
    }
    got += (u64)k;
  }
  p.len = *held ? (u32)got : 0;
  return str_view_owned(e, p);
}

Term file_get_under_run(Env e, Term* f, IoWork* w) {
  u64   rn = 0, pn = 0;
  char* root = io_cstr(e, f[0], &rn);
  char* path = io_cstr(e, f[1], &pn);
  u64   small = (u64)(u32)f[2];
  int   fd = -1;
  struct stat st;
  errno = EILSEQ;
  if (!io_nul(root, rn) && !io_nul(path, pn)) {
    fd = file_open_under_stat(root, path, &st);
  }
  int no = errno;
  free(root);
  free(path);
  if (fd >= 0 && st.st_size > (off_t)UINT32_MAX) {
    close(fd);
    fd = -1;
    no = EOVERFLOW;
  }
  if (fd < 0) {
    return io_fail(e, (u32)no, NULL);
  }
  u64  n    = (u64)st.st_size;
  bool held = false;
  Term body = n < small ? file_get_under_body(e, fd, n, &held)
    : term_pak(CID_SNIL, 0);
  Term file = term_pak(CID_NONE, 0);
  if (held) {
    close(fd);
  } else {
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) & ~O_NONBLOCK);
    file = io_box(e, CID_SOME, io_hand(fd));
  }
  (void)w;
  return io_done(e, io_tup(e, (u32)n, io_tup(e, (u32)st.st_mtime,
    io_tup(e, file, body))));
}

static void __attribute__((constructor)) file_get_under_use(void) {
  io_eff(CID_FILE_GET_UNDER, file_get_under_run, 0);
}

#endif
