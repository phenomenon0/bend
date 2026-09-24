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

// The root's descriptor is kept, per thread, for up to a second: a root
// renamed or swapped (a deploy that repoints a link) is seen within it.
typedef struct {
  char* root;
  int   fd;
  u64   until;
} FileTop;

static __thread FileTop file_open_under_top = { NULL, -1, 0 };

static int file_open_under_dir(const char* root) {
  FileTop* t   = &file_open_under_top;
  u64      now = io_tick();
  if (t->fd >= 0 && now < t->until && strcmp(t->root, root) == 0) {
    return t->fd;
  }
  if (t->fd >= 0) {
    close(t->fd);
    free(t->root);
    t->fd = -1;
  }
  int dir = open(root, O_PATH | O_DIRECTORY | O_CLOEXEC);
  if (dir >= 0) {
    t->root  = io_mem(strdup(root));
    t->fd    = dir;
    t->until = now + 1000000000ull;
  }
  return dir;
}

static int file_open_under_two(const char* root, const char* at) {
  if (!file_open_under_shape(at)) {
    errno = EACCES;
    return -1;
  }
  int dir = file_open_under_dir(root);
  if (dir < 0) {
    return -1;
  }
  struct { u64 flags, mode, resolve; } how = {
    O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NOCTTY | O_NONBLOCK, 0,
    0x08 | 0x04 | 0x02 };  // RESOLVE_BENEATH, NO_SYMLINKS, NO_MAGICLINKS
  return (int)syscall(SYS_openat2, dir, at, &how, sizeof how);
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
  return io_work(w, file_open_under_call, file_open_under_pack);
}

static void __attribute__((constructor)) file_open_under_use(void) {
  io_eff(CID_FILE_OPEN_UNDER, file_open_under_run, 0);
}
