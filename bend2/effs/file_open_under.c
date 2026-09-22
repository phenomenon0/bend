// File
// ====

#include <sys/stat.h>

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
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
      no = S_ISDIR(st.st_mode) ? EISDIR : EACCES;
      close(fd);
      errno = no;
      return -1;
    }
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) & ~O_NONBLOCK);
    return fd;
  }
  return -1;
}

static void file_open_under_call(IoWork* w) {
  w->made = (intptr_t)io_sys_end(w, file_open_under_walk(w->text, w->data));
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
