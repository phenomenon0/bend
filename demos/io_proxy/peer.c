// Peer.addr(sock): the dotted IPv4 address of the socket's peer, for
// X-Forwarded-For ("" when the kernel has none to give, or it is not
// IPv4). One getpeername on the descriptor; over TLS the descriptor is
// the socket under the session, as for every byte effect.
#include <arpa/inet.h>
#include <sys/socket.h>

Term peer_addr_run(Env e, Term* f, IoWork* w) {
  int                fd  = (int)io_hand_v(f[0]);
  struct sockaddr_in sa;
  socklen_t          len = sizeof(sa);
  char               out[INET_ADDRSTRLEN] = { 0 };
  if (getpeername(fd, (struct sockaddr*)&sa, &len) == 0 && sa.sin_family == AF_INET) {
    inet_ntop(AF_INET, &sa.sin_addr, out, sizeof(out));
  }
  return io_tup(e, io_hand(fd), io_str(e, out, strlen(out)));
}

static void __attribute__((constructor)) peer_addr_use(void) {
  io_eff(CID_PEER_ADDR, peer_addr_run, 0);
}
