// Peer.addr(sock): the address of the socket's peer, for X-Forwarded-For
// and a request's remote: dotted for IPv4, and for IPv6 inet_ntop's text
// (RFC 5952's: "::1"); an IPv4 peer of a dual-stack listener
// (::ffff:a.b.c.d) is its dotted IPv4 address. "" when the kernel has none
// to give. One getpeername on the descriptor; over TLS the descriptor is
// the socket under the session, as for every byte effect.
#include <arpa/inet.h>
#include <sys/socket.h>

Term peer_addr_run(Env e, Term* f, IoWork* w) {
  int                     fd  = (int)io_hand_v(f[0]);
  struct sockaddr_storage sa;
  socklen_t               len = sizeof(sa);
  char                    out[INET6_ADDRSTRLEN] = { 0 };
  if (getpeername(fd, (struct sockaddr*)&sa, &len) == 0) {
    if (sa.ss_family == AF_INET) {
      inet_ntop(AF_INET, &((struct sockaddr_in*)&sa)->sin_addr, out, sizeof(out));
    } else if (sa.ss_family == AF_INET6) {
      struct in6_addr* a = &((struct sockaddr_in6*)&sa)->sin6_addr;
      if (IN6_IS_ADDR_V4MAPPED(a)) {
        inet_ntop(AF_INET, a->s6_addr + 12, out, sizeof(out));
      } else {
        inet_ntop(AF_INET6, a, out, sizeof(out));
      }
    }
  }
  return io_tup(e, io_hand(fd), io_str(e, out, strlen(out)));
}

static void __attribute__((constructor)) peer_addr_use(void) {
  io_eff(CID_PEER_ADDR, peer_addr_run, 0);
}
