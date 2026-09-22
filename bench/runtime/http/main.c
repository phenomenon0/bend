// Native C twin of main.bend: same generator (one keep-alive GET per
// line index, the index folded into the target and into two header
// values), same mode machine (the ten head modes, one class and one
// arithmetic step per byte, one mix per completed token), same
// checksum (tokens folded in order per request, requests summed),
// single-threaded. Each head lives in one stack byte buffer, and the
// machine runs as a switch over it: the same work as main.bend's mode
// machine, one classification and one transition per byte.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef DEPTH
#define DEPTH 19
#endif

enum { K_SP, K_CR, K_LF, K_CO, K_CH };
enum { IN_M, IN_T, IN_V, CR_M, LIN, IN_N, OWS, IN_L, CR_L, DON, BAD };

static const uint32_t FNV = 2166136261u;

static uint32_t fnv(uint32_t h, uint32_t c) { return (h ^ c) * 16777619u; }
static uint32_t mix(uint32_t a, uint32_t k, uint32_t x) {
  return (a * 2654435761u) ^ (k * 40503u + x);
}
static int cls(uint8_t c) {
  return c == 32 ? K_SP : c == 13 ? K_CR : c == 10 ? K_LF
    : c == 58 ? K_CO : K_CH;
}

// the decimal of a 32-bit word, as U32.show writes it
static int dec(char* p, uint32_t n) {
  char t[10];
  int k = 0;
  do { t[k++] = (char)('0' + n % 10u); n /= 10u; } while (n);
  for (int j = 0; j < k; j++) p[j] = t[k - 1 - j];
  return k;
}

static int lit(char* p, const char* s) {
  size_t n = strlen(s);
  memcpy(p, s, n);
  return (int)n;
}

// one request head, byte for byte as main.bend's req builds it
static int req(char* p, uint32_t i) {
  char* q = p;
  q += lit(q, "GET /v1/items/");
  q += dec(q, i);
  q += lit(q, "?page=");
  q += dec(q, i % 97u);
  q += lit(q, " HTTP/1.1\r\nHost: bench.example\r\nUser-Agent: bend-http/1.0"
    "\r\nAccept: */*\r\nAccept-Encoding: identity\r\nX-Request-Id: ");
  q += dec(q, i * 2654435761u);
  q += lit(q, "\r\nContent-Length: 0\r\nConnection: keep-alive\r\n\r\n");
  return (int)(q - p);
}

// the machine: one step per byte, the mode and its open hash riding
static uint32_t parse(const char* p, int n) {
  int st = IN_M;
  uint32_t h = FNV, acc = 0;
  for (int i = 0; i < n; i++) {
    uint32_t c = (uint8_t)p[i];
    int k = cls((uint8_t)c);
    switch (st) {
      case IN_M:
        if (k == K_SP) { acc = mix(acc, 1, h); h = FNV; st = IN_T; }
        else h = fnv(h, c);
        break;
      case IN_T:
        if (k == K_SP) { acc = mix(acc, 2, h); st = IN_V; }
        else h = fnv(h, c);
        break;
      case IN_V:
        if (k == K_CR) st = CR_M;
        break;
      case CR_M:
        st = k == K_LF ? LIN : BAD;
        break;
      case LIN:
        if (k == K_CR) st = CR_L;
        else { h = fnv(FNV, c); st = IN_N; }
        break;
      case IN_N:
        if (k == K_CO) { acc = mix(acc, 3, h); st = OWS; }
        else h = fnv(h, c);
        break;
      case OWS:
        if (k == K_SP) break;
        if (k == K_CR) { st = CR_M; break; }
        h = fnv(FNV, c); st = IN_L;
        break;
      case IN_L:
        if (k == K_CR) { acc = mix(acc, 4, h); st = CR_M; }
        else h = fnv(h, c);
        break;
      case CR_L:
        st = k == K_LF ? DON : BAD;
        break;
      default:
        break;
    }
  }
  return st == DON ? acc : 0u;
}

int main(void) {
  char buf[512];
  uint32_t sum = 0;
  for (uint32_t i = 0; i < (1u << DEPTH); i++) sum += parse(buf, req(buf, i));
  printf("%u\n", sum);
}
