// The C twin of main.bend: the same rows, the same F32 order, the same
// four-way join tree, so it prints the same four lines. PLACE_COLS sets m.
// The rows run on 16 threads into an array; the tree joins them serially.
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t u32;
typedef struct { u32 acc, orb, andb, nf; } S;

static u32 h(u32 p) { return ((p + 1) * 2654435761u) ^ (p >> 3); }
static float v(u32 p) { return ((float)(h(p) >> 19) - 4096.0f) / 4096.0f; }
static u32 nonfin(u32 b) { return ((b & 2139095040u) + 8388608u) & 2147483648u; }
static u32 mix(u32 a, u32 x) { u32 t = a * 31 + x; return (t << 7) | (t >> 25); }

static S join(S a, S b) {
  return (S){ mix(a.acc, b.acc), a.orb | b.orb, a.andb & b.andb, a.nf | b.nf };
}

static u32 m, y[16384];

static void* rows(void* t) {
  for (u32 i = (u32)(uintptr_t)t; i < 16384; i += 16) {
    float s = 0.0f;
    u32 p = i * m;
    for (u32 j = 0; j < m; j++, p++) s = s + v(p) * v(j ^ 2654435769u);
    memcpy(&y[i], &s, 4);
  }
  return NULL;
}

static S node(int k, u32 i) {
  if (k == 0) return (S){ y[i], y[i], y[i], nonfin(y[i]) };
  S a = node(k - 1, i * 4), b = node(k - 1, i * 4 + 1);
  S c = node(k - 1, i * 4 + 2), d = node(k - 1, i * 4 + 3);
  return join(join(a, b), join(c, d));
}

int main(void) {
  const char* e = getenv("PLACE_COLS");
  m = e ? (u32)strtoul(e, NULL, 10) : 1024;
  pthread_t th[16];
  for (uintptr_t t = 0; t < 16; t++) pthread_create(&th[t], NULL, rows, (void*)t);
  for (int t = 0; t < 16; t++) pthread_join(th[t], NULL);
  S s = node(7, 0);
  printf("%u\n%u\n%u\n%u\n", s.acc, s.orb, s.andb, s.nf);
}
