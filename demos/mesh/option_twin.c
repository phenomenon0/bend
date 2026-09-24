// option.bend in C, twice: the same operations in the same order (the twin),
// and what a practitioner writes first (libm exp/log, a double sum).
//
//   cc -O2 -ffp-contract=off -o option_twin option_twin.c -lm -lpthread
//   ./option_twin twin N [THREADS [SEED]]    same bits as option.bend
//   ./option_twin libm N [THREADS [SEED]]    libm + double sums, per-thread
//                                            partials joined in thread order
//
// -ffp-contract=off matters: with a*b+c fused into one FMA (GCC's default
// outside ISO mode, and clang's on ARM), the twin rounds differently from
// option.bend and CPython and the bits drift.
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static const double S0 = 100.0, K = 105.0, R = 0.05, SIG = 0.2, T = 1.0;
static const double LN2_HI = 6.93147180369123816490e-01;
static const double LN2_LO = 1.90821492927058770002e-10;
static const double INV_LN2 = 1.44269504088896338700e+00;
static const double SQRT2 = 1.4142135623730951;
static const double TWO32 = 4294967296.0;

static uint32_t rotl(uint32_t x, int r) { return (x << r) | (x >> (32 - r)); }

// Threefry-2x32-20, as power/rng.bend's block
static void block(uint32_t k0, uint32_t k1, uint32_t c0, uint32_t c1, uint32_t *oa, uint32_t *ob) {
  static const int ROT[8] = {13, 15, 26, 6, 17, 29, 16, 24};
  uint32_t ks[3] = {k0, k1, k0 ^ k1 ^ 0x1BD11BDAu};
  uint32_t a = c0 + ks[0], b = c1 + ks[1];
  for (int r = 0; r < 20; r++) {
    a += b;
    b = rotl(b, ROT[r % 8]) ^ a;
    if (r % 4 == 3) {
      int n = r / 4 + 1;
      a += ks[n % 3];
      b += ks[(n + 1) % 3] + (uint32_t)n;
    }
  }
  *oa = a, *ob = b;
}

static double inv_fact[14];

static double exp_(double x) {
  double k = floor(x * INV_LN2 + 0.5);
  double r = (x - k * LN2_HI) - k * LN2_LO;
  double p = inv_fact[13];
  for (int n = 12; n >= 0; n--) p = p * r + inv_fact[n];
  double s = k > 0 ? 2.0 : 0.5;
  for (int i = 0, m = (int)fabs(k); i < m; i++) p = p * s;
  return p;
}

static double log_(double y) {
  double e = 0.0;
  for (int i = 0; i < 80; i++)
    if (y < 1.0) y = y * 2.0, e = e - 1.0;
  if (y > SQRT2) y = y * 0.5, e = e + 1.0;
  double t = (y - 1.0) / (y + 1.0), t2 = t * t, q = 1.0 / 25.0;
  for (int k = 11; k >= 0; k--) q = q * t2 + 1.0 / (double)(2 * k + 1);
  return e * LN2_HI + (e * LN2_LO + 2.0 * t * q);
}

static double unit(uint32_t w) { return 2.0 * (((double)w + 0.5) / TWO32) - 1.0; }

static int use_libm;

static double normal(uint32_t seed, uint32_t i) {
  for (uint32_t j = 0; j < 16; j++) {
    uint32_t a, b;
    block(seed, i, j, 0, &a, &b);
    double u = unit(a), v = unit(b), s = u * u + v * v;
    if (s > 0.0 && s < 1.0) return u * sqrt((-2.0 * (use_libm ? log(s) : log_(s))) / s);
  }
  return 0.0;
}

static double payoff(uint32_t seed, uint32_t i) {
  double mu = (R - 0.5 * SIG * SIG) * T, sd = SIG * sqrt(T);
  double x = mu + sd * normal(seed, i);
  double st = S0 * (use_libm ? exp(x) : exp_(x));
  return st > K ? st - K : 0.0;
}

typedef unsigned __int128 u128;
typedef struct { uint32_t seed, lo, n; u128 s1, s2; double d1, d2; pthread_t th; } Part;

static void *run(void *v) {
  Part *p = v;
  for (uint32_t i = p->lo; i < p->lo + p->n; i++) {
    double x = payoff(p->seed, i);
    if (use_libm) p->d1 += x, p->d2 += x * x;
    else p->s1 += (u128)floor(x * TWO32), p->s2 += (u128)floor(x * x * 65536.0);
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) return fprintf(stderr, "usage: %s twin|libm N [THREADS [SEED]]\n", argv[0]), 2;
  use_libm = !strcmp(argv[1], "libm");
  uint32_t n = (uint32_t)strtoul(argv[2], 0, 10);
  int th = argc > 3 ? atoi(argv[3]) : 1;
  uint32_t seed = argc > 4 ? (uint32_t)strtoul(argv[4], 0, 10) : 1;
  double f = 1.0;
  inv_fact[0] = 1.0;
  for (int i = 1; i <= 13; i++) f = f * (double)(i < 2 ? 1 : i), inv_fact[i] = 1.0 / f;
  Part *ps = calloc(th, sizeof *ps);
  struct timespec a, b;
  clock_gettime(CLOCK_MONOTONIC, &a);
  for (int t = 0; t < th; t++) {
    uint32_t lo = (uint32_t)((uint64_t)n * t / th), hi = (uint32_t)((uint64_t)n * (t + 1) / th);
    ps[t] = (Part){seed, lo, hi - lo};
    pthread_create(&ps[t].th, 0, run, &ps[t]);
  }
  u128 s1 = 0, s2 = 0;
  double d1 = 0, d2 = 0;
  for (int t = 0; t < th; t++) {
    pthread_join(ps[t].th, 0);
    s1 += ps[t].s1, s2 += ps[t].s2, d1 += ps[t].d1, d2 += ps[t].d2;
  }
  clock_gettime(CLOCK_MONOTONIC, &b);
  double secs = (b.tv_sec - a.tv_sec) + (b.tv_nsec - a.tv_nsec) * 1e-9;
  double disc = exp(-R * T), mean, var;
  if (use_libm) {
    mean = d1 / n, var = d2 / n - mean * mean;
    printf("option paths=%u libm price=%.17g se=%.17g (%a)\n", n, disc * mean,
           disc * sqrt(fmax(var, 0.0) / n), disc * mean);
  } else {
    mean = (double)s1 / TWO32 / n, var = (double)s2 / 65536.0 / n - mean * mean;
    printf("option paths=%u acc=", n);
    for (int j = 0; j < 3; j++) printf("%08x ", (uint32_t)(s1 >> (32 * j)));
    for (int j = 0; j < 3; j++) printf("%08x%s", (uint32_t)(s2 >> (32 * j)), j < 2 ? " " : "");
    printf(" price=%.6f se=%.6f\n", disc * mean, disc * sqrt(fmax(var, 0.0) / n));
  }
  fprintf(stderr, "%.3f s, %.0f paths/s, %d threads\n", secs, n / secs, th);
  return 0;
}
