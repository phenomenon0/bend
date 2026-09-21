// The C twin of the tensor benches: plain single-thread C at clang -O3 over
// one contiguous float block, the speed to be near. `twin gemv` is the decode
// skeleton -- 256 rounds of y <- A x then x <- 9y/64 -- and prints the same
// four lines (checksum, or, and, nonfin) that bench_gemv.bend and
// bench_split.bend print, which is what lets demos/tensor/bench.sh time them.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint32_t u32;

#define N 1024
#define REPS 256
#define CELLS (1u << 21)

static u32 h(u32 p) { return ((p + 1) * 2654435761u) ^ (p >> 3); }
static float v(u32 p) { return ((float)(u32)(h(p) >> 19) - 4096.0f) / 4096.0f; }
static u32 rot7(u32 x) { return (x << 7) | (x >> 25); }
static u32 mix(u32 a, u32 x) { return rot7(a * 31u + x); }
static u32 bits(float f) { u32 u; memcpy(&u, &f, 4); return u; }

// y <- A x: A is rows x cols with a row stride, x and y are contiguous runs,
// all three inside one block -- the same three descriptors the Bend side has.
static void gemv(float *t, u32 oa, u32 rows, u32 cols, u32 sa, u32 ox, u32 oy) {
  for (u32 r = 0; r < rows; r++) {
    float s = 0.0f;
    for (u32 c = 0; c < cols; c++) s += t[oa + r * sa + c] * t[ox + c];
    t[oy + r] = s;
  }
}

// the same product with four accumulators, lane c into s[c mod 4], summed as
// (s0+s1)+(s2+s3): a fixed order, so the Bend twin agrees bit for bit, but a
// four-deep chain rather than one, which is what lets clang widen it.
static void gemv4(float *t, u32 oa, u32 rows, u32 cols, u32 sa, u32 ox, u32 oy) {
  for (u32 r = 0; r < rows; r++) {
    float s0 = 0.0f, s1 = 0.0f, s2 = 0.0f, s3 = 0.0f;
    for (u32 c = 0; c < cols; c += 4) {
      s0 += t[oa + r * sa + c] * t[ox + c];
      s1 += t[oa + r * sa + c + 1] * t[ox + c + 1];
      s2 += t[oa + r * sa + c + 2] * t[ox + c + 2];
      s3 += t[oa + r * sa + c + 3] * t[ox + c + 3];
    }
    t[oy + r] = (s0 + s1) + (s2 + s3);
  }
}

static void scale(float *t, u32 op, u32 oq, u32 n) {
  for (u32 i = 0; i < n; i++) t[oq + i] = t[op + i] * 0.140625f;
}

// 0x80000000 when the exponent is all ones (an infinity or a NaN), 0 when the
// number is finite -- the Bend side's `nonfin`, bit for bit.
static u32 nonfin(u32 b) { return ((b & 0x7f800000u) + 0x00800000u) & 0x80000000u; }

static void run_gemv(int blocked) {
  float *t = calloc(CELLS, sizeof(float));
  for (u32 i = 0; i < N * N + N; i++) t[i] = v(i);
  for (u32 k = 0; k < REPS; k++) {
    if (blocked) gemv4(t, 0, N, N, N, N * N, N * N + N);
    else gemv(t, 0, N, N, N, N * N, N * N + N);
    scale(t, N * N + N, N * N, N);
  }
  u32 acc = 0, orb = 0, andb = 0xffffffffu, nf = 0;
  for (u32 i = 0; i < N; i++) {
    u32 b = bits(t[N * N + i]);
    acc = mix(acc, b); orb |= b; andb &= b; nf |= nonfin(b);
  }
  free(t);
  printf("%u\n%u\n%u\n%u\n", acc, orb, andb, nf);
}

int main(int argc, char **argv) {
  const char *which = argc > 1 ? argv[1] : "gemv";
  if (!strcmp(which, "gemv")) { run_gemv(0); return 0; }
  if (!strcmp(which, "blocked")) { run_gemv(1); return 0; }
  fprintf(stderr, "twin: no bench named %s\n", which);
  return 1;
}
