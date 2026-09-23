// The sequential twin of pcg_big.bend: pcg-c-basic's pcg32_srandom_r and
// pcg32_random_r verbatim, one loop over 2^31 draws, no jumps, no threads.
// cc -O2 pcg_twin.c -o pcg_twin && ./pcg_twin   ->   hits 843353130
#include <stdint.h>
#include <stdio.h>

typedef struct { uint64_t state, inc; } pcg32_random_t;

static uint32_t pcg32_random_r(pcg32_random_t* rng) {
  uint64_t oldstate = rng->state;
  rng->state = oldstate * 6364136223846793005ULL + (rng->inc | 1);
  uint32_t xorshifted = ((oldstate >> 18u) ^ oldstate) >> 27u;
  uint32_t rot = oldstate >> 59u;
  return (xorshifted >> rot) | (xorshifted << ((-rot) & 31));
}

static void pcg32_srandom_r(pcg32_random_t* rng, uint64_t initstate, uint64_t initseq) {
  rng->state = 0U;
  rng->inc = (initseq << 1u) | 1u;
  pcg32_random_r(rng);
  rng->state += initstate;
  pcg32_random_r(rng);
}

int main(void) {
  pcg32_random_t r;
  pcg32_srandom_r(&r, 42u, 54u);
  uint64_t hits = 0;
  for (uint64_t i = 0; i < (1ull << 30); i++) {
    uint32_t x = pcg32_random_r(&r) >> 17, y = pcg32_random_r(&r) >> 17;
    hits += x * x + y * y < (1u << 30);
  }
  printf("hits %llu\n", (unsigned long long)hits);
}
