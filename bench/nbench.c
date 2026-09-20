// The machine baseline for nbench.bend: the same 10,000,000 increments on
// a machine u64. The counter is volatile so clang -O3 must actually run
// the loop -- the Bend program has no volatile to write, which is exactly
// why its native number lands on the process floor once the operation is
// a single machine add and LLVM closes the counted loop.
#include <stdio.h>

#ifndef SIZE
#define SIZE 10000000
#endif

int main(void) {
  volatile unsigned long long acc = 0;
  for (unsigned long long i = 0; i < (unsigned long long)SIZE; i += 1) {
    acc = acc + 1;
  }
  printf("u64 native sum: %llu\nNB-END\n", acc);
  return 0;
}
