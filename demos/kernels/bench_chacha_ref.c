#include <stdio.h>
#include <stdint.h>
#include <string.h>

/* ref-style C ChaCha20: 16 MB of keystream (counter 0..262143), word-summed.
   Same key/nonce/counter convention as the Bend bench. */

static uint32_t rotl32(uint32_t x, int n){ return (x << n) | (x >> (32 - n)); }

#define QR(a,b,c,d) do { a += b; d ^= a; d = rotl32(d,16); \
                         c += d; b ^= c; b = rotl32(b,12); \
                         a += b; d ^= a; d = rotl32(d, 8); \
                         c += d; b ^= c; b = rotl32(b, 7); } while (0)

static void block(uint32_t out[16], const uint32_t in[16]){
    uint32_t x[16];
    memcpy(x, in, 64);
    for (int i = 0; i < 10; i++){
        QR(x[0],x[4],x[ 8],x[12]); QR(x[1],x[5],x[ 9],x[13]);
        QR(x[2],x[6],x[10],x[14]); QR(x[3],x[7],x[11],x[15]);
        QR(x[0],x[5],x[10],x[15]); QR(x[1],x[6],x[11],x[12]);
        QR(x[2],x[7],x[ 8],x[13]); QR(x[3],x[4],x[ 9],x[14]);
    }
    for (int i = 0; i < 16; i++) out[i] = x[i] + in[i];
}

int main(void){
    uint32_t st[16] = {
        0x61707865u,0x3320646eu,0x79622d32u,0x6b206574u,
        50462976u,117835012u,185207048u,252579084u,
        319951120u,387323156u,454695192u,522067228u,
        0u,0u,1241513984u,0u };
    uint32_t sum = 0;   /* byte-unit sum, wrapped at 32 bits: bend's convention */
    uint32_t out[16];
    for (uint32_t ctr = 0; ctr < 262144u; ctr++){
        st[12] = ctr;
        block(out, st);
        for (int i = 0; i < 16; i++){
            uint32_t w = out[i];
            sum += (w & 255u) + ((w >> 8) & 255u) + ((w >> 16) & 255u) + (w >> 24);
        }
    }
    printf("chacha16m sum=%u\n", (unsigned)sum);
    return 0;
}
