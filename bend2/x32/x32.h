// x32: (f32)fn((double)x) for fn = exp, sin, cos, pow, without fp64.
// Metal has no double; these return what a correctly rounded double fn,
// then rounded to f32, returns. They work in u64 fixed point (about 2^-60
// relative), so they agree with a host libm except where the host itself
// is off by more; tools/x32/check_* compares every f32 input.
// Compiles as C (host checks) and as MSL.

#ifdef __METAL_VERSION__
typedef ulong x32_u64;
typedef long  x32_i64;
typedef uint  x32_u32;
#define X32_FN  static inline
#define X32_TBL constant
#define x32_hi(a, b)  mulhi((x32_u64)(a), (x32_u64)(b))
#define x32_his(a, b) mulhi((x32_i64)(a), (x32_i64)(b))
#define x32_clz(a)    ((int)clz((x32_u64)(a)))
#define x32_bits(f)   as_type<x32_u32>(f)
#define x32_float(u)  as_type<float>((x32_u32)(u))
#else
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t x32_u64;
typedef int64_t  x32_i64;
typedef uint32_t x32_u32;
#define X32_FN  static inline
#define X32_TBL static const
#define x32_hi(a, b)  ((x32_u64)(((unsigned __int128)(x32_u64)(a) * (x32_u64)(b)) >> 64))
#define x32_his(a, b) ((x32_i64)(((__int128)(x32_i64)(a) * (x32_i64)(b)) >> 64))
#define x32_clz(a)    ((a) ? __builtin_clzll(a) : 64)
static inline x32_u32 x32_bits(float f) { x32_u32 u; memcpy(&u, &f, 4); return u; }
static inline float x32_float(x32_u32 u) { float f; memcpy(&f, &u, 4); return f; }
#endif

#define X32_LN2_64_HI 0x0002c5c85fdf473dull
#define X32_LN2_64_LO 0xe6af278ece600fccull
#define X32_LN2_HI 0x00b17217f7d1cf79ull
#define X32_LN2_LO 0xabc9e3b39803f2f7ull
#define X32_PIO2_Q63 0xc90fdaa22168c235ull
#define X32_THIRD_Q64 0x5555555555555555ull
#define X32_FIFTH_Q64 0x3333333333333333ull
#define X32_SEVENTH_Q64 0x2492492492492492ull
X32_TBL x32_u64 x32_exp2j[64] = {
  0x8000000000000000ull,
  0x8164d1f3bc030773ull,
  0x82cd8698ac2ba1d7ull,
  0x843a28c3acde4046ull,
  0x85aac367cc487b15ull,
  0x871f61969e8d1010ull,
  0x88980e8092da8527ull,
  0x8a14d575496efd9aull,
  0x8b95c1e3ea8bd6e7ull,
  0x8d1adf5b7e5ba9e6ull,
  0x8ea4398b45cd53c0ull,
  0x9031dc431466b1dcull,
  0x91c3d373ab11c336ull,
  0x935a2b2f13e6e92cull,
  0x94f4efa8fef70961ull,
  0x96942d3720185a00ull,
  0x9837f0518db8a96full,
  0x99e0459320b7fa65ull,
  0x9b8d39b9d54e5539ull,
  0x9d3ed9a72cffb751ull,
  0x9ef5326091a111aeull,
  0xa0b0510fb9714fc2ull,
  0xa27043030c496819ull,
  0xa43515ae09e6809eull,
  0xa5fed6a9b15138eaull,
  0xa7cd93b4e965356aull,
  0xa9a15ab4ea7c0ef8ull,
  0xab7a39b5a93ed337ull,
  0xad583eea42a14ac6ull,
  0xaf3b78ad690a4375ull,
  0xb123f581d2ac2590ull,
  0xb311c412a9112489ull,
  0xb504f333f9de6484ull,
  0xb6fd91e328d17791ull,
  0xb8fbaf4762fb9ee9ull,
  0xbaff5ab2133e45fbull,
  0xbd08a39f580c36bfull,
  0xbf1799b67a731083ull,
  0xc12c4cca66709456ull,
  0xc346ccda24976407ull,
  0xc5672a115506daddull,
  0xc78d74c8abb9b15dull,
  0xc9b9bd866e2f27a3ull,
  0xcbec14fef2727c5dull,
  0xce248c151f8480e4ull,
  0xd06333daef2b2595ull,
  0xd2a81d91f12ae45aull,
  0xd4f35aabcfedfa1full,
  0xd744fccad69d6af4ull,
  0xd99d15c278afd7b6ull,
  0xdbfbb797daf23755ull,
  0xde60f4825e0e9124ull,
  0xe0ccdeec2a94e111ull,
  0xe33f8972be8a5a51ull,
  0xe5b906e77c8348a8ull,
  0xe8396a503c4bdc68ull,
  0xeac0c6e7dd24392full,
  0xed4f301ed9942b84ull,
  0xefe4b99bdcdaf5cbull,
  0xf281773c59ffb13aull,
  0xf5257d152486cc2cull,
  0xf7d0df730ad13bb9ull,
  0xfa83b2db722a033aull,
  0xfd3e0c0cf486c175ull};
X32_TBL x32_i64 x32_expc[7] = {0, 0, (x32_i64)0x4000000000000000ull, (x32_i64)0x1555555555555555ull, (x32_i64)0x0555555555555555ull, (x32_i64)0x0111111111111111ull, (x32_i64)0x002d82d82d82d82eull};
X32_TBL x32_i64 x32_sinc[10] = {
  (x32_i64)0x1555555555555555ull,
  (x32_i64)0xfeeeeeeeeeeeeeefull,
  (x32_i64)0x0006806806806807ull,
  (x32_i64)0xffffe8e21c5aa939ull,
  (x32_i64)0x00000035cc8acfebull,
  (x32_i64)0xffffffffa7b6e7b1ull,
  (x32_i64)0x00000000006b9fd0ull,
  (x32_i64)0xffffffffffff9ab5ull,
  (x32_i64)0x000000000000004cull,
  (x32_i64)0x0000000000000000ull};
X32_TBL x32_i64 x32_cosc[10] = {
  (x32_i64)0x4000000000000000ull,
  (x32_i64)0xfaaaaaaaaaaaaaabull,
  (x32_i64)0x002d82d82d82d82eull,
  (x32_i64)0xffff2ff2ff2ff2ffull,
  (x32_i64)0x0000024fc9f6ef14ull,
  (x32_i64)0xfffffffb8449c402ull,
  (x32_i64)0x00000000064e5d2aull,
  (x32_i64)0xfffffffffff94603ull,
  (x32_i64)0x00000000000005a1ull,
  (x32_i64)0xfffffffffffffffcull};
X32_TBL x32_u64 x32_lnc[65][2] = {
  {0x0000000000000000ull, 0x0000000000000000ull},
  {0x0003f815161f807cull, 0x79f3db4e9a6f57abull},
  {0x0007e0a6c39e0cc0ull, 0x133e3f04f1ef22a0ull},
  {0x000bba2c7b196e7eull, 0x231a7950f7252c16ull},
  {0x000f85186008b153ull, 0x30be64b8b7759979ull},
  {0x001341d7961bd1d0ull, 0x92998376104d1375ull},
  {0x0016f0d28ae56b4bull, 0x9be499b9ed19b641ull},
  {0x001a926d3a4ad563ull, 0x650bd22a9c3aa4c8ull},
  {0x001e27076e2af2e5ull, 0xe9ea87ffe1fe9e15ull},
  {0x0021aefcf9a11cb2ull, 0xcd2ee2f481855d1cull},
  {0x00252aa5f03fea46ull, 0x980bb8e203edf4d1ull},
  {0x00289a56d996fa3cull, 0xcfa7b2a1f0fc3c19ull},
  {0x002bfe60e14f27a7ull, 0x90e7c4140e424776ull},
  {0x002f57120421b212ull, 0x37c6d65ad40c100dull},
  {0x0032a4b539e8ad68ull, 0xec8260ea71712cecull},
  {0x0035e7929d017fe5ull, 0xb19cc0326f99eb97ull},
  {0x00391fef8f353443ull, 0x584bb03de5ff7345ull},
  {0x003c4e0edc55e5cbull, 0xd3d50fffc3fd3c2bull},
  {0x003f7230dabc7c55ull, 0x1aaa8cd86f29a594ull},
  {0x00428c9389ce438dull, 0x7dcfde8061c030e3ull},
  {0x00459d72aeae9838ull, 0x0e731f55c41b8b82ull},
  {0x0048a507ef3de596ull, 0x890a14f69d750cbdull},
  {0x004ba38aeb8474c2ull, 0x70b3246a14206cf3ull},
  {0x004e993155a517a7ull, 0x1cbcd735d034237dull},
  {0x0051862f08717b09ull, 0xf42decdeccf1cd10ull},
  {0x00546ab61cb7e0b4ull, 0x2724f5833eabc624ull},
  {0x005746f6fd602729ull, 0x4236383dc7fe115aull},
  {0x005a1b207a6c52bbull, 0x110af840538e1a59ull},
  {0x005ce75fdaef401aull, 0x7389314feb4fbde6ull},
  {0x005fabe0ee0abf0dull, 0x92ce979ed2950437ull},
  {0x006268ce1b05096aull, 0xd69c620440f055b4ull},
  {0x00651e5070845beaull, 0xe9337451f441babbull},
  {0x0067cc8fb2fe612full, 0xcada35d9bd014886ull},
  {0x006a73b26a682126ull, 0x35213fd4bc950d7cull},
  {0x006d13ddef323d8aull, 0x32fbb6aba63878efull},
  {0x006fad36769c6defull, 0xde1874deaef06b26ull},
  {0x00723fdf1e6a6886ull, 0xb097607bcbfee689ull},
  {0x0074cbf9f803af55ull, 0x877b232fafa36fd2ull},
  {0x007751a813071282ull, 0xfb989a927476e1ffull},
  {0x0079d109875a1e1full, 0x8df68dbcf2ed1bb4ull},
  {0x007c4a3d7ebc1bb2ull, 0xcd720ec44c73d75dull},
  {0x007ebd623de3cc7bull, 0x66becf93aa1afec7ull},
  {0x00812a952d2e87f6ull, 0x34e34aebf73ffe34ull},
  {0x008391f2e0e6fa02ull, 0x72bcb1c488b755b3ull},
  {0x0085f39721295415ull, 0xb4c4bdd99effe69bull},
  {0x00884f9cf16a64b7ull, 0xef1f64d85bc8c5f2ull},
  {0x008aa61e97a6af4dull, 0x4c799d1cb2f14055ull},
  {0x008cf735a33e4b76ull, 0x62e5eebbc0ef3d57ull},
  {0x008f42faf3820681ull, 0xef62cd2f9f1e35f3ull},
  {0x00918986bdf5fa14ull, 0x16f1b439165240a4ull},
  {0x0093caf0944d88d7ull, 0x5bc1f9edcb438ffcull},
  {0x0096074f6a24745dull, 0xcbd4e18dd14f312aull},
  {0x00983eb99a7885f0ull, 0xfdac850fab36cdeeull},
  {0x009a7144ece70e98ull, 0xb75c96c42e727572ull},
  {0x009c9f069ab150cdull, 0x4e221301b6f8c38full},
  {0x009ec813538ab7d5ull, 0x202131e85693cf6cull},
  {0x00a0ec7f42339573ull, 0x2325e617a300bbcbull},
  {0x00a30c5e10e2f613ull, 0xe85bd9bd99e39a21ull},
  {0x00a527c2ed81f5d8ull, 0x113dfa3d3761b631ull},
  {0x00a73ec08dbadd84ull, 0xe584c2b22c2aee1aull},
  {0x00a9516932de2d57ull, 0x73be4578ad97aea8ull},
  {0x00ab5fcead9f9ccaull, 0x08e310b9b1fe59ceull},
  {0x00ad6a0261acf967ull, 0xd94d552f811cd408ull},
  {0x00af70154920b3abull, 0x86b04afe92103ef5ull},
  {0x00b17217f7d1cf79ull, 0xabc9e3b39803f2f7ull}};
X32_TBL x32_u32 x32_2opi[12] = {
  0x00000000u,
  0x00000000u,
  0xa2f9836eu,
  0x4e441529u,
  0xfc2757d1u,
  0xf534ddc0u,
  0xdb629599u,
  0x3c439041u,
  0xfe5163abu,
  0xdebbc561u,
  0xb7246e3au,
  0x424dd2e0u};

// Q63 multiply of signed fractions
#define x32_mul63(a, b) ((x32_i64)((x32_u64)x32_his(a, b) << 1))

// Round M/2^63 * 2^E (M's top bit set) as the host does: to a double
// (53 bits), then that double to f32, ties to even. Exact results (pow's
// x^2) and the double's own ties then land where the host's do.
X32_FN float x32_round(x32_u64 M, int E, x32_u32 sgn) {
  x32_u64 D = (M >> 11) + ((M >> 10) & 1);               // D/2^52 * 2^E
  if (D >> 53) { D >>= 1; E++; }
  int eb = E + 127, sh = eb >= 1 ? 29 : 30 - eb;
  x32_u32 b = 0;
  if (eb >= 255) {
    b = 0x7f800000u;
  } else if (sh < 64) {
    x32_u64 q = D >> sh, rem = D & ((1ull << sh) - 1), hf = 1ull << (sh - 1);
    q += rem > hf || (rem == hf && (q & 1));
    b = (eb >= 1 ? (x32_u32)(eb - 1) << 23 : 0) + (x32_u32)q;
  }
  return x32_float(b | sgn);
}

// e^t for t = +-(hi:lo)/2^120, |t| < 2^7.
X32_FN float x32_exp_core(int neg, x32_u64 hi, x32_u64 lo) {
  int kk = (int)rint((float)hi * 0x1p-56f * 92.332482616893656f);
  // r = |t| - kk ln2/64, 128-bit, then Q63
  x32_u64 blo = (x32_u64)kk * X32_LN2_64_LO;
  x32_u64 bhi = (x32_u64)kk * X32_LN2_64_HI + x32_hi(kk, X32_LN2_64_LO);
  x32_u64 dlo = lo - blo;
  x32_u64 dhi = hi - bhi - (lo < blo);
  x32_i64 r = (x32_i64)((dhi << 7) | (dlo >> 57));
  int k = kk;
  if (neg) { r = -r; k = -k; }
  x32_i64 q = x32_expc[6];
  for (int n = 5; n >= 2; n--) q = x32_expc[n] + x32_mul63(q, r);
  x32_i64 p = r + x32_mul63(x32_mul63(r, r), q);  // e^r - 1, Q63
  x32_u64 T = x32_exp2j[k & 63];
  x32_u64 d = x32_hi(T, p < 0 ? -p : p);
  x32_u64 V = p < 0 ? (T >> 1) - d : (T >> 1) + d;  // Q62
  int z = x32_clz(V);
  return x32_round(V << z, (k >> 6) + 1 - z, 0);
}

X32_FN float x32_exp(float x) {
  x32_u32 u = x32_bits(x), a = u & 0x7fffffffu;
  if (a >= 0x7f800000u) return a > 0x7f800000u ? x + x : (u >> 31) ? 0.0f : x;
  if (a < 0x32800000u) return 1.0f;                      // |x| < 2^-26
  if (a >= 0x42d00000u) return x32_float((u >> 31) ? 0 : 0x7f800000u);  // 104
  x32_u64 m = (a & 0x7fffffu) | 0x800000u;
  return x32_exp_core(u >> 31, m << ((a >> 23) - 94), 0);
}

// sin (want_cos = 0) or cos (1)
X32_FN float x32_sincos(float x, int want_cos) {
  x32_u32 u = x32_bits(x), a = u & 0x7fffffffu;
  if (a >= 0x7f800000u) return a > 0x7f800000u ? x + x : x32_float(0x7fc00000u);
  if (a < 0x39800000u) return want_cos ? 1.0f : x;       // |x| < 2^-12
  x32_u64 m = (a & 0x7fffffu) | 0x800000u;
  int s = (int)(a >> 23) - 150;
  x32_u64 R;
  int er;
  x32_u32 N = 0, rneg = 0;
  if (a <= 0x3f490fdau) {                                // |x| < pi/4
    R = m << 40;
    er = s + 24;
  } else {
    // Payne-Hanek: 4m * (192 bits of 2/pi from bit s-1) / 2^192 mod 4
    int p0 = s + 62, w = p0 >> 5, o = p0 & 31;
    x32_u32 W[6], out[6];
    for (int i = 0; i < 6; i++)
      W[i] = o ? (x32_2opi[w + i] << o) | (x32_2opi[w + i + 1] >> (32 - o))
               : x32_2opi[w + i];
    x32_u64 acc = 0, m4 = m << 2;
    for (int i = 5; i >= 0; i--) {
      acc = (acc >> 32) + m4 * W[i];
      out[i] = (x32_u32)acc;
    }
    N = (x32_u32)(acc >> 32) & 3;
    x32_u64 fh = ((x32_u64)out[0] << 32) | out[1];
    x32_u64 fl = ((x32_u64)out[2] << 32) | out[3];
    if (fh >> 63) {                                      // f -= 1
      N++;
      rneg = 1;
      fh = ~fh + (fl == 0);
      fl = -fl;
    }
    int z = fh ? x32_clz(fh) : 64 + x32_clz(fl);
    x32_u64 F = z == 0 ? fh : z < 64 ? (fh << z) | (fl >> (64 - z))
      : z < 128 ? fl << (z - 64) : 0;
    x32_u64 Rp = x32_hi(F, X32_PIO2_Q63);                // r = Rp/2^63 * 2^-z
    int z2 = x32_clz(Rp);
    R = Rp << z2;
    er = 1 - z2 - z;
  }
  // r = R/2^64 * 2^er, |r| <= pi/4; z = r^2 in Q63
  int zs = 1 - 2 * er;
  x32_i64 zz = zs < 64 ? (x32_i64)(x32_hi(R, R) >> zs) : 0;
  int use_cos = (N + want_cos) & 1;
  x32_u32 neg = (((N + want_cos) >> 1) ^ (!use_cos && rneg)
    ^ (!want_cos && (u >> 31))) & 1;
  x32_u64 M;
  int E;
  if (use_cos) {                                         // 1 - z C(z)
    x32_i64 c = x32_cosc[9];
    for (int k = 8; k >= 0; k--) c = x32_cosc[k] + x32_mul63(c, zz);
    x32_u64 cq = (1ull << 62) - (x32_u64)x32_his(zz, c);
    int l = x32_clz(cq);
    M = cq << l;
    E = 1 - l;
  } else {                                               // r (1 - z A(z))
    x32_i64 c = x32_sinc[9];
    for (int k = 8; k >= 0; k--) c = x32_sinc[k] + x32_mul63(c, zz);
    x32_u64 sm = R - (x32_hi(R, (x32_u64)x32_mul63(zz, c)) << 1);
    int l = x32_clz(sm);
    M = sm << l;
    E = er - 1 - l;
  }
  return x32_round(M, E, neg << 31);
}

X32_FN float x32_sin(float x) { return x32_sincos(x, 0); }
X32_FN float x32_cos(float x) { return x32_sincos(x, 1); }

// 0: not an integer, 1: odd integer, 2: even integer (y finite)
X32_FN int x32_yint(x32_u32 a) {
  int e = (int)(a >> 23) - 150;
  if (a == 0) return 2;
  if (e >= 1) return 2;
  if (e < -23) return 0;
  x32_u32 m = (a & 0x7fffffu) | 0x800000u;
  if (m & ((1u << -e) - 1)) return 0;
  return ((m >> -e) & 1) ? 1 : 2;
}

// ln x for finite x > 0, as a signed 128-bit Q120 in (*hi, *lo)
X32_FN void x32_ln(x32_u32 a, x32_u64* hi, x32_u64* lo) {
  int s;
  x32_u64 m;
  if (a >= 0x800000u) {
    m = (a & 0x7fffffu) | 0x800000u;
    s = (int)(a >> 23) - 150;
  } else {                                               // subnormal
    int z = x32_clz((x32_u64)a) - 40;
    m = (x32_u64)a << z;
    s = -149 - z;
  }
  // x = 2^(s+23) * c * (1+w)/(1-w), c = 1 + j/64, |w| < 2^-8
  int j = (int)((m + (1u << 16)) >> 17) - 64;
  x32_u64 cm = (x32_u64)(64 + j) << 17, den = m + cm;
  int wneg = m < cm;
  x32_u64 num = wneg ? cm - m : m - cm;
  x32_u64 q1 = (num << 39) / den, r1 = (num << 39) % den;
  x32_u64 W = (q1 << 32) | ((r1 << 32) / den);           // |w|, Q71
  x32_u64 w2 = x32_hi(W, W) >> 14;                       // Q64
  x32_u64 S = X32_THIRD_Q64 + x32_hi(w2, X32_FIFTH_Q64 + x32_hi(w2, X32_SEVENTH_Q64));
  x32_u64 at = W + x32_hi(W, x32_hi(w2, S));            // atanh|w|, Q71
  // 2 atanh w in Q120: at << 50
  x32_u64 ahi = at >> 14, alo = at << 50;
  if (wneg) { ahi = ~ahi + (alo == 0); alo = -alo; }
  // (s+23) ln2
  int n = s + 23;
  x32_u64 un = (x32_u64)(n < 0 ? -n : n);
  x32_u64 nlo = un * X32_LN2_LO;
  x32_u64 nhi = un * X32_LN2_HI + x32_hi(un, X32_LN2_LO);
  if (n < 0) { nhi = ~nhi + (nlo == 0); nlo = -nlo; }
  x32_u64 l = nlo + x32_lnc[j][1];
  x32_u64 h = nhi + x32_lnc[j][0] + (l < nlo);
  x32_u64 l2 = l + alo;
  *hi = h + ahi + (l2 < l);
  *lo = l2;
}

X32_FN float x32_pow(float x, float y) {
  x32_u32 ux = x32_bits(x), uy = x32_bits(y);
  x32_u32 ax = ux & 0x7fffffffu, ay = uy & 0x7fffffffu;
  const float inf = x32_float(0x7f800000u);
  if (ay == 0 || ux == 0x3f800000u) return 1.0f;
  if (ax > 0x7f800000u || ay > 0x7f800000u) return x + y;
  int yi = ay == 0x7f800000u ? 2 : x32_yint(ay);
  x32_u32 sgn = (ux >> 31) && yi == 1 ? 0x80000000u : 0;
  if (ay == 0x7f800000u) {                               // y = +-inf
    if (ax == 0x3f800000u) return 1.0f;
    return ((ax > 0x3f800000u) == !(uy >> 31)) ? inf : 0.0f;
  }
  if (ax == 0) return x32_float(((uy >> 31) ? 0x7f800000u : 0) | sgn);
  if (ax == 0x7f800000u) return x32_float(((uy >> 31) ? 0 : 0x7f800000u) | sgn);
  if ((ux >> 31) && yi == 0) return x32_float(0x7fc00000u);
  x32_u64 lh, ll;
  x32_ln(ax, &lh, &ll);
  int lneg = (x32_i64)lh < 0;
  if (lneg) { lh = ~lh + (ll == 0); ll = -ll; }
  float est = (float)lh * 0x1p-56f * (y < 0 ? -y : y);
  int tneg = lneg ^ (uy >> 31);
  if (est > 120.0f) return x32_float((tneg ? 0 : 0x7f800000u) | sgn);
  // t = my * |L| * 2^ey, Q120
  x32_u64 my = (ay & 0x7fffffu) | (ay >= 0x800000u ? 0x800000u : 0);
  int ey = (ay >= 0x800000u ? (int)(ay >> 23) : 1) - 150;
  x32_u64 p0 = my * ll;
  x32_u64 c0 = x32_hi(my, ll);
  x32_u64 p1 = my * lh + c0;
  x32_u64 p2 = x32_hi(my, lh) + (p1 < c0);
  x32_u64 th, tl;
  if (ey >= 0) {                                         // est bounds it
    th = ey ? (p1 << ey) | (p0 >> (64 - ey)) : p1;
    tl = p0 << ey;
  } else {
    int sh = -ey;
    if (sh >= 128) { th = 0; tl = sh < 192 ? p2 >> (sh - 128) : 0; }
    else if (sh >= 64) { th = sh == 64 ? p2 : p2 >> (sh - 64);
      tl = sh == 64 ? p1 : (p1 >> (sh - 64)) | (p2 << (128 - sh)); }
    else { th = (p1 >> sh) | (p2 << (64 - sh)); tl = (p0 >> sh) | (p1 << (64 - sh)); }
  }
  float r = x32_exp_core(tneg, th, tl);
  return sgn ? -r : r;
}

// e^t as M/2^63 * 2^E (M's top bit set): x32_exp_core before its rounding
// (tools/metal-9b.patch; the same reduction, polynomial and table).
X32_FN x32_u64 x32_exp_parts(int neg, x32_u64 hi, x32_u64 lo, int* Eo) {
  int kk = (int)rint((float)hi * 0x1p-56f * 92.332482616893656f);
  x32_u64 blo = (x32_u64)kk * X32_LN2_64_LO;
  x32_u64 bhi = (x32_u64)kk * X32_LN2_64_HI + x32_hi(kk, X32_LN2_64_LO);
  x32_u64 dlo = lo - blo;
  x32_u64 dhi = hi - bhi - (lo < blo);
  x32_i64 r = (x32_i64)((dhi << 7) | (dlo >> 57));
  int k = kk;
  if (neg) { r = -r; k = -k; }
  x32_i64 q = x32_expc[6];
  for (int n = 5; n >= 2; n--) q = x32_expc[n] + x32_mul63(q, r);
  x32_i64 p = r + x32_mul63(x32_mul63(r, r), q);
  x32_u64 T = x32_exp2j[k & 63];
  x32_u64 d = x32_hi(T, p < 0 ? -p : p);
  x32_u64 V = p < 0 ? (T >> 1) - d : (T >> 1) + d;
  int z = x32_clz(V);
  *Eo = (k >> 6) + 1 - z;
  return V << z;
}

// (tools/metal-moe.patch, M24 lever L1) the series constants 2^63 / (2n + 1),
// n = 0 .. 24, as a table: the same integers the loop divided out at run time
// (a 64-bit division is a software loop on the GPU: 59 -> 7.7 us a call);
// x32_softplus is bit-identical on all 2^32 f32 inputs (out/s3-softplus-exh.txt)
X32_TBL x32_u64 x32_inv_odd[25] = {
  0x8000000000000000ull,
  0x2aaaaaaaaaaaaaaaull,
  0x1999999999999999ull,
  0x1249249249249249ull,
  0x0e38e38e38e38e38ull,
  0x0ba2e8ba2e8ba2e8ull,
  0x09d89d89d89d89d8ull,
  0x0888888888888888ull,
  0x0787878787878787ull,
  0x06bca1af286bca1aull,
  0x0618618618618618ull,
  0x0590b21642c8590bull,
  0x051eb851eb851eb8ull,
  0x04bda12f684bda12ull,
  0x0469ee58469ee584ull,
  0x0421084210842108ull,
  0x03e0f83e0f83e0f8ull,
  0x03a83a83a83a83a8ull,
  0x03759f22983759f2ull,
  0x0348348348348348ull,
  0x031f3831f3831f38ull,
  0x02fa0be82fa0be82ull,
  0x02d82d82d82d82d8ull,
  0x02b9310572620ae4ull,
  0x029cbc14e5e0a72full};

// (f32)log(1.0 + exp((double)x)) for x <= 88, the softplus of CUDA's
// llb_mid32 and of kernels/ops.bend's softplus.hi, with the host's three
// double roundings: e = exp(x) to 53 bits, s = 1 + e to 53 bits (ties to
// even; for x < 0 this keeps only e's bits above 2^-53), log(s) to 53 bits,
// then to f32 (x32_round). ln s = (Se) ln2 + 2 atanh(w), w = (u-1)/(u+1) for
// s's mantissa u: w by long division, atanh(w)/w = sum t^n/(2n+1), t = w^2.
// tools/x32/check_softplus.c compares every f32 x <= 20 with this libm.
X32_FN float x32_softplus(float x) {
  x32_u32 u = x32_bits(x), a = u & 0x7fffffffu;
  if (a > 0x7f800000u) return x + x;
  if (a == 0x7f800000u) return (u >> 31) ? 0.0f : x;
  if ((u >> 31) && a >= 0x42200000u) return 0.0f;        // x <= -40: s = 1
  if (a < 0x32800000u) return x32_float(0x3f317218u);    // |x| < 2^-26: ln 2
  x32_u64 m = (a & 0x7fffffu) | 0x800000u;
  int E;
  x32_u64 M = x32_exp_parts(u >> 31, m << ((a >> 23) - 94), 0, &E);
  x32_u64 D = (M >> 11) + ((M >> 10) & 1);               // e = D/2^52 * 2^E
  if (D >> 53) { D >>= 1; E++; }
  x32_u64 Sm;                                            // s = Sm/2^52 * 2^Se
  int Se;
  if (E >= 0) {
    Se = E;
    Sm = E <= 52 ? D + (1ull << (52 - E)) : E == 53 ? D + (D & 1) : D;
  } else {
    int sh = -E;
    x32_u64 q = 0;
    if (sh <= 53) {
      x32_u64 rem = D & ((1ull << sh) - 1), hf = 1ull << (sh - 1);
      q = (D >> sh) + (rem > hf || (rem == hf && ((D >> sh) & 1)));
    }
    Sm = (1ull << 52) + q;
    Se = 0;
  }
  while (Sm >> 53) {
    Sm = (Sm >> 1) + ((Sm & 1) & ((Sm >> 1) & 1));
    Se++;
  }
  x32_u64 k = Sm - (1ull << 52), den = Sm + (1ull << 52);
  x32_u64 ph = 0, pl = 0;
  int i = 0;
  if (k != 0) {
    x32_u64 W = 0, r = k;                                // w = W * 2^-i
    while (!(W >> 63)) {
      r <<= 1;
      W <<= 1;
      if (r >= den) { r -= den; W |= 1; }
      i++;
    }
    int ts = 2 * i - 128;                                // t = w^2, Q64
    x32_u64 t = ts >= 64 ? 0 : ts > 0 ? x32_hi(W, W) >> ts : x32_hi(W, W) << -ts;
    x32_u64 F = 0;                                       // Q63
    for (int n = 24; n >= 0; n--) F = x32_inv_odd[n] + x32_hi(F, t);
    ph = x32_hi(W, F);                                   // ln u = (ph:pl) 2^(-i-62)
    pl = W * F;
  }
  if (Se == 0) {
    if (k == 0) return 0.0f;
    int z = x32_clz(ph);
    x32_u64 Mo = z ? (ph << z) | (pl >> (64 - z)) : ph;
    return x32_round(Mo, 65 - z - i, 0);
  }
  // Q120: ln u = (ph:pl) >> (i - 58), plus Se ln2
  x32_u64 lh = 0, ll = 0;
  if (k != 0) {
    int sh = i - 58;
    lh = ph >> sh;
    ll = (pl >> sh) | (ph << (64 - sh));
  }
  x32_u64 un = (x32_u64)Se;
  x32_u64 nlo = un * X32_LN2_LO;
  x32_u64 nhi = un * X32_LN2_HI + x32_hi(un, X32_LN2_LO);
  x32_u64 l = ll + nlo;
  x32_u64 h = lh + nhi + (l < ll);
  int z = h ? x32_clz(h) : 64 + x32_clz(l);
  x32_u64 Mo = z == 0 ? h : z < 64 ? (h << z) | (l >> (64 - z)) : l << (z - 64);
  return x32_round(Mo, 7 - z, 0);
}
