
// Imports
// =======

#pragma clang fp contract(off)

#ifdef __METAL_VERSION__
#include <metal_stdlib>
using namespace metal;
#elif !defined(__CUDACC_RTC__)
#ifndef __APPLE__
#define _GNU_SOURCE
#endif
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#include <time.h>
#include <poll.h>
#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif
#ifdef __OBJC__
// #include, not #import: bend -o reads an #import as an effect's framework
#include <Metal/Metal.h>
#include <Foundation/Foundation.h>
#elif BEND_CUDA
#include <cuda.h>
#include <nvrtc.h>
#include <fcntl.h>
#include <sys/stat.h>
#endif
#endif

// Dialect
// =======

#ifdef __METAL_VERSION__
// coherent(device) (MSL 3.2): M1-class parts else lose stores across
// threadgroups within a dispatch
#if __METAL_VERSION__ >= 320
#define DEV     coherent(device) device
#define DEVL    coherent(device) device
#else
#define DEV     device
#define DEVL    device
#endif
#define GA32    threadgroup atomic_uint
#define THR     thread
#define INLINE  inline
#define OUTLINE static
#define CONSTV  constant
#define DEVICE  1
#define CLZ(x)  clz(x)
#define A32(p)  ((DEV atomic_uint*)(p))
#define RLX     memory_order_relaxed
#define FENCE() atomic_thread_fence(mem_flags::mem_device, memory_order_seq_cst)
#define BAR()   threadgroup_barrier(mem_flags::mem_threadgroup)
#define BARD()  threadgroup_barrier(mem_flags::mem_device \
  | mem_flags::mem_threadgroup)

#define g32_ini(p)    atomic_store_explicit(p, 0, RLX)
#define g32_add(p, v) atomic_fetch_add_explicit(p, v, RLX)
#define g32_get(p)    atomic_load_explicit(p, RLX)
#else
#define DEVL
#define THR
#define INLINE  static inline
#define CONSTV  static const

#define g32_ini(p)    a32_store(p, 0)
#define g32_add(p, v) a32_add(p, v)
#define g32_get(p)    a32_load(p)
#ifdef __CUDACC_RTC__
// plain data stays L1-cacheable: cross-lane handoffs go through a32 + FENCE
#define DEV
#define GA32    __shared__ u32
#define OUTLINE static __attribute__((noinline))
#define DEVICE  1
#define CLZ(x)  (u32)__clz((int)(x))
#define FENCE() __threadfence()
#define BAR()   __syncthreads()
#define BARD()  \
  { __threadfence(); __syncthreads(); }
#else
#define DEV
// only clang 19+ has both, and only it compiles preserve_most soundly
#if __has_attribute(preserve_none) && __has_attribute(preserve_most)
#define PRESERVE(A) __attribute__((A))
#else
#define PRESERVE(A)
#endif
#define OUTLINE static __attribute__((noinline, cold)) PRESERVE(preserve_most)
#define DEVICE  0
#define CLZ(x)  (u32)__builtin_clz(x)
#endif
#endif
#define FAR static __attribute__((noinline))

// A segment: a case of the device's switch; on the host, a preserve_none
// function (WL_SIG) left by a musttail call, its words fresh at WL_OPEN.
#if DEVICE
#define LOCK(l)
#define UNLOCK(l)
#define WL_CASE(F) case F:
#define WL_OPEN    {
#define WL_JMP(F)  { fid = (F); break; }
#define WL_DYN     WL_JMP
#else
#define LOCK(l)    while (__atomic_exchange_n(&(l), 1, __ATOMIC_ACQUIRE)) {}
#define UNLOCK(l)  __atomic_store_n(&(l), 0, __ATOMIC_RELEASE)
#define WL_FN      static PRESERVE(preserve_none) __attribute__((noinline)) Reply
#define WL_CASE(F) WL_FN WL_##F(WL_SIG)
#define WL_OPEN    { WL_BANK u32 rn;
#define WL_JMP(F)  __attribute__((musttail)) return WL_##F(WL_ALL)
#define WL_DYN(F)  __attribute__((musttail)) return wl_tab[F](WL_ALL)
#endif
#define WL_SPIN     for (;;) { if (err_spun(e.mem, &wpoll)) { return 0; }
#define WL_SPUN     } break;
#define WL_AGAIN(F) continue
#define WL_POP()    { sp -= LANE_STEP; WL_DYN((Fid)STK(0)); }

#define LANE_STEP (DEVICE ? (int64_t)CUBE : 1)
#define STK(I)    sp[(int64_t)(I) * LANE_STEP]

#define WL_RETN(N)  { rn = (N); WL_POP(); }
#define WL_CONT     STK(-3)
#define WL_IDX      STK(-2)
#define WL_POPN(N)  sp -= N * LANE_STEP
#define WL_PUSHN(N) sp += N * LANE_STEP
#define WL_FRAME(T) \
  Loc wtl = task_tail(T); \
  u64 wtw = e.mem[wtl + 1]; \
  STK(0) = e.mem[wtl]; \
  STK(1) = (wtw >> 32) & 0xFFFF; \
  STK(2) = FID_EXIT; \
  sp += 3 * LANE_STEP;
#define WL_ARGS(A, N) \
  for (u32 wi = 0; wi + 1 < N; wi += 1) { \
    STK(wi) = e.mem[A + wi]; \
  } \
  sp += (N - 1) * LANE_STEP;
#define WL_ROOM(N) \
  if (DEVICE && sp + (N) * CUBE >= e.mem + HEAP_OFF + CUBE) { \
    err_post(e.mem, ERR_DEEP); \
    return 0; \
  }

// Types
// =====

#ifdef __METAL_VERSION__
typedef ulong u64;
typedef uint  u32;
typedef uchar u8;
typedef float f32;
// Metal Shading Language has no fp64: F64 is a host and CUDA type, and the
// helpers below are guarded so an F32 program compiles for Metal unchanged
#elif defined(__CUDACC_RTC__)
typedef unsigned long long u64;
typedef long long          int64_t;
typedef unsigned int       u32;
typedef unsigned char      u8;
typedef float              f32;
typedef double             f64;
#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
typedef float    f32;
typedef double   f64;
#endif

typedef u64 Loc;
#define LOC_MASK ((1ull << 40) - 1)

typedef u32 Cls;
typedef u32 Fid;

typedef u64 Term;
#define TAG_PAK 1ull
#define TAG_CTR 2ull
#define TAG_CLO 3ull
#define TAG_BUF 4ull
#define TAG_TSK 5ull
#define TAG_ARR 6ull
#define TAG_STR 7ull

#define TERM_HOLE (~0ull)

#define RFC_BIT  (1ull << 63)
#define RFC_CNT  ((1u << 24) - 1)

typedef Term Reply;

typedef u32 Err;
#define ERR_RING 1
#define ERR_TAGS 2
#define ERR_HEAP 3
#define ERR_FIDS 4
#define ERR_NATS 5
#define ERR_RFCS 6
#define ERR_DEEP 7
#define ERR_ARRS 8
#define ERR_STRS 9

typedef u32 Ring;

typedef DEV u64* Corpus;

typedef struct {
  Corpus   mem;
  DEV u64* alc;
} Env;

typedef struct {
  u64 off;
  u32 rd;
  u32 wr;
  u32 top;
} Bank;

typedef DEVL Term* Stk;

typedef Term Nat;
#define NAT_IMM ((1ull << 48) - 1)

typedef Term U32;

#if DEVICE
typedef u32 u32a;
#else
typedef u32 __attribute__((may_alias)) u32a;
#endif

#ifdef __METAL_VERSION__
typedef threadgroup atomic_uint* Cur;
#else
typedef u32* Cur;
#endif

// Constants
// =========

#define LINE      16
#define PAGE_BITS 7
#define PAGE_LEN  (1ull << PAGE_BITS)
#define CUBE_T    128
#define CUBE      ((u64)CUBE_T * CUBE_T)
#define CUBE_G    (1u << CUBE_LOG)
#define LANES     ((u64)CUBE_T << CUBE_LOG)
#define RING_LOG  (17 - CUBE_LOG)
#define RING_LEN  (1ull << RING_LOG)
#define STAK_LEN  (1ull << 11)
#define NCLS      8
#define NCLS_ALL  32
#define IO_HELP   64

#define ALC_WORDS NCLS_ALL
#define TG_HOLD   2304
#define CHUNK     256
#define CAP_WORDS 32768
#define QUANTUM   (DEVICE ? PAGE_LEN \
  : KEEP_WORDS < 32 * PAGE_LEN ? KEEP_WORDS : 32 * PAGE_LEN)
#if DEVICE
#define KEEP_WORDS CHUNK
#endif
#define RING_WORDS ((1ull << 10) + 2)

#define H_BUMP       0
#define H_CAP        1
#define H_CURSOR     LINE
#define H_ROOT_DONE  (2 * LINE)
#define H_ERROR_CODE (3 * LINE)
#define H_ROOT_WORD  (4 * LINE)
#define H_BANK       (H_ROOT_WORD + WL_RESW)

#define PAGE_UP(n) (((n) + PAGE_LEN - 1) & ~(PAGE_LEN - 1))
#define ALC_OFF  PAGE_UP(H_BANK + 3 * NCLS_ALL)
#define RING_OFF (ALC_OFF + CUBE * 2 * ALC_WORDS)
#define STAK_OFF (RING_OFF + CUBE * RING_WORDS)
#define STAT_OFF (STAK_OFF + CUBE * STAK_LEN)
#define HEAP_OFF (STAT_OFF + PAGE_UP(STAT_LEN))

// Globals
// =======

#if !DEVICE

typedef pthread_mutex_t lock;

static Corpus CORPUS;
static u64    ALC[CUBE_T + 1][3 * ALC_WORDS] __attribute__((aligned(128)));
static u32    KEEP_WORDS;
// the bag: 2^CUBE_LOG groups of CUBE_T lanes (a -D constant on the device)
static u32    CUBE_LOG = 7;
static u32    bank_lock;

static u32            pool_size;
static _Atomic u32    pool_row;
static bool           pool_grow;
static _Atomic u64    pool_tick;
static _Atomic u32    pool_done;
static lock           pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t pool_wake = PTHREAD_COND_INITIALIZER;

// The device program compiles from the binary's own text.
#if BEND_METAL || BEND_CUDA
#pragma clang diagnostic ignored "-Wc23-extensions"
static const char BEND_SRC[] = {
#embed __FILE__
, 0 };
#endif

#ifdef __OBJC__
static id<MTLDevice>               gpu_dev;
static id<MTLCommandQueue>         gpu_que;
static id<MTLComputePipelineState> gpu_pso;
static id<MTLBuffer>               gpu_buf;
static id<MTLComputeCommandEncoder> gpu_enc;
#elif BEND_CUDA
static CUdevice   gpu_dev;
static CUmodule   gpu_lib;
static CUfunction gpu_pso;
#endif
static bool io_gpu;
static Stk  io_stk;

static const char* CLI_HELP =
  "usage: %s [options] [arguments]\n"
  "  --threads N       worker threads, 1 to 128 (default: the CPU count)\n"
  "  --gpu on|off|4GB  run ! calls on the GPU, over this much of its memory\n"
  "                    (default: on if present, over 2GB on Metal)\n"
  "  --gpu-build       write the GPU program and exit\n"
  "  --help            show this text\n"
  "  --                the rest are the program's arguments (IO.args)\n";

#endif

// Tables
// ======

#define CID_TUPLE 0
#define CID_SNIL 1
#define CID_SCON 2
#define CID_WCON 3
#define CID_EMIT 4
#define CID_HALT 5
#define CID_FAIL 6
#define CID_DONE 7
#define CID_NONE 8
#define CID_SOME 9
#define CID_FALSE 10
#define CID_TRUE 11
#define CID_UNIT 12
#define CID_NIL 13
#define CID_CON 14
#define CID_CHR 15
#define CID_LT 16
#define CID_EQ 17
#define CID_GT 18
#define CID_ICHR 19
#define CID_IANY 20
#define CID_ISET 21
#define CID_ISPLIT 22
#define CID_IJMP 23
#define CID_ISAVE 24
#define CID_IBOL 25
#define CID_IEOL 26
#define CID_IWORDB 27
#define CID_IMATCH 28
#define CID_MATCH 29
#define CID_WNIL 30
#define CID_IO_PRINT 31
#define FID_WORD_TO_NAT 0
#define FID_WORD_TO_NAT_K2 1
#define FID_WORD_TO_NAT_K3 2
#define FID_NAT_SHOW_FIN 3
#define FID_SHOW 4
#define FID_NAT_SHOW 5
#define FID_WORD_ZERO 6
#define FID_WORD_ZERO_K12 7
#define FID_MAIN 8
#define FID_MAIN_K14 9
#define FID_MAIN_K15 10
#define FID_MAIN_K16 11
#define FID_MAIN_C17 12
#define FID_MAIN_C18 13
#define FID_MAIN_C19 14
#define FID_MAIN_K20 15
#define FID_IO_PRINT 16
#define FID_IO_EMIT 17
#define FID_CLO_APPLY 18
#define FID_EXIT 19
#define FID_ENTER 20
CONSTV u8 FID_ARITY_T[] = { 2, 1, 1, 4, 1, 1, 1, 1, 0, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2 };
CONSTV u8 FID_FLAG_T[] = { 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 };
CONSTV u8 FID_RESW_T[] = { 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0 };
CONSTV u8 CID_ARITY_T[] = { 2, 0, 2, 2, 1, 2, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1, 1, 1, 1, 0, 3, 0, 2 };
CONSTV u8 CID_HOT_T[] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
#define STAT_LEN 9

#define WL_RESW 1
#define BANGS   0

#define WL_BANK Term r0, r1, r2, r3;

#define WL_LOAD(A, N) \
  do { \
    if ((N) <= 0) break; r0 = e.mem[(A) + 0]; \
    if ((N) <= 1) break; r1 = e.mem[(A) + 1]; \
    if ((N) <= 2) break; r2 = e.mem[(A) + 2]; \
    if ((N) <= 3) break; r3 = e.mem[(A) + 3]; \
  } while (0);

#define WL_LAST(X) \
  switch (war) { \
    case 0: r0 = (X); \
      break; \
    case 1: r1 = (X); \
      break; \
    case 2: r2 = (X); \
      break; \
    case 3: r3 = (X); \
      break; \
  }

#define WL_SAVE(V) (V)[0] = r0;

#define WL_TAKE(V) r0 = (V)[0];

#define WL_SIG Env e, Stk sp, u32 seq, u32 rn, Term r0, Term r1, Term r2, Term r3

#define WL_ALL e, sp, seq, rn, r0, r1, r2, r3

#define WL_TABLE WL_X(FID_WORD_TO_NAT) WL_X(FID_WORD_TO_NAT_K2) WL_X(FID_WORD_TO_NAT_K3) WL_X(FID_NAT_SHOW_FIN) WL_X(FID_SHOW) WL_X(FID_NAT_SHOW) WL_X(FID_WORD_ZERO) WL_X(FID_WORD_ZERO_K12) WL_X(FID_MAIN) WL_X(FID_MAIN_K14) WL_X(FID_MAIN_K15) WL_X(FID_MAIN_K16) WL_X(FID_MAIN_C17) WL_X(FID_MAIN_C18) WL_X(FID_MAIN_C19) WL_X(FID_MAIN_K20) WL_X(FID_IO_PRINT) WL_X(FID_IO_EMIT) WL_X(FID_CLO_APPLY) WL_X(FID_EXIT)
#define MAIN_FID FID_MAIN
#define MAIN_PURE 0

#define TAB_AT(T, S, I) T[S < I ? S : I]

// Fid
// ===

#define fid_arity(x) ((u32)FID_ARITY_T[x])

#define fid_bangs(x) ((bool)(FID_FLAG_T[x] & 1))

#define fid_nofk(x) ((bool)(FID_FLAG_T[x] & 2))

#define fid_seqk(x) (fid_resw(x) != 0)

#define fid_resw(x) ((u32)FID_RESW_T[x])

// Cid
// ===

#define cid_arity(x) ((u32)CID_ARITY_T[x])
#define cid_hot(x) ((bool)CID_HOT_T[x])

// A32
// ===

#ifdef __METAL_VERSION__

// via a volatile local: else the M1 backend folds the zext into the atomic
// load, cannot legalize it, and the pipeline build dies
#define a32_load(p)      \
  ({ volatile thread u32 _a32v = atomic_load_explicit(A32(p), RLX); _a32v; })
#define a32_store(p, v)  atomic_store_explicit(A32(p), v, RLX)
#define a32_add(p, v)    atomic_fetch_add_explicit(A32(p), v, RLX)
#define a32_sub(p, v)    atomic_fetch_sub_explicit(A32(p), v, RLX)
#define a32_swp(p, e, v) \
  atomic_compare_exchange_weak_explicit(A32(p), e, v, RLX, RLX)

#elif defined(__CUDACC_RTC__)

#define a32_load(p)     (*(volatile u32*)(p))
#define a32_store(p, v) (*(volatile u32*)(p) = (v))
#define a32_add(p, v)   atomicAdd((u32*)(p), v)
#define a32_sub(p, v)   atomicSub((u32*)(p), v)

INLINE bool a32_swp(DEV u32* p, u32* e, u32 v) {
  u32 x = *e;
  *e = atomicCAS((u32*)p, x, v);
  return *e == x;
}

#endif

#if DEVICE

INLINE u32 a32_sub_rel(DEV u32* p, u32 v) {
  FENCE();
  return a32_sub(p, v);
}

INLINE void a32_store_rel(DEV u32* p, u32 v) {
  FENCE();
  a32_store(p, v);
}

INLINE u32 a32_load_acq(DEV u32* p) {
  u32 v = a32_load(p);
  FENCE();
  return v;
}

#define a32_acq(p) FENCE()

INLINE bool a32_cas(DEV u32* p, THR u32* e, u32 v) {
  FENCE();
  bool ok = a32_swp(p, e, v);
  FENCE();
  return ok;
}

#else

#define a32_load(p)         __atomic_load_n(p, __ATOMIC_RELAXED)
#define a32_store(p, v)     __atomic_store_n(p, v, __ATOMIC_RELAXED)
#define a32_add(p, v)       __atomic_fetch_add(p, v, __ATOMIC_RELAXED)
#define a32_sub(p, v)       __atomic_fetch_sub(p, v, __ATOMIC_RELAXED)
#define a32_sub_rel(p, v)   __atomic_fetch_sub(p, v, __ATOMIC_RELEASE)
#define a32_store_rel(p, v) __atomic_store_n(p, v, __ATOMIC_RELEASE)
#define a32_load_acq(p)     __atomic_load_n(p, __ATOMIC_ACQUIRE)
#define a32_acq(p)          ((void)a32_load_acq(p))

INLINE bool a32_cas(u32* p, u32* e, u32 v) {
  return __atomic_compare_exchange_n(
    p, e, v, 1, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}

#endif

#define a32_at(H, word) ((DEV u32*)&(H)[word])

// Err
// ===

#if DEVICE

INLINE void err_post(Corpus H, Err code) {
  u32 seen = 0;
  while (seen == 0 && !a32_cas(a32_at(H, H_ERROR_CODE), &seen, code)) {}
}

#else

static const char* ERR_TEXT[] = { "",
  "runtime fail-stop",
  "runtime fail-stop",
  "out of memory: run again with a bigger span, as in --gpu 8GB",
  "a function the device does not hold",
  "a Nat past the largest immediate 2^48-1",
  "runtime fail-stop",
  "memory fault (machine stack overflow?)",
  "an array past the deepest block class 31",
  "a string past the maximum length 2^31" };

static void err_fail(const char* msg) {
  fflush(stdout);
  fprintf(stderr, "bend: %s\n", msg);
  _exit(1);
}

static void err_post(Corpus H, Err code) {
  err_fail(ERR_TEXT[code]);
}

static void err_trap(int sig) {
  err_post(NULL, ERR_DEEP);
}

#endif

#define err_seen(H)    (DEVICE && a32_load(a32_at(H, H_ERROR_CODE)) != 0)
#define err_spun(H, n) ((++*(n) & 4095) == 0 && err_seen(H))

#ifdef __METAL_VERSION__
// Metal's atan2 is NaN at the origin; libm answers +-0 or +-pi there
INLINE f32 atan2_c99(f32 y, f32 x) {
  return y == 0.0f && x == x
    ? copysign(signbit(x) ? M_PI_F : 0.0f, y) : atan2(y, x);
}
#define sqrt  precise::sqrt
#define exp   precise::exp
#define log   precise::log
#define log2  precise::log2
#define log10 precise::log10
#define sin   precise::sin
#define cos   precise::cos
#define tan   precise::tan
#define pow   precise::pow
#define fmod  precise::fmod
#define atan2 atan2_c99
#endif

#define U32_BIN(a, o, b) ((u64)((u32)(a) o (u32)(b)))

// Metal folds a constant dividend within 128 of 2^32 through an f32: divide
// its half, then fix the odd bit.
#define U32_QUO(a, b) \
  ((a) / 2 / (b) * 2 + ((a) - (a) / 2 / (b) * 2 * (b) >= (b)))

INLINE f32 f32_unbox(u64 x) {
  union { u32 u; f32 f; } p = { (u32)x };
  return p.f;
}

INLINE u64 f32_rewrap(f32 x) {
  union { f32 f; u32 u; } p = { x };
  return p.u;
}

INLINE U32 f32_to_u32(U32 a) {
  f32 v = f32_unbox(a);
  return v >= 0.0f && v < 4294967296.0f ? (u32)v : 0;
}

#ifndef __METAL_VERSION__

INLINE f64 f64_unbox(u64 x) {
  union { u64 u; f64 f; } p = { x };
  return p.f;
}

INLINE u64 f64_rewrap(f64 x) {
  union { f64 f; u64 u; } p = { x };
  return p.u;
}

INLINE U32 f64_to_u32(U32 a) {
  f64 v = f64_unbox(a);
  return v >= 0.0 && v < 4294967296.0 ? (u32)v : 0;
}

#endif

INLINE Nat nat_chk(Env e, Nat n) {
  if (n > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
    return NAT_IMM;
  }
  return n;
}

INLINE Nat nat_mul(Env e, Nat a, Nat b) {
  return nat_chk(e, b != 0 && a > NAT_IMM / b ? NAT_IMM + 1 : a * b);
}

#if DEVICE

#define f32_show(e, x) (err_post(e.mem, ERR_FIDS), 0)
#define f32_read(e, s) (err_post(e.mem, ERR_FIDS), 0)

#define f64_show(e, x) (err_post(e.mem, ERR_FIDS), 0)
#define f64_read(e, s) (err_post(e.mem, ERR_FIDS), 0)

#else

static Term f32_show(Env e, Term x);
static Term f32_read(Env e, Term s);
static Term f64_show(Env e, Term x);
static Term f64_read(Env e, Term s);

#endif

// Cls
// ===

INLINE Cls cls_fit(u32 words) {
  return words > 1 ? 32 - CLZ(words - 1) : 0;
}

// Bank
// ====

// One stack of exact generations per class; 2 heap_words / max(CHUNK,
// 2^c) entries cover the old ones plus a pass of returns. The host
// pops and pushes at rd under bank_lock; a device pass pops down from
// rd and pushes above top, and the host then compacts [top, wr) onto
// rd, so a pass never sees what it handed.

#define bank_at(H, c) ((DEV Bank*)((H) + H_BANK) + (c))

INLINE Loc bank_pop(Corpus H, Cls c) {
  DEV Bank* b = bank_at(H, c);
  Loc got = 0;
  LOCK(bank_lock);
  u32 t = a32_sub(&b->rd, 1);
  if ((int)t > 0) {
    got = H[b->off + t - 1];
  } else {
    a32_add(&b->rd, 1);
  }
  if (!DEVICE) {
    b->wr = b->top = b->rd;
  }
  UNLOCK(bank_lock);
  return got;
}

INLINE void bank_push(Corpus H, Cls c, Loc head) {
  DEV Bank* b = bank_at(H, c);
  LOCK(bank_lock);
  H[b->off + a32_add(&b->wr, 1)] = head;
  if (!DEVICE) {
    b->rd = b->top = b->wr;
  }
  UNLOCK(bank_lock);
}

// Heap
// ====

// Per lane and class (a tile row on the device): HOT, a LIFO chain of
// free slots (word 0 the head it replaced); LEN, its exact length in
// words, off the chain; on the host COLD, one generation. A free is a
// push and an add. A host free at KEEP_WORDS (a slot for a wide class)
// runs heap_hand: COLD to the bank, HOT parked as COLD, generations
// exact. A miss takes COLD, else a bank entry, else a quantum of at
// most a generation, and sets LEN to what it took: no adoption past a
// generation, no list re-aged. A device lane keeps its frees for the
// pass; at the kernel end dev_cut hands its complete generations,
// walking only those. KEEP_WORDS is CAP_WORDS, or CHUNK with the GPU
// (fixed at boot), so a device lane may adopt every host entry.
// Bounds: a host lane and class under 2 max(KEEP_WORDS, 2^c) words, a
// device one under max(CHUNK, 2^c) after each kernel plus its own
// frees within one, bank entries exact. The bump grows only when this
// lane's HOT and COLD and the class's bank are empty. A zero row is an
// empty lane.

#define ALC_AT(e, i)   (e).alc[(i) * LANE_STEP]
#define ALC_LEN(e, c)  ALC_AT(e, ALC_WORDS + (c))
#define ALC_COLD(e, c) ALC_AT(e, 2 * ALC_WORDS + (c))
#define KEEP(c)        (KEEP_WORDS >> (c) ? KEEP_WORDS >> (c) : 1)

OUTLINE void heap_hand(Env e, Cls cls) {
  Loc cold = ALC_COLD(e, cls);
  if (cold) {
    bank_push(e.mem, cls, cold);
  }
  ALC_COLD(e, cls) = ALC_AT(e, cls);
  ALC_AT(e, cls)   = 0;
  ALC_LEN(e, cls)  = 0;
}

OUTLINE Loc heap_alloc_miss(Env e, Cls cls) {
  Corpus H = e.mem;
  Loc  got = 0;
  if (!DEVICE) {
    got = ALC_COLD(e, cls);
    ALC_COLD(e, cls) = 0;
  }
  if (!got) {
    got = bank_pop(H, cls);
  }
  u32 n = got ? KEEP(cls) : cls < NCLS ? QUANTUM >> cls : 1;
  if (!got) {
    u32 pages = (n << cls) >> PAGE_BITS;
    u32 p     = a32_add(a32_at(H, H_BUMP), pages);
    if ((u64)p + pages > a32_load(a32_at(H, H_CAP))) {
      err_post(H, ERR_HEAP);
      p = 0;
    }
    got = HEAP_OFF + ((u64)p << PAGE_BITS);
    for (u32 i = 1; i <= n; i += 1) {
      H[got + ((u64)(i - 1) << cls)] = i < n ? got + ((u64)i << cls) : 0;
    }
  }
  ALC_AT(e, cls)  = H[got];
  ALC_LEN(e, cls) = (u64)(n - 1) << cls;
  return got;
}

INLINE Loc heap_alloc(Env e, Cls cls) {
  Loc h = ALC_AT(e, cls);
  if (h) {
    ALC_AT(e, cls)   = e.mem[h];
    ALC_LEN(e, cls) -= 1ull << cls;
    return h;
  }
  return heap_alloc_miss(e, cls);
}

INLINE void heap_free(Env e, Cls cls, Loc loc) {
  if (err_seen(e.mem)) {
    return;
  }
  e.mem[loc]       = ALC_AT(e, cls);
  ALC_AT(e, cls)   = loc;
  ALC_LEN(e, cls) += 1ull << cls;
  if (!DEVICE && ALC_LEN(e, cls) >= KEEP_WORDS) {
    heap_hand(e, cls);
  }
}

// Spare
// =====

INLINE void spare_free(Env e, Cls cls, Loc loc) {
  if (loc >= HEAP_OFF) {
    heap_free(e, cls, loc);
  }
}

// Term
// ====

#define term_make(tag, aux, loc) \
  (((u64)(tag) << 56) | ((u64)(aux) << 40) | (u64)(loc))

#define term_ctr(cid, loc) term_make(TAG_CTR, cid, loc)
#define term_pak(cid, loc) term_make(TAG_PAK, cid, loc)
#define term_clo(fid, loc) term_make(TAG_CLO, fid, loc)
#define term_buf(cls, loc) term_make(TAG_BUF, cls, loc)
#define term_tsk(fid, loc) term_make(TAG_TSK, fid, loc)

INLINE Term term_blk(bool arr, Cls cls, Loc loc) {
  return term_buf(cls, loc) | ((u64)arr << 57);
}

INLINE u64 term_tag(Term t) {
  return (t >> 56) & 0x7f;
}

INLINE bool term_rfc(Term t) {
  return (t & RFC_BIT) != 0;
}

INLINE u64 term_aux(Term t) {
  return (t >> 40) & 0xFFFF;
}

INLINE Loc term_loc(Term t) {
  return t & LOC_MASK;
}

// A static node (below the heap) is trivial, as is a captureless closure.
INLINE bool term_triv(Term t) {
  return term_tag(t) <= TAG_PAK || t == TERM_HOLE || term_loc(t) < HEAP_OFF;
}

OUTLINE Term rfc_wrap(Env e, Term t, u32 cnt) {
  if (term_tag(t) == TAG_CLO || term_tag(t) == TAG_TSK) {
    err_post(e.mem, ERR_RFCS);
    return t;
  }
  Loc r = heap_alloc(e, 0);
  if (err_seen(e.mem)) { return t; }
  e.mem[r] = ((u64)term_loc(t) << 24) | cnt;
  return (t & ~LOC_MASK) | RFC_BIT | r;
}

INLINE Term rfc_seal(Env e, Term t) {
  if ((term_tag(t) != TAG_CTR && term_tag(t) != TAG_STR)
    || term_rfc(t) || term_triv(t)) {
    return t;
  }
  return rfc_wrap(e, t, 1);
}

INLINE u64 rfc_view(Env e, Loc r) {
  DEV u32* w = a32_at(e.mem, r);
  u64 cell = ((u64)a32_load(w + 1) << 32) | a32_load(w);
  if ((cell & RFC_CNT) == 1) {
    a32_acq(w);
  }
  return cell;
}

INLINE void rfc_bump(Env e, Loc r, u32 k) {
  u32 c = a32_add(a32_at(e.mem, r), k);
  if ((c & RFC_CNT) >= RFC_CNT - k) {
    err_post(e.mem, ERR_RFCS);
  }
}

INLINE Term term_keep(Env e, Term t) {
  if (term_rfc(t)) {
    rfc_bump(e, term_loc(t), 1);
    return t;
  }
  if (term_triv(t)) {
    return t;
  }
  return rfc_wrap(e, t, 2);
}

INLINE Loc term_peek(Env e, Term t) {
  if (term_rfc(t)) {
    return rfc_view(e, term_loc(t)) >> 24;
  }
  return term_loc(t);
}

INLINE Cls blk_cls(Term t) {
  return (u32)term_aux(t) & 31;
}

#define buf_wcls(c) ((c) == 0 ? 0 : (c) - 1)

INLINE Cls blk_span(Term t) {
  Cls c = blk_cls(t);
  return term_tag(t) == TAG_ARR ? c : buf_wcls(c);
}

INLINE void blk_free(Env e, Term t) {
  heap_free(e, blk_span(t), term_loc(t));
}

FAR void term_drop(Env e, Term t) {
  Corpus H = e.mem;
  u64  cur = 0;
  Term c0  = 0;
  u32  step = 0;
  for (;;) {
    if (!term_triv(t) && term_rfc(t)) {
      Loc      r = term_loc(t);
      DEV u32* p = a32_at(H, r);
      if ((a32_sub_rel(p, 1) & RFC_CNT) != 1) {
        t = 0;
      } else {
        a32_acq(p);
        t = (t & ~(RFC_BIT | LOC_MASK)) | (H[r] >> 24);
        heap_free(e, 0, r);
      }
    }
    if (!term_triv(t)) {
      u64 tag = term_tag(t);
      if (tag == TAG_BUF) {
        blk_free(e, t);
      } else {
        u32 aux = (u32)term_aux(t);
        Loc loc = term_loc(t);
        u32 n   = 0;
        Cls cls;
        if (tag == TAG_STR) {
          n = 1;
          cls = 1;
        } else if (tag == TAG_ARR) {
          cls = 64 | blk_cls(t);
        } else {
          u32 ar;
          if (tag == TAG_CTR) {
            ar = cid_arity(aux);
          } else if (tag == TAG_CLO) {
            ar = fid_arity(aux) - 1;
          } else {
            ar = fid_arity(aux);
          }
          n   = ar;
          cls = cls_fit(tag == TAG_TSK ? ar + 2 : ar);
        }
        c0 = H[loc];
        H[loc] = cur;
        cur = loc | ((u64)n << 48) | ((u64)cls << 56);
      }
    }
    for (;;) {
      if (err_spun(H, &step)) {
        return;
      }
      if (cur == 0) {
        return;
      }
      Loc  loc = cur & LOC_MASK;
      u32  i   = (u8)(cur >> 40);
      u32  n   = (u8)(cur >> 48);
      Cls  cls = (u32)(cur >> 56);
      bool arr = cls > 63;
      u32  j   = i;
      if (arr) {
        cls &= 63;
        n   = 1u << cls;
        if (i == 2) {
          j = (u32)H[loc + 1];
        }
      }
      if (j < n) {
        Term c = j == 0 ? c0 : H[loc + j];
        if (arr && j > 0) {
          H[loc + 1] = j + 1;
        }
        if (!arr || i < 2) {
          cur += 1ull << 40;
        }
        if (!term_triv(c)) {
          t = c;
          break;
        }
      } else {
        u64 up = H[loc];
        heap_free(e, cls, loc);
        cur = up;
      }
    }
  }
}

INLINE void term_sink(Env e, Term t) {
  if (!term_triv(t)) {
    term_drop(e, t);
  }
}

OUTLINE void span_fade(Env e, Term t, Loc src, u32 n) {
  for (u32 j = 0; j < n; j += 1) {
    Term f = e.mem[src + j];
    if (term_rfc(f)) {
      rfc_bump(e, term_loc(f), 1);
    } else if (!term_triv(f)) {
      err_post(e.mem, ERR_RFCS);
    }
  }
  term_drop(e, t);
}

INLINE Loc ctr_take(Env e, Term t, u32 n, THR Term* out) {
  Corpus H = e.mem;
  if (!term_rfc(t)) {
    for (u32 j = 0; j < n; j += 1) {
      out[j] = H[term_loc(t) + j];
    }
    return term_loc(t);
  }
  Loc r    = term_loc(t);
  u64 cell = rfc_view(e, r);
  Loc src  = cell >> 24;
  for (u32 j = 0; j < n; j += 1) {
    out[j] = H[src + j];
  }
  if ((cell & RFC_CNT) == 1) {
    heap_free(e, 0, r);
    return src;
  }
  span_fade(e, t, src, n);
  return 0;
}

INLINE Term term_word(Env e, Term w) {
  u32 x = 0;
  Term t = w;
  for (u32 i = 0; i < 32 && term_aux(t) == CID_WCON; i += 1) {
    Loc l = term_peek(e, t);
    x |= (u32)(e.mem[l] & 1) << i;
    t = e.mem[l + 1];
  }
  term_sink(e, w);
  return x;
}

// Blk
// ===

// A block owns one allocation in its physical class (an ARR of class
// c 2^c Terms in 2^c words, a BUF 2^c u32 in 2^buf_wcls(c) words) and
// blk_free returns it there. A match on ANode is blk_half twice: each
// half allocated in its class and copied, the source freed shallow by
// the high call (its elements moved; the emitter binds the low half
// first). ANode{l, r} is blk_node: the merged class, l and r copied
// and freed shallow. Array.clone is blk_copy: a BUF raw, an ARR's
// elements retained through blk_keep. A match to the leaves copies
// O(n log n) words where a view copied none; get, set, swap, size and
// new open no half.

#define BLK_ALLOC(n, w) \
  Loc n = heap_alloc(e, w); \
  if (err_seen(e.mem)) { \
    return term_buf(0, n); \
  }

INLINE DEV u32a* blk_ptr(Corpus H, Loc loc, u32 i) {
  return (DEV u32a*)(H + loc) + i;
}

INLINE Term blk_read(Corpus H, bool arr, Loc loc, u32 i) {
  if (arr) {
    return H[loc + i];
  }
  return (u64)*blk_ptr(H, loc, i);
}

INLINE void blk_write(Corpus H, bool arr, Loc loc, u32 i, Term v) {
  if (arr) {
    H[loc + i] = v;
  } else {
    *blk_ptr(H, loc, i) = (u32)v;
  }
}

INLINE u32 blk_at(Term a, U32 i, u32 lgs) {
  return ((u32)i & (u32)((1ull << (blk_cls(a) - lgs)) - 1)) << lgs;
}

INLINE Term blk_keep(Env e, Loc at) {
  Term w = e.mem[at];
  Term v = term_keep(e, w);
  if (v != w) {
    e.mem[at] = v;
  }
  return v;
}

OUTLINE Term blk_copy(Env e, Term a) {
  Corpus H = e.mem;
  bool arr = term_tag(a) == TAG_ARR;
  Cls cls = blk_span(a);
  Loc src = term_loc(a);
  BLK_ALLOC(dst, cls)
  for (u64 j = 0; j < (1ull << cls); j += 1) {
    H[dst + j] = arr ? blk_keep(e, src + j) : H[src + j];
  }
  return term_blk(arr, blk_cls(a), dst);
}

INLINE Term blk_node(Env e, Term l, Term r) {
  Corpus H = e.mem;
  bool arr = term_tag(l) == TAG_ARR;
  Cls c = blk_cls(l);
  if (c != blk_cls(r) || c + 1 >= NCLS_ALL) {
    err_post(H, ERR_TAGS);
    return l;
  }
  Loc pl = term_loc(l);
  Loc pr = term_loc(r);
  BLK_ALLOC(n, arr ? c + 1 : c)
  if (!arr && c == 0) {
    H[n] = (u64)*blk_ptr(H, pl, 0) | ((u64)*blk_ptr(H, pr, 0) << 32);
  } else {
    u64 cw = 1ull << blk_span(l);
    for (u64 w = 0; w < cw; w += 1) {
      H[n + w]      = H[pl + w];
      H[n + cw + w] = H[pr + w];
    }
  }
  blk_free(e, l);
  blk_free(e, r);
  return term_blk(arr, c + 1, n);
}

INLINE Term blk_half(Env e, Term a, u32 hi) {
  Corpus H = e.mem;
  bool arr = term_tag(a) == TAG_ARR;
  Cls c = blk_cls(a);
  if (c == 0) {
    err_post(H, ERR_TAGS);
    return a;
  }
  c -= 1;
  Cls cw = arr ? c : buf_wcls(c);
  BLK_ALLOC(n, cw)
  if (!arr && c == 0) {
    H[n] = (u64)*blk_ptr(H, term_loc(a), hi);
  } else {
    Loc src = term_loc(a) + ((u64)hi << cw);
    for (u64 w = 0; w < (1ull << cw); w += 1) {
      H[n + w] = H[src + w];
    }
  }
  if (hi) {
    blk_free(e, a);
  }
  return term_blk(arr, c, n);
}

INLINE Term blk_new(Env e, bool arr, Nat d, u32 lgs, u32 n, THR Term* v) {
  Corpus H = e.mem;
  if (d + lgs > 31) {
    err_post(H, ERR_ARRS);
    d = 0;
  }
  Cls c = (u32)d + lgs;
  BLK_ALLOC(l, arr ? c : buf_wcls(c))
  for (u32 j = 0; j < n; j += 1) {
    Term w = v[j];
    if (arr && d > 0 && !term_triv(w)) {
      if (d >= 24) {
        err_post(H, ERR_RFCS);
      } else if (term_rfc(w)) {
        rfc_bump(e, term_loc(w), (1u << d) - 1);
      } else {
        w = rfc_wrap(e, w, 1u << d);
      }
    }
    v[j] = w;
  }
  for (u64 i = 0; i < (1ull << c); i += 1) {
    blk_write(H, arr, l, (u32)i, i % (1u << lgs) < n ? v[i % (1u << lgs)] : 0);
  }
  return term_blk(arr, c, l);
}

// String: each descriptor owns one already-counted packed payload, its cells
// 4, 2 or 1 bytes wide: the payload Term's aux holds nar = 0, 1, 2 above the
// class, the narrowest width its content allowed when it was built. A view
// never changes nar; a write of a wider cell reallocates in str_reserve.
// Peek borrows. Take consumes metadata and moves/retains the payload BEFORE
// releasing a shared descriptor. Only taken parts may enter str_writable.
#define STR_LIMIT (1ull << 31)
#define str_nar(p) ((p).data ? (u32)(term_aux((p).data) >> 5) & 3 : 2)
#define str_cap(d) (1ull << (blk_cls(d) + ((term_aux(d) >> 5) & 3)))
typedef struct { Term data; u32 off; u32 len; } StrParts;

INLINE u32 str_fit(u32 c) { return c < 256 ? 2 : c < 65536 ? 1 : 0; }

INLINE StrParts str_peek(Env e, Term s) {
  StrParts p = {0, 0, 0};
  if (term_tag(s) == TAG_STR) {
    Loc l = term_peek(e, s);
    p.data = e.mem[l];
    p.off = (u32)(e.mem[l + 1] >> 32);
    p.len = (u32)e.mem[l + 1];
  }
  return p;
}

INLINE StrParts str_take(Env e, Term s) {
  StrParts p = str_peek(e, s);
  if (p.len) {
    Term data[1];
    Loc l = ctr_take(e, s, 1, data);
    p.data = data[0];
    spare_free(e, 1, l);
  }
  return p;
}

INLINE Term str_view_owned(Env e, StrParts p) {
  if (!p.len || err_seen(e.mem)) {
    term_sink(e, p.data);
    return term_pak(CID_SNIL, 0);
  }
  u64 cap = str_cap(p.data);
  if (cap > STR_LIMIT || p.len > cap || p.off > cap - p.len) {
    err_post(e.mem, ERR_STRS);
    term_sink(e, p.data);
    return term_pak(CID_SNIL, 0);
  }
  Loc l = heap_alloc(e, 1);
  if (err_seen(e.mem)) { term_sink(e, p.data); return term_pak(CID_SNIL, 0); }
  e.mem[l] = p.data;
  e.mem[l + 1] = ((u64)p.off << 32) | p.len;
  return rfc_seal(e, term_make(TAG_STR, CID_SCON, l));
}

INLINE StrParts str_alloc(Env e, u64 n, u32 nar) {
  StrParts p = {0, 0, 0};
  if (!n || err_seen(e.mem)) { return p; }
  if (n > STR_LIMIT) { err_post(e.mem, ERR_STRS); return p; }
  Cls c = cls_fit((u32)((n + (1u << nar) - 1) >> nar));
  Loc l = heap_alloc(e, buf_wcls(c));
  if (err_seen(e.mem)) { return p; }
  // Install the count cell before this payload can escape into metadata.
  p.data = rfc_wrap(e, term_buf(c | nar << 5, l), 1);
  p.len = (u32)n;
  return p;
}

INLINE u32 str_cell(Corpus H, Loc l, u32 nar, u32 i) {
  DEV u8* b = (DEV u8*)(H + l);
  return nar == 2 ? b[i] : nar == 1 ? b[2 * i] | (u32)b[2 * i + 1] << 8
    : *blk_ptr(H, l, i);
}

INLINE void str_cell_put(Corpus H, Loc l, u32 nar, u32 i, u32 c) {
  DEV u8* b = (DEV u8*)(H + l);
  if (nar == 2) { b[i] = (u8)c; }
  else if (nar == 1) { b[2 * i] = (u8)c; b[2 * i + 1] = (u8)(c >> 8); }
  else { *blk_ptr(H, l, i) = c; }
}

INLINE u32 str_at_peek(Env e, StrParts p, u32 i) {
  return str_cell(e.mem, term_peek(e, p.data), str_nar(p), p.off + i);
}

INLINE void str_put(Env e, StrParts p, u32 i, u32 c) {
  str_cell_put(e.mem, term_peek(e, p.data), str_nar(p), p.off + i, c);
}

// Three-part write test: owned private metadata (str_take), dynamic origin,
// and a count of one, observed with the runtime's acquire discipline.
INLINE bool str_writable(Env e, StrParts p) {
  return p.data && term_rfc(p.data) && term_peek(e, p.data) >= HEAP_OFF
    && (rfc_view(e, term_loc(p.data)) & RFC_CNT) == 1;
}

INLINE void str_copy_cells(Env e, StrParts dst, u32 at, StrParts src) {
  if (err_seen(e.mem)) { return; }
  u32 poll = 0;
  Loc from = term_peek(e, src.data), to = term_peek(e, dst.data);
  u32 sn = str_nar(src), dn = str_nar(dst);
  for (u32 i = 0; i < src.len; i++) {
    if (err_spun(e.mem, &poll)) { return; }
    str_cell_put(e.mem, to, dn, dst.off + at + i,
      str_cell(e.mem, from, sn, src.off + i));
  }
}

// Consumes owned parts, copying only their visible range when necessary:
// no room, not writable, or cells narrower than nar, what the write needs.
INLINE StrParts str_reserve(Env e, StrParts p, u64 need, bool front, u32 nar) {
  u64 n = (u64)p.len + need;
  if (n > STR_LIMIT) {
    err_post(e.mem, ERR_STRS);
    term_sink(e, p.data);
    StrParts z = {0, 0, 0}; return z;
  }
  u64 cap = p.data ? str_cap(p.data) : 0;
  if (str_nar(p) < nar) { nar = str_nar(p); }
  if (str_writable(e, p) && str_nar(p) == nar && (front ? p.off >= need
      : cap - p.off - p.len >= need)) { return p; }
  u64 target = (u64)p.len * (need ? 2 : 1);
  if (target < n) { target = n; }
  if (target > STR_LIMIT) { target = STR_LIMIT; }
  StrParts q = str_alloc(e, target, nar);
  if (!err_seen(e.mem) && q.data) {
    q.len = p.len;
    q.off = front ? (u32)(str_cap(q.data) - p.len) : 0;
    str_copy_cells(e, q, 0, p);
  }
  term_sink(e, p.data);
  return q;
}

INLINE Term str_prepend_take(Env e, u32 c, Term s) {
  StrParts p = str_take(e, s);
  // Putting back the cell an uncons just stepped past is a view, not a
  // write: nothing is stored, so a shared or static payload qualifies.
  if (p.data && p.off > 0) {
    StrParts b = {p.data, p.off - 1, p.len + 1};
    if (str_at_peek(e, b, 0) == c) { return str_view_owned(e, b); }
  }
  p = str_reserve(e, p, 1, true, str_fit(c));
  if (err_seen(e.mem)) { return str_view_owned(e, p); }
  p.off--; p.len++;
  str_put(e, p, 0, c);
  return str_view_owned(e, p);
}

INLINE Term str_slice_take(Env e, Term s, u64 lo, u64 hi) {
  StrParts p = str_take(e, s);
  if (lo > p.len) { lo = p.len; }
  if (hi > p.len) { hi = p.len; }
  if (hi < lo) { hi = lo; }
  p.off += (u32)lo;
  p.len = (u32)(hi - lo);
  return str_view_owned(e, p);
}

INLINE void str_uncons(Env e, Term s, THR Term* out) {
  // A heap descriptor with a count of one advances in place: the walk
  // over a token then frees and allocates no descriptor/count pair.
  if (!term_triv(s) && term_rfc(s)) {
    u64 cell = rfc_view(e, term_loc(s));
    Loc l = cell >> 24;
    if ((cell & RFC_CNT) == 1 && (u32)e.mem[l + 1] > 1) {
      StrParts p = {e.mem[l], (u32)(e.mem[l + 1] >> 32), (u32)e.mem[l + 1]};
      out[0] = str_at_peek(e, p, 0);
      e.mem[l + 1] = ((u64)(p.off + 1) << 32) | (p.len - 1);
      out[1] = s;
      return;
    }
  }
  StrParts p = str_take(e, s);
  if (err_seen(e.mem)) { out[0] = 0; out[1] = term_pak(CID_SNIL, 0); return; }
  out[0] = str_at_peek(e, p, 0);
  p.off++; p.len--;
  out[1] = str_view_owned(e, p);
}

INLINE Nat str_length_take(Env e, Term s) {
  Nat n = str_peek(e, s).len;
  term_sink(e, s);
  return n;
}

INLINE Term str_append_take(Env e, Term a, Term b) {
  StrParts q = str_peek(e, b);
  if (!q.len) { term_sink(e, b); return a; }
  if (!str_peek(e, a).len) { term_sink(e, a); return b; }
  StrParts p = str_reserve(e, str_take(e, a), q.len, false, str_nar(q));
  if (!err_seen(e.mem)) {
    str_copy_cells(e, p, p.len, q);
    p.len += q.len;
  }
  term_sink(e, b);
  return str_view_owned(e, p);
}

INLINE Term str_copy_take(Env e, Term s) {
  StrParts p = str_peek(e, s);
  u32 nar = 2, poll = 0;
  for (u32 i = 0; i < p.len && nar > str_nar(p); i++) {
    if (err_spun(e.mem, &poll)) { break; }
    u32 fit = str_fit(str_at_peek(e, p, i));
    if (fit < nar) { nar = fit; }
  }
  StrParts q = str_alloc(e, p.len, nar);
  if (!err_seen(e.mem)) { str_copy_cells(e, q, 0, p); }
  term_sink(e, s);
  return str_view_owned(e, q);
}

// A fresh node of n <= 3 words, its boxed fields already sealed.
INLINE Term str_node(Env e, u32 cid, u32 n, u64 a, u64 b, u64 c) {
  Loc l = heap_alloc(e, cls_fit(n));
  if (err_seen(e.mem)) { return term_pak(CID_NONE, 0); }
  e.mem[l] = a;
  if (n > 1) { e.mem[l + 1] = b; }
  if (n > 2) { e.mem[l + 2] = c; }
  return term_ctr(cid, l);
}

INLINE Term str_get_take(Env e, Term s, Nat n, bool end) {
  StrParts p = str_peek(e, s);
  bool ok = end ? n > 0 && n <= p.len : n < p.len;
  Term c = ok ? term_pak(CID_CHR, str_at_peek(e, p,
    end ? p.len - (u32)n : (u32)n)) : 0;
  term_sink(e, s);
  return ok ? str_node(e, CID_SOME, 1, c, 0, 0) : term_pak(CID_NONE, 0);
}

// Map.bit's 33-bit key protocol: position 33*i says whether cell i exists;
// positions 33*i+1..33*i+32 are its U32 bits, high first. Borrows the key;
// the row hands the original owned key back beside the Bool.
INLINE bool str_bit_peek(Env e, Term s, Nat pos) {
  StrParts p = str_peek(e, s);
  u64 ci = pos / 33, off = pos % 33;
  if (ci >= p.len) { return false; }
  return off == 0 || ((str_at_peek(e, p, (u32)ci) >> (32 - off)) & 1) != 0;
}

INLINE Term str_end_take(Env e, Term s, Nat n, bool take) {
  u64 len = str_peek(e, s).len;
  u64 at = n > len ? 0 : len - n;
  return str_slice_take(e, s, take ? at : 0, take ? len : at);
}

// Borrow both; Cmp is flattened as LT=0, EQ=1, GT=2.
INLINE u32 str_order_peek(Env e, Term a, Term b) {
  StrParts p = str_peek(e, a), q = str_peek(e, b);
  u32 poll = 0, n = p.len < q.len ? p.len : q.len;
  Loc pl = term_peek(e, p.data), ql = term_peek(e, q.data);
  for (u32 i = 0; i < n; i++) {
    if (err_spun(e.mem, &poll)) { return 1; }
    u32 x = str_cell(e.mem, pl, str_nar(p), p.off + i);
    u32 y = str_cell(e.mem, ql, str_nar(q), q.off + i);
    if (x != y) { return x < y ? 0 : 2; }
  }
  return p.len == q.len ? 1 : p.len < q.len ? 0 : 2;
}

INLINE u32 str_order_take(Env e, Term a, Term b) {
  u32 c = str_order_peek(e, a, b);
  term_sink(e, a); term_sink(e, b);
  return c;
}

INLINE bool str_edge_take(Env e, Term s, Term sub, bool end) {
  StrParts p = str_peek(e, s), q = str_peek(e, sub);
  bool ok = q.len <= p.len;
  u32 off = ok && end ? p.len - q.len : 0, poll = 0;
  Loc pl = term_peek(e, p.data), ql = term_peek(e, q.data);
  for (u32 i = 0; ok && i < q.len; i++) {
    if (err_spun(e.mem, &poll)) { ok = false; break; }
    ok = str_cell(e.mem, pl, str_nar(p), p.off + off + i)
      == str_cell(e.mem, ql, str_nar(q), q.off + i);
  }
  term_sink(e, s); term_sink(e, sub);
  return ok;
}

INLINE bool str_space(u32 c) { return c == 32 || (c >= 9 && c <= 13); }

INLINE Term str_trim_take(Env e, Term s, u32 ends) {
  StrParts p = str_peek(e, s);
  u32 lo = 0, hi = p.len, poll = 0;
  Loc l = term_peek(e, p.data);
  while ((ends & 1) && lo < hi && str_space(str_cell(e.mem, l, str_nar(p), p.off + lo))) {
    if (err_spun(e.mem, &poll)) { break; } lo++;
  }
  while ((ends & 2) && hi > lo && str_space(str_cell(e.mem, l, str_nar(p), p.off + hi - 1))) {
    if (err_spun(e.mem, &poll)) { break; } hi--;
  }
  return str_slice_take(e, s, lo, hi);
}

// mode: reverse=0, ASCII upper=1, ASCII lower=2, capitalize=3. Private visible copy
// on shared/static input; bounds changes alone never require a payload copy.
INLINE Term str_transform_take(Env e, Term s, u32 mode) {
  StrParts p = str_take(e, s);
  if (!p.len) { return str_view_owned(e, p); }
  p = str_reserve(e, p, 0, false, 2);
  if (err_seen(e.mem)) { return str_view_owned(e, p); }
  u32 poll = 0;
  for (u32 i = 0; i < (mode ? p.len : p.len / 2); i++) {
    if (err_spun(e.mem, &poll)) { break; }
    u32 c = str_at_peek(e, p, i);
    if (!mode) {
      str_put(e, p, i, str_at_peek(e, p, p.len - 1 - i));
      str_put(e, p, p.len - 1 - i, c);
    } else {
      bool upper = mode == 1 || (mode == 3 && i == 0);
      if (upper && c >= 97 && c <= 122) { c -= 32; }
      else if (!upper && c >= 65 && c <= 90) { c += 32; }
      str_put(e, p, i, c);
    }
  }
  return str_view_owned(e, p);
}

// Generic List fields are boxed. Seal before publishing to a container.
INLINE Term str_cons(Env e, Term h, Term t) {
  Loc l = heap_alloc(e, 1);
  if (err_seen(e.mem)) { term_sink(e, h); term_sink(e, t); return term_pak(CID_NIL, 0); }
  e.mem[l] = rfc_seal(e, h);
  e.mem[l + 1] = rfc_seal(e, t);
  return term_ctr(CID_CON, l);
}

INLINE Term str_to_list_take(Env e, Term s) {
  StrParts p = str_peek(e, s);
  Term out = term_pak(CID_NIL, 0);
  u32 poll = 0;
  for (u32 i = p.len; i > 0; i--) {
    if (err_spun(e.mem, &poll)) { break; }
    out = str_cons(e, term_pak(CID_CHR, str_at_peek(e, p, i - 1)), out);
  }
  term_sink(e, s);
  return out;
}

INLINE Term str_from_list_take(Env e, Term xs) {
  StrParts p = {0, 0, 0};
  u32 poll = 0;
  while (term_aux(xs) == CID_CON) {
    if (err_spun(e.mem, &poll)) { break; }
    Term f[2]; spare_free(e, 1, ctr_take(e, xs, 2, f));
    xs = f[1];
    p = str_reserve(e, p, 1, false, str_fit((u32)term_loc(f[0])));
    if (err_seen(e.mem)) { break; }
    str_put(e, p, p.len, (u32)term_loc(f[0])); p.len++;
  }
  term_sink(e, xs);
  return str_view_owned(e, p);
}

// Split emits views in reverse scan order directly into a forward list.
// words=true skips empty runs; split preserves every empty field.
INLINE Term str_split_take(Env e, Term s, u32 sep, bool words) {
  StrParts p = str_peek(e, s);
  Term out = term_pak(CID_NIL, 0);
  u32 hi = p.len, poll = 0;
  Loc l = term_peek(e, p.data);
  for (u64 j = (u64)p.len + 1; j > 0; j--) {
    if (err_spun(e.mem, &poll)) { break; }
    u32 i = (u32)(j - 1);
    bool cut = i == 0;
    if (!cut) {
      u32 c = str_cell(e.mem, l, str_nar(p), p.off + i - 1);
      cut = words ? str_space(c) : c == sep;
    }
    if (cut) {
      if (!words || hi > i) {
        StrParts q = {term_keep(e, p.data), p.off + i, hi - i};
        out = str_cons(e, str_view_owned(e, q), out);
      }
      hi = i ? i - 1 : 0;
    }
  }
  term_sink(e, s);
  return out;
}

// Bulk construction uses a single destination, including repeat's wide
// pre-multiply check. These also keep deep specimen construction bounded.
INLINE Term str_repeat_take(Env e, Term s, Nat n) {
  StrParts p = str_peek(e, s);
  if (p.len && n > STR_LIMIT / p.len) {
    err_post(e.mem, ERR_STRS); term_sink(e, s); return term_pak(CID_SNIL, 0);
  }
  StrParts q = str_alloc(e, (u64)p.len * n, str_nar(p));
  if (err_seen(e.mem)) { term_sink(e, s); return str_view_owned(e, q); }
  u32 poll = 0;
  for (u64 i = 0; p.len && i < n; i++) {
    if (err_spun(e.mem, &poll)) { break; }
    str_copy_cells(e, q, (u32)(i * p.len), p);
  }
  term_sink(e, s);
  return str_view_owned(e, q);
}

INLINE Term str_join_take(Env e, Term xs, Term sep) {
  StrParts p = {0, 0, 0}, sp = str_peek(e, sep);
  bool first = true;
  u32 poll = 0;
  while (term_aux(xs) == CID_CON) {
    if (err_spun(e.mem, &poll)) { break; }
    Term f[2]; spare_free(e, 1, ctr_take(e, xs, 2, f)); xs = f[1];
    StrParts q = str_peek(e, f[0]);
    u64 add = (u64)q.len + (first ? 0 : sp.len);
    p = str_reserve(e, p, add, false, str_nar(q) < str_nar(sp) || first ? str_nar(q) : str_nar(sp));
    if (!err_seen(e.mem)) {
      if (!first) { str_copy_cells(e, p, p.len, sp); p.len += sp.len; }
      str_copy_cells(e, p, p.len, q); p.len += q.len;
    }
    term_sink(e, f[0]); first = false;
  }
  term_sink(e, xs); term_sink(e, sep);
  return str_view_owned(e, p);
}

// A search cursor borrows text/needle and owns exactly one packed prefix
// table. All consumers close it, including early results and device errors.
// Empty needles are handled by each public contract; one-cell needles and
// needles longer than the text do not allocate a table.
#define STR_ABSENT (~0ull)
typedef struct {
  StrParts text, needle;
  Loc table;
  Cls cls;
  u32 pos, matched, poll;
} StrSearch;

INLINE void str_scratch_free(Env e, Cls cls, Loc l) {
  if (err_seen(e.mem)) {
    // heap_free intentionally stops on a sticky error. This private scratch
    // block has no children: recycle it locally without clearing the error
    // or publishing to the shared bank after a device failure.
    e.mem[l] = ALC_AT(e, cls);
    ALC_AT(e, cls) = l;
    ALC_LEN(e, cls) += 1ull << cls;
  } else {
    heap_free(e, cls, l);
  }
}

INLINE void str_search_close(Env e, THR StrSearch* k) {
  if (k->table) { str_scratch_free(e, k->cls, k->table); k->table = 0; }
}

INLINE StrSearch str_search_open(Env e, StrParts text, StrParts needle) {
  StrSearch k = {text, needle, 0, 0, 0, 0, 0};
  if (needle.len <= 1 || needle.len > text.len || err_seen(e.mem)) { return k; }
  k.cls = buf_wcls(cls_fit(needle.len));
  Loc table = heap_alloc(e, k.cls);
  if (err_seen(e.mem)) { return k; }
  k.table = table;
  blk_write(e.mem, false, table, 0, 0);
  for (u32 i = 1, j = 0; i < needle.len; i++) {
    if (err_spun(e.mem, &k.poll)) { break; }
    u32 c = str_at_peek(e, needle, i);
    while (j && c != str_at_peek(e, needle, j)) {
      if (err_spun(e.mem, &k.poll)) { break; }
      j = (u32)blk_read(e.mem, false, table, j - 1);
    }
    if (err_seen(e.mem)) { break; }
    if (c == str_at_peek(e, needle, j)) { j++; }
    blk_write(e.mem, false, table, i, j);
  }
  return k;
}

INLINE bool str_search_next(Env e, THR StrSearch* k, bool overlap, THR u32* at) {
  if (!k->needle.len || k->needle.len > k->text.len || err_seen(e.mem)) { return false; }
  while (k->pos < k->text.len) {
    if (err_spun(e.mem, &k->poll)) { return false; }
    u32 c = str_at_peek(e, k->text, k->pos++);
    while (k->matched && c != str_at_peek(e, k->needle, k->matched)) {
      if (err_spun(e.mem, &k->poll)) { return false; }
      k->matched = (u32)blk_read(e.mem, false, k->table, k->matched - 1);
    }
    if (c == str_at_peek(e, k->needle, k->matched)) { k->matched++; }
    if (k->matched == k->needle.len) {
      *at = k->pos - k->needle.len;
      k->matched = overlap && k->needle.len > 1
        ? (u32)blk_read(e.mem, false, k->table, k->matched - 1) : 0;
      return true;
    }
  }
  return false;
}

// Consume both inputs. mode: first=0, last overlapping start=1, count=2.
INLINE u64 str_search_take(Env e, Term s, Term needle, u32 mode) {
  StrParts p = str_peek(e, s), q = str_peek(e, needle);
  u64 out = mode == 2 ? 0 : STR_ABSENT;
  if (!q.len) { out = mode == 0 ? 0 : (u64)p.len + (mode == 2); }
  else {
    StrSearch k = str_search_open(e, p, q);
    u32 at;
    while (str_search_next(e, &k, mode == 1, &at)) {
      out = mode == 2 ? out + 1 : at;
      if (mode == 0) { break; }
    }
    str_search_close(e, &k);
  }
  term_sink(e, s); term_sink(e, needle);
  return out;
}

INLINE Term str_find_take(Env e, Term s, Term needle, bool last) {
  u64 at = str_search_take(e, s, needle, last ? 1 : 0);
  if (at == STR_ABSENT || err_seen(e.mem)) { return term_pak(CID_NONE, 0); }
  // Nat is a raw word even in a generic Some payload.
  return str_node(e, CID_SOME, 1, at, 0, 0);
}

// Borrow a range, return an owned zero-copy window (empty never pins).
INLINE Term str_window(Env e, StrParts p, u32 lo, u32 hi) {
  StrParts q = {lo < hi ? term_keep(e, p.data) : 0, p.off + lo, hi - lo};
  return str_view_owned(e, q);
}

// Consumes the destination parts, borrows the source; one growing output.
INLINE void str_push_range(Env e, THR StrParts* out, StrParts p, u32 lo, u32 hi) {
  if (lo == hi || err_seen(e.mem)) { return; }
  p.off += lo; p.len = hi - lo;
  *out = str_reserve(e, *out, p.len, false, str_nar(p));
  if (!err_seen(e.mem)) { str_copy_cells(e, *out, out->len, p); out->len += p.len; }
}

INLINE Term str_replace_take(Env e, Term s, Term old, Term value) {
  StrParts p = str_peek(e, s), q = str_peek(e, old), r = str_peek(e, value);
  StrParts out = {0, 0, 0};
  StrSearch k = str_search_open(e, p, q);
  u32 at = 0, lo = 0, poll = 0;
  // A counting pass sizes the output once: no doubling, no recopying.
  u64 hits = q.len ? 0 : (u64)p.len + 1;
  while (q.len && str_search_next(e, &k, false, &at)) { hits++; }
  k.pos = k.matched = 0;
  out = str_reserve(e, out, p.len + hits * r.len - (q.len ? hits * q.len : 0), false,
    hits && str_nar(r) < str_nar(p) ? str_nar(r) : str_nar(p));
  if (!q.len) {
    for (u64 i = 0; i <= p.len; i++) {
      if (err_spun(e.mem, &poll)) { break; }
      str_push_range(e, &out, r, 0, r.len);
      if (i < p.len) { str_push_range(e, &out, p, (u32)i, (u32)i + 1); }
    }
  } else {
    while (str_search_next(e, &k, false, &at)) {
      str_push_range(e, &out, p, lo, at);
      str_push_range(e, &out, r, 0, r.len);
      lo = at + q.len;
    }
    str_push_range(e, &out, p, lo, p.len);
  }
  str_search_close(e, &k);
  term_sink(e, s); term_sink(e, old); term_sink(e, value);
  return str_view_owned(e, out);
}

// Owns a private forward list during construction; seal every link before
// publication. Consumes field, mutates only fresh unaliased list metadata.
INLINE void str_list_push(Env e, THR Term* out, THR Loc* tail, Term field) {
  if (err_seen(e.mem)) { term_sink(e, field); return; }
  Term node = rfc_seal(e, str_cons(e, field, term_pak(CID_NIL, 0)));
  if (err_seen(e.mem)) { term_sink(e, node); return; }
  if (*tail) { e.mem[*tail] = node; } else { *out = node; }
  *tail = term_peek(e, node) + 1;
}

INLINE Term str_split_on_take(Env e, Term s, Term sep) {
  StrParts p = str_peek(e, s), q = str_peek(e, sep);
  Term out = term_pak(CID_NIL, 0);
  Loc tail = 0;
  StrSearch k = str_search_open(e, p, q);
  u32 at, lo = 0;
  while (str_search_next(e, &k, false, &at)) {
    str_list_push(e, &out, &tail, str_window(e, p, lo, at));
    lo = at + q.len;
  }
  if (!err_seen(e.mem)) { str_list_push(e, &out, &tail, str_window(e, p, lo, p.len)); }
  str_search_close(e, &k);
  term_sink(e, s); term_sink(e, sep);
  return out;
}

// Own both fields; nested tuple payloads obey the same sealing protocol.
INLINE Term str_pair(Env e, Term a, Term b) {
  if (err_seen(e.mem)) { term_sink(e, a); term_sink(e, b); return 0; }
  Loc l = heap_alloc(e, 1);
  if (err_seen(e.mem)) { term_sink(e, a); term_sink(e, b); return 0; }
  e.mem[l] = rfc_seal(e, a); e.mem[l + 1] = rfc_seal(e, b);
  return term_ctr(CID_TUPLE, l);
}

INLINE Term str_partition_take(Env e, Term s, Term sep) {
  StrParts p = str_peek(e, s), q = str_peek(e, sep);
  StrSearch k = str_search_open(e, p, q);
  u32 at;
  bool found = str_search_next(e, &k, false, &at);
  str_search_close(e, &k);
  Term a = s, b = term_pak(CID_SNIL, 0), c = b;
  if (found) {
    a = str_window(e, p, 0, at); b = sep;
    c = str_window(e, p, at + q.len, p.len);
    term_sink(e, s);
  } else { term_sink(e, sep); }
  return str_pair(e, a, str_pair(e, b, c));
}

INLINE bool str_line_break(u32 c) {
  return (c >= 10 && c <= 13) || (c >= 28 && c <= 30)
    || c == 133 || c == 8232 || c == 8233;
}

INLINE Term str_splitlines_take(Env e, Term s) {
  StrParts p = str_peek(e, s);
  Term out = term_pak(CID_NIL, 0);
  Loc tail = 0;
  u32 lo = 0, poll = 0;
  for (u32 i = 0; i < p.len; i++) {
    if (err_spun(e.mem, &poll)) { break; }
    u32 c = str_at_peek(e, p, i);
    if (str_line_break(c)) {
      str_list_push(e, &out, &tail, str_window(e, p, lo, i));
      if (c == 13 && i + 1 < p.len && str_at_peek(e, p, i + 1) == 10) { i++; }
      lo = i + 1;
    }
  }
  if (lo < p.len && !err_seen(e.mem)) { str_list_push(e, &out, &tail, str_window(e, p, lo, p.len)); }
  term_sink(e, s);
  return out;
}

// Consume s; raw U32 fill values are ordinary cells. mode: start=0, end=1,
// sign-aware zero fill=2. Widen/check before narrowing or subtracting.
INLINE Term str_pad_take(Env e, Term s, Nat width, u32 c, u32 mode) {
  u32 len = str_peek(e, s).len;
  if (width <= len) { return s; }
  if (width > STR_LIMIT) { err_post(e.mem, ERR_STRS); term_sink(e, s); return term_pak(CID_SNIL, 0); }
  u32 n = (u32)(width - len);
  StrParts p = str_reserve(e, str_take(e, s), n, mode != 1, str_fit(c));
  if (err_seen(e.mem)) { return str_view_owned(e, p); }
  u32 sign = 0, first = len ? str_at_peek(e, p, 0) : 0;
  if (mode == 2 && (first == '+' || first == '-')) { sign = 1; }
  if (mode != 1) { p.off -= n; }
  p.len = (u32)width;
  u32 start = mode == 1 ? len : sign, poll = 0;
  if (sign) { str_put(e, p, 0, first); }
  for (u32 i = 0; i < n; i++) {
    if (err_spun(e.mem, &poll)) { break; }
    str_put(e, p, start + i, c);
  }
  return str_view_owned(e, p);
}

INLINE u32 str_hash_take(Env e, Term s) {
  StrParts p = str_peek(e, s);
  u32 h = 2166136261u, poll = 0;
  for (u32 i = 0; i < p.len; i++) {
    if (err_spun(e.mem, &poll)) { break; }
    u32 c = str_at_peek(e, p, i);
    for (u32 shift = 0; shift < 32; shift += 8) { h = (h ^ ((c >> shift) & 255)) * 16777619u; }
  }
  term_sink(e, s);
  return h;
}

// Regex
// =====

// The Pike VM of base (Regex.exec.go, full and ne off): its priorities, its
// dead threads (a pc or a slot out of range), so a forged Regex never
// faults. One scratch block per call: the program packed op:8|a:24|b:24 (an
// IChr keeps its 32 bits in a:b), the set ranges lo|hi<<32, a visited row
// stamped by generation (never cleared per step), the raw and the closed
// thread banks (a pc row and a slot row each), the current and the best
// slots, the closure stack (a visited pc nets <= 2 words: 2m + 1 deep). A slot is a
// position, RE_NONE unset; RE_NONE is also the char before 0 and at the end.
#define RE_NONE (~0ull)
#define RE_DEAD 0xFFFFFFu
#define RE_CHR   0
#define RE_ANY   1
#define RE_SET   2
#define RE_NSET  3
#define RE_SPLIT 4
#define RE_JMP   5
#define RE_SAVE  6
#define RE_BOL   7
#define RE_EOL   8
#define RE_WORDB 9
#define RE_MATCH 10
#define re_ins(op, a, b) ((u64)(op) << 48 | (u64)(a) << 24 | (u64)(b))
#define re_arg(n, m) ((n) < (m) ? (u64)(n) : (u64)RE_DEAD)

INLINE bool re_word(u64 c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || c == 95
    || (c >= 97 && c <= 122);
}

INLINE void re_copy(Env e, Loc dst, Loc src, u64 n) {
  for (u64 j = 0; j < n; j++) { e.mem[dst + j] = e.mem[src + j]; }
}

// Consumes prog and s; returns a boxed Maybe<Match>.
INLINE Term re_exec_take(Env e, Term prog, u64 ng, Term s, u64 at, bool anchored) {
  StrParts p = str_peek(e, s);
  Term out = term_pak(CID_NONE, 0);
  u64 m = 0, sets = 0, len = p.len, ns = 2 * (1 + ng);
  u32 poll = 0;
  for (Term t = prog; term_aux(t) == CID_CON; m++) {
    if (err_spun(e.mem, &poll)) { break; }
    Loc l = term_peek(e, t);
    Term h = e.mem[l];
    t = e.mem[l + 1];
    if (term_aux(h) != CID_ISET) { continue; }
    for (Term r = e.mem[term_peek(e, h) + 1]; term_aux(r) == CID_CON; sets++) {
      r = e.mem[term_peek(e, r) + 1];
    }
  }
  u64 words = 6 * m + sets + 2 * m * (1 + ns) + 2 * ns + 2;
  if (m >= RE_DEAD || sets >= RE_DEAD || ng >= 1u << 22 || words > STR_LIMIT) {
    err_post(e.mem, ERR_HEAP);
  }
  Cls cls = cls_fit((u32)words);
  Loc P = err_seen(e.mem) ? 0 : heap_alloc(e, cls);
  if (err_seen(e.mem)) { term_sink(e, prog); term_sink(e, s); return out; }
  Loc S = P + m, V = S + sets, RP = V + m, RS = RP + m, CP = RS + m * ns;
  Loc CS = CP + m, CUR = CS + m * ns, BEST = CUR + ns, STK = BEST + ns;
  u64 i = 0, k = 0;
  for (Term t = prog; term_aux(t) == CID_CON; i++) {
    if (err_spun(e.mem, &poll)) { break; }
    Loc l = term_peek(e, t);
    Term h = e.mem[l];
    t = e.mem[l + 1];
    u64 c = term_aux(h), w = re_ins(RE_MATCH, 0, 0);
    Loc f = c == CID_ISET || c == CID_ISPLIT || c == CID_IJMP || c == CID_ISAVE
      ? term_peek(e, h) : 0;
    if (c == CID_ICHR) { w = re_ins(RE_CHR, 0, 0) | (u32)term_loc(h); }
    else if (c == CID_IANY) { w = re_ins(RE_ANY, 0, 0); }
    else if (c == CID_ISPLIT) { w = re_ins(RE_SPLIT, re_arg(e.mem[f], m), re_arg(e.mem[f + 1], m)); }
    else if (c == CID_IJMP) { w = re_ins(RE_JMP, re_arg(e.mem[f], m), 0); }
    else if (c == CID_ISAVE) { w = re_ins(RE_SAVE, re_arg(e.mem[f], ns), 0); }
    else if (c == CID_IBOL) { w = re_ins(RE_BOL, term_loc(h) & 1, 0); }
    else if (c == CID_IEOL) { w = re_ins(RE_EOL, term_loc(h) & 1, 0); }
    else if (c == CID_IWORDB) { w = re_ins(RE_WORDB, term_loc(h) & 1, 0); }
    else if (c == CID_ISET) {
      u64 k0 = k;
      for (Term r = e.mem[f + 1]; term_aux(r) == CID_CON; k++) {
        Loc q = term_peek(e, r), u = term_peek(e, e.mem[q]);
        e.mem[S + k] = (u64)(u32)e.mem[u] | (u64)(u32)e.mem[u + 1] << 32;
        r = e.mem[q + 1];
      }
      w = re_ins(e.mem[f] & 1 ? RE_NSET : RE_SET, k0, k - k0);
    }
    e.mem[P + i] = w;
    e.mem[V + i] = 0;
  }
  if (at > len) { at = len; }
  u64 nraw = 0, best = 0;
  u64 prev = at ? str_at_peek(e, p, (u32)at - 1) : RE_NONE;
  for (u64 pos = at; !err_seen(e.mem); pos++) {
    u64 fresh = !best && (pos == at || !anchored), gen = pos - at + 1, ncl = 0;
    if (nraw + fresh == 0) { break; }
    u64 c = pos < len ? str_at_peek(e, p, (u32)pos) : RE_NONE;
    for (u64 r = 0; r < nraw + fresh; r++) {
      if (r < nraw) { re_copy(e, CUR, RS + r * ns, ns); }
      else { for (u64 j = 0; j < ns; j++) { e.mem[CUR + j] = RE_NONE; } }
      u64 sp = 1;
      e.mem[STK] = r < nraw ? e.mem[RP + r] : 0;
      while (sp) {
        if (err_spun(e.mem, &poll)) { break; }
        u64 x = e.mem[STK + --sp];
        if (x >> 63) { e.mem[CUR + (u32)x] = e.mem[STK + --sp]; continue; }
        if (x >= m || e.mem[V + x] == gen) { continue; }
        e.mem[V + x] = gen;
        u64 w = e.mem[P + x];
        u32 op = (u32)(w >> 48), a = (u32)(w >> 24) & RE_DEAD, b = (u32)w & RE_DEAD;
        bool go = false;
        if (op == RE_SPLIT) { e.mem[STK + sp++] = b; e.mem[STK + sp++] = a; }
        else if (op == RE_JMP) { e.mem[STK + sp++] = a; }
        else if (op == RE_SAVE) {
          if (a < ns) {
            e.mem[STK + sp++] = e.mem[CUR + a];
            e.mem[STK + sp++] = 1ull << 63 | a;
            e.mem[CUR + a] = pos;
            go = true;
          }
        }
        else if (op == RE_BOL) { go = pos == 0 || (a && prev == 10); }
        else if (op == RE_EOL) { go = c == RE_NONE || (c == 10 && (a || pos + 1 == len)); }
        else if (op == RE_WORDB) { go = (pos || len) && (a != 0) != (re_word(prev) != re_word(c)); }
        else { e.mem[CP + ncl] = x; re_copy(e, CS + ncl++ * ns, CUR, ns); }
        if (go) { e.mem[STK + sp++] = x + 1; }
      }
    }
    nraw = 0;
    for (u64 t = 0; t < ncl; t++) {
      u64 x = e.mem[CP + t], w = e.mem[P + x];
      u32 op = (u32)(w >> 48), a = (u32)(w >> 24) & RE_DEAD, b = (u32)w & RE_DEAD;
      if (op == RE_MATCH) { re_copy(e, BEST, CS + t * ns, ns); best = 1; break; }
      bool eat = op == RE_CHR ? (u32)w == c : op == RE_ANY ? c != 10 : false;
      if (op == RE_SET || op == RE_NSET) {
        for (u64 j = 0; j < b && !eat; j++) {
          u64 r = e.mem[S + a + j];
          eat = (u32)r <= c && c <= r >> 32;
        }
        eat = eat != (op == RE_NSET);
      }
      if (eat && c != RE_NONE) {
        e.mem[RP + nraw] = x + 1;
        re_copy(e, RS + nraw++ * ns, CS + t * ns, ns);
      }
    }
    prev = c;
    if (c == RE_NONE) { break; }
  }
  u64 lo = e.mem[BEST], hi = e.mem[BEST + 1];
  if (best && lo != RE_NONE && hi != RE_NONE && !err_seen(e.mem)) {
    Term gs = term_pak(CID_NIL, 0);
    for (u64 g = ng; g > 0; g--) {
      u64 a = e.mem[BEST + 2 * g], b = e.mem[BEST + 2 * g + 1];
      Term f = term_pak(CID_NONE, 0);
      if (a != RE_NONE && b != RE_NONE) {
        f = str_node(e, CID_SOME, 1, rfc_seal(e, str_node(e, CID_TUPLE, 2, a, b, 0)), 0, 0);
      }
      gs = str_cons(e, f, gs);
    }
    out = str_node(e, CID_SOME, 1,
      rfc_seal(e, str_node(e, CID_MATCH, 3, lo, hi, rfc_seal(e, gs))), 0, 0);
  }
  str_scratch_free(e, cls, P);
  term_sink(e, prog); term_sink(e, s);
  return out;
}

// Ring
// ====

// planes LANES wide: a smaller bag has deeper rings in the same region
#define ring_word(H, r, w) ((H) + RING_OFF + (w) * LANES + (r))
#define ring_slot(H, r, p) ring_word(H, r, (p) & (RING_LEN - 1))
#define ring_get(H, r)     ((DEV u32*)ring_word(H, r, RING_LEN))
#define ring_put(H, r)     ((DEV u32*)ring_word(H, r, RING_LEN + 1))

INLINE u32 ring_lap(u32 pos) {
  return ~(u32)(pos / RING_LEN) & 1;
}

INLINE void ring_push(Corpus H, Ring r, Term tsk) {
  u32 pos = a32_add(ring_put(H, r), 1);
  if (pos - a32_load(ring_get(H, r)) >= RING_LEN) {
    err_post(H, ERR_RING);
    return;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, r, pos);
  a32_store(lo, (u32)tsk);
  a32_store_rel(lo + 1, (u32)(tsk >> 32) | (ring_lap(pos) << 31));
}

INLINE Ring ring_flip(u32 i) {
  return (i % CUBE_T << CUBE_LOG) + i / CUBE_T;
}

#define ring_pick(b, s, c) ((b) + (s) * (g32_add(c, 1) & (CUBE_T - 1)))

// Task
// ====

INLINE Loc task_node(Env e, Fid fid, Term cont, u32 idx, u32 rem) {
  u32 ar  = fid_arity(fid);
  Loc loc = heap_alloc(e, cls_fit(ar + 2));
  for (u32 i = 0; rem && i < ar; i += 1) {
    e.mem[loc + i] = TERM_HOLE;
  }
  e.mem[loc + ar]     = cont;
  e.mem[loc + ar + 1] = ((u64)idx << 32) | rem;
  return loc;
}

INLINE Loc task_tail(Term t) {
  return term_loc(t) + fid_arity((u32)term_aux(t));
}

INLINE Term task_deliver(Corpus H, Term cont, u32 idx, THR Term* v, u32 n) {
  Loc at = cont == TERM_HOLE ? H_ROOT_WORD : term_loc(cont) + idx;
  for (u32 j = 0; j < WL_RESW; j += 1) {
    if (j < n) {
      H[at + j] = v[j];
    }
  }
  if (cont == TERM_HOLE) {
    a32_store_rel(a32_at(H, H_ROOT_DONE), n + 1);
    return 0;
  }
  Loc tl = task_tail(cont);
  if (a32_sub_rel(a32_at(H, tl + 1), 1) == 1) {
    a32_acq(a32_at(H, tl + 1));
    return cont;
  }
  return 0;
}

INLINE void task_deal(Corpus H, Term join, u32 base, u32 stride, Cur cur) {
  Loc loc = term_loc(join);
  u32 ar  = fid_arity((u32)term_aux(join));
  u32 g   = 0;
  if (stride == 0) {
    u32 rem = (u32)H[loc + ar + 1];
    g = a32_add(a32_at(H, H_CURSOR), rem);
  }
  for (u32 i = 0; i < ar; i += 1) {
    Term k = H[loc + i];
    if (term_tag(k) == TAG_TSK) {
      H[loc + i] = TERM_HOLE;
      Ring to;
      if (stride != 0) {
        to = ring_pick(base, stride, cur);
      } else {
        to = ring_flip(g & (u32)(LANES - 1));
        g += 1;
      }
      ring_push(H, to, k);
    }
  }
}

// Root
// ====

INLINE bool root_done(Corpus H) {
  return a32_load_acq(a32_at(H, H_ROOT_DONE)) != 0;
}

static u32 root_take(Corpus H, THR Term* v) {
  u32 n = a32_load_acq(a32_at(H, H_ROOT_DONE)) - 1;
  for (u32 j = 0; j < n; j += 1) {
    v[j] = H[H_ROOT_WORD + j];
  }
  a32_store(a32_at(H, H_ROOT_DONE), 0);
  return n;
}

// Spins
// =====

CONSTV u64 STAT_IMG[] = { 138418548329ull, term_buf(65, STAT_OFF + 0), 5ull, 10ull, term_buf(64, STAT_OFF + 3), 1ull, 2889852725834068ull, term_buf(65, STAT_OFF + 6), 7ull };

INLINE Term spin_0(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  u32 v_4 = 0;
  Term v_5 = 0;
  Term qr_0 = r0;
  Term qr_1 = r1;
  WL_SPIN
    v_4 = ((u64)(u32)(nat_chk(e, 48ull + qr_1)));
    v_5 = qr_0;
  break;
  }
  o[0] = v_4;
  o[1] = v_5;
  return 1;
}

// Work
// ====

// A host self-jump is a tail call: as a loop, MachineLICM hoisted eleven
// constants into symreg's entry (3.05 s against 2.51 s).
#if !DEVICE
#undef  WL_SPIN
#undef  WL_SPUN
#undef  WL_AGAIN
#define WL_SPIN
#define WL_SPUN
#define WL_AGAIN(F) __attribute__((musttail)) return WL_##F(WL_ALL)

typedef Reply (PRESERVE(preserve_none) *WlFn)(WL_SIG);
#define WL_X(F) WL_FN WL_##F(WL_SIG);
WL_TABLE WL_X(FID_ENTER)
#undef WL_X
#define WL_X(F) WL_##F,
static const WlFn wl_tab[] = { WL_TABLE };
#undef WL_X
#endif

static Reply work_loop(Env e, Stk sp, Term t, bool seq) {
  WL_BANK
  u32 rn = 0;
  r0 = t;
#if DEVICE
  Fid fid   = FID_ENTER;
  u32 wpoll = 0;
  for (;;) {
  if (err_spun(e.mem, &wpoll)) {
    return 0;
  }
  switch (fid) {
#else
  return WL_FID_ENTER(WL_ALL);
}
#endif

// Segments
// ========

#if !DEVICE
  WL_CASE(FID_WORD_TO_NAT)
  {
    Term n_0 = r0;
    Term w_0 = r1;
    WL_OPEN
    WL_SPIN
    if (n_0 == 0) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term p_0 = (n_0 - 1);
      u64 sp_0 = term_loc(w_0);
      u32 f_0 = e.mem[sp_0 + 0];
      Term f_1 = e.mem[sp_0 + 1];
      heap_free(e, cls_fit(2), sp_0);
      if (f_0 == 0) {
        if (seq) {
          WL_ROOM(1);
          STK(0) = FID_WORD_TO_NAT_K2;
          WL_PUSHN(1);
        } else {
          u64 t_0 = task_node(e, FID_WORD_TO_NAT_K2, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_WORD_TO_NAT_K2, t_0);
          WL_IDX = 0;
        }
        r0 = p_0;
        r1 = f_1;
        n_0 = r0;
        w_0 = r1;
        WL_AGAIN(FID_WORD_TO_NAT);
      } else {
        if (seq) {
          WL_ROOM(1);
          STK(0) = FID_WORD_TO_NAT_K3;
          WL_PUSHN(1);
        } else {
          u64 t_1 = task_node(e, FID_WORD_TO_NAT_K3, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_WORD_TO_NAT_K3, t_1);
          WL_IDX = 0;
        }
        r0 = p_0;
        r1 = f_1;
        n_0 = r0;
        w_0 = r1;
        WL_AGAIN(FID_WORD_TO_NAT);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_WORD_TO_NAT_K2)
  {
    Term h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, h_0 + h_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_WORD_TO_NAT_K3)
  {
    Term h_1 = r0;
    WL_OPEN
    r0 = nat_chk(e, nat_chk(e, h_1 + h_1) + 1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_NAT_SHOW_FIN)
  {
    Term g_0 = r0;
    Term acc_0 = r1;
    u32 dq_0 = r2;
    Term dq_1 = r3;
    WL_OPEN
    WL_SPIN
    if (dq_1 == 0) {
      r0 = str_prepend_take(e, dq_0, acc_0);
      WL_RETN(1);
    } else {
      Term p_0 = (dq_1 - 1);
      if (g_0 == 0) {
        Term n_0 = nat_chk(e, p_0 + 1);
        Term acc_1 = str_prepend_take(e, dq_0, acc_0);
        r0 = acc_1;
        WL_RETN(1);
      } else {
        Term g_1 = (g_0 - 1);
        Term n_1 = nat_chk(e, p_0 + 1);
        Term acc_2 = str_prepend_take(e, dq_0, acc_0);
        u32 v_0 = 0;
        Term v_1 = 0;
        Term a_0 = 10ull;
        Term a_1 = (a_0 == 0 ? 0 : n_1 / a_0);
        Term a_2 = (a_0 == 0 ? n_1 : n_1 % a_0);
        u32 v_2 = 0;
        Term v_3 = 0;
        Term o_0[2];
        if (spin_0(e, o_0, a_1, a_2) == 0) {
          return 0;
        }
        v_2 = o_0[0];
        v_3 = o_0[1];
        v_0 = v_2;
        v_1 = v_3;
        r0 = g_1;
        r1 = acc_2;
        r2 = v_0;
        r3 = v_1;
        g_0 = r0;
        acc_0 = r1;
        dq_0 = r2;
        dq_1 = r3;
        WL_AGAIN(FID_NAT_SHOW_FIN);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_SHOW)
  {
    Term a_0 = r0;
    WL_OPEN
    u32 s_0 = ((a_0 >> 0) & 1);
    u32 s_1 = ((a_0 >> 1) & 1);
    u32 s_2 = ((a_0 >> 2) & 1);
    u32 s_3 = ((a_0 >> 3) & 1);
    u32 s_4 = ((a_0 >> 4) & 1);
    u32 s_5 = ((a_0 >> 5) & 1);
    u32 s_6 = ((a_0 >> 6) & 1);
    u32 s_7 = ((a_0 >> 7) & 1);
    u32 s_8 = ((a_0 >> 8) & 1);
    u32 s_9 = ((a_0 >> 9) & 1);
    u32 s_10 = ((a_0 >> 10) & 1);
    u32 s_11 = ((a_0 >> 11) & 1);
    u32 s_12 = ((a_0 >> 12) & 1);
    u32 s_13 = ((a_0 >> 13) & 1);
    u32 s_14 = ((a_0 >> 14) & 1);
    u32 s_15 = ((a_0 >> 15) & 1);
    u32 s_16 = ((a_0 >> 16) & 1);
    u32 s_17 = ((a_0 >> 17) & 1);
    u32 s_18 = ((a_0 >> 18) & 1);
    u32 s_19 = ((a_0 >> 19) & 1);
    u32 s_20 = ((a_0 >> 20) & 1);
    u32 s_21 = ((a_0 >> 21) & 1);
    u32 s_22 = ((a_0 >> 22) & 1);
    u32 s_23 = ((a_0 >> 23) & 1);
    u32 s_24 = ((a_0 >> 24) & 1);
    u32 s_25 = ((a_0 >> 25) & 1);
    u32 s_26 = ((a_0 >> 26) & 1);
    u32 s_27 = ((a_0 >> 27) & 1);
    u32 s_28 = ((a_0 >> 28) & 1);
    u32 s_29 = ((a_0 >> 29) & 1);
    u32 s_30 = ((a_0 >> 30) & 1);
    u32 s_31 = ((a_0 >> 31) & 1);
    u32 s_32 = ((a_0 >> 32) & 1);
    u32 s_33 = ((a_0 >> 33) & 1);
    u32 s_34 = ((a_0 >> 34) & 1);
    u32 s_35 = ((a_0 >> 35) & 1);
    u32 s_36 = ((a_0 >> 36) & 1);
    u32 s_37 = ((a_0 >> 37) & 1);
    u32 s_38 = ((a_0 >> 38) & 1);
    u32 s_39 = ((a_0 >> 39) & 1);
    u32 s_40 = ((a_0 >> 40) & 1);
    u32 s_41 = ((a_0 >> 41) & 1);
    u32 s_42 = ((a_0 >> 42) & 1);
    u32 s_43 = ((a_0 >> 43) & 1);
    u32 s_44 = ((a_0 >> 44) & 1);
    u32 s_45 = ((a_0 >> 45) & 1);
    u32 s_46 = ((a_0 >> 46) & 1);
    u32 s_47 = ((a_0 >> 47) & 1);
    u32 s_48 = ((a_0 >> 48) & 1);
    u32 s_49 = ((a_0 >> 49) & 1);
    u32 s_50 = ((a_0 >> 50) & 1);
    u32 s_51 = ((a_0 >> 51) & 1);
    u32 s_52 = ((a_0 >> 52) & 1);
    u32 s_53 = ((a_0 >> 53) & 1);
    u32 s_54 = ((a_0 >> 54) & 1);
    u32 s_55 = ((a_0 >> 55) & 1);
    u32 s_56 = ((a_0 >> 56) & 1);
    u32 s_57 = ((a_0 >> 57) & 1);
    u32 s_58 = ((a_0 >> 58) & 1);
    u32 s_59 = ((a_0 >> 59) & 1);
    u32 s_60 = ((a_0 >> 60) & 1);
    u32 s_61 = ((a_0 >> 61) & 1);
    u32 s_62 = ((a_0 >> 62) & 1);
    u32 s_63 = ((a_0 >> 63) & 1);
    u64 nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[nd_0 + 0] = s_63;
    e.mem[nd_0 + 1] = term_pak(CID_WNIL, 0);
    u64 nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[nd_1 + 0] = s_62;
    e.mem[nd_1 + 1] = term_ctr(CID_WCON, nd_0);
    u64 nd_2 = heap_alloc(e, cls_fit(2));
    e.mem[nd_2 + 0] = s_61;
    e.mem[nd_2 + 1] = term_ctr(CID_WCON, nd_1);
    u64 nd_3 = heap_alloc(e, cls_fit(2));
    e.mem[nd_3 + 0] = s_60;
    e.mem[nd_3 + 1] = term_ctr(CID_WCON, nd_2);
    u64 nd_4 = heap_alloc(e, cls_fit(2));
    e.mem[nd_4 + 0] = s_59;
    e.mem[nd_4 + 1] = term_ctr(CID_WCON, nd_3);
    u64 nd_5 = heap_alloc(e, cls_fit(2));
    e.mem[nd_5 + 0] = s_58;
    e.mem[nd_5 + 1] = term_ctr(CID_WCON, nd_4);
    u64 nd_6 = heap_alloc(e, cls_fit(2));
    e.mem[nd_6 + 0] = s_57;
    e.mem[nd_6 + 1] = term_ctr(CID_WCON, nd_5);
    u64 nd_7 = heap_alloc(e, cls_fit(2));
    e.mem[nd_7 + 0] = s_56;
    e.mem[nd_7 + 1] = term_ctr(CID_WCON, nd_6);
    u64 nd_8 = heap_alloc(e, cls_fit(2));
    e.mem[nd_8 + 0] = s_55;
    e.mem[nd_8 + 1] = term_ctr(CID_WCON, nd_7);
    u64 nd_9 = heap_alloc(e, cls_fit(2));
    e.mem[nd_9 + 0] = s_54;
    e.mem[nd_9 + 1] = term_ctr(CID_WCON, nd_8);
    u64 nd_10 = heap_alloc(e, cls_fit(2));
    e.mem[nd_10 + 0] = s_53;
    e.mem[nd_10 + 1] = term_ctr(CID_WCON, nd_9);
    u64 nd_11 = heap_alloc(e, cls_fit(2));
    e.mem[nd_11 + 0] = s_52;
    e.mem[nd_11 + 1] = term_ctr(CID_WCON, nd_10);
    u64 nd_12 = heap_alloc(e, cls_fit(2));
    e.mem[nd_12 + 0] = s_51;
    e.mem[nd_12 + 1] = term_ctr(CID_WCON, nd_11);
    u64 nd_13 = heap_alloc(e, cls_fit(2));
    e.mem[nd_13 + 0] = s_50;
    e.mem[nd_13 + 1] = term_ctr(CID_WCON, nd_12);
    u64 nd_14 = heap_alloc(e, cls_fit(2));
    e.mem[nd_14 + 0] = s_49;
    e.mem[nd_14 + 1] = term_ctr(CID_WCON, nd_13);
    u64 nd_15 = heap_alloc(e, cls_fit(2));
    e.mem[nd_15 + 0] = s_48;
    e.mem[nd_15 + 1] = term_ctr(CID_WCON, nd_14);
    u64 nd_16 = heap_alloc(e, cls_fit(2));
    e.mem[nd_16 + 0] = s_47;
    e.mem[nd_16 + 1] = term_ctr(CID_WCON, nd_15);
    u64 nd_17 = heap_alloc(e, cls_fit(2));
    e.mem[nd_17 + 0] = s_46;
    e.mem[nd_17 + 1] = term_ctr(CID_WCON, nd_16);
    u64 nd_18 = heap_alloc(e, cls_fit(2));
    e.mem[nd_18 + 0] = s_45;
    e.mem[nd_18 + 1] = term_ctr(CID_WCON, nd_17);
    u64 nd_19 = heap_alloc(e, cls_fit(2));
    e.mem[nd_19 + 0] = s_44;
    e.mem[nd_19 + 1] = term_ctr(CID_WCON, nd_18);
    u64 nd_20 = heap_alloc(e, cls_fit(2));
    e.mem[nd_20 + 0] = s_43;
    e.mem[nd_20 + 1] = term_ctr(CID_WCON, nd_19);
    u64 nd_21 = heap_alloc(e, cls_fit(2));
    e.mem[nd_21 + 0] = s_42;
    e.mem[nd_21 + 1] = term_ctr(CID_WCON, nd_20);
    u64 nd_22 = heap_alloc(e, cls_fit(2));
    e.mem[nd_22 + 0] = s_41;
    e.mem[nd_22 + 1] = term_ctr(CID_WCON, nd_21);
    u64 nd_23 = heap_alloc(e, cls_fit(2));
    e.mem[nd_23 + 0] = s_40;
    e.mem[nd_23 + 1] = term_ctr(CID_WCON, nd_22);
    u64 nd_24 = heap_alloc(e, cls_fit(2));
    e.mem[nd_24 + 0] = s_39;
    e.mem[nd_24 + 1] = term_ctr(CID_WCON, nd_23);
    u64 nd_25 = heap_alloc(e, cls_fit(2));
    e.mem[nd_25 + 0] = s_38;
    e.mem[nd_25 + 1] = term_ctr(CID_WCON, nd_24);
    u64 nd_26 = heap_alloc(e, cls_fit(2));
    e.mem[nd_26 + 0] = s_37;
    e.mem[nd_26 + 1] = term_ctr(CID_WCON, nd_25);
    u64 nd_27 = heap_alloc(e, cls_fit(2));
    e.mem[nd_27 + 0] = s_36;
    e.mem[nd_27 + 1] = term_ctr(CID_WCON, nd_26);
    u64 nd_28 = heap_alloc(e, cls_fit(2));
    e.mem[nd_28 + 0] = s_35;
    e.mem[nd_28 + 1] = term_ctr(CID_WCON, nd_27);
    u64 nd_29 = heap_alloc(e, cls_fit(2));
    e.mem[nd_29 + 0] = s_34;
    e.mem[nd_29 + 1] = term_ctr(CID_WCON, nd_28);
    u64 nd_30 = heap_alloc(e, cls_fit(2));
    e.mem[nd_30 + 0] = s_33;
    e.mem[nd_30 + 1] = term_ctr(CID_WCON, nd_29);
    u64 nd_31 = heap_alloc(e, cls_fit(2));
    e.mem[nd_31 + 0] = s_32;
    e.mem[nd_31 + 1] = term_ctr(CID_WCON, nd_30);
    u64 nd_32 = heap_alloc(e, cls_fit(2));
    e.mem[nd_32 + 0] = s_31;
    e.mem[nd_32 + 1] = term_ctr(CID_WCON, nd_31);
    u64 nd_33 = heap_alloc(e, cls_fit(2));
    e.mem[nd_33 + 0] = s_30;
    e.mem[nd_33 + 1] = term_ctr(CID_WCON, nd_32);
    u64 nd_34 = heap_alloc(e, cls_fit(2));
    e.mem[nd_34 + 0] = s_29;
    e.mem[nd_34 + 1] = term_ctr(CID_WCON, nd_33);
    u64 nd_35 = heap_alloc(e, cls_fit(2));
    e.mem[nd_35 + 0] = s_28;
    e.mem[nd_35 + 1] = term_ctr(CID_WCON, nd_34);
    u64 nd_36 = heap_alloc(e, cls_fit(2));
    e.mem[nd_36 + 0] = s_27;
    e.mem[nd_36 + 1] = term_ctr(CID_WCON, nd_35);
    u64 nd_37 = heap_alloc(e, cls_fit(2));
    e.mem[nd_37 + 0] = s_26;
    e.mem[nd_37 + 1] = term_ctr(CID_WCON, nd_36);
    u64 nd_38 = heap_alloc(e, cls_fit(2));
    e.mem[nd_38 + 0] = s_25;
    e.mem[nd_38 + 1] = term_ctr(CID_WCON, nd_37);
    u64 nd_39 = heap_alloc(e, cls_fit(2));
    e.mem[nd_39 + 0] = s_24;
    e.mem[nd_39 + 1] = term_ctr(CID_WCON, nd_38);
    u64 nd_40 = heap_alloc(e, cls_fit(2));
    e.mem[nd_40 + 0] = s_23;
    e.mem[nd_40 + 1] = term_ctr(CID_WCON, nd_39);
    u64 nd_41 = heap_alloc(e, cls_fit(2));
    e.mem[nd_41 + 0] = s_22;
    e.mem[nd_41 + 1] = term_ctr(CID_WCON, nd_40);
    u64 nd_42 = heap_alloc(e, cls_fit(2));
    e.mem[nd_42 + 0] = s_21;
    e.mem[nd_42 + 1] = term_ctr(CID_WCON, nd_41);
    u64 nd_43 = heap_alloc(e, cls_fit(2));
    e.mem[nd_43 + 0] = s_20;
    e.mem[nd_43 + 1] = term_ctr(CID_WCON, nd_42);
    u64 nd_44 = heap_alloc(e, cls_fit(2));
    e.mem[nd_44 + 0] = s_19;
    e.mem[nd_44 + 1] = term_ctr(CID_WCON, nd_43);
    u64 nd_45 = heap_alloc(e, cls_fit(2));
    e.mem[nd_45 + 0] = s_18;
    e.mem[nd_45 + 1] = term_ctr(CID_WCON, nd_44);
    u64 nd_46 = heap_alloc(e, cls_fit(2));
    e.mem[nd_46 + 0] = s_17;
    e.mem[nd_46 + 1] = term_ctr(CID_WCON, nd_45);
    u64 nd_47 = heap_alloc(e, cls_fit(2));
    e.mem[nd_47 + 0] = s_16;
    e.mem[nd_47 + 1] = term_ctr(CID_WCON, nd_46);
    u64 nd_48 = heap_alloc(e, cls_fit(2));
    e.mem[nd_48 + 0] = s_15;
    e.mem[nd_48 + 1] = term_ctr(CID_WCON, nd_47);
    u64 nd_49 = heap_alloc(e, cls_fit(2));
    e.mem[nd_49 + 0] = s_14;
    e.mem[nd_49 + 1] = term_ctr(CID_WCON, nd_48);
    u64 nd_50 = heap_alloc(e, cls_fit(2));
    e.mem[nd_50 + 0] = s_13;
    e.mem[nd_50 + 1] = term_ctr(CID_WCON, nd_49);
    u64 nd_51 = heap_alloc(e, cls_fit(2));
    e.mem[nd_51 + 0] = s_12;
    e.mem[nd_51 + 1] = term_ctr(CID_WCON, nd_50);
    u64 nd_52 = heap_alloc(e, cls_fit(2));
    e.mem[nd_52 + 0] = s_11;
    e.mem[nd_52 + 1] = term_ctr(CID_WCON, nd_51);
    u64 nd_53 = heap_alloc(e, cls_fit(2));
    e.mem[nd_53 + 0] = s_10;
    e.mem[nd_53 + 1] = term_ctr(CID_WCON, nd_52);
    u64 nd_54 = heap_alloc(e, cls_fit(2));
    e.mem[nd_54 + 0] = s_9;
    e.mem[nd_54 + 1] = term_ctr(CID_WCON, nd_53);
    u64 nd_55 = heap_alloc(e, cls_fit(2));
    e.mem[nd_55 + 0] = s_8;
    e.mem[nd_55 + 1] = term_ctr(CID_WCON, nd_54);
    u64 nd_56 = heap_alloc(e, cls_fit(2));
    e.mem[nd_56 + 0] = s_7;
    e.mem[nd_56 + 1] = term_ctr(CID_WCON, nd_55);
    u64 nd_57 = heap_alloc(e, cls_fit(2));
    e.mem[nd_57 + 0] = s_6;
    e.mem[nd_57 + 1] = term_ctr(CID_WCON, nd_56);
    u64 nd_58 = heap_alloc(e, cls_fit(2));
    e.mem[nd_58 + 0] = s_5;
    e.mem[nd_58 + 1] = term_ctr(CID_WCON, nd_57);
    u64 nd_59 = heap_alloc(e, cls_fit(2));
    e.mem[nd_59 + 0] = s_4;
    e.mem[nd_59 + 1] = term_ctr(CID_WCON, nd_58);
    u64 nd_60 = heap_alloc(e, cls_fit(2));
    e.mem[nd_60 + 0] = s_3;
    e.mem[nd_60 + 1] = term_ctr(CID_WCON, nd_59);
    u64 nd_61 = heap_alloc(e, cls_fit(2));
    e.mem[nd_61 + 0] = s_2;
    e.mem[nd_61 + 1] = term_ctr(CID_WCON, nd_60);
    u64 nd_62 = heap_alloc(e, cls_fit(2));
    e.mem[nd_62 + 0] = s_1;
    e.mem[nd_62 + 1] = term_ctr(CID_WCON, nd_61);
    u64 nd_63 = heap_alloc(e, cls_fit(2));
    e.mem[nd_63 + 0] = s_0;
    e.mem[nd_63 + 1] = term_ctr(CID_WCON, nd_62);
    r0 = 64ull;
    r1 = term_ctr(CID_WCON, nd_63);
    WL_JMP(FID_WORD_TO_NAT);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_NAT_SHOW)
  {
    Term n_0 = r0;
    WL_OPEN
    u32 v_0 = 0;
    Term v_1 = 0;
    Term a_0 = 10ull;
    Term a_1 = (a_0 == 0 ? 0 : n_0 / a_0);
    Term a_2 = (a_0 == 0 ? n_0 : n_0 % a_0);
    u32 v_2 = 0;
    Term v_3 = 0;
    Term o_0[2];
    if (spin_0(e, o_0, a_1, a_2) == 0) {
      return 0;
    }
    v_2 = o_0[0];
    v_3 = o_0[1];
    v_0 = v_2;
    v_1 = v_3;
    r0 = n_0;
    r1 = term_pak(CID_SNIL, 0);
    r2 = v_0;
    r3 = v_1;
    WL_JMP(FID_NAT_SHOW_FIN);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_WORD_ZERO)
  {
    Term n_0 = r0;
    WL_OPEN
    WL_SPIN
    if (n_0 == 0) {
      r0 = term_pak(CID_WNIL, 0);
      WL_RETN(1);
    } else {
      Term p_0 = (n_0 - 1);
      if (seq) {
        WL_ROOM(1);
        STK(0) = FID_WORD_ZERO_K12;
        WL_PUSHN(1);
      } else {
        u64 t_0 = task_node(e, FID_WORD_ZERO_K12, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_WORD_ZERO_K12, t_0);
        WL_IDX = 0;
      }
      r0 = p_0;
      n_0 = r0;
      WL_AGAIN(FID_WORD_ZERO);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_WORD_ZERO_K12)
  {
    Term h_0 = r0;
    WL_OPEN
    u64 nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[nd_0 + 0] = 0;
    e.mem[nd_0 + 1] = h_0;
    r0 = term_ctr(CID_WCON, nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN)
  {
    WL_OPEN
    if (seq) {
      WL_ROOM(1);
      STK(0) = FID_MAIN_K14;
      WL_PUSHN(1);
    } else {
      u64 t_0 = task_node(e, FID_MAIN_K14, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_MAIN_K14, t_0);
      WL_IDX = 0;
    }
    r0 = 64ull;
    WL_JMP(FID_WORD_ZERO);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_K14)
  {
    Term h_0 = r0;
    WL_OPEN
    Term a_0 = ((u64)((u64)(term_word(e, h_0)) + 1));
    if (seq) {
      WL_ROOM(1);
      STK(0) = FID_MAIN_K15;
      WL_PUSHN(1);
    } else {
      u64 t_1 = task_node(e, FID_MAIN_K15, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_MAIN_K15, t_1);
      WL_IDX = 0;
    }
    r0 = a_0;
    WL_JMP(FID_SHOW);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_K15)
  {
    Term h_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1);
      STK(0) = FID_MAIN_K16;
      WL_PUSHN(1);
    } else {
      u64 t_2 = task_node(e, FID_MAIN_K16, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_MAIN_K16, t_2);
      WL_IDX = 0;
    }
    r0 = h_1;
    WL_JMP(FID_NAT_SHOW);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_K16)
  {
    Term h_2 = r0;
    WL_OPEN
    u64 nd_0 = heap_alloc(e, cls_fit(1));
    e.mem[nd_0 + 0] = h_2;
    r0 = term_clo(FID_MAIN_C17, nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_C17)
  {
    Term h_3 = r0;
    Term x_0 = r1;
    WL_OPEN
    u64 nd_1 = heap_alloc(e, cls_fit(1));
    e.mem[nd_1 + 0] = str_append_take(e, term_make(TAG_STR, CID_SCON, STAT_OFF + 1), str_append_take(e, h_3, term_make(TAG_STR, CID_SCON, STAT_OFF + 4)));
    Term m_0 = term_clo(FID_IO_PRINT, nd_1);
    Term f_0 = term_clo(FID_MAIN_C18, 0);
    u64 nd_3 = heap_alloc(e, cls_fit(2));
    e.mem[nd_3 + 0] = f_0;
    e.mem[nd_3 + 1] = x_0;
    r0 = m_0;
    r1 = term_clo(FID_MAIN_C19, nd_3);
    WL_JMP(FID_CLO_APPLY);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_C18)
  {
    Term x_1 = r0;
    WL_OPEN
    u64 nd_2 = heap_alloc(e, cls_fit(1));
    e.mem[nd_2 + 0] = term_make(TAG_STR, CID_SCON, STAT_OFF + 7);
    r0 = term_clo(FID_IO_PRINT, nd_2);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_C19)
  {
    Term f_1 = r0;
    Term x_2 = r1;
    Term x_3 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2);
      STK(0) = x_2;
      STK(1) = FID_MAIN_K20;
      WL_PUSHN(2);
    } else {
      u64 t_3 = task_node(e, FID_MAIN_K20, WL_CONT, WL_IDX, 1);
      e.mem[t_3 + 0] = x_2;
      WL_CONT = term_tsk(FID_MAIN_K20, t_3);
      WL_IDX = 1;
    }
    r0 = f_1;
    r1 = x_3;
    WL_JMP(FID_CLO_APPLY);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_MAIN_K20)
  {
    WL_POPN(1);
    Term x_4 = STK(0);
    Term h_4 = r0;
    WL_OPEN
    r0 = h_4;
    r1 = x_4;
    WL_JMP(FID_CLO_APPLY);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_PRINT)
  {
    Term text_0 = r0;
    Term k_0 = r1;
    WL_OPEN
    u64 nd_4 = heap_alloc(e, cls_fit(2));
    e.mem[nd_4 + 0] = text_0;
    e.mem[nd_4 + 1] = k_0;
    r0 = term_ctr(CID_IO_PRINT, nd_4);
    WL_RETN(1);
  }}
#endif

// A task enters through its words: a continuation's results ride r0.. and
// its parameters the stack; any other segment's parameters ride r0...
  WL_CASE(FID_ENTER)
  {
    Term t = r0;
    WL_OPEN
    Fid f   = (u32)term_aux(t);
    Loc a   = term_loc(t);
    u32 war = fid_arity(f);
    WL_FRAME(t)
    if (fid_seqk(f)) {
      u32 rw = fid_resw(f);
      WL_LOAD(a + war - rw, rw)
      WL_ARGS(a, war - rw + 1)
    } else {
      WL_LOAD(a, war)
    }
    heap_free(e, cls_fit(war + 2), a);
    WL_DYN(f);
  }}

  WL_CASE(FID_IO_EMIT)
  {
    Term x = r0;
    WL_OPEN
    Loc l = heap_alloc(e, 0);
    e.mem[l] = x;
    r0 = term_ctr(CID_EMIT, l);
    WL_RETN(1);
  }}

  WL_CASE(FID_CLO_APPLY)
  {
    Term fun = r0;
    Term arg = r1;
    WL_OPEN
    Fid f    = (Fid)term_aux(fun);
    u32 war  = fid_arity(f) - 1;
    Loc a    = term_loc(fun);
    WL_LOAD(a, war)
    spare_free(e, cls_fit(war), a);
    WL_LAST(arg)
    WL_DYN(f);
  }}

  WL_CASE(FID_EXIT)
  {
    u32  n = rn;
    Term rv[WL_RESW];
    WL_SAVE(rv)
    WL_OPEN
    if (err_seen(e.mem)) {
      return 0;
    }
    sp -= 2 * LANE_STEP;
    Term cont = STK(0);
    u32  idx  = (u32)STK(1);
    if (cont != TERM_HOLE && fid_seqk((u32)term_aux(cont))) {
      Fid wf = (u32)term_aux(cont);
      Loc wa = term_loc(cont);
      u32 wn = fid_arity(wf);
      WL_FRAME(cont)
      WL_ARGS(wa, wn - n + 1)
      heap_free(e, cls_fit(wn + 2), wa);
      WL_TAKE(rv)
      WL_DYN(wf);
    }
    return task_deliver(e.mem, cont, idx, rv, n);
  }}

#if DEVICE
  default: {
    err_post(e.mem, ERR_FIDS);
    return 0;
  }
  }
  }
}
#endif

// Monk
// ====

// One turn on a ring: its head task below put0 runs (a growing lane skips
// a fork-free one). The host grows a row ring by ring and works a ring
// until it drains; a device lane does both.
INLINE u32 monk_step(Env e, Stk stk, Ring rg, u32 put0, bool seq, u32 base,
  u32 stride, Cur cur) {
  Corpus   H   = e.mem;
  DEV u32* get = ring_get(H, rg);
  if (*get == put0) {
    return 0;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, rg, *get);
  u32      hi = a32_load_acq(lo + 1);
  Term     t  = (((u64)hi << 32) | a32_load(lo)) & ~RFC_BIT;
  if ((hi >> 31) != ring_lap(*get) || (!seq && fid_nofk((u32)term_aux(t)))) {
    return 0;
  }
  a32_store(get, *get + 1);
  u32 spin = 0;
  for (;;) {
    Reply r = work_loop(e, stk, t, seq);
    if (r == 0) {
      return 2;
    }
    if ((u32)H[task_tail(r) + 1] == 0) {
      if (err_spun(H, &spin)) {
        return 2;
      }
      if (stride != 0 && fid_nofk((u32)term_aux(r))) {
        ring_push(H, ring_pick(base, stride, cur), r);
        return 2;
      }
      t      = r;
      seq    = false;
      stride = 0;
      continue;
    }
    task_deal(H, r, base, stride, cur);
    return 1;
  }
}

// Dev
// ===

// TG_HOLD words of threadgroup memory (lane 0's write keeps them) hold
// one group per Apple core: without them bitonic runs 1.35x, kmeans
// 1.19x, matmul 1.13x. A grow pass runs at most CUBE_T rounds, so a group
// that never fills still cuts at a kernel end.

#if DEVICE

INLINE void dev_cut(Env e) {
  if (err_seen(e.mem)) {
    return;
  }
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    u64 gen = (u64)KEEP(c) << c;
    while (ALC_LEN(e, c) >= gen) {
      Loc head = ALC_AT(e, c);
      Loc tail = head;
      for (u32 i = KEEP(c); --i;) {
        tail = e.mem[tail];
      }
      ALC_AT(e, c)    = e.mem[tail];
      ALC_LEN(e, c)  -= gen;
      e.mem[tail]     = 0;
      bank_push(e.mem, c, head);
    }
  }
}

// Pass 2, one group: each bank's [top, wr) slides onto rd, CUBE_T entries
// a step (loads, barrier, stores: rd <= top), off the host's pages.
INLINE void bank_pack(Corpus H, u32 lane) {
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    DEV Bank* b  = bank_at(H, c);
    u32       rd = b->rd;
    u32       n  = b->wr - b->top;
    for (u32 i = 0; i < n; i += CUBE_T) {
      Term v = i + lane < n ? H[b->off + b->top + i + lane] : 0;
      BAR();
      if (i + lane < n) {
        H[b->off + rd + i + lane] = v;
      }
    }
    BAR();
    if (lane == 0) {
      b->rd = b->wr = b->top = rd + n;
    }
  }
}

// One kernel, one pipeline: pass 0 grows the frontier (a task a lane a
// turn, votes between barriers), pass 1 works it (a lane drains its
// ring), pass 2 packs the banks; one call of monk_step, so the program
// compiles once.
#ifdef __METAL_VERSION__
kernel void bend_dev(Corpus H [[buffer(0)]], constant u32& pass [[buffer(1)]],
  threadgroup volatile u64* hold [[threadgroup(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void bend_dev(Corpus H, u32 pass) {
  extern __shared__ volatile u64 hold[];
  u32 grids = gridDim.x;
  u32 row   = blockIdx.x;
  u32 lane  = threadIdx.x;
#endif
  if (pass == 2) {
    bank_pack(H, lane);
    return;
  }
  u32  stride = grids == 1 ? CUBE_G : 1;
  u32  me     = row * CUBE_T + stride * lane;
  Ring rg     = pass ? ring_flip(me) : me;
  Env  e      = { H, H + ALC_OFF + me };
  Stk  stk    = (Stk)(H + STAK_OFF + me);
  if (lane == 0) {
    hold[0] = 0;
  }
  GA32 tg_cur, tg_grew, tg_has;
  g32_ini(&tg_cur);
  g32_ini(&tg_grew);
  g32_ini(&tg_has);
  BAR();
  u32 put0      = a32_load(ring_put(H, rg));
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (u32 turn = 0; pass || turn < CUBE_T; turn += 1) {
    if (pass) {
      if (*ring_get(H, rg) == put0 || err_seen(H)) {
        break;
      }
    } else {
      put0 = a32_load(ring_put(H, rg));
      u32 vote = put0 != a32_load(ring_get(H, rg));
      if (lane == 0 && (err_seen(H) || root_done(H))) {
        vote = CUBE_T;
      }
      g32_add(&tg_has, vote);
      BAR();
      u32 has = g32_get(&tg_has);
      if (has - seen_has >= CUBE_T) {
        break;
      }
      seen_has = has;
    }
    u32 ran = monk_step(e, stk, rg, put0, pass, pass ? rg : row * CUBE_T,
      pass ? 0 : stride, &tg_cur);
    if (!pass) {
      if (ran == 1) {
        g32_add(&tg_grew, 1);
      }
      BARD();
      u32 grew = g32_get(&tg_grew);
      if (grew == seen_grew) {
        break;
      }
      seen_grew = grew;
    }
  }
  dev_cut(e);
}

#endif

// Window
// ======

// The Linux kit's fill, the Mac's window_msl in the runtime's dialect:
// a ! build carries window_dev in its cubin, a host build walks the
// pixels itself. An Image is a quadtree over 2^k x 2^k: a Qua at level
// i splits its square in four (tl, tr, bl, br), a Qua under the pixels
// follows tl, a Pix is 0xRRGGBB.
#if defined(__linux__) || defined(__CUDACC_RTC__)

INLINE u32 window_pix(Corpus H, Term t, u32 k, u32 x, u32 y) {
  for (u32 i = k; term_tag(t) == TAG_CTR;) {
    u32 j = 0;
    if (i > 0) {
      i -= 1;
      j = ((y >> i) & 1) * 2 + ((x >> i) & 1);
    }
    Loc l = term_rfc(t) ? H[term_loc(t)] >> 24 : term_loc(t);
    t = H[l + j];
  }
  return (u32)term_loc(t) & 0xFFFFFF;
}

#ifdef __CUDACC_RTC__
extern "C" __global__ void window_dev(Corpus H, Term root, u32 w, u32 h,
  u32 k, u32* out) {
  u32 x = blockIdx.x * blockDim.x + threadIdx.x;
  u32 y = blockIdx.y * blockDim.y + threadIdx.y;
  if (x < w && y < h) {
    out[y * w + x] = window_pix(H, root, k, x, y);
  }
}
#endif

#endif

#if !DEVICE

// Row
// ===

static void row_grow(Env e, Stk stk, u32 base, u32 stride, u32 want) {
  Corpus H = e.mem;
  u32 cur = 0;
  for (;;) {
    u32 put0[CUBE_T];
    u32 has = 0;
    for (u32 i = 0; i < CUBE_T; i += 1) {
      put0[i] = *ring_put(H, base + i * stride);
      has += put0[i] != *ring_get(H, base + i * stride);
    }
    if (root_done(H) || has >= want) {
      return;
    }
    u32 grew = 0;
    u32 ran  = 0;
    for (u32 i = 0; i < CUBE_T && ran != 2; i += 1) {
      ran   = monk_step(e, stk, base + i * stride, put0[i], false, base,
        stride, &cur);
      grew += ran == 1;
    }
    if (grew == 0) {
      return;
    }
  }
}

// Pool
// ====

static void* pool_try(u64 bytes) {
  return mmap(NULL, bytes, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
}

static void* pool_mmap(u64 bytes) {
  void* p = pool_try(bytes);
  if (p == MAP_FAILED) {
    err_fail("reservation failed");
  }
  return p;
}

static Term* pool_stack(void) {
  u64   len = 1ull << 31;
  char* p   = pool_mmap(len + 16384 + SIGSTKSZ);
  if (mprotect(p + len, 16384, PROT_NONE) != 0) {
    err_fail("stack guard failed");
  }
  stack_t ss = { .ss_sp = p + len + 16384, .ss_size = SIGSTKSZ };
  sigaltstack(&ss, NULL);
  struct sigaction sa = { .sa_handler = err_trap, .sa_flags = SA_ONSTACK };
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
  return (Term*)p;
}

static void* pool_work(void* arg) {
  Term* stk  = pool_stack();
  u64   seen = 0;
  for (;;) {
    pthread_mutex_lock(&pool_lock);
    while (atomic_load_explicit(&pool_tick, memory_order_acquire) == seen) {
      pthread_cond_wait(&pool_wake, &pool_lock);
    }
    pthread_mutex_unlock(&pool_lock);
    seen = atomic_load_explicit(&pool_tick, memory_order_acquire);
    Env e = { CORPUS, ALC[1 + (u32)(uintptr_t)arg] };
    for (;;) {
      u32 r = atomic_fetch_add_explicit(&pool_row, 1, memory_order_relaxed);
      if (r >= (pool_grow ? CUBE_G : LANES / LINE)) {
        break;
      }
      if (pool_grow) {
        row_grow(e, stk, r * CUBE_T, 1, CUBE_T);
      } else {
        for (u32 i = 0; i < LINE; i += 1) {
          Ring rg   = r * LINE + i;
          u32  put0 = a32_load(ring_put(e.mem, rg));
          while (*ring_get(e.mem, rg) != put0 && !err_seen(e.mem)) {
            monk_step(e, stk, rg, put0, true, rg, 0, NULL);
          }
        }
      }
    }
    u32 done = atomic_fetch_add_explicit(&pool_done, 1, memory_order_release);
    if (done + 1 == pool_size) {
      pthread_mutex_lock(&pool_lock);
      pthread_cond_broadcast(&pool_wake);
      pthread_mutex_unlock(&pool_lock);
    }
  }
}

OUTLINE void pool_open(void) {
  static bool up;
  if (up) {
    return;
  }
  up = true;
  for (u32 w = 0; w < pool_size; w += 1) {
    pthread_t tid;
    if (pthread_create(&tid, NULL, pool_work, (void*)(uintptr_t)w)) {
      err_fail("pthread_create");
    }
  }
}

// The CPUs this process may use: affinity mask under the cgroup quota
static int cpu_read(const char* path, long* a, long* b) {
  FILE* f = fopen(path, "r");
  int   n = f == NULL ? 0 : fscanf(f, "%ld %ld", a, b);
  if (f != NULL) {
    fclose(f);
  }
  return n;
}

static long cpu_count(void) {
  long n = sysconf(_SC_NPROCESSORS_ONLN);
#ifdef __linux__
  cpu_set_t set;
  if (sched_getaffinity(0, sizeof set, &set) == 0) {
    n = CPU_COUNT(&set);
  }
  long q = 0;
  long p = 0;
  if (cpu_read("/sys/fs/cgroup/cpu.max", &q, &p) != 2) {
    cpu_read("/sys/fs/cgroup/cpu/cpu.cfs_quota_us", &q, &p);
    cpu_read("/sys/fs/cgroup/cpu/cpu.cfs_period_us", &p, &p);
  }
  if (q > 0 && p > 0 && (q + p - 1) / p < n) {
    n = (q + p - 1) / p;
  }
#endif
  return n;
}

OUTLINE void pool_turn(bool grow) {
  pool_grow = grow;
  atomic_store_explicit(&pool_row, 0, memory_order_relaxed);
  atomic_store_explicit(&pool_done, 0, memory_order_relaxed);
  pthread_mutex_lock(&pool_lock);
  atomic_fetch_add_explicit(&pool_tick, 1, memory_order_release);
  pthread_cond_broadcast(&pool_wake);
  while (atomic_load_explicit(&pool_done, memory_order_acquire) < pool_size) {
    pthread_cond_wait(&pool_wake, &pool_lock);
  }
  pthread_mutex_unlock(&pool_lock);
}

// Gpu
// ===

// gpu_make compiles the device program and, given a path, writes it as
// <binary>.gpu (--gpu-build, run by bend -o): Metal's binary archive
// of the pipeline (keyed by the compiled function, so a wrong file
// misses), CUDA's cubin behind a hash of the text. A launch loads it,
// else notes and compiles (Metal's OS cache keeps that pipeline; CUDA
// writes the file).

static const char* gpu_path(void) {
  static char path[4096];
  u32 n = sizeof path - 8;
#ifdef __APPLE__
  _NSGetExecutablePath(path, &n);
#else
  path[readlink("/proc/self/exe", path, n)] = 0;
#endif
  return strcat(path, ".gpu");
}

static void gpu_note(const char* path) {
  fprintf(stderr, "bend: compiling the GPU program (%s is missing or"
    " stale)\n", path);
}

#if !BEND_CUDA
#define gpu_map pool_mmap
#endif

#if BEND_METAL || BEND_CUDA

static void gpu_kernel(u32 pass, u32 groups);

static void gpu_run(u32 f) {
  if (f < CUBE_T) {
    gpu_kernel(0, 1);
  }
  if (f < LANES) {
    gpu_kernel(0, CUBE_G);
  }
  gpu_kernel(1, CUBE_G);
  gpu_kernel(2, 1);
}

#endif

#if BEND_METAL

static bool gpu_probe(void) {
  return (gpu_dev = MTLCreateSystemDefaultDevice()) != nil;
}

static MTLComputePipelineDescriptor* gpu_desc(void) {
  NSError* err = nil;
  MTLCompileOptions* opts = [MTLCompileOptions new];
  opts.mathMode = MTLMathModeSafe;
  opts.preprocessorMacros = @{ @"CUBE_LOG": @(CUBE_LOG) };
  id<MTLLibrary> lib = [gpu_dev newLibraryWithSource:@(BEND_SRC) options:opts
    error:&err];
  if (!lib) {
    err_fail([[err localizedDescription] UTF8String]);
  }
  MTLComputePipelineDescriptor* d = [MTLComputePipelineDescriptor new];
  d.computeFunction = [lib newFunctionWithName:@"bend_dev"];
  return d;
}

static bool gpu_make(const char* path) {
  NSError* err = nil;
  id<MTLBinaryArchive> ar = [gpu_dev
    newBinaryArchiveWithDescriptor:[MTLBinaryArchiveDescriptor new] error:&err];
  if (![ar addComputePipelineFunctionsWithDescriptor:gpu_desc() error:&err]) {
    err_fail([[err localizedDescription] UTF8String]);
  }
  return [ar serializeToURL:[NSURL fileURLWithPath:@(path)] error:&err];
}

static id<MTLComputePipelineState> gpu_pipe(MTLComputePipelineDescriptor* d,
  id<MTLBinaryArchive> ar) {
  NSError* err = nil;
  d.binaryArchives = ar ? @[ar] : @[];
  id<MTLComputePipelineState> pso = [gpu_dev
    newComputePipelineStateWithDescriptor:d
    options:ar ? MTLPipelineOptionFailOnBinaryArchiveMiss : 0 reflection:nil
    error:&err];
  if (!pso && !ar) {
    err_fail([[err localizedDescription] UTF8String]);
  }
  return pso;
}

static u64 gpu_span(void) {
  u64 span = [gpu_dev recommendedMaxWorkingSetSize];
  u64 most = [gpu_dev maxBufferLength];
  span = span < most ? span : most;
  return span < (2ull << 30) ? span : 2ull << 30;
}

static void gpu_load(u64 bytes) {
  gpu_buf = [gpu_dev newBufferWithBytesNoCopy:CORPUS length:bytes
    options:MTLResourceStorageModeShared
      | MTLResourceHazardTrackingModeUntracked deallocator:nil];
  if (!gpu_buf) {
    err_fail("the GPU span is more than the device has");
  }
  @autoreleasepool {
    gpu_que = [gpu_dev newCommandQueue];
    const char* path = gpu_path();
    MTLBinaryArchiveDescriptor* ad = [MTLBinaryArchiveDescriptor new];
    ad.url = [NSURL fileURLWithPath:@(path)];
    MTLComputePipelineDescriptor* d = gpu_desc();
    id<MTLBinaryArchive> ar = [gpu_dev newBinaryArchiveWithDescriptor:ad
      error:nil];
    gpu_pso = ar ? gpu_pipe(d, ar) : nil;
    if (!gpu_pso) {
      gpu_note(path);
      gpu_pso = gpu_pipe(d, nil);
    }
  }
}

static void gpu_kernel(u32 pass, u32 groups) {
  [gpu_enc setComputePipelineState:gpu_pso];
  [gpu_enc setBuffer:gpu_buf offset:0 atIndex:0];
  [gpu_enc setBytes:&pass length:sizeof pass atIndex:1];
  [gpu_enc setThreadgroupMemoryLength:TG_HOLD * 8 atIndex:0];
  [gpu_enc dispatchThreadgroups:MTLSizeMake(groups, 1, 1)
    threadsPerThreadgroup:MTLSizeMake(CUBE_T, 1, 1)];
  [gpu_enc memoryBarrierWithScope:MTLBarrierScopeBuffers];
}

static void gpu_pass(u32 f) {
  @autoreleasepool {
    id<MTLCommandBuffer> cb = [gpu_que commandBuffer];
    gpu_enc = [cb computeCommandEncoder];
    gpu_run(f);
    [gpu_enc endEncoding];
    [cb commit];
    [cb waitUntilCompleted];
    if ([cb error]) {
      err_fail([[[cb error] localizedDescription] UTF8String]);
    }
  }
}

#elif BEND_CUDA

// the bag from the device: a group of 128 lanes per 64 KB of L2, a power of
// two from 16 to 128 groups. Apple keeps the 128 the bag was tuned on: on an
// M4 (10 cores) 32 groups ran bitonic 1.85 -> 1.29 s, but the light one-pass
// benches 1.25x, their lanes four times fewer.
static void gpu_shape(int units) {
  CUBE_LOG = 31 - CLZ(units < 16 ? 16 : units > 128 ? 128 : units);
}

static bool gpu_probe(void) {
  int       managed = 0;
  CUcontext ctx;
  // one stream, so one hardware queue: the default 8 each cost a channel
  // at context creation and teardown, about half of the startup
  setenv("CUDA_DEVICE_MAX_CONNECTIONS", "1", 0);
  if (cuInit(0) == CUDA_SUCCESS && cuDeviceGet(&gpu_dev, 0) == CUDA_SUCCESS) {
    cuDeviceGetAttribute(&managed,
      CU_DEVICE_ATTRIBUTE_CONCURRENT_MANAGED_ACCESS, gpu_dev);
  }
  int l2 = 1 << 23;
  cuDeviceGetAttribute(&l2, CU_DEVICE_ATTRIBUTE_L2_CACHE_SIZE, gpu_dev);
  gpu_shape(l2 >> 16);
  return managed != 0
    && cuDevicePrimaryCtxRetain(&ctx, gpu_dev) == CUDA_SUCCESS
    && cuCtxSetCurrent(ctx) == CUDA_SUCCESS;
}

static Corpus gpu_map(u64 bytes) {
  CUdeviceptr p = 0;
  if (cuMemAllocManaged(&p, bytes, CU_MEM_ATTACH_GLOBAL) != CUDA_SUCCESS) {
    err_fail("corpus reservation failed");
  }
#if CUDA_VERSION >= 13000
  cuMemAdvise(p, bytes, CU_MEM_ADVISE_SET_PREFERRED_LOCATION,
    (CUmemLocation){ CU_MEM_LOCATION_TYPE_DEVICE, gpu_dev });
#else
  cuMemAdvise(p, bytes, CU_MEM_ADVISE_SET_PREFERRED_LOCATION, gpu_dev);
#endif
  return (Corpus)(uintptr_t)p;
}

static u64 gpu_hash(void) {
  u64 key = 14695981039346656037ull ^ CUBE_LOG;
  for (const char* p = BEND_SRC; *p != 0; p += 1) {
    key = (key ^ (u8)*p) * 1099511628211ull;
  }
  return key;
}

static bool gpu_make(const char* path) {
  int cc[2] = {0, 0};
  cuDeviceGetAttribute(cc,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, gpu_dev);
  cuDeviceGetAttribute(cc + 1,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, gpu_dev);
  char arch[40];
  char bag[24];
  snprintf(arch, sizeof arch, "--gpu-architecture=sm_%d%d", cc[0], cc[1]);
  snprintf(bag, sizeof bag, "-DCUBE_LOG=%u", CUBE_LOG);
  const char* opts[] = { arch, bag, "--fmad=false", "-default-device" };
  nvrtcProgram prog;
  if (nvrtcCreateProgram(&prog, BEND_SRC, "bend.cu", 0, NULL, NULL)
    != NVRTC_SUCCESS) {
    err_fail("cannot compile the CUDA library");
  }
  if (nvrtcCompileProgram(prog, 4, opts) != NVRTC_SUCCESS) {
    size_t n = 0;
    nvrtcGetProgramLogSize(prog, &n);
    char* log = calloc(n + 1, 1);
    if (log != NULL && nvrtcGetProgramLog(prog, log) == NVRTC_SUCCESS) {
      fprintf(stderr, "%s\n", log);
    }
    err_fail("cannot compile the CUDA library");
  }
  size_t len = 0;
  nvrtcGetCUBINSize(prog, &len);
  char* bin = malloc(len);
  if (bin == NULL || nvrtcGetCUBIN(prog, bin) != NVRTC_SUCCESS) {
    err_fail("cannot load the CUDA library");
  }
  nvrtcDestroyProgram(&prog);
  u64   key = gpu_hash();
  FILE* out = path == NULL ? NULL : fopen(path, "wb");
  bool  ok  = out != NULL && fwrite(&key, 8, 1, out) == 1
    && fwrite(bin, 1, len, out) == len && fclose(out) == 0;
  if (cuModuleLoadData(&gpu_lib, bin) != CUDA_SUCCESS) {
    err_fail("cannot load the CUDA library");
  }
  free(bin);
  return path == NULL || ok;
}

static u64 gpu_span(void) {
  size_t span = 0;
  cuDeviceTotalMem(&span, gpu_dev);
  return span;
}

static void gpu_load(u64 bytes) {
  const char* path = gpu_path();
  int         fd   = open(path, O_RDONLY);
  struct stat st   = { 0 };
  u64         key  = 0;
  char*       bin  = fd < 0 || fstat(fd, &st) != 0 || st.st_size <= 8 ? NULL
    : mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (bin != NULL && bin != MAP_FAILED) {
    memcpy(&key, bin, 8);
  }
  if (key != gpu_hash()
    || cuModuleLoadData(&gpu_lib, bin + 8) != CUDA_SUCCESS) {
    gpu_note(path);
    gpu_make(path);
  }
  if (cuModuleGetFunction(&gpu_pso, gpu_lib, "bend_dev") != CUDA_SUCCESS) {
    err_fail("cannot load the GPU program");
  }
}

static void gpu_kernel(u32 pass, u32 groups) {
  void* args[] = { &CORPUS, &pass };
  if (cuLaunchKernel(gpu_pso, groups, 1, 1, CUBE_T, 1, 1, TG_HOLD * 8, NULL,
    args, NULL) != CUDA_SUCCESS) {
    err_fail("device launch failed");
  }
}

static void gpu_pass(u32 f) {
  gpu_run(f);
  if (cuCtxSynchronize() != CUDA_SUCCESS) {
    err_fail("device fault");
  }
}

#else

#define gpu_probe() false
#define gpu_make(p) true
#define gpu_span()  0
#define gpu_load(b)
#define gpu_pass(f)

#endif

// Cube
// ====

static void cube_run(Corpus H, bool gpu) {
  for (;;) {
    u32 f = a32_load(a32_at(H, H_CURSOR));
    a32_store(a32_at(H, H_CURSOR), 0);
    if (root_done(H)) {
      return;
    }
    if (f == 0) {
      err_fail("frontier drained without a result");
    }
    if (gpu) {
      gpu_pass(f);
    } else {
      // Under a unit (CUBE_T / LINE a row) per thread, the column grows to
      // the rows that give one; no more: each touches a page of every plane.
      if (f * (CUBE_T / LINE) < pool_size) {
        row_grow((Env){ H, ALC[0] }, io_stk, 0, CUBE_G,
          (pool_size + CUBE_T / LINE - 1) / (CUBE_T / LINE));
      }
      if (f < CUBE) {
        pool_turn(true);
      }
      pool_turn(false);
    }
    u32 ec = a32_load(a32_at(H, H_ERROR_CODE));
    if (ec != 0) {
      err_post(H, ec);
    }
  }
}

// Corpus
// ======

static Corpus corpus_setup(bool gpu, long threads, u64 bytes) {
  io_gpu     = gpu;
  KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;
  u64 dflt   = gpu ? gpu_span() : 1ull << 43;
  u64 size   = (gpu && bytes != 0 ? bytes : dflt) & ~16383ull;
  // The cores reserve the whole Loc space (8 TiB, MAP_NORESERVE). A kernel
  // with fewer address bits (39-bit arm64, Sv39) or a ulimit -v gets the
  // largest power of two that fits, down to 8 GiB.
  CORPUS = gpu ? gpu_map(size) : pool_try(size);
  while (CORPUS == MAP_FAILED && size > 1ull << 33) {
    CORPUS = pool_try(size /= 2);
  }
  if (CORPUS == MAP_FAILED) {
    err_fail("reservation failed");
  }
  u64 span = size / 8;
  u64 cap  = span > HEAP_OFF ? (span - HEAP_OFF) / (PAGE_LEN + 10) : 0;
  if (cap <= CUBE) {
    err_fail("the GPU span is under the rings, stacks and a page per lane");
  }
  cap = cap < ~0u ? cap : ~0u - 1;
  Corpus H  = CORPUS;
#if BEND_CUDA
  if (gpu) {
    cuMemsetD8((CUdeviceptr)(uintptr_t)H, 0, STAK_OFF * 8);
    cuCtxSynchronize();
  }
#endif
  memcpy(H + STAT_OFF, STAT_IMG, STAT_LEN * sizeof(u64));
  u64    at = HEAP_OFF + (cap << PAGE_BITS);
  for (u32 c = 0; c < NCLS_ALL; c += 1) {
    bank_at(H, c)->off = at;
    at += 2 * (cap >> ((c < NCLS ? NCLS : c) - PAGE_BITS));
  }
  a32_store(a32_at(H, H_BUMP), 1);
  a32_store(a32_at(H, H_CAP), (u32)cap);
  if (gpu) {
    gpu_load(size);
  }
  pool_size = threads < 1 ? 1 : threads < CUBE_T ? threads : CUBE_T;
  return H;
}

OUTLINE Term corpus_eval(Corpus H, Term t) {
  Env  e = { H, ALC[0] };
  Term rv[WL_RESW];
  for (;;) {
    Reply r = work_loop(e, io_stk, t, !BANGS
      && (pool_size == 1 || fid_nofk((u32)term_aux(t))));
    if (r == 0) {
      if (root_done(H)) {
        break;
      }
      err_fail("solo delivery lost");
    }
    if ((u32)H[task_tail(r) + 1] == 0) {
      t = r;
      if (io_gpu && fid_bangs((u32)term_aux(t))) {
        Loc  tl   = task_tail(t);
        Term cont = H[tl];
        u32  idx  = (u32)(H[tl + 1] >> 32) & 0xFFFF;
        H[tl]     = TERM_HOLE;
        a32_store(a32_at(H, H_CURSOR), 1);
        ring_push(H, 0, t);
        cube_run(H, true);
        Term p = task_deliver(H, cont, idx, rv, root_take(H, rv));
        if (root_done(H)) {
          break;
        }
        if (p == 0) {
          err_fail("seam delivery lost");
        }
        t = p;
      }
      continue;
    }
    task_deal(H, r, 0, 0, (Cur)0);
    pool_open();
    cube_run(H, false);
    break;
  }
  root_take(H, rv);
  return rv[0];
}

// Io
// ==

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <sys/socket.h>

#define IO_READ 1
#define IO_TIME 2
#define IO_PARK TERM_HOLE

// A handle is its host value, a descriptor or a pointer, packed in one
// word (a pointer split over the aux and loc bits). Its type is a law of
// base, opaque and linear: a program cannot forge, copy or reuse one, so
// nothing stands between the value and the host.
#define io_hand(v)   term_make(TAG_PAK, (u64)(v) >> 40, (u64)(v) & LOC_MASK)
#define io_hand_v(t) (((u64)term_aux(t) << 40) | term_loc(t))

struct IoWork;
typedef void (*IoCall)(struct IoWork* w);
typedef Term (*IoPack)(Env e, struct IoWork* w);

// IoWork ::=
//   | IoWork(hand, made, word, size, data, text, code, call, pack)
typedef struct IoWork {
  intptr_t hand;
  intptr_t made;
  u32      word;
  u64      size;
  char*    data;
  char*    text;
  u32      code;
  IoCall   call;
  IoPack   pack;
} IoWork;

typedef Term (*Effect)(Env e, Term* f, IoWork* w);

// IoEff ::=
//   | IoEff(run, ask)
typedef struct {
  Effect run;
  u32    ask;
} IoEff;

static IoEff io_eff_rows[1 << 16];
static u32   io_live;

static u64 io_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (u64)ts.tv_sec * 1000000000ull + (u64)ts.tv_nsec;
}

OUTLINE void* io_mem(void* mem) {
  if (mem == NULL) {
    err_fail("host allocation failed");
  }
  return mem;
}

static int io_sys_addr(const char* host, u32 port, struct sockaddr_in* at) {
  memset(at, 0, sizeof(*at));
  at->sin_family = AF_INET;
  at->sin_port   = htons((uint16_t)port);
  for (const char* p = host; *p != 0; p += 1) {
    bool zero = *p == '0' && p[1] >= '0' && p[1] <= '9';
    if ((p == host || p[-1] == '.') && zero) {
      return -1;
    }
  }
  return port > 65535 || inet_pton(AF_INET, host, &at->sin_addr) != 1
    ? -1 : 0;
}

// The program's arguments (IO.args).
static int    io_argc = 0;
static char** io_argv = NULL;

static void io_eff(u32 cid, Effect run, u32 need) {
  IoEff row = { run, need };
  io_eff_rows[cid] = row;
}

static u64 io_sys_end(IoWork* w, ssize_t n) {
  w->code = n < 0 ? (u32)errno : 0;
  return n < 0 ? 0 : (u64)n;
}

// A computation's activation for its whole life: cont over item is its
// next request; parked, work.word and time are its fd and deadline, evts
// what the fd must be ready for, and work.pack resumes it (io_exec runs
// cont, the request); work leads, so an effect's IoWork* is its activation.
// IoAct ::=
//   | IoAct(work, cont, item, time, evts, next)
typedef struct IoAct {
  IoWork        work;
  Term          cont;
  Term          item;
  u64           time;
  short         evts;
  struct IoAct* next;
} IoAct;

// IoQue ::=
//   | IoQue(head, last)
typedef struct {
  IoAct* head;
  IoAct* last;
} IoQue;

static IoQue io_runs;
static IoQue io_park;
static IoQue io_jobs;

static void io_push(IoQue* q, IoAct* a) {
  a->next = NULL;
  *(q->head == NULL ? &q->head : &q->last->next) = a;
  q->last = a;
}

static IoAct* io_pop(IoQue* q) {
  IoAct* a = q->head;
  q->head  = a->next;
  return a;
}

static void io_spawn(Term m) {
  IoAct* a = io_mem(calloc(1, sizeof(IoAct)));
  a->cont  = m;
  a->item  = term_clo(FID_IO_EMIT, 0);
  io_push(&io_runs, a);
  io_live += 1;
}

// Parks the effect's activation until fd is ready for evts (POLLIN or
// POLLOUT; 0 for no fd), or until time (a tick; 0 for no deadline),
// whichever comes first; the loop then calls more on its thread, whose
// value readies the activation, or IO_PARK, a re-park.
static Term io_wait_on(IoWork* w, int fd, short evts, u64 time, IoPack more) {
  IoAct* a     = (IoAct*)w;
  a->work.word = (u32)fd;
  a->work.pack = more;
  a->time      = time;
  a->evts      = evts;
  io_push(&io_park, a);
  return IO_PARK;
}

// the deadline a parked activation waits for (0 for none)
static u64 io_wait_time(IoWork* w) {
  return ((IoAct*)w)->time;
}

OUTLINE void io_out(FILE* h, const char* data, u64 len) {
  if (fwrite(data, 1, len, h) != len) {
    err_fail("a short write on a standard stream");
  }
}

OUTLINE void io_sync(void) {
  if (fflush(stdout) != 0) {
    err_fail("a short write on a standard stream");
  }
}

// the edge is UTF-8
static u64 io_utf8(char* buf, u64 c) {
  u64 k = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
  for (u64 i = k; i > 1; i -= 1) {
    buf[i - 1] = (char)(0x80 | (c & 0x3F));
    c >>= 6;
  }
  buf[0] = (char)(k == 1 ? c : (0xF00 >> k) | c);
  return k;
}

OUTLINE char* io_cstr(Env e, Term s, u64* len) {
  StrParts p = str_peek(e, s);
  u64 n = 0;
  char* buf = io_mem(malloc((u64)p.len * 4 + 1));
  for (u32 i = 0; i < p.len; i++) {
    u32 c = str_at_peek(e, p, i);
    if (c > 0x10ffff || (c >= 0xd800 && c <= 0xdfff)) {
      free(buf); term_sink(e, s);
      err_fail("cannot encode a non-scalar Char as UTF-8");
    }
    n += io_utf8(buf + n, c);
  }
  term_sink(e, s);
  buf[n] = 0;
  *len = n;
  return buf;
}

OUTLINE void io_errs(Env e, Term s) {
  u64   n    = 0;
  char* text = io_cstr(e, s, &n);
  io_sync();
  io_out(stderr, text, n);
  io_out(stderr, "\n", 1);
  free(text);
}

#define io_nul(s, n) (strlen(s) != (n))

#define io_seal(e, t, cid) (cid_hot(cid) ? rfc_seal(e, t) : (t))

static Term io_node(Env e, u64 cid, Term a, Term b) {
  Loc l = heap_alloc(e, 1);
  e.mem[l]     = io_seal(e, a, cid);
  e.mem[l + 1] = io_seal(e, b, cid);
  return term_ctr(cid, l);
}

// 1-byte cells until a wider scalar arrives; then the decoded cells move to
// that width (at most twice).
static Term io_str(Env e, const char* p, u64 n) {
  StrParts out = str_alloc(e, n, 2);
  if (err_seen(e.mem)) { return str_view_owned(e, out); }
  u32 len = 0;
  for (u64 i = 0; i < n;) {
    u32 b = (u8)p[i], c = b, k = b < 0x80 ? 1
      : b >= 0xc2 && b <= 0xdf ? 2 : b >= 0xe0 && b <= 0xef ? 3
      : b >= 0xf0 && b <= 0xf4 ? 4 : 0;
    bool ok = k && k <= n - i;
    if (k > 1) {
      c = b & (0x7f >> k);
      for (u32 j = 1; ok && j < k; j++) {
        u32 t = (u8)p[i + j]; ok = (t & 0xc0) == 0x80;
        c = (c << 6) | (t & 63);
      }
      ok = ok && c >= (k == 2 ? 0x80u : k == 3 ? 0x800u : 0x10000u)
        && c <= 0x10ffff && !(c >= 0xd800 && c <= 0xdfff);
    }
    c = ok ? c : 0xfffd;
    i += ok ? k : 1;
    if (str_fit(c) < str_nar(out)) {
      StrParts q = str_alloc(e, len + 1 + (n - i), str_fit(c));
      out.len = len;
      if (q.data) { str_copy_cells(e, q, 0, out); }
      term_sink(e, out.data);
      out = q;
      if (err_seen(e.mem)) { break; }
    }
    str_put(e, out, len++, c);
  }
  out.len = len;
  return str_view_owned(e, out);
}

#define io_tup(e, a, b) io_node(e, CID_TUPLE, a, b)
#define io_done(e, v)   io_box(e, CID_DONE, v)

static Term io_box(Env e, u64 cid, Term v) {
  Loc l = heap_alloc(e, 0);
  e.mem[l] = io_seal(e, v, cid);
  return term_ctr(cid, l);
}

static Term io_fail(Env e, u32 code, const char* text) {
  const char* s = text != NULL ? text : strerror((int)code);
  Term t = io_tup(e, code, io_str(e, s, strlen(s)));
  return io_box(e, CID_FAIL, t);
}

static lock           io_gate = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t io_bell = PTHREAD_COND_INITIALIZER;
static u32            io_busy;
static u32            io_size;
static int            io_wake_fd[2];

static void io_take(Env e) {
  IoAct*  acts[64];
  ssize_t n;
  while ((n = read(io_wake_fd[0], acts, sizeof acts)) > 0) {
    for (u32 i = 0; i < (u32)n / sizeof(IoAct*); i += 1) {
      IoAct* a = acts[i];
      a->item  = a->work.pack(e, &a->work);
      io_push(&io_runs, a);
      io_busy -= 1;
    }
  }
}

static void* io_help(void* arg) {
  for (;;) {
    pthread_mutex_lock(&io_gate);
    while (io_jobs.head == NULL) {
      pthread_cond_wait(&io_bell, &io_gate);
    }
    IoAct* a = io_pop(&io_jobs);
    pthread_mutex_unlock(&io_gate);
    a->work.call(&a->work);
    while (write(io_wake_fd[1], &a, sizeof a) != sizeof a) {
    }
  }
}

// A helper takes the effect's activation: call on its thread, then pack
// on the loop's, whose value readies the activation.
static Term io_work(IoWork* w, IoCall call, IoPack pack) {
  w->call  = call;
  w->pack  = pack;
  io_busy += 1;
  if (io_busy > io_size && io_size < IO_HELP) {
    pthread_t tid;
    if (pthread_create(&tid, NULL, io_help, NULL)) {
      err_fail("pthread_create");
    }
    pthread_detach(tid);
    io_size += 1;
  }
  pthread_mutex_lock(&io_gate);
  io_push(&io_jobs, (IoAct*)w);
  pthread_cond_signal(&io_bell);
  pthread_mutex_unlock(&io_gate);
  return IO_PARK;
}

// Runs the request in cont: the effect takes its fields (the node goes)
// and answers a value, which readies the activation, or IO_PARK, a moved.
static Term io_exec(Env e, IoWork* w) {
  IoAct* a = (IoAct*)w;
  Term   fs[256];
  u32    c = (u32)term_aux(a->cont);
  u32    n = cid_arity(c);
  spare_free(e, cls_fit(n), ctr_take(e, a->cont, n, fs));
  a->cont = fs[n - 1];
  return io_eff_rows[c].run(e, fs, w);
}

static void io_wait(Env e) {
  struct pollfd* fds = io_mem(malloc((io_live + 1) * sizeof *fds));
  u32 n    = 1;
  u64 soon = 0;
  int ms   = -1;
  fds[0].fd     = io_wake_fd[0];
  fds[0].events = POLLIN;
  for (IoAct* a = io_park.head; a != NULL; a = a->next) {
    if (a->time != 0) {
      soon = soon == 0 || a->time < soon ? a->time : soon;
    }
    if (a->evts != 0) {
      fds[n].fd     = (int)a->work.word;
      fds[n].events = a->evts;
      n += 1;
    }
  }
  if (soon != 0) {
    u64 now = io_tick();
    u64 gap = soon > now ? (soon - now) / 1000000 + 1 : 0;
    ms = gap > 0x7fffffff ? 0x7fffffff : (int)gap;
  }
  io_sync();
  while (poll(fds, n, ms) < 0) {
    if (errno != EINTR) {
      err_fail("the poller failed");
    }
  }
  if (fds[0].revents != 0) {
    io_take(e);
  }
  u64   now  = io_tick();
  u32   i    = 1;
  IoQue todo = io_park;
  io_park.head = NULL;
  io_park.last = NULL;
  while (todo.head != NULL) {
    IoAct* a   = io_pop(&todo);
    bool   due = (a->evts != 0 && fds[i].revents != 0)
      || (a->time != 0 && a->time <= now);
    i += a->evts != 0;
    if (!due) {
      io_push(&io_park, a);
      continue;
    }
    Term x = a->work.pack(e, &a->work);
    if (x != IO_PARK) {
      a->item = x;
      io_push(&io_runs, a);
    }
  }
  free(fds);
}

static int f32_text(char* buf, f32 v) {
  int n = 0;
  int p = 0;
  if (v != v) {
    return sprintf(buf, "nan");
  }
  for (; p < 9; p += 1) {
    n = snprintf(buf, 40, "%.*e", p, (double)v);
    if (strtof(buf, NULL) == v) {
      break;
    }
  }
  char* ep = strchr(buf, 'e');
  if (ep == NULL) {
    return n;
  }
  int ex = atoi(ep + 1);
  if (ex >= 21 || ex <= -7) {
    n = (int)(ep - buf) + sprintf(ep, "e%c%d", ex < 0 ? '-' : '+', abs(ex));
  } else if (ex <= p) {
    n = snprintf(buf, 40, "%.*f", p - ex, (double)v);
  } else {
    int s = *buf == '-';
    memmove(buf + s + 1, buf + s + 2, p);
    memset(buf + s + 1 + p, '0', ex - p);
    n = s + 1 + ex;
  }
  return n;
}

static Term f32_show(Env e, Term x) {
  char buf[40];
  return io_str(e, buf, f32_text(buf, f32_unbox(x)));
}

// F32.read/F64.read accept one grammar on both lanes, over the whole
// extent: ASCII space, a sign, digits with a point and an exponent, or
// inf/infinity/nan, any case. A NUL is a character, not an end, and the
// strtod extras (hex floats, nan(...)) are not spellings.
static bool io_word(const char* p, u64 n, const char* w) {
  for (u64 i = 0; i < n; i++) {
    if ((p[i] | 32) != w[i]) { return false; }
  }
  return w[n] == 0;
}

static bool io_num(const char* p, u64 n) {
  u64 i = 0, d = 0;
  while (i < n && (p[i] == ' ' || (p[i] >= 9 && p[i] <= 13))) { i++; }
  if (i < n && (p[i] == '+' || p[i] == '-')) { i++; }
  if (io_word(p + i, n - i, "inf") || io_word(p + i, n - i, "infinity")
    || io_word(p + i, n - i, "nan")) {
    return true;
  }
  while (i < n && p[i] >= '0' && p[i] <= '9') { i++; d++; }
  if (i < n && p[i] == '.') {
    i++;
    while (i < n && p[i] >= '0' && p[i] <= '9') { i++; d++; }
  }
  if (d == 0) { return false; }
  if (i < n && (p[i] == 'e' || p[i] == 'E')) {
    i++;
    if (i < n && (p[i] == '+' || p[i] == '-')) { i++; }
    d = 0;
    while (i < n && p[i] >= '0' && p[i] <= '9') { i++; d++; }
    if (d == 0) { return false; }
  }
  return i == n;
}

static Term f32_read(Env e, Term s) {
  u64 n = 0;
  char* text = io_cstr(e, s, &n);
  char* end;
  f32 v = strtof(text, &end);
  Term out = n > 0 && (u64)(end - text) == n && strpbrk(text, "xX(") == NULL
    ? io_box(e, CID_SOME, f32_rewrap(v)) : term_pak(CID_NONE, 0);
  free(text);
  return out;
}

static int f64_text(char* buf, f64 v) {
  int n = 0;
  int p = 0;
  if (v != v) {
    return sprintf(buf, "nan");
  }
  for (; p < 17; p += 1) {
    n = snprintf(buf, 40, "%.*e", p, (double)v);
    if (strtod(buf, NULL) == v) {
      break;
    }
  }
  char* ep = strchr(buf, 'e');
  if (ep == NULL) {
    return n;
  }
  int ex = atoi(ep + 1);
  if (ex >= 21 || ex <= -7) {
    n = (int)(ep - buf) + sprintf(ep, "e%c%d", ex < 0 ? '-' : '+', abs(ex));
  } else if (ex <= p) {
    n = snprintf(buf, 40, "%.*f", p - ex, (double)v);
  } else {
    int s = *buf == '-';
    memmove(buf + s + 1, buf + s + 2, p);
    memset(buf + s + 1 + p, '0', ex - p);
    n = s + 1 + ex;
  }
  return n;
}

static Term f64_show(Env e, Term x) {
  char buf[48];
  return io_str(e, buf, f64_text(buf, f64_unbox(x)));
}

static Term f64_read(Env e, Term s) {
  u64 n = 0;
  char* text = io_cstr(e, s, &n);
  Term out = io_num(text, n) ? io_box(e, CID_SOME, f64_rewrap(strtod(text, NULL)))
    : term_pak(CID_NONE, 0);
  free(text);
  return out;
}

// Show
// ====

#if MAIN_PURE

// A pure main's value, spelled as term_show spells it: d is a node of
// SHOW_DESC (see show_main), w the value's words. A boxed Data reads its
// arm by cid off a Term (packed, or a node), an inline one by tag off
// its words.
static void show_val(Env e, u32 d, const Term* w, char chain);

// char_show: an escape, a \u{hex}, else the code point in UTF-8
static void show_chr(u64 c, char q) {
  char b[4];
  int  k = c == 10 ? 'n' : c == 9 ? 't' : c == 13 ? 'r' : c == 0 ? '0'
    : c == 92 || c == (u64)q ? (int)c : 0;
  if (k != 0) {
    printf("\\%c", k);
  } else if (c < 32 || c == 127 || (c >= 0xD800 && c <= 0xDFFF)
    || c > 0x10FFFF) {
    printf("\\u{%llx}", (unsigned long long)c);
  } else {
    fwrite(b, 1, io_utf8(b, c), stdout);
  }
}

// The shortest text that reads back, as a literal: a point before an e
static void show_f32(u32 x) {
  char  buf[40];
  int   n  = f32_text(buf, f32_unbox(x));
  char* ep = memchr(buf, 'e', n);
  int   m  = ep == NULL ? n : (int)(ep - buf);
  buf[n] = 0;
  if (strpbrk(buf, ".ni") == NULL) {
    printf("%.*s.0%s", m, buf, buf + m);
  } else {
    fputs(buf, stdout);
  }
}

static void show_arr(Env e, u32 d, Term t, u32 lo, u32 c) {
  if (c > SHOW_DESC[d + 2]) {
    c -= 1;
    show_arr(e, d, t, lo, c);
    fputs(", ", stdout);
    show_arr(e, d, t, lo + (1u << c), c);
  } else {
    Term v[1u << c];
    for (u32 j = 0; j < 1u << c; j += 1) {
      v[j] = blk_read(e.mem, term_tag(t) == TAG_ARR, term_peek(e, t), lo + j);
    }
    show_val(e, SHOW_DESC[d + 1], v, 0);
  }
}

// chain is the bracket of the [a, b] or (a, b) this value continues, or
// 0: a Con or Nil spells a list, a Tuple a tuple, their tails continue
static void show_val(Env e, u32 d, const Term* w, char chain) {
  const u32* D = SHOW_DESC;
  Term one;
  char zs[4];
  u32  zn = 0;
  for (bool tail = true; tail;) switch (tail = false, D[d]) {
    case 0: printf("%u", (u32)w[0]); break;
    case 1: show_f32((u32)w[0]); break;
    case 2: printf("%llun", (unsigned long long)w[0]); break;
    case 3:
      putchar('\'');
      show_chr(D[d + 1] != 0 ? term_loc(w[0]) : w[0], '\'');
      putchar('\'');
      break;
    case 4:
      putchar('"');
      {
        StrParts p = str_peek(e, w[0]);
        for (u32 i = 0; i < p.len; i++) { show_chr(str_at_peek(e, p, i), '"'); }
      }
      putchar('"');
      break;
    case 5: fputs("{==}", stdout); break;
    case 6:
      putchar('[');
      show_arr(e, d, w[0], 0, blk_cls(w[0]));
      putchar(']');
      break;
    default: {
      Term t   = w[0];
      bool box = D[d + 1] != 0;
      u32  key = box ? (u32)term_aux(t) : D[d + 2] > 1 ? (u32)t : 0;
      u32  a   = d + 3;
      for (u32 i = 0; box ? D[a + 1] != key : i != key; i += 1) {
        a += 3 + 2 * D[a + 2];
      }
      if (box) {
        one = term_loc(t);
        w   = term_tag(t) == TAG_PAK ? &one : e.mem + term_peek(e, t);
      }
      const char* k = SHOW_NAMES[D[a]];
      char o = '{';
      char z = '}';
      if (strcmp(k, "Con") == 0 || strcmp(k, "Nil") == 0) {
        o = '[';
        z = ']';
      } else if (strcmp(k, "Tuple") == 0) {
        o = '(';
        z = ')';
      }
      if (o == '{') {
        printf("%s{", k);
      } else if (chain != o) {
        putchar(o);
      }
      if (o == '{' || chain != o) {
        zs[zn++] = z;
      }
      for (u32 j = 0; j < D[a + 2]; j += 1) {
        if (o == '[' ? j == 0 && chain == o : j > 0) {
          fputs(", ", stdout);
        }
        if (j == 1 && o != '{') {
          tail  = true;
          chain = o;
          d     = D[a + 4 + 2 * j];
          w     = w + D[a + 3 + 2 * j];
        } else {
          show_val(e, D[a + 4 + 2 * j], w + D[a + 3 + 2 * j], 0);
        }
      }
    }
  }
  while (zn > 0) {
    putchar(zs[--zn]);
  }
}

#endif

// The continuation applied to the item is the next request.
static int io_step(Env e, IoAct* a) {
  for (;;) {
    Loc  ap  = task_node(e, FID_CLO_APPLY, TERM_HOLE, 0, 0);
    e.mem[ap]     = a->cont;
    e.mem[ap + 1] = a->item;
    Term req = corpus_eval(e.mem, term_tsk(FID_CLO_APPLY, ap));
    u32  c   = (u32)term_aux(req);
    Loc  at  = term_peek(e, req);
    if (c == CID_EMIT) {
      term_drop(e, req);
      free(a);
      io_live -= 1;
      return -1;
    }
    if (c == CID_HALT) {
      io_errs(e, e.mem[at + 1]);
      return (int)(u32)e.mem[at];
    }
    if (io_eff_rows[c].run == NULL) {
      err_fail("an alien request");
    }
    u32 need = io_eff_rows[c].ask;
    u32 word = (u32)(need & IO_READ ? io_hand_v(e.mem[at]) : e.mem[at]);
    a->cont  = req;
    if (need != 0) {
      io_wait_on(&a->work, (int)word, need & IO_READ ? POLLIN : 0,
        need & IO_TIME ? io_tick() + (u64)word * 1000000ull : 0, io_exec);
      return -1;
    }
    Term x = io_exec(e, &a->work);
    if (x == IO_PARK) {
      return -1;
    }
    a->item = x;
  }
}

OUTLINE int io_loop(Corpus H) {
  Env e = { H, ALC[0] };
  io_stk = pool_stack();
  signal(SIGPIPE, SIG_IGN);
  if (pipe(io_wake_fd) | fcntl(io_wake_fd[0], F_SETFL, O_NONBLOCK)) {
    err_fail("the event loop failed to open");
  }
  Term m = corpus_eval(H, term_tsk(MAIN_FID, task_node(e, MAIN_FID,
    TERM_HOLE, 0, 0)));
#if MAIN_PURE
  show_val(e, 0, H + H_ROOT_WORD, 0);
  putchar('\n');
  return 0;
#endif
  io_spawn(m);
  for (u32 n = 0;; n += 1) {
    if (io_runs.head == NULL) {
      if (io_live == 0) {
        return 0;
      }
      if (io_park.head == NULL && io_busy == 0) {
        io_sync();
        fprintf(stderr, "bend: deadlock: every computation waits on a"
          " channel\n");
        return 1;
      }
      io_wait(e);
      continue;
    }
    if ((n & 63) == 0 && io_busy != 0) {
      io_take(e);
    }
    int code = io_step(e, io_pop(&io_runs));
    if (code >= 0) {
      return code;
    }
  }
}

// Chan
// ====

// ChanRow ::=
//   | ChanRow(gen, next, room, size, head, live, shut, ring, wait)
typedef struct {
  u32   gen;
  u32   next;
  u32   room;
  u32   size;
  u32   head;
  u32   live;
  u32   shut;
  Term* ring;
  IoQue wait;
} ChanRow;

// A channel is Data: its handle is copied and may outlive the row, so it
// names the row by index and generation, a freed row waits on a list and
// comes back one generation up, and a stale copy finds no row (closed).
static ChanRow* chan_rows;
static u32      chan_len;
static u32      chan_idle = ~0u;

#define chan_some(e, v) io_box(e, CID_SOME, v)
#define chan_bool(b)    term_pak((b) ? CID_TRUE : CID_FALSE, 0)

static Term chan_open(u32 room) {
  u32 i = chan_idle;
  if (i != ~0u) {
    chan_idle = chan_rows[i].next;
  } else {
    if (chan_len == 1u << 24) {
      err_fail("more than 16777216 channels at once");
    }
    if ((chan_len & (chan_len - 1)) == 0) {
      chan_rows = io_mem(realloc(chan_rows,
        (chan_len == 0 ? 1 : 2 * chan_len) * sizeof(ChanRow)));
    }
    i = chan_len;
    chan_len += 1;
    chan_rows[i].gen = 0;
  }
  ChanRow* row = &chan_rows[i];
  row->gen  += 1;
  row->room  = room;
  row->size  = 0;
  row->head  = 0;
  row->live  = 1;
  row->shut  = 0;
  row->ring  = room == 0 ? NULL : io_mem(malloc(room * sizeof(Term)));
  row->wait.head = NULL;
  row->wait.last = NULL;
  return io_hand(((u64)row->gen << 24) | i);
}

static ChanRow* chan_at(Term t) {
  u64      v   = io_hand_v(t);
  u32      i   = (u32)v & 0xFFFFFF;
  ChanRow* row = i < chan_len ? &chan_rows[i] : NULL;
  return row != NULL && row->live && row->gen == (u32)(v >> 24) ? row : NULL;
}

// Parks the effect's activation on row with item: a sent value, or
// TERM_HOLE for a receiver.
static Term chan_park(ChanRow* row, IoWork* w, Term item) {
  IoAct* a = (IoAct*)w;
  a->item  = item;
  io_push(&row->wait, a);
  return IO_PARK;
}

static Term chan_wake(ChanRow* row, Term x) {
  IoAct* a  = io_pop(&row->wait);
  Term item = a->item;
  a->item   = x;
  io_push(&io_runs, a);
  return item;
}

static Term chan_take(ChanRow* row) {
  Term v = row->ring[row->head];
  row->head = (row->head + 1) % row->room;
  row->size -= 1;
  if (row->wait.head != NULL) {
    Term item = chan_wake(row, chan_bool(true));
    row->ring[(row->head + row->size) % row->room] = item;
    row->size += 1;
  }
  return v;
}

static void chan_free(ChanRow* row) {
  free(row->ring);
  row->live = 0;
  row->next = chan_idle;
  chan_idle = (u32)(row - chan_rows);
}

static void chan_shut(Env e, ChanRow* row) {
  row->shut = 1;
  while (row->wait.head != NULL) {
    bool rcv = row->wait.head->item == TERM_HOLE;
    Term x = rcv ? term_pak(CID_NONE, 0) : chan_bool(false);
    term_sink(e, chan_wake(row, x));
  }
  if (row->size == 0) {
    chan_free(row);
  }
}

// Requests
// ========

// IO
// ==

void io_print(const char* data, uint64_t len) {
  io_out(stdout, data, len);
  io_out(stdout, "\n", 1);
}

Term io_print_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* text = io_cstr(e, f[0], &n);
  io_print(text, n);
  free(text);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) io_print_use(void) {
  io_eff(CID_IO_PRINT, io_print_run, 0);
}


// Cli
// ===

static void cli_fail(const char* msg, const char* arg) {
  fprintf(stderr, "bend: %s%s\n", msg, arg != NULL ? arg : "");
  exit(1);
}

// Main
// ====

int main(int argc, char** argv) {
  long thr = 0;
  int  gpu = -1;
  u64  mem = 0;
  io_argv = argv + 1;
  for (int i = 1; i < argc; i += 1) {
    const char* a = argv[i];
    const char* v = i + 1 < argc ? argv[i + 1] : NULL;
    if (strcmp(a, "--") == 0) {
      while (i + 1 < argc) {
        io_argv[io_argc++] = argv[++i];
      }
    } else if (strcmp(a, "--help") == 0) {
      printf(CLI_HELP, argv[0]);
      return 0;
    } else if (strcmp(a, "--gpu-build") == 0) {
      if (gpu_probe() && !gpu_make(gpu_path())) {
        cli_fail("cannot write ", gpu_path());
      }
      return 0;
    } else if (strcmp(a, "--threads") == 0) {
      char* end = NULL;
      thr = v != NULL ? strtol(v, &end, 10) : 0;
      if (thr < 1 || end == NULL || *end != '\0') {
        cli_fail("expected a thread count of 1 or more after --threads", NULL);
      }
      i += 1;
    } else if (strcmp(a, "--gpu") == 0) {
      char*  end = NULL;
      double n   = v != NULL ? strtod(v, &end) : 0;
      u64    mul = end == NULL ? 0 : strcmp(end, "GB") == 0 ? 1ull << 30
        : strcmp(end, "MB") == 0 ? 1ull << 20 : 0;
      if (v != NULL && strcmp(v, "off") == 0) {
        gpu = 0;
      } else if (v != NULL && (strcmp(v, "on") == 0 || (mul != 0 && n > 0))) {
        gpu = 1;
        mem = (u64)(n * (double)mul);
      } else {
        cli_fail("expected on, off or a size like 4GB after --gpu", NULL);
      }
      i += 1;
    } else {
      io_argv[io_argc++] = argv[i];
    }
  }
  bool dev = gpu != 0 && BANGS != 0 && gpu_probe();
  if (gpu == 1 && BANGS != 0 && !dev) {
    cli_fail("--gpu on, but this binary found no GPU device", NULL);
  }
  Corpus H  = corpus_setup(dev, thr > 0 ? thr : cpu_count(), mem);
  int code  = io_loop(H);
  io_sync();
  return code;
}

#endif
