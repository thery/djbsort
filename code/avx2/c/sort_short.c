/* sort_short.c -- the shortened AVX2 int32_sort, real intrinsics.
   Same compare-exchanges, in the same order, as djbsort's sort.c;
   the copy-pasted batches become loops over named helpers. */

#include <stdint.h>
#include <immintrin.h>

#define int32 int32_t
typedef __m256i int32x8;

#define V_load(z) _mm256_loadu_si256((__m256i *) (z))
#define V_store(z,i) _mm256_storeu_si256((__m256i *) (z),(i))
#define V_MINMAX(a,b) \
  do { int32x8 c_ = _mm256_min_epi32(a,b); b = _mm256_max_epi32(a,b); a = c_; } while (0)

static void s_minmax(int32 *a, int32 *b)
{
  int32 ab = *b ^ *a;
  int32 c = (int32)((int64_t)*b - (int64_t)*a);
  c ^= ab & (c ^ *b);
  c >>= 31;
  c &= ab;
  *a ^= c;
  *b ^= c;
}

/* ---- comparator batches -------------------------------------------------- */

typedef struct { const unsigned char (*p)[2]; int n; } net_t;

static const unsigned char P_mrg8[12][2] =
  { {0,4},{1,5},{2,6},{3,7}, {0,2},{1,3},{4,6},{5,7}, {0,1},{2,3},{4,5},{6,7} };
static const unsigned char P_mrg8r[12][2] =
  { {0,1},{2,3},{4,5},{6,7}, {0,2},{1,3},{4,6},{5,7}, {0,4},{1,5},{2,6},{3,7} };
static const unsigned char P_mrg4[4][2] = { {0,2},{1,3},{0,1},{2,3} };
static const unsigned char P_mrg2[1][2] = { {0,1} };
static const unsigned char P_tail8[12][2] =
  { {0,4},{1,5},{2,6},{3,7}, {0,2},{1,3}, {0,1},{2,3}, {4,6},{5,7}, {4,5},{6,7} };
static const unsigned char P_even4[5][2] = { {2,0},{3,1},{1,0},{3,2},{1,2} };
static const unsigned char P_odd4[5][2]  = { {0,2},{1,3},{0,1},{2,3},{2,1} };

static const net_t N_mrg8   = { P_mrg8, 12 };
static const net_t N_mrg8r  = { P_mrg8r, 12 };
static const net_t N_mrg4   = { P_mrg4, 4 };
static const net_t N_mrg2   = { P_mrg2, 1 };

static inline __attribute__((always_inline)) void vnet(int32x8 *v, net_t g)
{
  for (int t = 0; t < g.n; t++) {
    int i = g.p[t][0], j = g.p[t][1];
    V_MINMAX(v[i], v[j]);
  }
}

static void snet(int32 *z, const unsigned char (*p)[2], int np)
{
  for (int t = 0; t < np; t++) s_minmax(&z[p[t][0]], &z[p[t][1]]);
}

static inline __attribute__((always_inline)) void vnet_adj(int32x8 *v, int w)
{
  for (int t = 0; t < w; t += 2) V_MINMAX(v[t], v[t+1]);
}

/* ---- pairwise lane shuffles --------------------------------------------- */

static inline __attribute__((always_inline)) void pw_perm(int32x8 *v, int w)
{
  for (int t = 0; t < w; t += 2) {
    int32x8 a = v[t], b = v[t+1];
    v[t]   = _mm256_permute2x128_si256(a,b,0x20);
    v[t+1] = _mm256_permute2x128_si256(a,b,0x31);
  }
}

static inline __attribute__((always_inline)) void pw_unpack64(int32x8 *v, int w)
{
  for (int t = 0; t < w; t += 2) {
    int32x8 a = v[t], b = v[t+1];
    v[t]   = _mm256_unpacklo_epi64(a,b);
    v[t+1] = _mm256_unpackhi_epi64(a,b);
  }
}

static inline __attribute__((always_inline)) void pw_unpack32(int32x8 *v, int w)
{
  for (int t = 0; t < w; t += 2) {
    int32x8 a = v[t], b = v[t+1];
    v[t]   = _mm256_unpacklo_epi32(a,b);
    v[t+1] = _mm256_unpackhi_epi32(a,b);
  }
}

/* ---- the 8x8 lane transpose, in its two halves --------------------------- */

/* out[r] collects lane sw[r%4] (+4*(r/4)) of v[4*(r/4)..4*(r/4)+3] */
static void tr_lo(int32x8 *v)
{
  int32x8 o[8];
  for (int g = 0; g < 8; g += 4) {
    int32x8 a0 = _mm256_unpacklo_epi32(v[g],v[g+1]);
    int32x8 a1 = _mm256_unpackhi_epi32(v[g],v[g+1]);
    int32x8 a2 = _mm256_unpacklo_epi32(v[g+2],v[g+3]);
    int32x8 a3 = _mm256_unpackhi_epi32(v[g+2],v[g+3]);
    o[g]   = _mm256_unpacklo_epi64(a0,a2);
    o[g+1] = _mm256_unpacklo_epi64(a1,a3);
    o[g+2] = _mm256_unpackhi_epi64(a0,a2);
    o[g+3] = _mm256_unpackhi_epi64(a1,a3);
  }
  for (int t = 0; t < 8; t++) v[t] = o[t];
}

static const int SW[4] = { 0,2,1,3 };

/* out[r] = permute2x128(v[sw[r%4]], v[4+sw[r%4]], r<4 ? 0x20 : 0x31) */
static void tr_hi(int32x8 *v)
{
  int32x8 o[8];
  for (int t = 0; t < 4; t++) {
    int32x8 a = v[SW[t]], b = v[4+SW[t]];
    o[t]   = _mm256_permute2x128_si256(a,b,0x20);
    o[t+4] = _mm256_permute2x128_si256(a,b,0x31);
  }
  for (int t = 0; t < 8; t++) v[t] = o[t];
}

static void transpose8(int32x8 *v) { tr_lo(v); tr_hi(v); }

/* rows in by swapping bits 0 and 2, full transpose, rows out by sw */
static void transpose8p(int32x8 *v)
{
  int32x8 u[8];
  for (int c = 0; c < 8; c++) u[c] = v[4*(c&1) + (c&2) + (c>>2)];
  transpose8(u);
  for (int r = 0; r < 8; r++) v[r] = u[4*(r/4) + SW[r%4]];
}

/* ---- strided compare-exchange sweeps ------------------------------------- */

static inline __attribute__((always_inline)) void blockn(int32 *x, long long base, long long span, long long q,
                   int cnt, net_t g)
{
  for (long long i = base; i < base + span; i += 8) {
    int32x8 v[8];
    for (int t = 0; t < cnt; t++) v[t] = V_load(&x[i + t*q]);
    vnet(v,g);
    for (int t = 0; t < cnt; t++) V_store(&x[i + t*q], v[t]);
  }
}

static inline __attribute__((always_inline)) long long stage(int32 *x, long long n, int cnt, long long q, net_t g)
{
  long long k = 0;
  while (k + cnt*q <= n) { blockn(x,k,q,q,cnt,g); k += cnt*q; }
  return k;
}

static void ladder(int32 *x, long long n)
{
  long long q = n >> 4;
  while (q >= 128 || q == 32) { stage(x,n,8,q>>2,N_mrg8); q >>= 3; }
  while (q >= 16) { q >>= 1; stage(x,n,4,q,N_mrg4); q >>= 1; }
  if (q == 8) stage(x,n,2,8,N_mrg2);
}

/* ---- the reversing passes ------------------------------------------------ */

static void rev_pass(int32 *x, long long n, int p)
{
  int32x8 m = (p == 4) ? _mm256_set_epi32(0,0,0,0,-1,-1,-1,-1)
            : (p == 2) ? _mm256_set_epi32(0,0,-1,-1,-1,-1,0,0)
                       : _mm256_set_epi32(0,-1,-1,0,0,-1,-1,0);
  int nlev = (p == 4) ? 0 : (p == 2) ? 1 : 2;   /* 0: perm, 1: unpack64 */
  for (long long z = 0; z < n; z += 16) {
    int32x8 v[2];
    v[0] = _mm256_xor_si256(V_load(&x[z]), m);
    v[1] = _mm256_xor_si256(V_load(&x[z+8]), m);
    for (int l = 0; l < nlev; l++) { if (l == 0) pw_perm(v,2); else pw_unpack64(v,2); }
    for (int l = nlev - 1; l >= 0; l--) {
      V_MINMAX(v[0], v[1]);
      if (l == 0) pw_perm(v,2); else pw_unpack64(v,2);
    }
    V_store(&x[z], v[0]);
    V_store(&x[z+8], v[1]);
  }
}

/* ---- one bitonic merge of w*8 contiguous elements, w in {2,4,8} ---------- */

static inline __attribute__((always_inline)) void bmerge(int32 *x, long long j, int w, net_t first)
{
  int32x8 v[8];
  for (int t = 0; t < w; t++) v[t] = V_load(&x[j + 8*t]);
  vnet(v,first);
  if (w == 2) for (int t = 0; t < w; t++) V_store(&x[j + 8*t], v[t]);
  pw_perm(v,w);      vnet_adj(v,w);
  pw_perm(v,w);
  pw_unpack64(v,w);  vnet_adj(v,w);
  pw_unpack32(v,w);
  pw_unpack64(v,w);  vnet_adj(v,w);
  pw_unpack32(v,w);
  for (int t = 0; t < w; t++) V_store(&x[j + 8*t], v[t]);
}

/* ---- minmax_vector, merge16_finish (verbatim from sort.c) ---------------- */

static void minmax_vector(int32 *x, int32 *y, long long n)
{
  if (n < 8) {
    while (n > 0) { s_minmax(x,y); ++x; ++y; --n; }
    return;
  }
  if (n & 7) {
    int32x8 x0 = V_load(&x[n-8]);
    int32x8 y0 = V_load(&y[n-8]);
    V_MINMAX(x0,y0);
    V_store(&x[n-8],x0);
    V_store(&y[n-8],y0);
    n &= ~7;
  }
  do {
    int32x8 x0 = V_load(x);
    int32x8 y0 = V_load(y);
    V_MINMAX(x0,y0);
    V_store(x,x0);
    V_store(y,y0);
    x += 8; y += 8; n -= 8;
  } while (n);
}

static void merge16_finish(int32 *x, int32x8 x0, int32x8 x1, int flagdown)
{
  int32x8 v[2];
  V_MINMAX(x0,x1);
  v[0] = x0; v[1] = x1;
  pw_perm(v,2);     V_MINMAX(v[0],v[1]);
  pw_unpack64(v,2); V_MINMAX(v[0],v[1]);
  pw_unpack32(v,2);
  pw_unpack64(v,2); V_MINMAX(v[0],v[1]);
  pw_unpack32(v,2);
  pw_perm(v,2);
  if (flagdown) {
    int32x8 mask = _mm256_set1_epi32(-1);
    v[0] = _mm256_xor_si256(v[0],mask);
    v[1] = _mm256_xor_si256(v[1],mask);
  }
  V_store(&x[0],v[0]);
  V_store(&x[8],v[1]);
}

/* ---- n a power of two, n >= 8 -------------------------------------------- */

static void sort_2power(int32 *x, long long n, int flagdown)
{
  int32x8 mask = _mm256_set1_epi32(-1);

  if (n == 8) {
    static const unsigned char p8[19][2] =
      { {1,0},{3,2},{2,0},{3,1},{2,1},
        {5,4},{7,6},{6,4},{7,5},{6,5},
        {4,0},{6,2},{4,2},
        {5,1},{7,3},{5,3},
        {2,1},{4,3},{6,5} };
    for (int t = 0; t < 19; t++) s_minmax(&x[p8[t][0]], &x[p8[t][1]]);
    return;
  }

  if (n == 16) {
    int32x8 v[2];
    int32x8 m = _mm256_set_epi32(0,0,-1,-1,0,0,-1,-1);
    v[0] = _mm256_xor_si256(V_load(&x[0]),m);
    v[1] = _mm256_xor_si256(V_load(&x[8]),m);
    pw_unpack32(v,2); pw_unpack64(v,2); V_MINMAX(v[0],v[1]);
    m = _mm256_set_epi32(0,0,-1,-1,-1,-1,0,0);
    v[0] = _mm256_xor_si256(v[0],m);
    v[1] = _mm256_xor_si256(v[1],m);
    pw_unpack32(v,2); V_MINMAX(v[0],v[1]);
    pw_unpack64(v,2);
    pw_unpack32(v,2); pw_unpack64(v,2); V_MINMAX(v[0],v[1]);
    pw_unpack32(v,2);
    v[0] = _mm256_xor_si256(v[0],m);
    v[1] = _mm256_xor_si256(v[1],m);
    pw_perm(v,2); V_MINMAX(v[0],v[1]);
    pw_perm(v,2); V_MINMAX(v[0],v[1]);
    pw_unpack64(v,2);
    pw_unpack32(v,2); pw_unpack64(v,2); V_MINMAX(v[0],v[1]);
    pw_unpack32(v,2); pw_unpack64(v,2);
    if (flagdown) v[1] = _mm256_xor_si256(v[1],mask);
    else          v[0] = _mm256_xor_si256(v[0],mask);
    merge16_finish(x,v[0],v[1],flagdown);
    return;
  }

  if (n == 32) {
    sort_2power(x,16,1);
    sort_2power(x+16,16,0);
    int32x8 x0 = V_load(&x[0]), x1 = V_load(&x[8]);
    int32x8 x2 = V_load(&x[16]), x3 = V_load(&x[24]);
    if (flagdown) {
      x0 = _mm256_xor_si256(x0,mask); x1 = _mm256_xor_si256(x1,mask);
      x2 = _mm256_xor_si256(x2,mask); x3 = _mm256_xor_si256(x3,mask);
    }
    V_MINMAX(x0,x2);
    V_MINMAX(x1,x3);
    merge16_finish(x,x0,x1,flagdown);
    merge16_finish(x+16,x2,x3,flagdown);
    return;
  }

  {
    long long p = n >> 3, i, j, k;

    for (i = 0; i < p; i += 8) {
      int32x8 e[4], o[4];
      for (int t = 0; t < 4; t++) e[t] = V_load(&x[i + 2*t*p]);
      vnet(e,(net_t){P_even4,5});
      for (int t = 0; t < 4; t++) V_store(&x[i + 2*t*p], e[t]);
      for (int t = 0; t < 4; t++) o[t] = V_load(&x[i + (2*t+1)*p]);
      vnet(o,(net_t){P_odd4,5});
      for (int t = 0; t < 4; t++) V_store(&x[i + (2*t+1)*p], o[t]);
    }

    if (n >= 128) {
      for (j = 0; j < n; j += 32) {
        V_store(&x[j],    _mm256_xor_si256(V_load(&x[j]),mask));
        V_store(&x[j+16], _mm256_xor_si256(V_load(&x[j+16]),mask));
      }

      for (p = 8;; p <<= 1) {
        long long q = p >> 1;
        while (q >= 128) { stage(x,n,8,q>>2,N_mrg8); q >>= 3; }
        if (q == 64) { stage(x,n,4,32,N_mrg4); q = 16; }
        if (q == 32) { stage(x,n,8,8,N_mrg8);  q = 4; }
        if (q == 16) { stage(x,n,4,8,N_mrg4);  q = 4; }
        if (q == 8)  { stage(x,n,2,8,N_mrg2); }

        q = n >> 3;
        int flip = (p << 1 == q);
        int flipflip = !flip;
        for (j = 0; j < q; j += p + p) {
          for (k = j; k < j + p + p; k += p) {
            for (i = k; i < k + p; i += 8) {
              int32x8 v[8];
              for (int t = 0; t < 8; t++) v[t] = V_load(&x[i + t*q]);
              vnet(v,N_mrg8r);
              if (flip) for (int t = 0; t < 8; t++) v[t] = _mm256_xor_si256(v[t],mask);
              for (int t = 0; t < 8; t++) V_store(&x[i + t*q], v[t]);
            }
            flip ^= 1;
          }
          flip ^= flipflip;
        }

        if (p << 4 == n) break;
      }
    }

    for (p = 4; p >= 1; p >>= 1) {
      rev_pass(x,n,(int)p);
      ladder(x,n);
      stage(x,n,8,n>>3,N_mrg8r);
    }

    for (i = 0; i < n; i += 64) {
      int32x8 v[8];
      for (int t = 0; t < 8; t++) v[t] = V_load(&x[i + 8*t]);
      tr_lo(v);
      if (flagdown) {
        v[2] = _mm256_xor_si256(v[2],mask); v[3] = _mm256_xor_si256(v[3],mask);
        v[6] = _mm256_xor_si256(v[6],mask); v[7] = _mm256_xor_si256(v[7],mask);
      } else {
        v[0] = _mm256_xor_si256(v[0],mask); v[1] = _mm256_xor_si256(v[1],mask);
        v[4] = _mm256_xor_si256(v[4],mask); v[5] = _mm256_xor_si256(v[5],mask);
      }
      tr_hi(v);
      vnet(v,N_mrg8r);
      transpose8(v);
      for (int t = 0; t < 8; t++) V_store(&x[i + 8*t], v[t]);
    }

    ladder(x,n);

    {
      long long q = n >> 3;
      static const int perm[8] = { 0,4,1,5,2,6,3,7 };
      for (i = 0; i < q; i += 8) {
        int32x8 v[8];
        for (int t = 0; t < 8; t++) v[t] = V_load(&x[i + t*q]);
        vnet(v,N_mrg8r);
        transpose8p(v);
        if (flagdown) for (int t = 0; t < 8; t++) v[t] = _mm256_xor_si256(v[t],mask);
        for (int t = 0; t < 8; t++) V_store(&x[i + t*q], v[perm[t]]);
      }
    }
  }
}

/* ---- entry point --------------------------------------------------------- */

void int32_sort_short(int32 *x, long long n)
{
  if (n <= 8) {
    for (long long len = n; len >= 2; len--)
      for (long long i = 0; i + 1 < len; i++) s_minmax(&x[i],&x[i+1]);
    return;
  }
  if ((n & (n-1)) == 0) { sort_2power(x,n,0); return; }

  {
    long long q = 8;
    while (q < n - q) q += q;

    if (q <= 128) {
      int32 y[256];
      for (long long i = q>>3; i < (q>>2); i++)
        for (int l = 0; l < 8; l++) y[8*i + l] = 0x7fffffff;
      for (long long i = 0; i < n; i++) y[i] = x[i];
      sort_2power(y,2*q,0);
      for (long long i = 0; i < n; i++) x[i] = y[i];
      return;
    }

    sort_2power(x,q,1);
    int32_sort_short(x+q, n-q);

    while (q >= 64) {
      q >>= 2;
      long long j = stage(x,n,8,q,N_mrg8);
      minmax_vector(&x[j],&x[j + 4*q], n - 4*q - j);
      if (j + 4*q <= n) { blockn(x,j,q,q,4,N_mrg4); j += 4*q; }
      minmax_vector(&x[j],&x[j + 2*q], n - 2*q - j);
      if (j + 2*q <= n) { blockn(x,j,q,q,2,N_mrg2); j += 2*q; }
      minmax_vector(&x[j],&x[j + q], n - q - j);
      q >>= 1;
    }

    {
      long long j = 0;
      for (int w = (int)(q >> 2); w >= 2; w >>= 1) {
        net_t first = (w == 8) ? N_mrg8 : (w == 4) ? N_mrg4 : N_mrg2;
        while (j + 8*w <= n) {
          if (w == 8) bmerge(x,j,8,first);
          else if (w == 4) bmerge(x,j,4,first);
          else bmerge(x,j,2,first);
          j += 8*w;
        }
        minmax_vector(&x[j],&x[j + 4*w], n - 4*w - j);
      }
      if (j + 8 <= n) { snet(&x[j],P_tail8,12); j += 8; }
      minmax_vector(&x[j],&x[j+4], n - 4 - j);
      if (j + 4 <= n) { snet(&x[j],P_mrg4,4); j += 4; }
      if (j + 3 <= n) s_minmax(&x[j],&x[j+2]);
      if (j + 2 <= n) s_minmax(&x[j],&x[j+1]);
    }
  }
}
