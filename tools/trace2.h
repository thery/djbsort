#include <stdint.h>
#include <immintrin.h>
extern int32_t *ct_a, *ct_b; extern long long ct_n;
static inline void ct_emit(int32_t p, int32_t q){ ct_a[ct_n]=p; ct_b[ct_n]=q; ct_n++; }
/* a cell is wire*2 + flip; xor with a lane mask of 0/-1 toggles the flip bit */
static inline __m256i ct_xor(__m256i a, __m256i m)
{ return _mm256_xor_si256(a, _mm256_and_si256(m, _mm256_set1_epi32(1))); }
/* emit the eight lane comparators of a vector compare-exchange, change nothing */
static inline void ct_vmm(__m256i a, __m256i b)
{ int32_t u[8],v[8];
  _mm256_storeu_si256((__m256i*)u,a); _mm256_storeu_si256((__m256i*)v,b);
  for (int k=0;k<8;k++) ct_emit(u[k],v[k]); }
