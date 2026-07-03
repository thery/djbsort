/* int32_minmax_x86.c -- scalar compare-exchange used by sort.c's tail cases.  */
/*                                                                            */
/* djbsort's original file of this name uses hand-written x86 `cmov` inline   */
/* assembly.  We substitute the portable branchless macro from the reference  */
/* (portable) int32_sort here: it has exactly the same semantics -- after     */
/* int32_MINMAX(a,b), a holds the signed minimum and b the signed maximum --  */
/* so sort.c (which #includes this file verbatim) behaves identically, while  */
/* the file stays platform independent and easy to reason about for the       */
/* proof.  Only the vectorized int32x8 path in sort.c is x86-specific.        */

#define int32_MINMAX(a,b) \
do { \
  int32 ab = b ^ a; \
  int32 c = b - a; \
  c ^= ab & (c ^ b); \
  c >>= 31; \
  c &= ab; \
  a ^= c; \
  b ^= c; \
} while(0)
