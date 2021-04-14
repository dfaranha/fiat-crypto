#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <time.h>

#define MAKE_FN_NAME1(x,y) x ## y
#define MAKE_FN_NAME(x,y) MAKE_FN_NAME1(x,y)

#define SAT_FROM_BYTES MAKE_FN_NAME(CURVE_DESCRIPTION,_sat_from_bytes)
#define FROM_BYTES MAKE_FN_NAME(CURVE_DESCRIPTION,_from_bytes)
#define TO_BYTES MAKE_FN_NAME(CURVE_DESCRIPTION,_to_bytes)
#define FROM_MONTGOMERY MAKE_FN_NAME(CURVE_DESCRIPTION,_from_montgomery)
#define TO_MONTGOMERY MAKE_FN_NAME(CURVE_DESCRIPTION,_to_montgomery)

inline long long cpucycles(void) {
  unsigned long long result;
  asm volatile(".byte 15;.byte 49;shlq $32,%%rdx;orq %%rdx,%%rax"
    : "=a" (result) ::  "%rdx");
  return result;
}

long long t[64];
WORD x[SAT_LIMBS];

void bench(void) {
  long long i,j;
  
  for (i = 0;i < 64;++i)
    t[i] = cpucycles();
  for (i = 63;i > 0;--i)
    t[i] -= t[i-1];

  printf("nothing");
  for (i = 1;i < 64;++i)
    printf(" %lld",t[i]);
  printf("\n");

  for (i = 0;i < 64;++i) {
    t[i] = cpucycles();
    inverse(x,x);
  }
  for (i = 63;i > 0;--i)
    t[i] -= t[i-1];

  printf("cycles");
  for (i = 1;i < 64;++i)
    printf(" %lld",t[i]);
  printf("\n");

  for (i = 1;i < 64;++i)
    for (j = 1;j < i;++j)
      if (t[i] < t[j]) {
        long long ti = t[i];
        t[i] = t[j];
        t[j] = ti;
      }
  printf("sorted");
  for (i = 1;i < 64;++i)
    printf(" %lld",t[i]);
  printf("\n");
  
  fflush(stdout);
}

int main() {
  WORD res[LIMBS], out[LIMBS], g[SAT_LIMBS], g1[LIMBS], g2[LIMBS];
  uint8_t a[BYTES];

  int seed = time(0);
  srand(seed);
  printf("seed: %i\n", seed);

  for (int j = 0; j < 10000; j++) {
    int i;
    for (i = 0; i < BYTES; i++) {
      a[i] = rand() % 256;
      if (i > (LEN_PRIME / 8)) a[i] = 0;
    }

    SAT_FROM_BYTES(g,a);
    FROM_BYTES(g1,a);
    TO_MONTGOMERY(g2,g1);

    inverse(out,g);

    MUL(res,out,g2);
    FROM_MONTGOMERY(out,res);
    TO_BYTES(a,out);

    if (a[0] != 1) {
			/* printf("%" PRId8 "\n", a[0]); */
      printf("FAIL\n");
      return 2;
    }
    for (i = 1; i < BYTES; i++) {
      if (a[i] != 0) {
				/* printf("%" PRId8 "\n", a[i]); */
        printf("FAIL\n");
        return 1;
      }
    }
  }
  printf("PASS\n");

  bench();
  
  return 0;
}
