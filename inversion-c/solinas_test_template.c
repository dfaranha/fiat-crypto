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

inline long long cpucycles(void) {
  unsigned long long result;
  asm volatile(".byte 15;.byte 49;shlq $32,%%rdx;orq %%rdx,%%rax"
    : "=a" (result) ::  "%rdx");
  return result;
}

long long t[64];
WORD x[SAT_LIMBS];

void bench(void (*inv)(WORD out[LIMBS], WORD in[LIMBS])) {
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
    inv(x,x);
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
  printf("median");
  printf(" %lld\n",t[32]);
  
  fflush(stdout);
}

int main() {
  WORD res[LIMBS], out[LIMBS], g[SAT_LIMBS], g1[LIMBS];
  uint8_t a[BYTES];

  int seed = time(0);
  srand(seed);
  printf("seed: %i\n", seed);	
	
  for (int j = 0; j < 10000; j++) {
    int i;
    for (i = 0; i < BYTES; i++) {
      a[i] = rand() % 256;
      if (i > BYTES - 8) a[i] = 0;
    }
		
    SAT_FROM_BYTES(g,a);
    FROM_BYTES(g1,a);
	
    inverse(out,g);

    MUL(res,out,g1);
    TO_BYTES(a,res);
		
    if (a[0] != 1) {
			/* printf("%" PRIu8 " ", a[0]); */
      printf("FAIL\n");
      return 2;
    }
    for (i = 1; i < BYTES; i++) {
      if (a[i] != 0) {
				/* printf("%" PRIu8 " ", a[i]); */
        printf("FAIL\n");
        return 1;
      }
    }

#ifdef FLT_INVERSION
    flt_inverse(out, g1);

    MUL(res,out,g1);
    TO_BYTES(a,res);
		
    if (a[0] != 1) {
      printf("FAIL\n");
      return 2;
    }
    for (i = 1; i < BYTES; i++) {
      if (a[i] != 0) {
        printf("FAIL\n");
        return 1;
      }
    }
#endif
		
  }
  printf("PASS\n");
  
  printf("\nbenchmarking inverse...\n");
  bench(inverse);

#ifdef FLT_INVERSION
  printf("\nbenchmarking flt_inverse...\n");
  bench(flt_inverse);
#endif 
  
  return 0;
}
