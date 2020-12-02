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

int main() {
  WORD res[LIMBS], out[LIMBS], g[SAT_LIMBS], g1[LIMBS];
  uint8_t a[BYTES];

  int seed = time(0);
  srand(seed);
  printf("%i\n", seed);	
	
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
  }
  printf("PASS\n");
  return 0;
}
