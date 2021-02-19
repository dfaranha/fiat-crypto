#define MAKE_FN_NAME1(x,y) x ## y
#define MAKE_FN_NAME(x,y) MAKE_FN_NAME1(x,y)

#define PRECOMP MAKE_FN_NAME(CURVE_DESCRIPTION,_jumpdivstep_precomp)
#define MSAT MAKE_FN_NAME(CURVE_DESCRIPTION,_msat)
#define MUL MAKE_FN_NAME(CURVE_DESCRIPTION,_carry_mul)
#define OPP MAKE_FN_NAME(CURVE_DESCRIPTION,_opp)
#define CARRY MAKE_FN_NAME(CURVE_DESCRIPTION,_carry)

#define BODY MAKE_FN_NAME(CURVE_DESCRIPTION,_outer_loop_body)	

#if LEN_PRIME < 46
#define ITERATIONS (((49 * LEN_PRIME) + 80) / 17)
#else
#define ITERATIONS (((49 * LEN_PRIME) + 57) / 17)
#endif

#define SAT_LIMBS (((LEN_PRIME - 1) / WORDSIZE) + 2) /* we might need 2 more bits to represent m in twos complement */
#define BYTES (((LEN_PRIME - 1) / 8) + 1)

#define INNER_LOOP (WORDSIZE - 2)
#define OUTER_LOOP ((ITERATIONS / INNER_LOOP) + 1)

void inverse(WORD out[LIMBS],  WORD g[SAT_LIMBS]) {

  WORD precomp[LIMBS];
	PRECOMP(precomp);

  WORD f1[SAT_LIMBS], f[SAT_LIMBS], g1[SAT_LIMBS];
  WORD v1[LIMBS], v[LIMBS];
  WORD r1[LIMBS], r[LIMBS];

  MSAT(f);
  for (int i = 0; i < LIMBS; i++) r[i] = 0;
  r[0] = 1;

  for (int j = 0; j < LIMBS; j++) v[j] = 0;

  for (int i = 0; i < OUTER_LOOP - (OUTER_LOOP % 2); i+=2) {
    BODY(f1,g1,v1,r1,f,g,v,r);
    BODY(f,g,v,r,f1,g1,v1,r1);
  }
  if (OUTER_LOOP % 2) {
    BODY(f1,g1,v1,r1,f,g,v,r);
    for (int k = 0; k < LIMBS; k++) v[k] = v1[k];
    for (int k = 0; k < SAT_LIMBS; k++) f[k] = f1[k];
  }
	
  WORD h[LIMBS];
  if (f[SAT_LIMBS - 1] >> (WORDSIZE - 1)) {
    OPP(h, v);
		CARRY(v, h);
  }

  MUL(out, v, precomp);

  return;
}
