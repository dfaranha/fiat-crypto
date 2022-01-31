#define MAKE_FN_NAME1(x,y) x ## y
#define MAKE_FN_NAME(x,y) MAKE_FN_NAME1(x,y)

#define PRECOMP MAKE_FN_NAME(CURVE_DESCRIPTION,_jumpdivstep_precomp)
#define MSAT MAKE_FN_NAME(CURVE_DESCRIPTION,_msat)
#define MUL MAKE_FN_NAME(CURVE_DESCRIPTION,_carry_mul)
#define OPP MAKE_FN_NAME(CURVE_DESCRIPTION,_opp)
#define CARRY MAKE_FN_NAME(CURVE_DESCRIPTION,_carry)
#define ADD MAKE_FN_NAME(CURVE_DESCRIPTION,_add)
#define DIVSTEP MAKE_FN_NAME(CURVE_DESCRIPTION,_twos_complement_word_full_divstep)
#define SHIFTR MAKE_FN_NAME(CURVE_DESCRIPTION,_asr_mw_sub2)
#define SIGNED_TO_SOLINA MAKE_FN_NAME(CURVE_DESCRIPTION,_word_to_solina)
#define SAT_ADD MAKE_FN_NAME(CURVE_DESCRIPTION,_tc_add)
#define WORD_SAT_MUL MAKE_FN_NAME(CURVE_DESCRIPTION,_word_tc_mul)
#define SZNZ MAKE_FN_NAME(CURVE_DESCRIPTION,_selectznz)

#if LEN_PRIME < 46
#define ITERATIONS (((49 * LEN_PRIME) + 80) / 17)
#else
#define ITERATIONS (((49 * LEN_PRIME) + 57) / 17)
#endif

#define SAT_LIMBS (((LEN_PRIME - 1) / WORDSIZE) + 2) /* we might need 2 more bits to represent m in twos complement */
#define WORD_SAT_MUL_LIMBS (SAT_LIMBS + 1) /* we might need 1 more limb to represent a word/multilimb multiplication */
#define BYTES (((LEN_PRIME - 1) / 8) + 1)

#define INNER_LOOP (WORDSIZE - 2)
#define OUTER_LOOP ((ITERATIONS / INNER_LOOP) + 1)

void inverse(WORD out[LIMBS], WORD g[SAT_LIMBS]) {

  WORD precomp[LIMBS];
  PRECOMP(precomp);

  WORD d = 1;
  WORD f[SAT_LIMBS];
  WORD v[LIMBS];
  WORD r[LIMBS];
  WORD f0, g0, u0, v0, q0, r0, out1, out2, out3, out4, out5, out6, out7;

  MSAT(f);
  for (int i = 0; i < LIMBS; i++) r[i] = 0;
  r[0] = 1;

  for (int j = 0; j < LIMBS; j++) v[j] = 0;

  for (int i = 0; i < OUTER_LOOP; i++) {
    u0 = 1;
    v0 = 0;
    q0 = 0;
    r0 = 1;

    f0 = f[0];
    g0 = g[0];
    for (int j = 0; j < INNER_LOOP; j += 2) {
      DIVSTEP(&out1, &out2, &out3, &out4, &out5, &out6, &out7, d, f0, g0, u0, v0, q0, r0);
      DIVSTEP(&d, &f0, &g0, &u0, &v0, &q0, &r0, out1, out2, out3, out4, out5, out6, out7);
    }
    WORD f1[WORD_SAT_MUL_LIMBS], f2[WORD_SAT_MUL_LIMBS], f3[WORD_SAT_MUL_LIMBS], g1[WORD_SAT_MUL_LIMBS], g2[WORD_SAT_MUL_LIMBS], g3[WORD_SAT_MUL_LIMBS];
    WORD_SAT_MUL(f1, u0, f);
    WORD_SAT_MUL(f2, v0, g);
    WORD_SAT_MUL(g1, q0, f);
    WORD_SAT_MUL(g2, r0, g);

    SAT_ADD(f3, f1, f2);
    SAT_ADD(g3, g1, g2);

    WORD f4[WORD_SAT_MUL_LIMBS], g4[WORD_SAT_MUL_LIMBS];
    SHIFTR(f4, f3);
    SHIFTR(g4, g3);

    for (int k = 0; k < SAT_LIMBS; k++) {
      f[k] = f4[k];
      g[k] = g4[k];
    }

    WORD u1[LIMBS], v01[LIMBS], q1[LIMBS], r01[LIMBS];

    SIGNED_TO_SOLINA(u1, u0);
    SIGNED_TO_SOLINA(v01, v0);
    SIGNED_TO_SOLINA(q1, q0);
    SIGNED_TO_SOLINA(r01, r0);

    WORD v1[LIMBS], v2[LIMBS], v3[LIMBS], r1[LIMBS], r2[LIMBS], r3[LIMBS];
    MUL(v1, u1, v);
    MUL(v2, v01, r);
    MUL(r1, q1, v);
    MUL(r2, r01, r);

    ADD(v3, v1, v2);
    CARRY(v, v3);
    ADD(r3, r1, r2);
    CARRY(r, r3);
  }

  WORD h[LIMBS];
  OPP(h, v);
  CARRY(h, h);
  SZNZ(v, f[SAT_LIMBS -1 ] >> (WORDSIZE - 1), v, h);
  MUL(out, v, precomp);

  return;
}
