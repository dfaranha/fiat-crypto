#define MAKE_FN_NAME1(x,y) x ## y
#define MAKE_FN_NAME(x,y) MAKE_FN_NAME1(x,y)

#define PRECOMP MAKE_FN_NAME(CURVE_DESCRIPTION,_jumpdivstep_precomp_hd)
#define MSAT MAKE_FN_NAME(CURVE_DESCRIPTION,_msat)
#define MUL MAKE_FN_NAME(CURVE_DESCRIPTION,_carry_mul)
#define OPP MAKE_FN_NAME(CURVE_DESCRIPTION,_opp)
#define CARRY MAKE_FN_NAME(CURVE_DESCRIPTION,_carry)
#define SZNZ MAKE_FN_NAME(CURVE_DESCRIPTION,_selectznz)

#define FN_INNER_LOOP MAKE_FN_NAME(CURVE_DESCRIPTION,_inner_loop_hd)
#define UPDATE_FG MAKE_FN_NAME(CURVE_DESCRIPTION,_update_fg)
#define UPDATE_VR MAKE_FN_NAME(CURVE_DESCRIPTION,_update_vr)
/* #define BODY MAKE_FN_NAME(CURVE_DESCRIPTION,_outer_loop_body_hd) */

#define ITERATIONS (45907 * LEN_PRIME + 26313) / 19929

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
  WORD d,d1,un,vn,qn,rn;

  MSAT(f);
  for (int i = 0; i < LIMBS; i++) r[i] = 0;
  r[0] = 1;

  for (int j = 0; j < LIMBS; j++) v[j] = 0;

  d = 1;

  for (int i = 0; i < OUTER_LOOP - (OUTER_LOOP % 2); i+=2) {
    FN_INNER_LOOP(&d1,&un,&vn,&qn,&rn,d,f,g);
    UPDATE_FG(f1,g1,f,g,un,vn,qn,rn);
    UPDATE_VR(v1,r1,v,r,un,vn,qn,rn);

    FN_INNER_LOOP(&d,&un,&vn,&qn,&rn,d1,f1,g1);
    UPDATE_FG(f,g,f1,g1,un,vn,qn,rn);
    UPDATE_VR(v,r,v1,r1,un,vn,qn,rn);
    /* BODY(f1,g1,v1,r1,f,g,v,r); */
    /* BODY(f,g,v,r,f1,g1,v1,r1); */
  }
  if (OUTER_LOOP % 2) {
    FN_INNER_LOOP(&d1,&un,&vn,&qn,&rn,d,f,g);
    UPDATE_FG(f1,g1,f,g,un,vn,qn,rn);
    UPDATE_VR(v1,r1,v,r,un,vn,qn,rn);
    /* BODY(f1,g1,v1,r1,f,g,v,r); */

    for (int k = 0; k < LIMBS; k++) v[k] = v1[k];
    for (int k = 0; k < SAT_LIMBS; k++) f[k] = f1[k];
    d = d1;
  }

  WORD h[LIMBS];
  OPP(h, v);
  CARRY(h, h);
  SZNZ(v, f[SAT_LIMBS -1 ] >> (WORDSIZE - 1), v, h);
  MUL(out, v, precomp);

  return;
}
