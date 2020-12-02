#include "curve25519_64.c"

static void flt_inverse(uint64_t *out, uint64_t *z) {
  uint64_t z2[5];
  uint64_t z9[5];
  uint64_t z11[5];
  uint64_t z2_5_0[5];
  uint64_t z2_10_0[5];
  uint64_t z2_20_0[5];
  uint64_t z2_50_0[5];
  uint64_t z2_100_0[5];
  uint64_t t0[5];
  uint64_t t1[5];
  int i;

  /* 2 */ fiat_25519_carry_square(z2,z);
  /* 4 */ fiat_25519_carry_square(t1,z2);
  /* 8 */ fiat_25519_carry_square(t0,t1);
  /* 9 */ fiat_25519_carry_mul(z9,t0,z);
  /* 11 */ fiat_25519_carry_mul(z11,z9,z2);
  /* 22 */ fiat_25519_carry_square(t0,z11);
  /* 2^5 - 2^0 = 31 */ fiat_25519_carry_mul(z2_5_0,t0,z9);

  /* 2^6 - 2^1 */ fiat_25519_carry_square(t0,z2_5_0);
  /* 2^7 - 2^2 */ fiat_25519_carry_square(t1,t0);
  /* 2^8 - 2^3 */ fiat_25519_carry_square(t0,t1);
  /* 2^9 - 2^4 */ fiat_25519_carry_square(t1,t0);
  /* 2^10 - 2^5 */ fiat_25519_carry_square(t0,t1);
  /* 2^10 - 2^0 */ fiat_25519_carry_mul(z2_10_0,t0,z2_5_0);

  /* 2^11 - 2^1 */ fiat_25519_carry_square(t0,z2_10_0);
  /* 2^12 - 2^2 */ fiat_25519_carry_square(t1,t0);
  /* 2^20 - 2^10 */ for (i = 2;i < 10;i += 2) { fiat_25519_carry_square(t0,t1); fiat_25519_carry_square(t1,t0); }
  /* 2^20 - 2^0 */ fiat_25519_carry_mul(z2_20_0,t1,z2_10_0);

  /* 2^21 - 2^1 */ fiat_25519_carry_square(t0,z2_20_0);
  /* 2^22 - 2^2 */ fiat_25519_carry_square(t1,t0);
  /* 2^40 - 2^20 */ for (i = 2;i < 20;i += 2) { fiat_25519_carry_square(t0,t1); fiat_25519_carry_square(t1,t0); }
  /* 2^40 - 2^0 */ fiat_25519_carry_mul(t0,t1,z2_20_0);

  /* 2^41 - 2^1 */ fiat_25519_carry_square(t1,t0);
  /* 2^42 - 2^2 */ fiat_25519_carry_square(t0,t1);
  /* 2^50 - 2^10 */ for (i = 2;i < 10;i += 2) { fiat_25519_carry_square(t1,t0); fiat_25519_carry_square(t0,t1); }
  /* 2^50 - 2^0 */ fiat_25519_carry_mul(z2_50_0,t0,z2_10_0);

  /* 2^51 - 2^1 */ fiat_25519_carry_square(t0,z2_50_0);
  /* 2^52 - 2^2 */ fiat_25519_carry_square(t1,t0);
  /* 2^100 - 2^50 */ for (i = 2;i < 50;i += 2) { fiat_25519_carry_square(t0,t1); fiat_25519_carry_square(t1,t0); }
  /* 2^100 - 2^0 */ fiat_25519_carry_mul(z2_100_0,t1,z2_50_0);

  /* 2^101 - 2^1 */ fiat_25519_carry_square(t1,z2_100_0);
  /* 2^102 - 2^2 */ fiat_25519_carry_square(t0,t1);
  /* 2^200 - 2^100 */ for (i = 2;i < 100;i += 2) { fiat_25519_carry_square(t1,t0); fiat_25519_carry_square(t0,t1); }
  /* 2^200 - 2^0 */ fiat_25519_carry_mul(t1,t0,z2_100_0);

  /* 2^201 - 2^1 */ fiat_25519_carry_square(t0,t1);
  /* 2^202 - 2^2 */ fiat_25519_carry_square(t1,t0);
  /* 2^250 - 2^50 */ for (i = 2;i < 50;i += 2) { fiat_25519_carry_square(t0,t1); fiat_25519_carry_square(t1,t0); }
  /* 2^250 - 2^0 */ fiat_25519_carry_mul(t0,t1,z2_50_0);

  /* 2^251 - 2^1 */ fiat_25519_carry_square(t1,t0);
  /* 2^252 - 2^2 */ fiat_25519_carry_square(t0,t1);
  /* 2^253 - 2^3 */ fiat_25519_carry_square(t1,t0);
  /* 2^254 - 2^4 */ fiat_25519_carry_square(t0,t1);
  /* 2^255 - 2^5 */ fiat_25519_carry_square(t1,t0);
  /* 2^255 - 21 */ fiat_25519_carry_mul(out,t1,z11);
}

#define FLT_INVERSION
#include "test_template.c"
