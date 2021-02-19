#include "p521_64.c"

typedef uint64_t fiat_p521_t[9];

static inline void fiat_p521_carry_nsqr(uint64_t a[9], uint64_t b[9], int n) {
        fiat_p521_carry_square(a, b);
        for (int i = 1; i < n; i++) {
                fiat_p521_carry_square(a, a);
        }
}

void flt_inverse(uint64_t einv[9], uint64_t e[9]) {
        fiat_p521_t t,t7,t2_7_0,t2_8_0,t2_16_0,t2_32_0,t2_64_0,t2_128_0,t2_256_0;

        /* 2  */ fiat_p521_carry_square(t,e);
        /* 3  */ fiat_p521_carry_mul(t,t,e);
        /* 6  */ fiat_p521_carry_square(t,t);
        /* 7  */ fiat_p521_carry_mul(t7,t,e);
        /* 14 */ fiat_p521_carry_square(t,t7);
        /* 15 */ fiat_p521_carry_mul(t,t,e);

        /* 2^7 - 2^3     */ fiat_p521_carry_nsqr(t,t,3);
        /* 2^7 - 1       */ fiat_p521_carry_mul(t2_7_0,t,t7);

        /* 2^8 - 2       */ fiat_p521_carry_square(t,t2_7_0);
        /* 2^8 - 1       */ fiat_p521_carry_mul(t2_8_0,t,e);

        /* 2^16 - 2^8    */ fiat_p521_carry_nsqr(t,t2_8_0,8);
        /* 2^16 - 1      */ fiat_p521_carry_mul(t2_16_0,t,t2_8_0);

        /* 2^32 - 2^16   */ fiat_p521_carry_nsqr(t,t2_16_0,16);
        /* 2^32 - 1      */ fiat_p521_carry_mul(t2_32_0,t,t2_16_0);

        /* 2^64 - 2^32   */ fiat_p521_carry_nsqr(t,t2_32_0,32);
        /* 2^64 - 1      */ fiat_p521_carry_mul(t2_64_0,t,t2_32_0);

        /* 2^128 - 2^64  */ fiat_p521_carry_nsqr(t,t2_64_0,64);
        /* 2^128 - 1     */ fiat_p521_carry_mul(t2_128_0,t,t2_64_0);

        /* 2^256 - 2^128 */ fiat_p521_carry_nsqr(t,t2_128_0,128);
        /* 2^256 - 1     */ fiat_p521_carry_mul(t2_256_0,t,t2_128_0);

        /* 2^512 - 2^256 */ fiat_p521_carry_nsqr(t,t2_256_0,256);
        /* 2^512 - 1     */ fiat_p521_carry_mul(t,t,t2_256_0);

        /* 2^519 - 2^7   */ fiat_p521_carry_nsqr(t,t,7);
        /* 2^519 - 1     */ fiat_p521_carry_mul(t,t,t2_7_0);

        /* 2^521 - 2^2   */ fiat_p521_carry_nsqr(t,t,2);
        /* 2^521 - 3     */ fiat_p521_carry_mul(einv,t,e);
}

#define FLT_INVERSION
#include "test_template.c"

