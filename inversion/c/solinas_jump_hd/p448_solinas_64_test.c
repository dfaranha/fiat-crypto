#include "p448_solinas_64.c"

static inline void fiat_p448_carry_nsqr(uint64_t a[8], uint64_t b[8], int n) {
        fiat_p448_carry_square(a, b);
        for (int i = 1; i < n; i++) {
                fiat_p448_carry_square(a, a);
        }
}

static void flt_inverse(uint64_t r[8], uint64_t a[8]) {
    uint64_t u[8];
    uint64_t v[8];

    fiat_p448_carry_square(u, a);
    fiat_p448_carry_mul(u, u, a); //A^(2^2 - 1)
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_mul(v, u, a); //A^(2^3 - 1)
    fiat_p448_carry_nsqr(u, v, 3);
    fiat_p448_carry_mul(v, u, v); //A^(2^6 - 1)
    fiat_p448_carry_nsqr(u, v, 6);
    fiat_p448_carry_mul(u, u, v); //A^(2^12 - 1)
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_mul(v, u, a); //A^(2^13 - 1)
    fiat_p448_carry_nsqr(u, v, 13);
    fiat_p448_carry_mul(u, u, v); //A^(2^26 - 1)
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_mul(v, u, a); //A^(2^27 - 1)
    fiat_p448_carry_nsqr(u, v, 27);
    fiat_p448_carry_mul(u, u, v); //A^(2^54 - 1)
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_mul(v, u, a); //A^(2^55 - 1)
    fiat_p448_carry_nsqr(u, v, 55);
    fiat_p448_carry_mul(u, u, v); //A^(2^110 - 1)
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_mul(v, u, a); //A^(2^111 - 1)
    fiat_p448_carry_nsqr(u, v, 111);
    fiat_p448_carry_mul(v, u, v); //A^(2^222 - 1)
    fiat_p448_carry_square(u, v);
    fiat_p448_carry_mul(u, u, a); //A^(2^223 - 1)
    fiat_p448_carry_nsqr(u, u, 223);
    fiat_p448_carry_mul(u, u, v); //A^(2^446 - 2^222 - 1)
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_square(u, u);
    fiat_p448_carry_mul(r, u, a); //A^(2^448 - 2^224 - 3)
}

#define FLT_INVERSION
#include "test_template.c"

