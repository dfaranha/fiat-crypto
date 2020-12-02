#include "../../fiat-c/src/poly1305_32.c"

#define LIMBS 5 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint32_t
#define WORDSIZE 32 /* wordsize */
#define LEN_PRIME 130 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_poly1305

#include "template.c"
