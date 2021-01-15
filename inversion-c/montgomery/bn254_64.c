#include "../../fiat-c/src/bn254_64.c"

#define LIMBS 4 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint64_t
#define WORDSIZE 64 /* wordsize */
#define LEN_PRIME 254 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_bn254

#include "template.c"
