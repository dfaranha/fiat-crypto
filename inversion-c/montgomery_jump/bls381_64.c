#include "../../fiat-c/src/bls381_64.c"

#define LIMBS 6 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint64_t
#define WORDSIZE 64 /* wordsize */
#define LEN_PRIME 381 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_bls381

#include "template.c"
