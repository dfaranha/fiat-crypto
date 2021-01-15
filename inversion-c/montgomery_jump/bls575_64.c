#include "../../fiat-c/src/bls575_64.c"

#define LIMBS 9 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint64_t
#define WORDSIZE 64 /* wordsize */
#define LEN_PRIME 575 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_bls575

#include "template.c"
