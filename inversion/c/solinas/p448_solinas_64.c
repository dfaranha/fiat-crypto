#include "../../../fiat-c/src/p448_solinas_64.c"

#define LIMBS 8 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint64_t
#define WORDSIZE 64 /* wordsize */
#define LEN_PRIME 448 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_p448

#include "template.c"
