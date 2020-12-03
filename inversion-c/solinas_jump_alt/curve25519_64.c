#include "../../fiat-c/src/curve25519_64.c"

#define LIMBS 5 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint64_t
#define WORDSIZE 64 /* wordsize */
#define LEN_PRIME 255 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_25519

#include "template.c"
