#include "../../fiat-c/src/curve25519_32.c"

#define LIMBS 10 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint32_t
#define WORDSIZE 32 /* wordsize */
#define LEN_PRIME 255 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_25519

#include "template.c"
