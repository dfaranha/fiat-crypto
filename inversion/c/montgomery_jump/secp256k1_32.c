#include "../../../fiat-c/src/secp256k1_32.c"

#define LIMBS 8 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint32_t
#define WORDSIZE 32 /* wordsize */
#define LEN_PRIME 256 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_secp256k1

#include "template.c"
