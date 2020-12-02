Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.TwosComplement.

Local Open Scope Z_scope.

Module Z.

  Lemma twos_complement_neg_spec m a
        (mw0 : 0 < m) :
    Z.twos_complement_neg m a = Z.b2z (Z.testbit a (m - 1)).
  Proof.
    unfold Z.twos_complement_neg. fold (Z.sign_bit m (a mod 2 ^ m)).
    rewrite Z.sign_bit_testbit, Z.mod_pow2_bits_low;
      try apply Z.mod_pos_bound; try apply Z.pow_pos_nonneg; lia. Qed.

End Z.
