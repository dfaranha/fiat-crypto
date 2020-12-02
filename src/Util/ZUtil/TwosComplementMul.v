Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.SignExtend.
Require Import Crypto.Util.ZUtil.Tactics.SolveRange.

Local Open Scope Z_scope.

Module Z.
  Lemma twos_complement_mul_aux_spec ma mb mab a b
        (Hma : 0 < ma <= mab)
        (Hmb : 0 < mb <= mab)
        (Ha : 0 <= a < 2 ^ ma)
        (Hb : 0 <= b < 2 ^ mb)
        (Hab : - 2 ^ (mab - 1) <= (Z.twos_complement ma a) * (Z.twos_complement mb b) < 2 ^ (mab - 1)) :
    Z.twos_complement mab (Z.twos_complement_mul_aux ma mb mab a b) =
    (Z.twos_complement ma a) * (Z.twos_complement mb b).
  Proof.
    unfold Z.twos_complement_mul_aux.
    rewrite Z.twos_complement_mul_full; rewrite <- ?(Z.sign_extend_spec _ _); lia. Qed.
  
  Lemma twos_complement_mul_spec ma mb mab a b
        (Hma : 0 < ma <= mab)
        (Hmb : 0 < mb <= mab)
        (Ha : 0 <= a < 2 ^ ma)
        (Hb : 0 <= b < 2 ^ mb)
        (Hab : - 2 ^ (ma + mb - 1) <= (Z.twos_complement ma a) * (Z.twos_complement mb b) < 2 ^ (ma + mb - 1)) :
    Z.twos_complement (ma + mb) (Z.twos_complement_mul ma mb a b) =
    (Z.twos_complement ma a) * (Z.twos_complement mb b).
  Proof. apply twos_complement_mul_aux_spec; lia. Qed.
End Z.
