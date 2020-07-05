Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.SignExtend.

Local Open Scope Z_scope.

Module Z.
  Lemma twos_complement_mul_spec ma mb a b
        (Hma : 0 < ma)
        (Hmb : 0 < mb)
        (Ha : 0 <= a < 2 ^ ma)
        (Hb : 0 <= b < 2 ^ mb) :
    Z.twos_complement (ma + mb) (Z.twos_complement_mul ma mb a b) =
    (Z.twos_complement ma a) * (Z.twos_complement mb b).
  Proof.
    unfold Z.twos_complement_mul.
    rewrite Z.twos_complement_mul_full; rewrite <- ?(Z.sign_extend_spec _ (ma + mb)); try lia.
    pose proof (Z.twos_complement_bounds a ma Hma).
    pose proof (Z.twos_complement_bounds b mb Hmb).
    assert (2 ^ (ma - 1) * 2 ^ (mb - 1) < 2 ^ (ma + mb - 1))
      by (rewrite <- Z.pow_add_r by lia; apply Z.pow_lt_mono_r; lia). nia. Qed.
End Z.
