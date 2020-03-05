Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Testbit.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma lor_add a b (Hand : a &' b = 0) : a |' b = a + b.
  Proof. rewrite <- Z.lxor_lor, Z.add_nocarry_lxor by assumption; reflexivity. Qed.

  Lemma lor_small_neg a b
        (Ha : - 2^b <= a < 0)
        (Hb : 0 < b) :
    2^b |' a = a.
  Proof.
    apply Z.bits_inj_iff; red; intros; rewrite Z.lor_spec.
    destruct (Z.eqb_spec b n); subst.
    - now rewrite (Testbit.Z.testbit_small_neg a), orb_true_r.
    - now rewrite Z.pow2_bits_false, orb_false_l. Qed.
End Z.
