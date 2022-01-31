Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.OnesAt.

Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.

Require Import Crypto.Util.LetIn.

Local Open Scope Z_scope.

Module Z.
  Local Ltac destruct_ltb a b :=
    let E := fresh in
    destruct (a <? b) eqn:E; [rewrite Z.ltb_lt in E|rewrite Z.ltb_ge in E].
  Local Ltac destruct_leb a b :=
    let E := fresh in
    destruct (a <=? b) eqn:E; [rewrite Z.leb_le in E|rewrite Z.leb_gt in E].
  Local Ltac destruct_eqb a b :=
    let E := fresh in
    destruct (a =? b) eqn:E; [rewrite Z.eqb_eq in E|rewrite Z.eqb_neq in E].

  Lemma sign_extend_testbit_spec_full old_m new_m a i
        (Hold_m : 0 < old_m)
        (Hold_new : old_m <= new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.testbit (Z.sign_extend old_m new_m a) i =
    if (i <? 0) then false else if (old_m <=? i) && (i <? new_m) then Z.testbit a (old_m - 1) else Z.testbit a i.
  Proof. unfold Z.sign_extend. rewrite unfold_Let_In, Zselect.Z.zselect_correct.
         Z.solve_testbit; rewrite <- Z.sign_bit_testbit in * by assumption; symmetry;
           [apply Z.sign_bit_0_testbit|apply Z.sign_bit_1_testbit]; assumption.
  Qed.

  Hint Rewrite sign_extend_testbit_spec_full : testbit_rewrite.

  Lemma sign_extend_sign_bit old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m < new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.testbit (Z.sign_extend old_m new_m a) (new_m - 1) = Z.testbit a (old_m - 1).
  Proof. Z.solve_testbit. Qed.

  Lemma sign_extend_bound old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m <= new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    0 <= Z.sign_extend old_m new_m a < 2 ^ new_m.
  Proof. assert (2 ^ old_m <= 2 ^ new_m) by (apply Z.pow_le_mono_r; lia). unfold Z.sign_extend.
         rewrite unfold_Let_In, Zselect.Z.zselect_correct, Z.sign_bit_equiv by assumption.
         destruct_ltb a (2 ^ (old_m - 1)); simpl; Z.solve_range. Qed.

  Hint Resolve sign_extend_bound : zarith.

  Lemma sign_extend_spec old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m <= new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.twos_complement old_m a = Z.twos_complement new_m (Z.sign_extend old_m new_m a).
  Proof. Z.solve_using_testbit. Qed.
  
  Lemma sign_extend_add old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m <= new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.sign_extend old_m new_m a =
    (if (negb (Z.testbit a (old_m - 1))) then 0 else (Z.ones_at old_m (new_m - old_m))) + a.
  Proof. rewrite <- Z.lor_add. 
         unfold Z.sign_extend, Z.ones_at.
         rewrite Z.sign_bit_testbit by assumption. 
         destruct (Z.testbit a (old_m - 1)) eqn:E; cbn; auto. 
         destruct (Z.testbit a (old_m - 1)) eqn:E; Z.solve_using_testbit. 
  Qed.
End Z.
