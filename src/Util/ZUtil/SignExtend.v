Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.SignBit.

Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.
Require Import Crypto.Util.ZUtil.Tactics.BruteForceIneq.

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

  Lemma sign_extend_testbit_spec old_m new_m a i
        (Hold_m : 0 < old_m)
        (Hold_new : old_m <= new_m)
        (Ha : 0 <= a < 2 ^ old_m)
        (Hi : 0 <= i) :
    Z.testbit (Z.sign_extend old_m new_m a) i =
    if (old_m <=? i) && (i <? new_m) then Z.testbit a (old_m - 1) else Z.testbit a i.
  Proof. solve_testbit. Qed.

  Lemma sign_extend_sign_bit old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m < new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.testbit (Z.sign_extend old_m new_m a) (new_m - 1) = Z.testbit a (old_m - 1).
  Proof. rewrite sign_extend_testbit_spec by lia; solve_testbit. Qed.

  Lemma sign_extend_bound old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m < new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    0 <= Z.sign_extend old_m new_m a < 2 ^ new_m.
  Proof. assert (2 ^ old_m <= 2 ^ new_m) by (apply Z.pow_le_mono_r; lia). unfold Z.sign_extend.
         rewrite unfold_Let_In, Zselect.Z.zselect_correct, Z.sign_bit_equiv by assumption.
         destruct_ltb a (2 ^ (old_m - 1)); simpl; solve_range. Qed.

  Lemma sign_extend_spec old_m new_m a
        (Hold_m : 0 < old_m)
        (Hold_new : old_m < new_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.twos_complement old_m a = Z.twos_complement new_m (Z.sign_extend old_m new_m a).
  Proof.
    unfold Z.twos_complement.
    assert (2 ^ old_m <= 2 ^ new_m) by (apply Z.pow_le_mono_r; lia).
    rewrite !Z.twos_complement_cond_equiv, sign_extend_sign_bit by lia. solve_testbit.
    rewrite Z.lor_add, Z.ones_equiv, Z.shiftl_mul_pow2, !Z.mod_small; try lia. solve_range. solve_range.
    apply Z.bits_inj'; intros i Hi. solve_testbit. rewrite !Z.mod_small; lia. Qed.

  Lemma sign_extend_add old_m new_m a
        (Hold_m : 0 < old_m)
        (Ha : 0 <= a < 2 ^ old_m) :
    Z.sign_extend old_m new_m a =
    (if (negb (Z.testbit a (old_m - 1))) then 0 else (Z.ones_at old_m (new_m - old_m))) + a.
  Proof.
    unfold Z.sign_extend.
    rewrite unfold_Let_In, Zselect.Z.zselect_correct, Z.sign_bit_testbit by lia.
    destruct (Z.testbit a (old_m - 1)); apply Z.lor_add; apply Z.bits_inj'; intros i Hi; solve_testbit. Qed.
End Z.
