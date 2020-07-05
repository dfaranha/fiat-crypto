Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.OnesFrom.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.TwosComplement.

Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.BruteForceIneq.
Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.

Local Open Scope Z_scope.

Module Z.
  (* note that this is only true since coq integer division rounds towards -infinity *)
  Lemma arithmetic_shiftr1_small m a
        (Ha : - 2 ^ (m - 1) <= a < 2 ^ (m - 1))
        (Hm : 0 < m) :
    Z.arithmetic_shiftr1 m a = a / 2.
  Proof.
    unfold Z.arithmetic_shiftr1. rewrite Z.shiftr_div_pow2, Z.pow_1_r; try lia.
    destruct (Z_dec 1 m) as [[]|]; [|lia|]. 
    - destruct (Z.leb_spec 0 a) as [H|H].
      + now rewrite Z.land_pow2_small, Z.lor_0_l. 
      + rewrite Z.land_pow2_small_neg; try lia.
        rewrite Z.lor_small_neg; try lia. split.
        apply Zdiv_le_lower_bound; lia.
        apply Zdiv_lt_upper_bound; lia.  
    - subst; simpl in *.
      destruct (Z_dec a 0) as [[]|]; subst; try lia; try reflexivity.
      destruct (Z_dec a (-1)) as [[]|]; subst; try lia; reflexivity. Qed.

  Lemma arithmetic_shiftr1_large m a
        (Ha : 2 ^ (m - 1) <= a < 2 ^ m)
        (Hm : 0 < m) :
    Z.arithmetic_shiftr1 m a = a / 2 + 2 ^ (m - 1).
  Proof.
    assert (0 < 2 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia).
    unfold Z.arithmetic_shiftr1.
    rewrite Z.land_pow2_testbit, Z.testbit_large, <- Z.div2_spec, Z.div2_div, Z.lor_add; try lia.
    rewrite Z.land_comm, Z.land_div2; try lia. 
    rewrite Z.sub_simpl_r; lia. Qed.

  Lemma arithmetic_shiftr1_testbit_spec m a i (Hm : 0 < m) (Hi : 0 <= i) (Ha : 0 <= a < 2 ^ m) :
    Z.testbit (Z.arithmetic_shiftr1 m a) i =
    if i =? (m - 1) then Z.testbit a (m - 1) else Z.testbit a (i + 1).
  Proof. unfold Z.arithmetic_shiftr1; solve_testbit. Qed.

  Lemma arithmetic_shiftr1_bound m a (Ha : 0 <= a < 2 ^ m) :
    0 <= Z.arithmetic_shiftr1 m a < 2 ^ m.
  Proof. unfold Z.arithmetic_shiftr1; solve_range. Qed.
  
  Lemma arithmetic_shiftr1_spec m a
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m) :
    Z.twos_complement m (Z.arithmetic_shiftr1 m a) = (Z.twos_complement m a) / 2.
  Proof.
    unfold Z.twos_complement.
    rewrite (Z.mod_small a) by lia.
    assert (0 <= a / 2 < 2 ^ (m - 1)).
    { split.
      apply Zdiv_le_lower_bound; lia. 
      apply Zdiv_lt_upper_bound; try lia. rewrite Z.mul_comm, Z.pow_mul_base, Z.sub_simpl_r; lia. }
    
    destruct (a <? 2 ^ (m - 1)) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
    - rewrite arithmetic_shiftr1_small, Z.mod_small; try lia.
      assert (a / 2 <? 2 ^ (m - 1) = true).
      { apply Z.ltb_lt; apply Zdiv_lt_upper_bound; lia. } 
      rewrite H0; lia. split.
      + apply Zdiv_le_lower_bound; lia. 
      + apply Zdiv_lt_upper_bound; lia. 
    - rewrite arithmetic_shiftr1_large, Z.mod_small; try lia.
      assert (a / 2 + 2 ^ (m - 1) <? 2 ^ (m - 1) = false) by (apply Z.ltb_ge; lia).
      rewrite H0. unfold Z.sub at 3.
      replace (- 2 ^ m) with (2 ^ m * (-1)) by ring.
      rewrite Z.div2_split by lia. 
      replace (-1 mod 2) with 1 by reflexivity.
      replace (-1 / 2) with (-1) by reflexivity; lia. 
      replace (2 ^ m) with (2 * 2 ^ (m - 1)); try lia.
      rewrite Z.pow_mul_base, Z.sub_simpl_r; lia. Qed.

  Local Fixpoint iter_arithmetic_shiftr1 m a k :=
    match k with
    | 0%nat => a
    | 1%nat => Z.arithmetic_shiftr1 m a
    | S k => iter_arithmetic_shiftr1 m (Z.arithmetic_shiftr1 m a) k
    end.

  Lemma iter_arithmetic_shiftr1_S m a k :
    iter_arithmetic_shiftr1 m a (S k) = iter_arithmetic_shiftr1 m (Z.arithmetic_shiftr1 m a) k.
  Proof. destruct k; reflexivity. Qed.
  
  Lemma arithmetic_shiftr_bound m a k
        (Hm : 0 <= m)
        (Ha : 0 <= a < 2 ^ m)
        (Hk : 0 <= k) :
    0 <= Z.arithmetic_shiftr m a k < 2 ^ m.
  Proof.
    unfold Z.arithmetic_shiftr; rewrite unfold_Let_In, Zselect.Z.zselect_correct.
    destruct (dec (Z.sign_bit m a = 0)); [solve_range|].
    destruct (dec (m - k <= 0)); solve_range. Qed.

  Lemma arithmetic_shiftr_1 m a (Ha : 0 <= a < 2 ^ m) :
    Z.arithmetic_shiftr m a 1 = Z.arithmetic_shiftr1 m a.
  Proof.
    unfold Z.arithmetic_shiftr, Z.arithmetic_shiftr1;
    rewrite unfold_Let_In, Zselect.Z.zselect_correct.
    destruct (dec (Z.sign_bit m a = 0)).
    - rewrite Z.sign_bit_0_land_pow2 by assumption. reflexivity. 
    - unfold Z.ones_from; rewrite Z.ones_equiv; simpl. rewrite Z.shiftl_1_l.
      destruct (dec (m <= 0)).
      + rewrite Z.pow_neg_r by lia; simpl; rewrite Z.land_0_r, Z.lor_0_l; reflexivity. 
      + rewrite Z.sign_bit_1_land_pow2 by lia; reflexivity. Qed.

  Lemma arithmetic_shiftr_testbit_spec m a k i
        (Hm : 0 < m)
        (Hk : 0 <= k)
        (Hi : 0 <= i)
        (Ha : 0 <= a < 2 ^ m) :
    Z.testbit (Z.arithmetic_shiftr m a k) i =
    if (m - k <=? i) && (i <? m) then Z.testbit a (m - 1) else Z.testbit a (i + k).
  Proof.
    unfold Z.arithmetic_shiftr; rewrite unfold_Let_In, Zselect.Z.zselect_correct.
    rewrite (Z.testbit_b2z a), Z.sign_bit_testbit by lia.
    destruct (Z.testbit a (m - 1)); simpl. 
    - rewrite Z.lor_spec, Z.ones_from_spec, Z.shiftr_spec by lia.
      destruct (m - k <=? i) eqn:lower; destruct (i <? m) eqn:upper; reflexivity.
    - rewrite Z.shiftr_spec by lia. brute_force_ineq.
      destruct (dec (a = 0)).
      + subst; apply Z.bits_0.
      + assert (2 ^ m <= 2 ^ (i + k)) by (apply Z.pow_le_mono; lia).
        apply Z.bits_above_log2. lia.
        apply Z.log2_lt_pow2; lia. Qed.
  
  Lemma arithmetic_shiftr_0 m a :
    Z.arithmetic_shiftr m a 0 = a.
  Proof.
    unfold Z.arithmetic_shiftr; rewrite unfold_Let_In, !Zselect.Z.zselect_correct.
    rewrite Z.shiftr_0_r, Z.ones_from_0.
    destruct (dec (Z.sign_bit m a = 0)); reflexivity. Qed.
  
  Lemma ones_lor_shift n m k
        (Hn : 0 <= n)
        (Hm : 0 <= m)
        (Hk : 0 <= k) :
    Z.ones n << k |' Z.ones m << (k - m) = Z.ones (n + m) << (k - m).
  Proof.
    apply Z.bits_inj'; intros i Hi.
    rewrite !Z.lor_spec, !Z.shiftl_spec, !Z.ones_spec_full by lia.
    brute_force_ineq. Qed.
  
  Lemma arithmetic_shiftr_sign_bit m a k
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m)
        (Hk : 0 <= k) :
    Z.sign_bit m (Z.arithmetic_shiftr m a k) = Z.sign_bit m a.
  Proof.
    rewrite !Z.sign_bit_testbit, arithmetic_shiftr_testbit_spec
      by (try apply arithmetic_shiftr_bound; lia); brute_force_ineq.
    assert (k = 0) by lia; subst; rewrite Z.add_0_r; reflexivity. Qed.
  
  Lemma arithmetic_shiftr_large m a k
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m)
        (Hk : m <= k) :
    Z.arithmetic_shiftr m a k = if (dec (Z.sign_bit m a = 0)) then 0 else Z.ones m.
  Proof.
    apply Z.bits_inj'; intros i Hi.
    rewrite arithmetic_shiftr_testbit_spec, Z.sign_bit_testbit by lia.
    assert (2 ^ m <= 2 ^ (i + k)) by (apply Z.pow_le_mono_r; lia). 
    destruct (Z.testbit a (m - 1)); simpl;
      [rewrite Z.ones_spec'|rewrite Z.bits_0]; brute_force_ineq;
        apply Z.bits_above_log2; try apply Log2.Z.log2_lt_pow2_alt; lia. Qed.
  
  Lemma arithmetic_shiftr_ones m k
        (Hm : 0 < m)
        (Hk : 0 <= k) :
    Z.arithmetic_shiftr m (Z.ones m) k = Z.ones m.
  Proof.
    apply Z.bits_inj'; intros i Hi.
    rewrite Z.arithmetic_shiftr_testbit_spec by (try apply Z.ones_bound; lia).
    rewrite !Z.ones_spec_full by lia; brute_force_ineq. Qed.
    
  Lemma arithmetic_shiftr_arithmetic_shiftr m a p q
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m)
        (Hp : 0 <= p)
        (Hq : 0 <= q) :
    Z.arithmetic_shiftr m (Z.arithmetic_shiftr m a p) q =
    Z.arithmetic_shiftr m a (p + q).
  Proof.
    apply Z.bits_inj'; intros i Hi.
    rewrite Z.arithmetic_shiftr_testbit_spec
      by (try apply arithmetic_shiftr_bound; lia).
    rewrite !Z.arithmetic_shiftr_testbit_spec by lia.
    brute_force_ineq; apply f_equal2; lia. Qed.
  
  Lemma arithmetic_shiftr_arithmetic_shiftr1 m a k
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m)
        (Hk : 0 <= k) :
    Z.arithmetic_shiftr m (Z.arithmetic_shiftr1 m a) k =
    Z.arithmetic_shiftr m a (k + 1).
  Proof.
    apply Z.bits_inj'; intros i Hi.
    rewrite !arithmetic_shiftr_testbit_spec by (try apply arithmetic_shiftr1_bound; lia). 
    rewrite !arithmetic_shiftr1_testbit_spec by lia.
    brute_force_ineq; apply f_equal2; lia.
  Qed.

  Lemma arithmetic_shiftr_iter_arithmetic_shiftr1 m a k
        (Hm : 0 < m)
        (Hk : 0 <= k)
        (Ha : 0 <= a < 2 ^ m) :
    Z.arithmetic_shiftr m a k = iter_arithmetic_shiftr1 m a (Z.abs_nat k).
  Proof.
    destruct (Z.abs_nat k) eqn:E.
    - replace k with 0 by lia. apply arithmetic_shiftr_0; lia.
    - generalize dependent k. generalize dependent a.
      induction n; intros.
      + replace k with (0 + 1) by lia.
        rewrite <- arithmetic_shiftr_arithmetic_shiftr1, arithmetic_shiftr_0 by lia.
        reflexivity.
      + specialize (IHn (Z.arithmetic_shiftr1 m a)
                        (arithmetic_shiftr1_bound m a Ha)
                        (k - 1) ltac:(lia) ltac:(lia)).
        rewrite iter_arithmetic_shiftr1_S, <- IHn, arithmetic_shiftr_arithmetic_shiftr1
          by lia.
        rewrite Z.sub_simpl_r; reflexivity. Qed.

  Lemma arithmetic_shiftr_spec m a k
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m)
        (Hk : 0 <= k) :
    Z.twos_complement m (Z.arithmetic_shiftr m a k) = (Z.twos_complement m a) / 2 ^ k.
  Proof.
    rewrite arithmetic_shiftr_iter_arithmetic_shiftr1 by assumption.
    destruct (Z.abs_nat k) eqn:E.
    - replace k with 0 by lia; rewrite Z.div_1_r; reflexivity.
    - generalize dependent k. generalize dependent a.
      induction n as [|n IHn]; intros.
      + replace k with 1 by lia. rewrite Z.pow_1_r.
        apply arithmetic_shiftr1_spec; lia.
      + rewrite iter_arithmetic_shiftr1_S.
        specialize (IHn (Z.arithmetic_shiftr1 m a)
                        (arithmetic_shiftr1_bound m a Ha)
                        (k - 1) ltac:(lia) ltac:(lia)).
        assert (0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
        rewrite IHn, arithmetic_shiftr1_spec by lia.
        rewrite Z.div_div, Z.pow_mul_base, Z.sub_simpl_r by lia. reflexivity. Qed.  
End Z.
