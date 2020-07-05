Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.nsatz.Nsatz.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Shift.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.SignExtend.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementMul.

Require Import Crypto.Util.ZUtil.Tactics.BruteForceIneq.
Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Arithmetic.Inv.

Import Positional.
Import ListNotations.
Import Definitions.
Import Crypto.Util.ZUtil.Notations.
Import WordByWordMontgomery.

Local Open Scope Z.

Local Coercion Z.of_nat : nat >-> Z.

Module WordByWordMontgomery.
  Definition sat_ones m n :=
    repeat (2 ^ m - 1) n.
  
  Definition sat_is_neg machine_wordsize n a :=
    nth_default 0 a (n - 1) >> (machine_wordsize - 1).

  (*Saturated multiplication of multi-limb integers *)
  Local Definition sat_mul machine_wordsize n1 n2 f g :=
    fst (Rows.mul (uweight machine_wordsize) (2^machine_wordsize) n1 n2 f g).
  
  Definition sat_arithmetic_shiftr machine_wordsize n f k :=
    (map
       (fun i =>
          ((nth_default 0 f i) >> k) |' (Z.truncating_shiftl machine_wordsize
                                                             (nth_default 0 f (i + 1))
                                                             (machine_wordsize - k)))
       (seq 0 (n - 1)))
      ++ [Z.arithmetic_shiftr machine_wordsize (nth_default 0 f (n - 1)) k].

  (* Extends a multi-limb integer in twos complement to a new base *)
  Definition sat_sign_extend machine_wordsize old_base new_base a :=
    let high_limb := nth_default 0 a (old_base - 1) in
    let cond := Z.sign_bit machine_wordsize high_limb in
    dlet parity := Z.zselect cond 0 (2^machine_wordsize - 1) in
    let padding := repeat parity (new_base - old_base) in
    a ++ padding.

  (* Converts a wordsized integer to montgomery domain *)
  Definition twosc_word_to_montgomery machine_wordsize n m m' a :=
    dlet cond := Z.twos_complement_neg machine_wordsize a in
    dlet a_opp := Z.twos_complement_opp machine_wordsize a in
    dlet a_enc := encodemod machine_wordsize n m m' a in
    dlet a_opp_enc := encodemod machine_wordsize n m m' (a_opp) in
    dlet a_opp_enc_opp := oppmod machine_wordsize n m (a_opp_enc) in
    dlet res := select cond a_enc a_opp_enc_opp in res.

  (* Converts a wordsize integer to montgomery domain (without multiplying by R2) *)
  Definition twos_complement_word_to_montgomery_no_encode machine_wordsize n m a :=
    dlet cond := Z.twos_complement_neg machine_wordsize a in
    dlet a_opp := Z.twos_complement_opp machine_wordsize a in
    dlet a_enc := encode_no_reduce (uweight machine_wordsize) n a in
    dlet a_opp_enc := encode_no_reduce (uweight machine_wordsize) n a_opp in
    dlet a_opp_enc_opp := oppmod machine_wordsize n m (a_opp_enc) in
    dlet res := select cond a_enc a_opp_enc_opp in res.

  Definition sat_word_bits machine_wordsize a :=
    nth_default 0 a 0 mod 2^(machine_wordsize - 2).

  Definition sat_mod_word machine_wordsize n a :=
    let cond := sat_is_neg machine_wordsize n a in
    let a' := select cond a (sat_opp machine_wordsize n a) in
    let t := (nth_default 0 a' 0) in
    let res := Z.zselect cond t (Z.twos_complement_opp machine_wordsize t) in res.

  Definition twosc_word_mod_m machine_wordsize n m a :=
    dlet cond := Z.twos_complement_neg machine_wordsize a in
    dlet a' := Z.zselect cond a (Z.twos_complement_opp machine_wordsize a) in
    let a'' := extend_to_length 1 n [a'] in
    let a''_opp := oppmod machine_wordsize n m a'' in
    select cond a'' a''_opp.

  Definition sat_twos_complement_mul machine_wordsize n m a b :=
    firstn m (fst (Rows.mul (uweight machine_wordsize) (2^machine_wordsize) m (2 * m)
                            (sat_sign_extend machine_wordsize n m a) (sat_sign_extend machine_wordsize n m b))).

  Definition sat64_mul machine_wordsize n a b :=
    firstn (S n) (fst (Rows.mul (uweight machine_wordsize) (2^machine_wordsize) (S n) (2 * (S n))
                                (sat_sign_extend machine_wordsize 1 (S n) [a]) (sat_sign_extend machine_wordsize n (S n) b))).
  
  Definition twos_complement_word_full_divstep_aux machine_wordsize (data : Z * Z * Z * Z * Z * Z * Z) :=
    let '(d,f,g,u,v,q,r) := data in
    let cond := Z.land (Z.twos_complement_pos machine_wordsize d) (g mod 2) in
    dlet d' := Z.zselect cond d (Z.twos_complement_opp machine_wordsize d) in
    dlet f' := Z.zselect cond f g in
    dlet g' := Z.zselect cond g (Z.twos_complement_opp machine_wordsize f) in
    dlet u' := Z.zselect cond u q in
    dlet v' := Z.zselect cond v r in
    let u'':= (u' + u') mod 2^machine_wordsize in
    let v'':= (v' + v') mod 2^machine_wordsize in
    dlet q' := Z.zselect cond q (Z.twos_complement_opp machine_wordsize u) in
    dlet r' := Z.zselect cond r (Z.twos_complement_opp machine_wordsize v) in
    let g0 := g' mod 2 in
    let d'' := (1 + d') mod 2^machine_wordsize in
    dlet f'' := Z.zselect g0 0 f' in
    let g'' := Z.arithmetic_shiftr1 machine_wordsize ((g' + f'') mod 2^machine_wordsize) in
    dlet u''' := Z.zselect g0 0 u' in
    dlet v''' := Z.zselect g0 0 v' in
    let q'' := (q' + u''') mod 2^machine_wordsize in
    let r'' := (r' + v''') mod 2^machine_wordsize in
    (d'',f',g'',u'',v'',q'',r'').
  Definition twos_complement_word_full_divstep machine_wordsize d f g u v q r :=
    twos_complement_word_full_divstep_aux machine_wordsize (d, f, g, u, v, q, r).

  Definition divstep_spec_full' d f g u v q r :=
    if (0 <? d) && Z.odd g
    then (1 - d, g, (g - f) / 2,
          2 * q, 2 * r, q - u, r - v)
    else (1 + d, f, (g + (g mod 2) * f) / 2,
          2 * u, 2 * v, q + (g mod 2) * u, r + (g mod 2) * v).

  (** Section about arithmetic right shift *)

  Lemma sat_arithmetic_shiftr_0 machine_wordsize n f
        (Hn : (0 < n)%nat)
        (Hf : length f = n) :
    sat_arithmetic_shiftr machine_wordsize n f 0 = f.
  Proof.
    unfold sat_arithmetic_shiftr. rewrite Z.arithmetic_shiftr_0.
    rewrite <- (map_nth_default_seq 0 n f) at 2 by assumption; destruct n; [lia|].
    rewrite seq_snoc, map_app.
    apply f_equal2; replace (S n - 1)%nat with n by lia; try reflexivity.
    apply map_seq_ext; try lia; intros i Hi.
    rewrite Z.shiftr_0_r, Z.truncating_shiftl_large, Z.lor_0_r, Nat.add_0_r by lia.
    reflexivity. Qed.
  
  Lemma sat_arithmetic_shiftr_1 machine_wordsize n f
        (Hm : 0 <= machine_wordsize)
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
    sat_arithmetic_shiftr machine_wordsize n f 1 =
    sat_arithmetic_shiftr1 machine_wordsize n f.
  Proof.
    unfold sat_arithmetic_shiftr, sat_arithmetic_shiftr1.
    rewrite Z.arithmetic_shiftr_1. reflexivity.
    apply nth_default_preserves_properties. assumption.
    solve_range. Qed.

  Lemma sat_arithmetic_shiftr_sat_arithmetic_shiftr1 machine_wordsize n (f : list Z) k
        (Hn : (0 < n)%nat)
        (Hf : length f = n)
        (Hk : 0 <= k < machine_wordsize)
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
    sat_arithmetic_shiftr machine_wordsize n
                          (sat_arithmetic_shiftr1 machine_wordsize n f) k =
    sat_arithmetic_shiftr machine_wordsize n f (k + 1).
  Proof.
    unfold sat_arithmetic_shiftr, sat_arithmetic_shiftr1.
    rewrite nth_default_app, map_length, seq_length.
    destruct (lt_dec (n - 1) (n - 1)); try lia.
    replace (n - 1 - (n - 1))%nat with 0%nat by lia.
    rewrite nth_default_cons, Z.arithmetic_shiftr_arithmetic_shiftr1
      by (try (apply nth_default_preserves_properties; [assumption|solve_range]); lia).
    apply f_equal2; try reflexivity. apply map_seq_ext; try lia; intros i Hi.
    rewrite !nth_default_app, map_length, seq_length.
    destruct (lt_dec i (n - 1)); try lia.
    destruct (lt_dec (i + 1) (n - 1)).
    - rewrite !(map_nth_default _ _ _ _ 0%nat 0) by (rewrite seq_length; lia).
      rewrite !nth_default_seq_inbounds by lia.
      rewrite Nat.add_0_r, Z.shiftr_lor, Z.shiftr_shiftr by lia.
      rewrite Z.add_comm, <- Z.lor_assoc. apply f_equal2; try reflexivity.
      rewrite Z.truncating_shiftl_lor by lia.
      rewrite Z.truncating_shiftl_truncating_shiftl by lia.

      apply Z.bits_inj'; intros j Hj. 
      rewrite !Z.lor_spec, Z.shiftr_spec, !Z.truncating_shiftl_testbit_spec by lia.
      brute_force_ineq.
      + rewrite !(Z.testbit_neg_r _ (j - _)), orb_false_r by lia.
        apply f_equal2; [reflexivity|lia]. 
      + rewrite Z.shiftr_spec, (Z.testbit_neg_r _ (j - _)), orb_false_r by lia; simpl.
        apply f_equal2; [reflexivity|lia].
    - destruct (dec (i + 1 = n - 1)%nat) as [E|E]; [|lia].
      rewrite !(map_nth_default _ _ _ _ 0%nat 0) by (rewrite seq_length; lia).
      rewrite !nth_default_seq_inbounds by lia; simpl; rewrite Nat.add_0_r.
      rewrite E. replace (n - 1 - (n - 1))%nat with 0%nat by lia.
      rewrite nth_default_cons, Z.shiftr_lor, Z.shiftr_shiftr, Z.add_comm by lia.
      rewrite <- Z.lor_assoc.
      apply f_equal2; [reflexivity|].

      apply Z.bits_inj'; intros j Hj.
      rewrite !Z.lor_spec, Z.shiftr_spec, !Z.truncating_shiftl_testbit_spec by lia.

      destruct (dec (j - (machine_wordsize - k) < 0)).
      + rewrite (Z.testbit_neg_r _ (j - _)) by lia.
        brute_force_ineq. rewrite orb_false_r. apply f_equal; lia.
      + rewrite Z.arithmetic_shiftr1_testbit_spec 
          by (try (apply nth_default_preserves_properties;
                   [assumption|solve_range]); lia).
        brute_force_ineq. simpl. apply f_equal; lia. Qed.

  Local Fixpoint iter_sat_arithmetic_shiftr1 m n f k :=
    match k with
    | 0%nat => f
    | 1%nat => sat_arithmetic_shiftr1 m n f
    | S k => iter_sat_arithmetic_shiftr1 m n (sat_arithmetic_shiftr1 m n f) k
    end.

  Lemma iter_sat_arithmetic_shiftr_S m n f k :
    iter_sat_arithmetic_shiftr1 m n f (S k)
    = iter_sat_arithmetic_shiftr1 m n (sat_arithmetic_shiftr1 m n f) k.
  Proof. destruct k; reflexivity. Qed.

  Lemma sat_arithmetic_shiftr_bound m n f
        (Hm : 0 <= m)
        (Hf : forall z, In z f -> 0 <= z < 2 ^ m) :
    forall y, In y (sat_arithmetic_shiftr1 m n f) -> 0 <= y < 2 ^ m.
  Proof.
    intros y H; unfold sat_arithmetic_shiftr1 in H.
    assert (H1 : 0 <= 0 < 2 ^ m) by solve_range.
    apply in_app_iff in H. destruct H; simpl in H.
    - apply in_map_iff in H; destruct H as [i [H H0] ]; rewrite <- H.
      pose proof nth_default_preserves_properties _ f i 0 Hf H1;
        simpl in H2; solve_range.
    - destruct H as [H|[] ]; rewrite <- H.
      apply Z.arithmetic_shiftr1_bound.
      pose proof nth_default_preserves_properties _ f (n - 1) 0 Hf H1;
        simpl in H0; solve_range. Qed.

  Lemma sat_arithmetic_shiftr1_length m n f
        (Hn : (0 < n)%nat)
        (Hf : length f = n) :
    length (sat_arithmetic_shiftr1 m n f) = n.
  Proof. unfold sat_arithmetic_shiftr1; rewrite app_length, map_length, seq_length; 
           simpl; lia. Qed.

  Lemma sat_arithmetic_shiftr_iter_sat_arithmetic_shiftr1 machine_wordsize n f k
        (Hn : (0 < n)%nat)
        (Hf : length f = n)
        (Hk : 0 <= k < machine_wordsize)
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
    sat_arithmetic_shiftr machine_wordsize n f k
    = iter_sat_arithmetic_shiftr1 machine_wordsize n f (Z.abs_nat k).
  Proof.
    assert (Hm : 0 <= machine_wordsize) by lia.
    destruct (Z.abs_nat k) as [|m] eqn:E.
    - replace k with 0 by lia; simpl; apply sat_arithmetic_shiftr_0; lia.
    - generalize dependent k. generalize dependent f.
      induction m; intros.
      + simpl; replace k with (0 + 1) by lia.
        rewrite sat_arithmetic_shiftr_1 by assumption. reflexivity.
      + specialize (IHm (sat_arithmetic_shiftr1 machine_wordsize n f)
                        (sat_arithmetic_shiftr1_length machine_wordsize n f Hn Hf)
                        (sat_arithmetic_shiftr_bound machine_wordsize n f Hm Hf2)
                        (k - 1) ltac:(lia) ltac:(lia)).
        rewrite iter_sat_arithmetic_shiftr_S, <- IHm.
        rewrite sat_arithmetic_shiftr_sat_arithmetic_shiftr1
          by (try lia; assumption).
        rewrite Z.sub_simpl_r; reflexivity. Qed.

  Lemma eval_sat_arithmetic_shiftr machine_wordsize n f k
        (Hn : (0 < n)%nat)
        (Hf : length f = n)
        (Hk : 0 <= k < machine_wordsize)
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
    eval_twos_complement machine_wordsize n
                         (sat_arithmetic_shiftr machine_wordsize n f k) =
    eval_twos_complement machine_wordsize n f / (2 ^ k).
  Proof.
    assert (Hm : 0 <= machine_wordsize) by lia.
    rewrite sat_arithmetic_shiftr_iter_sat_arithmetic_shiftr1 by assumption.
    destruct (Z.abs_nat k) as [|m] eqn:E.
    - replace k with 0 by lia; simpl; rewrite Z.div_1_r; reflexivity.
    - generalize dependent k. generalize dependent f. induction m; intros.
      + simpl. replace k with 1 by lia; rewrite Z.pow_1_r.
        apply eval_twos_complement_sat_arithmetic_shiftr1; try assumption; lia.
      + rewrite iter_sat_arithmetic_shiftr_S.
        specialize (IHm (sat_arithmetic_shiftr1 machine_wordsize n f)
                        (sat_arithmetic_shiftr1_length machine_wordsize n f Hn Hf)
                        (sat_arithmetic_shiftr_bound machine_wordsize n f Hm Hf2)
                        (k - 1) ltac:(lia) ltac:(lia)).
        assert (0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
        rewrite IHm, eval_twos_complement_sat_arithmetic_shiftr1 by (try assumption; lia).
        rewrite Z.div_div, Z.pow_mul_base, Z.sub_simpl_r by lia. reflexivity. Qed.

  (** Section for firstn *)
  Lemma firstn_eval m n f k
        (Hm : 0 < m)
        (Hf : length f = n)
        (Hf2 : forall z : Z, In z f -> 0 <= z < 2 ^ m)
        (Hk : (k <= n)%nat) :
    Positional.eval (uweight m) k (firstn k f) = Positional.eval (uweight m) n f mod 2 ^ (m * k).
  Proof.
    rewrite <- (firstn_skipn k f) at 2.
    replace n with (k + length (skipn k f))%nat.
    rewrite (uweight_eval_app' m ltac:(lia) k).
    rewrite uweight_eq_alt.
    rewrite <- Z.pow_mul_r.
    autorewrite with push_Zmod. rewrite Z.mod_0_l, Z.add_0_r.
    rewrite Z.mod_mod. rewrite Z.mod_small. reflexivity.
    apply eval_bound. lia. intros.
    apply Hf2. apply (In_firstn k).  assumption.
    auto with zarith. rewrite firstn_length. rewrite Nat.min_l. reflexivity. lia.  

    apply Z.pow_nonzero; nia.   apply Z.pow_nonzero; nia. lia. lia. lia.
    rewrite firstn_length. rewrite Nat.min_l. reflexivity. lia.
    rewrite skipn_length. lia. Qed.

  Local Notation eval m n f := (Positional.eval (uweight m) n f).

  (** sat_ones section *)
  Lemma sat_ones_spec m n
        (Hm : 0 <= m) :
    eval m n (sat_ones m n) = Z.ones (m * n).
  Proof.
    unfold sat_ones.
    induction n.
    - rewrite Z.mul_0_r. simpl. reflexivity.
    - simpl. rewrite eval_cons. rewrite uweight_eval_shift.
      rewrite IHn. rewrite uweight_0, uweight_eq_alt, Z.pow_1_r.
      rewrite !Z.ones_equiv. rewrite <- !Z.sub_1_r. ring_simplify.
      rewrite <- Z.pow_add_r. repeat apply f_equal2.  lia. lia. lia. lia. lia. lia. lia.
      apply repeat_length.    apply repeat_length. Qed.

  (** sat_sign_extend section *)
  Lemma sat_sign_extend_eval m n_old n_new f
        (Hn_old : (0 < n_old)%nat)
        (Hn_new : (n_old <= n_new)%nat)
        (Hf : (length f = n_old))
        (Hm : 0 < m)
        (Hf2 : forall z : Z, In z f -> 0 <= z < 2 ^ m) :
    Positional.eval (uweight m) n_new (sat_sign_extend m n_old n_new f)
    = Z.sign_extend (m * n_old) (m * n_new) (Positional.eval (uweight m) n_old f).
  Proof.
    rewrite Z.sign_extend_add.
    unfold sat_sign_extend.
    rewrite unfold_Let_In, Zselect.Z.zselect_correct.
    rewrite Z.sign_bit_testbit.
    
    rewrite eval_testbit.
    assert ((Z.abs_nat ((m * Z.of_nat n_old - 1) / m)) = (n_old - 1)%nat).
    unfold Z.sub. rewrite Z.div_add_l'.
    assert (((- (1)) / m) = - (1)). destruct (dec (m = 1)); subst. reflexivity. 
    rewrite Z_div_nz_opp_full.
    rewrite Z.div_small. lia.  lia. rewrite Z.mod_1_l. lia. lia. rewrite H. lia. lia.
    rewrite H.
    assert ((m * Z.of_nat n_old - 1) mod m = m - 1).
    destruct (dec (m = 1)); subst. rewrite Z.mod_1_r. reflexivity.
    repeat (pull_Zmod; push_Zmod). rewrite Z.mod_1_l. rewrite Z.mod_neg_small. lia. lia. lia.
    rewrite H0.
    destruct (Z.testbit (nth_default 0 f (n_old - 1)) (m - 1)); simpl.
    rewrite (uweight_eval_app) with (n := (n_old)%nat).
    rewrite repeat_length. fold (sat_ones m (n_new - n_old)).
    rewrite sat_ones_spec. 
    rewrite uweight_eq_alt. unfold Z.ones_at. rewrite Z.shiftl_mul_pow2.
    rewrite Z.pow_mul_r. replace (m * Z.of_nat (n_new - n_old)) with (m * Z.of_nat n_new - m * Z.of_nat n_old) by nia.
    lia. lia. lia. lia. lia. lia. lia. lia.
    rewrite repeat_length. nia.
    rewrite (uweight_eval_app) with (n := (n_old)%nat).
    rewrite repeat_length. fold (zeros (n_new - n_old)). rewrite eval_zeros. lia. lia.
    lia.  rewrite repeat_length. nia. assumption. lia. lia. lia. lia.  apply nth_default_preserves_properties. assumption.
    assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia). lia. lia. apply eval_bound. lia. assumption. lia. Qed.

  Lemma sat_sign_extend_length m n_old n_new f
        (Hn_old : (0 < n_old)%nat)
        (Hn_new : (n_old <= n_new)%nat)
        (Hf : (length f = n_old)) :
    length (sat_sign_extend m n_old n_new f) = n_new.
  Proof. unfold sat_sign_extend; rewrite unfold_Let_In, app_length, repeat_length. lia. Qed.

  (** sat_mul section *)
  Lemma sat_mul_bounds machine_wordsize n1 n2 f g
        (mw0 : 0 < machine_wordsize)
        (Hn2 : (0 < n2)%nat)
        (Hf : length f = n1)
        (Hg : length g = n1) :
    forall z, In z (sat_mul machine_wordsize n1 n2 f g) -> 0 <= z < 2 ^ machine_wordsize.
  Proof.
    intros. unfold sat_mul in *.
    rewrite Rows.mul_partitions in * by (try apply uwprops; try apply Z.pow_nonzero; lia).
    unfold Partition.partition in H.
    apply ListAux.in_map_inv in H.
    destruct H as [a [H]].
    rewrite H0, !uweight_eq_alt; try lia.
    split.
    - apply Z.div_le_lower_bound;
        ring_simplify; try apply Z.mod_pos_bound;
          apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
    - apply Z.div_lt_upper_bound.
      apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
      replace ((_ ^ _) ^ _ * _) with ((2 ^ machine_wordsize) ^ Z.of_nat (S a)).
      apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
      rewrite Z.mul_comm, Pow.Z.pow_mul_base; 
        try (replace (Z.of_nat (S a)) with ((Z.of_nat a + 1)) by lia; lia). Qed.

  (** Section for proving sat64_mul correct *NOTE* that this should
  probably be generalized to sat_twos_complement_mul (of which
  sat64_mul is a special case) *)
  Theorem sat64_mul_correct m n a b
          (Hm : 0 < m)
          (Hn : (0 < n)%nat)
          (Ha : 0 <= a < 2 ^ m)
          (Hb : length b = n)
          (Hb2 : forall z : Z, In z b -> 0 <= z < 2 ^ m) :
    eval_twos_complement m (S n) (sat64_mul m n a b) =
    (Z.twos_complement m a) * eval_twos_complement m n b.
  Proof.
    unfold sat64_mul.
    unfold eval_twos_complement. rewrite (firstn_eval m (2 * (S n))).
    rewrite Rows.mul_partitions.
    rewrite !sat_sign_extend_eval.
    rewrite eval_cons, uweight_eval_shift, eval0, uweight_0, Z.mul_1_l, Z.mul_0_r, Z.add_0_r, Z.mul_1_r.
    rewrite eval_partition.
    rewrite Z.twos_complement_mod.
    rewrite Z.mod_small. 
    replace (m * Z.of_nat (S n)) with (m + m * n) by lia.
    fold (Z.twos_complement_mul m (m * (Z.of_nat n)) a (eval m n b)).
    rewrite Z.twos_complement_mul_spec. reflexivity.
    all: try nia; try assumption. apply eval_bound. lia. assumption. assumption.
    pose proof (Z.sign_extend_bound m (m * Z.of_nat (S n)) a ltac:(lia) ltac:(nia) ltac:(assumption)).
    pose proof (Z.sign_extend_bound (m * Z.of_nat n) (m * Z.of_nat (S n)) (eval m n b) ltac:(lia) ltac:(nia) ltac:(apply eval_bound; assumption)).
    assert (2 ^ (m * Z.of_nat (S n)) * 2 ^ (m * Z.of_nat (S n)) = 2 ^ (m * Z.of_nat (2 * S n))).
    rewrite <- Z.pow_add_r by lia; apply f_equal. lia.
    rewrite uweight_eq_alt.
    rewrite <- Z.pow_mul_r. nia. lia. lia. lia.
    apply uwprops; lia. reflexivity. reflexivity. reflexivity.
    intros. destruct H as [|[]]; lia. apply uwprops; lia.
    apply sat_sign_extend_length. lia. lia. reflexivity.
    apply sat_sign_extend_length. lia. lia. assumption.
    apply Rows.length_mul. apply uwprops; lia.
    apply sat_sign_extend_length. lia. lia. reflexivity.
    apply sat_sign_extend_length. lia. lia. assumption.
    fold (sat_mul m (S n) (2 * S n) (sat_sign_extend m 1 (S n) [a]) (sat_sign_extend m n (S n) b)).
    apply sat_mul_bounds. lia. lia. apply sat_sign_extend_length. lia. lia. reflexivity.
    apply sat_sign_extend_length. lia. lia. assumption. Qed.

  (** Correctness of wordsized divstep *)
  Theorem twos_complement_word_full_divstep_correct
          machine_wordsize d f g u v q r
          (fodd : Z.odd f = true)
          (mw1 : 2 < machine_wordsize)
          (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                        Z.twos_complement machine_wordsize d <
                        2 ^ (machine_wordsize - 1) - 1)
          (overflow_f : - 2 ^ (machine_wordsize - 2) <
                        Z.twos_complement machine_wordsize f <
                        2 ^ (machine_wordsize - 2))
          (overflow_g : - 2 ^ (machine_wordsize - 2) <
                        Z.twos_complement machine_wordsize g <
                        2 ^ (machine_wordsize - 2))
          (overflow_u : - 2 ^ (machine_wordsize - 2) <
                        Z.twos_complement machine_wordsize u <
                        2 ^ (machine_wordsize - 2))
          (overflow_v : - 2 ^ (machine_wordsize - 2) <
                        Z.twos_complement machine_wordsize v <
                        2 ^ (machine_wordsize - 2))
          (overflow_q : - 2 ^ (machine_wordsize - 2) <
                        Z.twos_complement machine_wordsize q <
                        2 ^ (machine_wordsize - 2))
          (overflow_r : - 2 ^ (machine_wordsize - 2) <
                        Z.twos_complement machine_wordsize r <
                        2 ^ (machine_wordsize - 2))            
          (Hf2 : 0 <= f < 2^machine_wordsize)
          (Hg2 : 0 <= g < 2^machine_wordsize) :
    let '(d1,f1,g1,u1,v1,q1,r1) :=
        (twos_complement_word_full_divstep machine_wordsize d f g u v q r) in
    (Z.twos_complement machine_wordsize d1,
     Z.twos_complement machine_wordsize f1,
     Z.twos_complement machine_wordsize g1,
     Z.twos_complement machine_wordsize u1,
     Z.twos_complement machine_wordsize v1,
     Z.twos_complement machine_wordsize q1,
     Z.twos_complement machine_wordsize r1) =
    divstep_spec_full' (Z.twos_complement machine_wordsize d)
                       (Z.twos_complement machine_wordsize f)
                       (Z.twos_complement machine_wordsize g)
                       (Z.twos_complement machine_wordsize u)
                       (Z.twos_complement machine_wordsize v)
                       (Z.twos_complement machine_wordsize q)
                       (Z.twos_complement machine_wordsize r).
  Proof.
    Arguments Z.add : simpl never.
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Z.pow_mul_base by lia; apply f_equal2; lia).
    assert (2 ^ (machine_wordsize - 2) < 2^(machine_wordsize - 1)) by
        (apply Z.pow_lt_mono_r; lia). 
    assert (2 <= 2 ^ (machine_wordsize - 2)) by
        (replace 2 with (2 ^ 1) by lia; apply Z.pow_le_mono_r; lia).
    unfold divstep_spec_full'; cbn.
    rewrite !Zselect.Z.zselect_correct.
    rewrite !twos_complement_pos_spec, Zmod_odd, Z.twos_complement_odd by lia.
    rewrite Z.twos_complement_mod2, (Zmod_odd g) by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d);
      destruct (Z.odd g) eqn:godd;
      rewrite (Zmod_odd); cbn;
        rewrite ?godd; cbn.
    rewrite <- (Z.twos_complement_odd machine_wordsize), !twos_complement_opp_spec by lia;
      rewrite Z.odd_opp, Z.twos_complement_odd, fodd by lia; cbn.

    all: (repeat apply f_equal2;
          repeat rewrite 1?Z.twos_complement_mod, 1?Z.twos_complement_add_full, 1?Z.twos_complement_one,
          1?Z.arithmetic_shiftr1_spec, 1?twos_complement_opp_spec, 1?Z.twos_complement_zero;
          rewrite ?Z.twos_complement_one, ?twos_complement_opp_spec;
          try apply Z.mod_pos_bound; try apply f_equal2; lia). Qed.
End WordByWordMontgomery.
