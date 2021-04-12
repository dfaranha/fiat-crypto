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
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.

Require Import Crypto.Arithmetic.BYInv.

Import Positional.
Import ListNotations.
Import Definitions.
Import Crypto.Util.ZUtil.Notations.
Import WordByWordMontgomery.

Local Open Scope Z.

Local Coercion Z.of_nat : nat >-> Z.

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

Definition sat_word_bits machine_wordsize a :=
  nth_default 0 a 0 mod 2^(machine_wordsize - 2).

Definition sat_mod_word machine_wordsize n a :=
  let cond := sat_is_neg machine_wordsize n a in
  let a' := select cond a (sat_opp machine_wordsize n a) in
  let t := (nth_default 0 a' 0) in
  let res := Z.zselect cond t (Z.twos_complement_opp machine_wordsize t) in res.


Definition sat_twos_complement_mul machine_wordsize na nb nab a b :=
  firstn nab (fst (Rows.mul (uweight machine_wordsize) (2^machine_wordsize) nab (2 * nab)
                            (sat_sign_extend machine_wordsize na nab a) (sat_sign_extend machine_wordsize nb nab b))).

Definition sat_twos_complement_mul_full machine_wordsize na nb a b :=
  sat_twos_complement_mul machine_wordsize na nb (na + nb) a b.

Definition word_sat_mul machine_wordsize n (a : Z) b :=
  sat_twos_complement_mul_full machine_wordsize 1 n [a] b.

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
  let d'' := (2 + d') mod 2^machine_wordsize in
  dlet f'' := Z.zselect g0 0 f' in
  let g'' := Z.arithmetic_shiftr1 machine_wordsize ((g' + f'') mod 2^machine_wordsize) in
  dlet u''' := Z.zselect g0 0 u' in
  dlet v''' := Z.zselect g0 0 v' in
  let q'' := (q' + u''') mod 2^machine_wordsize in
  let r'' := (r' + v''') mod 2^machine_wordsize in
  (d'',f',g'',u'',v'',q'',r'').

Definition twos_complement_word_full_divstep machine_wordsize d f g u v q r :=
  twos_complement_word_full_divstep_aux machine_wordsize (d, f, g, u, v, q, r).

Definition hddivstep_spec_full m d f g v r :=
  if (0 <? d) && Z.odd g
  then (2 - d, g, (g - f) / 2, 2 * r mod m, (r - v) mod m)
  else (2 + d, f, (g + (g mod 2) * f) / 2, 2 * v mod m, (r + (g mod 2) * v) mod m).

Definition hddivstep_spec_full' d f g u v q r :=
  if (0 <? d) && Z.odd g
  then (2 - d, g, (g - f) / 2,
        2 * q, 2 * r, q - u, r - v)
  else (2 + d, f, (g + (g mod 2) * f) / 2,
        2 * u, 2 * v, q + (g mod 2) * u, r + (g mod 2) * v).

Fixpoint hddivstep_spec_full'_iter d f g u v q r n :=
  match n with
  | 0%nat => (d, f, g, u, v, q, r)
  | S n => let '(d, f, g, u, v, q, r) := hddivstep_spec_full'_iter d f g u v q r n in hddivstep_spec_full' d f g u v q r
  end.

Fixpoint hddivstep_full_iter m d f g v r n :=
  match n with
  | 0%nat => (d, f, g, v, r)
  | S n => let '(d, f, g, v, r) := hddivstep_full_iter m d f g v r n in hddivstep_spec_full m d f g v r
  end.

(**Brief section on twos_complement_neg (move at some point)  *)

Lemma twos_complement_neg_spec m a
      (mw0 : 0 < m) :
  Z.twos_complement_neg m a = Z.b2z (Z.testbit a (m - 1)).
Proof.
  unfold Z.twos_complement_neg.
  fold (Z.sign_bit m (a mod 2 ^ m)).
  rewrite Z.sign_bit_testbit. rewrite Z.mod_pow2_bits_low. lia. lia. lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg.
  lia. lia. Qed.

Lemma twos_complement_neg_spec_old m a
      (mw0 : 0 < m) :
  Z.twos_complement_neg m a =  Z.b2z (Z.twos_complement m a <? 0).
Proof.
  unfold Z.twos_complement_neg.
  fold (Z.sign_bit m (a mod 2 ^ m)).
  rewrite Z.sign_bit_testbit. rewrite Z.mod_pow2_bits_low.
  unfold Z.twos_complement. rewrite Z.twos_complement_cond_equiv.
  pose proof Z.mod_pos_bound a (2 ^ m) ltac:(apply Z.pow_pos_nonneg; lia).
  destruct (Z.testbit a (m - 1)); simpl.
  assert (a mod 2 ^ m - 2 ^ m <? 0 = true). apply Z.ltb_lt. lia. rewrite H0. reflexivity.
  assert (a mod 2 ^ m <? 0 = false). apply Z.ltb_ge. lia. rewrite H0. reflexivity. lia. lia. lia.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg. lia. lia. Qed.

(** Section about arithmetic right shift *)

Lemma sat_arithmetic_shiftr_0 machine_wordsize n f
      (Hm : 0 < machine_wordsize)
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  sat_arithmetic_shiftr machine_wordsize n f 0 = f.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  unfold sat_arithmetic_shiftr.
  rewrite Z.arithmetic_shiftr_0 by
      (try apply nth_default_preserves_properties; try assumption; lia).
  rewrite <- (map_nth_default_seq 0 n f) at 2 by assumption; destruct n; [lia|].
  rewrite seq_snoc, map_app.
  apply f_equal2; replace (S n - 1)%nat with n by lia; try reflexivity.
  apply map_seq_ext; try lia; intros i Hi.
  rewrite Z.shiftr_0_r, Z.truncating_shiftl_large, Z.lor_0_r, Nat.add_0_r by lia.
  reflexivity. Qed.

Lemma sat_arithmetic_shiftr_1 machine_wordsize n f
      (Hm : 0 < machine_wordsize)
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  sat_arithmetic_shiftr machine_wordsize n f 1 =
  sat_arithmetic_shiftr1 machine_wordsize n f.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  unfold sat_arithmetic_shiftr, sat_arithmetic_shiftr1.
  rewrite Z.arithmetic_shiftr_1 by
      (try apply nth_default_preserves_properties; try assumption; lia).
  reflexivity. Qed.

Lemma sat_arithmetic_shiftr_sat_arithmetic_shiftr1 machine_wordsize n (f : list Z) k
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hk : 0 <= k < machine_wordsize)
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  sat_arithmetic_shiftr machine_wordsize n
                        (sat_arithmetic_shiftr1 machine_wordsize n f) k =
  sat_arithmetic_shiftr machine_wordsize n f (k + 1).
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  unfold sat_arithmetic_shiftr, sat_arithmetic_shiftr1.
  rewrite nth_default_app, map_length, seq_length.
  destruct (lt_dec (n - 1) (n - 1)); try lia.
  replace (n - 1 - (n - 1))%nat with 0%nat by lia.
  rewrite nth_default_cons, Z.arithmetic_shiftr_arithmetic_shiftr1
    by (try (apply nth_default_preserves_properties; [assumption|Z.solve_range]); lia).
  apply f_equal2; try reflexivity. apply map_seq_ext; try lia; intros i Hi.
  rewrite !nth_default_app, map_length, seq_length.
  destruct (lt_dec i (n - 1));
    destruct (lt_dec (i + 1) (n - 1)); try lia.
  - rewrite !(map_nth_default _ _ _ _ 0%nat 0) by (rewrite seq_length; lia).
    rewrite !nth_default_seq_inbounds by lia.
    rewrite Nat.add_0_r, Z.shiftr_lor, Z.shiftr_shiftr by lia.
    rewrite Z.add_comm, <- Z.lor_assoc. apply f_equal2; try reflexivity.
    rewrite Z.truncating_shiftl_lor by lia.
    rewrite Z.truncating_shiftl_truncating_shiftl by lia.
    Z.solve_using_testbit; rewrite (Z.testbit_neg_r _ (n1 - _)), orb_false_r, ?orb_false_l by lia;
      apply f_equal2; try lia.
    all: apply f_equal2; try reflexivity; lia.
  - assert (E : (i + 1 = n - 1)%nat) by lia.
    rewrite !(map_nth_default _ _ _ _ 0%nat 0) by (rewrite seq_length; lia).
    rewrite !nth_default_seq_inbounds by lia; simpl; rewrite Nat.add_0_r.
    rewrite E. replace (n - 1 - (n - 1))%nat with 0%nat by lia.
    rewrite nth_default_cons, Z.shiftr_lor, Z.shiftr_shiftr, Z.add_comm by lia.
    rewrite <- Z.lor_assoc.
    apply f_equal2; [reflexivity|].
    Z.solve_using_testbit.
    apply nth_default_preserves_properties; [assumption|lia]. Qed.

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
  assert (H1 : 0 <= 0 < 2 ^ m) by Z.solve_range.
  apply in_app_iff in H. destruct H; simpl in H.
  - apply in_map_iff in H; destruct H as [i [H H0] ]; rewrite <- H.
    pose proof nth_default_preserves_properties _ f i 0 Hf H1;
      simpl in H2; Z.solve_range.
  - destruct H as [H|[] ]; rewrite <- H.
    apply Z.arithmetic_shiftr1_bound.
    pose proof nth_default_preserves_properties _ f (n - 1) 0 Hf H1;
      simpl in H0; Z.solve_range. Qed.

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
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm : 0 <= machine_wordsize) by lia.
  destruct (Z.abs_nat k) as [|m] eqn:E.
  - replace k with 0 by lia; simpl; apply sat_arithmetic_shiftr_0; try assumption; lia.
  - generalize dependent k. generalize dependent f.
    induction m; intros.
    + simpl; replace k with (0 + 1) by lia.
      rewrite sat_arithmetic_shiftr_1 by (try assumption; lia). reflexivity.
    + specialize (IHm (sat_arithmetic_shiftr1 machine_wordsize n f)
                      (sat_arithmetic_shiftr1_length machine_wordsize n f Hn Hf)
                      (sat_arithmetic_shiftr_bound machine_wordsize n f Hm Hf2)
                      (k - 1) ltac:(lia) ltac:(lia)).
      rewrite iter_sat_arithmetic_shiftr_S, <- IHm.
      rewrite sat_arithmetic_shiftr_sat_arithmetic_shiftr1
        by (try lia; assumption).
      rewrite Z.sub_simpl_r; reflexivity. Qed.

Lemma sat_arithmetic_shiftr_length machine_wordsize n f k
      (Hn : (0 < n)%nat)
      (Hf : length f = n) :
  length (sat_arithmetic_shiftr machine_wordsize n f k) = n.
Proof. unfold sat_arithmetic_shiftr; autorewrite with distr_length; lia. Qed.

Lemma sat_arithmetic_shiftr_bounds machine_wordsize n f k
      (Hn : (0 < n)%nat)
      (Hk : 0 <= k)
      (Hm : 0 < machine_wordsize)
      (Hf : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  forall y, In y (sat_arithmetic_shiftr machine_wordsize n f k) -> 0 <= y < 2 ^ machine_wordsize.
Proof.
  intros. unfold sat_arithmetic_shiftr in H.
  assert (H1 : 0 <= 0 < 2 ^ machine_wordsize) by Z.solve_range.
  apply in_app_iff in H; destruct H; simpl in H.
  - apply in_map_iff in H; destruct H as [i [H H0] ]; rewrite <- H.
    epose proof nth_default_preserves_properties _ f i 0 Hf H1.
      simpl in H2; Z.solve_range.
  - destruct H as [H|[] ]; rewrite <- H.
    apply Z.arithmetic_shiftr_bound; try lia.
    pose proof nth_default_preserves_properties _ f (n - 1) 0 Hf H1; simpl in H0;
      Z.solve_range. Qed.

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
  - generalize dependent k; generalize dependent f; induction m; intros.
    + simpl; replace k with 1 by lia; rewrite Z.pow_1_r.
      apply eval_twos_complement_sat_arithmetic_shiftr1; try assumption; lia.
    + rewrite iter_sat_arithmetic_shiftr_S.
      specialize (IHm (sat_arithmetic_shiftr1 machine_wordsize n f)
                      (sat_arithmetic_shiftr1_length machine_wordsize n f Hn Hf)
                      (sat_arithmetic_shiftr_bound machine_wordsize n f Hm Hf2)
                      (k - 1) ltac:(lia) ltac:(lia)).
      assert (0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
      rewrite IHm, eval_twos_complement_sat_arithmetic_shiftr1 by (try assumption; lia).
      rewrite Z.div_div, Z.pow_mul_base, Z.sub_simpl_r by lia; reflexivity. Qed.

(** Section for firstn *)
Lemma firstn_eval m n f k
      (Hm : 0 < m)
      (Hf : length f = n)
      (Hf2 : forall z : Z, In z f -> 0 <= z < 2 ^ m)
      (Hk : (k <= n)%nat) :
  Positional.eval (uweight m) k (firstn k f) = Positional.eval (uweight m) n f mod 2 ^ (m * k).
Proof.
  rewrite <- (firstn_skipn k f) at 2.
  replace n with (k + length (skipn k f))%nat by (rewrite skipn_length; lia).
  rewrite (uweight_eval_app' m ltac:(lia) k), uweight_eq_alt, <- Z.pow_mul_r
    by (rewrite ?firstn_length, ?Nat.min_l; lia).
  autorewrite with push_Zmod.
  rewrite Z.mod_0_l, Z.add_0_r,  Z.mod_mod
    by (try apply Z.pow_nonzero; nia).
  rewrite Z.mod_small. reflexivity.
  apply eval_bound. lia. intros.
  apply Hf2. apply (In_firstn k).  assumption.
  rewrite firstn_length, Nat.min_l. reflexivity. lia. Qed.

Local Notation eval m n f := (Positional.eval (uweight m) n f).

(**Section for nth_default 0 f 0  *)

Lemma eval_nth_default_0 m n f
      (Hm : 0 < m)
      (Hf : length f = n)
      (Hf2 : forall z : Z, In z f -> 0 <= z < 2 ^ m) :
  nth_default 0 f 0 = Positional.eval (uweight m) n f mod 2 ^ m.
Proof.
  induction f.
  - cbn; rewrite eval_nil, Z.mod_0_l. reflexivity. apply Z.pow_nonzero. lia. lia.
  - cbn. destruct n; [inversion Hf|].
    rewrite eval_cons, uweight_eval_shift.
    rewrite uweight_0, uweight_1, Z.mul_1_l.
    autorewrite with push_Zmod.
    rewrite Z.mod_0_l, Z.add_0_r, Z.mod_mod. rewrite Z.mod_small. reflexivity. apply Hf2. left. reflexivity.
    apply Z.pow_nonzero. lia. lia.
    apply Z.pow_nonzero. lia. lia. lia. auto. auto. Qed.

(** sat_ones section *)
Lemma sat_ones_spec m n
      (Hm : 0 <= m) :
  eval m n (sat_ones m n) = Z.ones (m * n).
Proof.
  unfold sat_ones. induction n.
  - rewrite Z.mul_0_r; reflexivity.
  - simpl.
    rewrite eval_cons, uweight_eval_shift by (try apply repeat_length; lia).
    rewrite IHn, uweight_0, uweight_eq_alt, Z.pow_1_r by lia.
    rewrite !Z.ones_equiv, <- !Z.sub_1_r. ring_simplify.
    rewrite <- Z.pow_add_r by lia. repeat apply f_equal2; lia. Qed.

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
  rewrite Z.sign_extend_add by (solve [ nia | apply eval_bound; assumption ]).
  unfold sat_sign_extend; rewrite unfold_Let_In, Zselect.Z.zselect_correct.
  rewrite Z.sign_bit_testbit
    by (solve [ lia | apply nth_default_preserves_properties; try assumption; Z.solve_range]).
  rewrite eval_testbit by (solve [ assumption | nia ]).
  assert (H : (Z.abs_nat ((m * Z.of_nat n_old - 1) / m)) = (n_old - 1)%nat).
  { unfold Z.sub. rewrite Z.div_add_l' by lia.
    assert (H2 : ((- (1)) / m) = - (1)).
    destruct (dec (m = 1)); subst; [reflexivity|].
    rewrite Z_div_nz_opp_full, Z.div_small by (rewrite ?Z.mod_1_l; lia); lia. rewrite H2; lia. }
  assert (H1 : (m * Z.of_nat n_old - 1) mod m = m - 1).
  { destruct (dec (m = 1)); subst; [now rewrite Z.mod_1_r|].
    repeat (pull_Zmod; push_Zmod). rewrite Z.mod_1_l, Z.mod_neg_small; lia. }
  rewrite H, H1.
  destruct (Z.testbit (nth_default 0 f (n_old - 1)) (m - 1)); simpl.
  -  rewrite (uweight_eval_app) with (n := (n_old)%nat) by (rewrite ?repeat_length; lia).
     rewrite repeat_length. fold (sat_ones m (n_new - n_old)).
     rewrite sat_ones_spec,  uweight_eq_alt by lia. unfold Z.ones_at. rewrite Z.shiftl_mul_pow2 by nia.
     rewrite Z.pow_mul_r by lia.
     replace (m * Z.of_nat (n_new - n_old)) with (m * Z.of_nat n_new - m * Z.of_nat n_old) by nia; lia.
  - rewrite (uweight_eval_app) with (n := (n_old)%nat) by (rewrite ?repeat_length; lia).
    rewrite repeat_length; fold (zeros (n_new - n_old)); rewrite eval_zeros; lia. Qed.

Lemma sat_sign_extend_length m n_old n_new f
      (Hn_old : (0 < n_old)%nat)
      (Hn_new : (n_old <= n_new)%nat)
      (Hf : (length f = n_old)) :
  length (sat_sign_extend m n_old n_new f) = n_new.
Proof. unfold sat_sign_extend; rewrite unfold_Let_In, app_length, repeat_length. lia. Qed.

Hint Rewrite sat_sign_extend_length : distr_length.

(** sat_mul section *)
Lemma sat_mul_bounds machine_wordsize n1 n2 f g
      (mw0 : 0 < machine_wordsize)
      (Hn2 : (0 < n2)%nat)
      (Hf : length f = n1)
      (Hg : length g = n1) :
  forall z, In z (sat_mul machine_wordsize n1 n2 f g) -> 0 <= z < 2 ^ machine_wordsize.
Proof.
  intros z H; unfold sat_mul in *.
  rewrite Rows.mul_partitions in * by (try apply uwprops; try apply Z.pow_nonzero; lia).
  unfold Partition.partition in H. apply ListAux.in_map_inv in H.
  destruct H as [a [H]]. rewrite H0, !uweight_eq_alt; try lia.
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

Lemma sat_mul_length machine_wordsize n1 n2 f g
      (mw0 : 0 < machine_wordsize)
      (Hn2 : (0 < n2)%nat)
      (Hf : length f = n1)
      (Hg : length g = n1) :
  length (sat_mul machine_wordsize n1 n2 f g) = n2.
Proof.
  unfold sat_mul. rewrite Rows.length_mul by (try apply uwprops; assumption). reflexivity. Qed.

Lemma sat_twos_complement_mul_length machine_wordsize na nb nab f g
      (mw0 : 0 < machine_wordsize)
      (Hna : (0 < na <= nab)%nat)
      (Hnb : (0 < nb <= nab)%nat)
      (Hf : length f = na)
      (Hg : length g = nb) :
  length (sat_twos_complement_mul machine_wordsize na nb nab f g) = nab.
Proof.
  unfold sat_twos_complement_mul. rewrite firstn_length, Rows.length_mul. lia.
  apply uwprops; lia. all: apply sat_sign_extend_length; lia. Qed.

Theorem sat_twos_complement_mul_correct m na nb nab a b
        (Hm : 0 < m)
        (Hna : (0 < na <= nab)%nat)
        (Hnb : (0 < nb <= nab)%nat)
        (Ha : length a = na)
        (Hb : length b = nb)
        (Ha2 : forall z : Z, In z a -> 0 <= z < 2 ^ m)
        (Hb2 : forall z : Z, In z b -> 0 <= z < 2 ^ m)
        (Hab_overflow : - 2 ^ (m * Z.of_nat nab - 1) <=
                        Z.twos_complement (m * Z.of_nat na) (eval m na a) * Z.twos_complement (m * Z.of_nat nb) (eval m nb b) <
                        2 ^ (m * Z.of_nat nab - 1)) :
  eval_twos_complement m (nab) (sat_twos_complement_mul m na nb nab a b) =
  (eval_twos_complement m na a) * (eval_twos_complement m nb b).
Proof.
  pose proof (uwprops m Hm).
  pose proof (eval_bound m na a Hm Ha2 Ha).
  pose proof (eval_bound m nb b Hm Hb2 Hb).
  unfold sat_twos_complement_mul, eval_twos_complement.
  rewrite (firstn_eval m (2 * nab)), Rows.mul_partitions, !sat_sign_extend_eval, eval_partition, Z.twos_complement_mod.
  rewrite Z.mod_small.
  fold (Z.twos_complement_mul_aux (m * na) (m * nb) (m * nab) (eval m na a) (eval m nb b)).
  rewrite Z.twos_complement_mul_aux_spec by nia. reflexivity.
  pose proof (Z.sign_extend_bound (m * na) (m * nab) (eval m na a) ltac:(nia) ltac:(nia) ltac:(assumption)).
  pose proof (Z.sign_extend_bound (m * nb) (m * nab) (eval m nb b) ltac:(nia) ltac:(nia) ltac:(assumption)).
  rewrite uweight_eq_alt.
  replace ((2 ^ m) ^ Z.of_nat (2 * nab)) with (2 ^ (m * Z.of_nat nab) * 2 ^ (m * Z.of_nat nab)) by
      (rewrite <- Z.pow_mul_r, <- Z.pow_add_r by nia; apply f_equal; nia). all: try nia; try assumption.
  apply Z.pow_nonzero; lia. distr_length. distr_length.
  apply Rows.length_mul; try assumption; distr_length.
  apply sat_mul_bounds; distr_length; lia. Qed.

Lemma sat_twos_complement_mul_full_length machine_wordsize na nb f g
      (mw0 : 0 < machine_wordsize)
      (Hna : (0 < na)%nat)
      (Hnb : (0 < nb)%nat)
      (Hf : length f = na)
      (Hg : length g = nb) :
  length (sat_twos_complement_mul_full machine_wordsize na nb f g) = (na + nb)%nat.
Proof.
  unfold sat_twos_complement_mul_full. apply sat_twos_complement_mul_length; lia. Qed.

Theorem sat_twos_complement_mul_full_correct m na nb a b
        (Hm : 0 < m)
        (Hna : (0 < na)%nat)
        (Hnb : (0 < nb)%nat)
        (Ha : length a = na)
        (Hb : length b = nb)
        (Ha2 : forall z : Z, In z a -> 0 <= z < 2 ^ m)
        (Hb2 : forall z : Z, In z b -> 0 <= z < 2 ^ m) :
  eval_twos_complement m (na + nb) (sat_twos_complement_mul_full m na nb a b) =
  (eval_twos_complement m na a) * (eval_twos_complement m nb b).
Proof.
  unfold sat_twos_complement_mul_full. apply sat_twos_complement_mul_correct; try assumption; try lia.
  pose proof (Z.twos_complement_bounds (m * Z.of_nat na) (eval m na a)).
  pose proof (Z.twos_complement_bounds (m * Z.of_nat nb) (eval m nb b)).
  assert (2 ^ (m * Z.of_nat na - 1) * 2 ^ (m * Z.of_nat nb - 1) < 2 ^ (m * Z.of_nat (na + nb) - 1)).
  rewrite <- Z.pow_add_r by nia. apply Z.pow_lt_mono_r; nia. nia. Qed.

Lemma word_sat_mul_length m n a b
        (Hm : 0 < m)
        (Hn : (0 < n)%nat)
        (Ha : 0 <= a < 2 ^ m)
        (Hb : length b = n) :
  length (word_sat_mul m n a b) = (1 + n)%nat.
Proof.
  unfold word_sat_mul. apply sat_twos_complement_mul_full_length; try lia; reflexivity. Qed.

Theorem word_sat_mul_correct m n a b
        (Hm : 0 < m)
        (Hn : (0 < n)%nat)
        (Ha : 0 <= a < 2 ^ m)
        (Hb : length b = n)
        (Hb2 : forall z : Z, In z b -> 0 <= z < 2 ^ m) :
  eval_twos_complement m (1 + n) (word_sat_mul m n a b) =
  (Z.twos_complement m a) * eval_twos_complement m n b.
Proof.
  unfold word_sat_mul.
  replace (Z.twos_complement m a) with (eval_twos_complement m 1 [a]).
  apply sat_twos_complement_mul_full_correct; try assumption; try lia; try reflexivity.
  intros z Hin; destruct Hin as [|[]]; subst; assumption.
  unfold eval_twos_complement.
  apply f_equal2; [lia|]; rewrite eval_cons, uweight_0, uweight_eval_shift, eval_nil, uweight_1; try reflexivity; lia. Qed.

(** Correctness of wordsized divstep *)
Theorem twos_complement_word_full_divstep_correct
        machine_wordsize d f g u v q r
        (fodd : Z.odd f = true)
        (mw1 : 2 < machine_wordsize)
        (overflow_d : - 2 ^ (machine_wordsize - 1) + 2 <
                      Z.twos_complement machine_wordsize d <
                      2 ^ (machine_wordsize - 1) - 2)
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
  hddivstep_spec_full' (Z.twos_complement machine_wordsize d)
                       (Z.twos_complement machine_wordsize f)
                       (Z.twos_complement machine_wordsize g)
                       (Z.twos_complement machine_wordsize u)
                       (Z.twos_complement machine_wordsize v)
                       (Z.twos_complement machine_wordsize q)
                       (Z.twos_complement machine_wordsize r).
Proof.
  assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
      (rewrite Z.pow_mul_base by lia; apply f_equal2; lia).
  assert (2 ^ (machine_wordsize - 2) < 2^(machine_wordsize - 1)) by
      (apply Z.pow_lt_mono_r; lia).
  assert (2 <= 2 ^ (machine_wordsize - 2)) by
      (replace 2 with (2 ^ 1) by lia; apply Z.pow_le_mono_r; lia).
  unfold hddivstep_spec_full'; cbn -[Z.mul Z.add].
  rewrite !Zselect.Z.zselect_correct.
  rewrite !twos_complement_pos_spec, Zmod_odd, Z.twos_complement_odd by lia.
  rewrite Z.twos_complement_mod2, (Zmod_odd g) by lia.
  destruct (0 <? Z.twos_complement machine_wordsize d);
    destruct (Z.odd g) eqn:godd;
    rewrite (Zmod_odd); cbn -[Z.mul Z.add];
      rewrite ?godd; cbn -[Z.mul Z.add].
  rewrite <- (Z.twos_complement_odd machine_wordsize), !twos_complement_opp_spec by lia;
    rewrite Z.odd_opp, Z.twos_complement_odd, fodd by lia; cbn -[Z.mul Z.add].
  all: (repeat apply f_equal2;
        repeat rewrite 1?Z.twos_complement_mod, 1?Z.twos_complement_add_full, 1?Z.twos_complement_one,
        1?Z.arithmetic_shiftr1_spec, 1?twos_complement_opp_spec, 1?Z.twos_complement_zero;
        rewrite ?Z.twos_complement_one, ?Z.twos_complement_two, ?twos_complement_opp_spec;
        try apply Z.mod_pos_bound; try apply f_equal2; lia). Qed.

Definition twos_complement_word_full_divsteps machine_wordsize d f g u v q r n :=
  fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r).

Lemma twos_complement_word_full_divsteps_d_bound
      machine_wordsize d f g u v q r n K
      (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - 2 * (Z.of_nat n))
      (mw1 : 2 < machine_wordsize)
      (overflow_d : - K <
                    Z.twos_complement machine_wordsize d <
                    K) :
  let '(d1,_,_,_,_,_,_) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
  - K - 2 * Z.of_nat n <
  Z.twos_complement machine_wordsize d1 <
  K + 2 * Z.of_nat n.
Proof.
  induction n; intros.
  - rewrite Z.add_0_r, Z.sub_0_r in *; cbn. assumption.
  - rewrite seq_snoc, fold_left_app.
    replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in * by lia.
    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
    cbn -[Z.mul Z.add].

    rewrite !Zselect.Z.zselect_correct.
    rewrite twos_complement_pos_spec.
    rewrite Zmod_odd.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add oppmod]; try assumption;
        rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?twos_complement_opp_spec, ?Z.twos_complement_one, ?Z.twos_complement_two; try lia;
          rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?twos_complement_opp_spec, ?Z.twos_complement_one, ?Z.twos_complement_two; try lia.
    lia. lia. Qed.

Lemma twos_complement_word_full_divsteps_f_odd
      machine_wordsize d f g u v q r n
      (mw0 : 0 < machine_wordsize)
      (fodd : Z.odd f = true) :
  let '(_,f1,_,_,_,_,_) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in
  Z.odd f1 = true.
Proof.
  induction n; [assumption|].
  rewrite seq_snoc, fold_left_app.
  destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
  cbn -[Z.mul Z.add].
  rewrite !Zselect.Z.zselect_correct.
  destruct (dec _); [assumption|].
  rewrite Zmod_odd in *. destruct (Z.odd g1). reflexivity. rewrite Z.land_0_r in n0. contradiction. Qed.

Lemma div_lt_lower_bound a b c : 0 < b -> b * (a + 1) <= c -> a < c / b.
Proof. intros. enough (a + 1 <= c / b) by lia. apply Z.div_le_lower_bound; assumption. Qed.

Lemma twos_complement_word_full_divsteps_bounds
      machine_wordsize d f g u v q r n K
      (HK : 0 < K)
      (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 1))
      (mw1 : 2 < machine_wordsize)
      (fodd : Z.odd f = true)
      (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n) <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n)
      (overflow_f : - 2 ^ (machine_wordsize - 2) <
                    Z.twos_complement machine_wordsize f <
                    2 ^ (machine_wordsize - 2))
      (overflow_g : - 2 ^ (machine_wordsize - 2) <
                    Z.twos_complement machine_wordsize g <
                    2 ^ (machine_wordsize - 2))
      (overflow_u : - K <
                    Z.twos_complement machine_wordsize u <
                    K)
      (overflow_v : - K <
                    Z.twos_complement machine_wordsize v <
                    K)
      (overflow_q : - K <
                    Z.twos_complement machine_wordsize q <
                    K)
      (overflow_r : - K <
                    Z.twos_complement machine_wordsize r <
                    K) :
  let '(_,f1,g1,u1,v1,q1,r1) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
      - 2 ^ (machine_wordsize - 2) <
      Z.twos_complement machine_wordsize f1 <
      2 ^ (machine_wordsize - 2) /\
      - 2 ^ (machine_wordsize - 2) <
      Z.twos_complement machine_wordsize g1 <
      2 ^ (machine_wordsize - 2) /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize u1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize v1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize q1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize r1 <
      2 ^ n * K.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).

  induction n; intros.
  - cbn -[Z.mul Z.add]. lia.
  -

    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).


    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct.
    rewrite twos_complement_pos_spec.
    rewrite Zmod_odd.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add oppmod].
    + rewrite Zmod_odd.
      rewrite !twos_complement_opp_odd by (try assumption; lia).  cbn -[Z.mul Z.add].
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full.
      rewrite !twos_complement_opp_spec by lia.
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
      lia.
      rewrite twos_complement_opp_spec. lia. lia. lia. lia.
      rewrite twos_complement_opp_spec. lia. lia. lia. lia.
      lia. lia. lia. lia.
      rewrite twos_complement_opp_spec. lia. lia. lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + lia.
    + lia.

      Unshelve.
      lia. lia. lia. assumption. Qed.

Lemma twos_complement_word_full_divsteps_partial_bounds
      machine_wordsize d f g u v q r n K
      (HK : 0 < K)
      (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 1))
      (mw1 : 2 < machine_wordsize)
      (fodd : Z.odd f = true)
      (u_pos : 0 <= u < 2 ^ machine_wordsize)
      (v_pos : 0 <= v < 2 ^ machine_wordsize)
      (q_pos : 0 <= q < 2 ^ machine_wordsize)
      (r_pos : 0 <= r < 2 ^ machine_wordsize)
      (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n) <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n)
      (overflow_u : - K <
                    Z.twos_complement machine_wordsize u <
                    K)
      (overflow_v : - K <
                    Z.twos_complement machine_wordsize v <
                    K)
      (overflow_q : - K <
                    Z.twos_complement machine_wordsize q <
                    K)
      (overflow_r : - K <
                    Z.twos_complement machine_wordsize r <
                    K) :
  let '(_,_,_,u1,v1,q1,r1) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize u1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize v1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize q1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize r1 <
      2 ^ n * K /\
      0 <= u1 < 2 ^ machine_wordsize /\
      0 <= v1 < 2 ^ machine_wordsize /\
      0 <= q1 < 2 ^ machine_wordsize /\
      0 <= r1 < 2 ^ machine_wordsize.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).

  induction n; intros.
  - cbn -[Z.mul Z.add]. lia.
  -

    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).


    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct.
    rewrite twos_complement_pos_spec.
    rewrite Zmod_odd.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add oppmod].
    + rewrite Zmod_odd.
      rewrite !twos_complement_opp_odd by (try assumption; lia).  cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full.
      rewrite !twos_complement_opp_spec by lia.
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
      lia.
      rewrite twos_complement_opp_spec. lia. lia. lia. lia.
      rewrite twos_complement_opp_spec. lia. lia. lia. lia.
      lia. lia. lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia.
    + lia.
    + lia.

      Unshelve.
      lia. lia. lia. assumption. Qed.

Lemma twos_complement_word_full_divsteps_partial_bounds2
      machine_wordsize d f g u v q r n K
      (HK : 0 < K)
      (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 1))
      (mw1 : 2 < machine_wordsize)
      (fodd : Z.odd f = true)
      (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n) <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n)
      (overflow_u : - K <
                    Z.twos_complement machine_wordsize u <
                    K)
      (overflow_v : - K <
                    Z.twos_complement machine_wordsize v <
                    K)
      (overflow_q : - K <
                    Z.twos_complement machine_wordsize q <
                    K)
      (overflow_r : - K <
                    Z.twos_complement machine_wordsize r <
                    K) :
  let '(_,_,_,u1,v1,q1,r1) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize u1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize v1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize q1 <
      2 ^ n * K /\
      - 2 ^ n * K <
      Z.twos_complement machine_wordsize r1 <
      2 ^ n * K.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).

  induction n; intros.
  - cbn -[Z.mul Z.add]. lia.
  -

    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).


    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct.
    rewrite twos_complement_pos_spec.
    rewrite Zmod_odd.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add oppmod].
    + rewrite Zmod_odd.
      rewrite !twos_complement_opp_odd by (try assumption; lia).  cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full.
      rewrite !twos_complement_opp_spec by lia.
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
      lia.
      rewrite twos_complement_opp_spec. lia. lia. lia. lia.
      rewrite twos_complement_opp_spec. lia. lia. lia. lia.
      lia. lia. lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod by lia.
      rewrite !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + lia.
    + lia.

      Unshelve.
      lia. lia. lia. assumption. Qed.

Theorem twos_complement_word_full_divstep_iter_correct
        machine_wordsize d f g u v q r n K
        (fodd : Z.odd f = true)
        (HK : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 1))
        (mw1 : 2 < machine_wordsize)
        (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n) <
                      Z.twos_complement machine_wordsize d <
                      2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n)
        (overflow_f : - 2 ^ (machine_wordsize - 2) <
                      Z.twos_complement machine_wordsize f <
                      2 ^ (machine_wordsize - 2))
        (overflow_g : - 2 ^ (machine_wordsize - 2) <
                      Z.twos_complement machine_wordsize g <
                      2 ^ (machine_wordsize - 2))
        (overflow_u : - K <
                      Z.twos_complement machine_wordsize u <
                      K)
        (overflow_v : - K <
                      Z.twos_complement machine_wordsize v <
                      K)
        (overflow_q : - K <
                      Z.twos_complement machine_wordsize q <
                      K)
        (overflow_r : - K <
                      Z.twos_complement machine_wordsize r <
                      K)
        (Hf2 : 0 <= f < 2^machine_wordsize)
        (Hg2 : 0 <= g < 2^machine_wordsize) :
  let '(d1,f1,g1,u1,v1,q1,r1) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in
  (Z.twos_complement machine_wordsize d1,
   Z.twos_complement machine_wordsize f1,
   Z.twos_complement machine_wordsize g1,
   Z.twos_complement machine_wordsize u1,
   Z.twos_complement machine_wordsize v1,
   Z.twos_complement machine_wordsize q1,
   Z.twos_complement machine_wordsize r1) =
  hddivstep_spec_full'_iter (Z.twos_complement machine_wordsize d)
                            (Z.twos_complement machine_wordsize f)
                            (Z.twos_complement machine_wordsize g)
                            (Z.twos_complement machine_wordsize u)
                            (Z.twos_complement machine_wordsize v)
                            (Z.twos_complement machine_wordsize q)
                            (Z.twos_complement machine_wordsize r) n.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
      (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

  induction n.
  - simpl. reflexivity.
  - intros.

    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.
    epose proof twos_complement_word_full_divsteps_bounds machine_wordsize d f g u v q r n K _ _ _ _ _ _ _ _ _ _ _.


    rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
    rewrite <- IHn.
    cbn -[Z.mul Z.add].
    unfold hddivstep_spec_full'. rewrite !Zselect.Z.zselect_correct.
    rewrite Z.twos_complement_odd.
    rewrite twos_complement_pos_spec.
    rewrite Zmod_odd.

    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add oppmod].
    + rewrite Zmod_odd. rewrite twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
      repeat apply f_equal2.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite twos_complement_opp_spec.
        rewrite Z.twos_complement_two. lia. lia. lia. lia. lia.
        rewrite twos_complement_opp_spec.
        rewrite Z.twos_complement_two. lia. lia. lia. lia. lia.
      * reflexivity.
      * reflexivity.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full by (try rewrite twos_complement_opp_spec; lia).
        rewrite twos_complement_opp_spec by lia. apply f_equal2; lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full by (try rewrite twos_complement_opp_spec; lia).
        rewrite twos_complement_opp_spec by lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full by (try rewrite twos_complement_opp_spec; lia).
        rewrite twos_complement_opp_spec by lia. lia.
    + rewrite !Zmod_odd, Z.twos_complement_odd, g1odd, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
      * reflexivity.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia. reflexivity.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      * rewrite Z.twos_complement_mod by lia. reflexivity.
      *
        rewrite Z.twos_complement_mod by lia. reflexivity.
    + rewrite !Zmod_odd, Z.twos_complement_odd, g1odd, !Z.mul_1_l by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
      * reflexivity.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      * rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
    + rewrite !Zmod_odd, Z.twos_complement_odd, g1odd, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
      * reflexivity.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia. reflexivity.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      * rewrite Z.twos_complement_mod by lia. reflexivity.
      *
        rewrite Z.twos_complement_mod by lia. reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.

      Unshelve.
      all: try lia; try assumption.  Qed.

Theorem twos_complement_word_full_divstep_iter_partially_correct
        machine_wordsize d f g u v q r n K
        (fodd : Z.odd f = true)
        (HK : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 1))
        (mw1 : 2 < machine_wordsize)
        (nmw : n < machine_wordsize)
        (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n) <
                      Z.twos_complement machine_wordsize d <
                      2 ^ (machine_wordsize - 1) - 1 - 2 * Z.of_nat n)
        (overflow_u : - K <
                      Z.twos_complement machine_wordsize u <
                      K)
        (overflow_v : - K <
                      Z.twos_complement machine_wordsize v <
                      K)
        (overflow_q : - K <
                      Z.twos_complement machine_wordsize q <
                      K)
        (overflow_r : - K <
                      Z.twos_complement machine_wordsize r <
                      K)
        (u_pos : 0 <= u < 2 ^ machine_wordsize)
        (v_pos : 0 <= v < 2 ^ machine_wordsize)
        (q_pos : 0 <= q < 2 ^ machine_wordsize)
        (r_pos : 0 <= r < 2 ^ machine_wordsize)
        (Hf2 : 0 <= f < 2^machine_wordsize)
        (Hg2 : 0 <= g < 2^machine_wordsize) :
  let '(d1,f1,g1,u1,v1,q1,r1) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in
  (Z.twos_complement machine_wordsize d1,
   Z.twos_complement machine_wordsize f1 mod 2 ^ (machine_wordsize - Z.of_nat n),
   Z.twos_complement machine_wordsize g1 mod 2 ^ (machine_wordsize - Z.of_nat n),
   Z.twos_complement machine_wordsize u1,
   Z.twos_complement machine_wordsize v1,
   Z.twos_complement machine_wordsize q1,
   Z.twos_complement machine_wordsize r1) =
  let '(d1',f1',g1',u1',v1',q1',r1') := hddivstep_spec_full'_iter (Z.twos_complement machine_wordsize d)
                                                                  (Z.twos_complement machine_wordsize f)
                                                                  (Z.twos_complement machine_wordsize g)
                                                                  (Z.twos_complement machine_wordsize u)
                                                                  (Z.twos_complement machine_wordsize v)
                                                                  (Z.twos_complement machine_wordsize q)
                                                                  (Z.twos_complement machine_wordsize r) n in
  (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1',v1',q1',r1').
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
      (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

  induction n.
  - simpl. reflexivity.
  - intros.

    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.
    epose proof twos_complement_word_full_divsteps_partial_bounds machine_wordsize d f g u v q r n K _ _ _ _ _ _ _ _ _.

    rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
    destruct (hddivstep_spec_full'_iter (Z.twos_complement machine_wordsize d) (Z.twos_complement machine_wordsize f)
        (Z.twos_complement machine_wordsize g) (Z.twos_complement machine_wordsize u) (Z.twos_complement machine_wordsize v)
        (Z.twos_complement machine_wordsize q) (Z.twos_complement machine_wordsize r) n) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2 .

    assert (        (Z.twos_complement machine_wordsize d1, Z.twos_complement machine_wordsize f1 mod 2 ^ (machine_wordsize - Z.of_nat n),
        Z.twos_complement machine_wordsize g1 mod 2 ^ (machine_wordsize - Z.of_nat n), Z.twos_complement machine_wordsize u1,
        Z.twos_complement machine_wordsize v1, Z.twos_complement machine_wordsize q1, Z.twos_complement machine_wordsize r1) =
        (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1', v1', q1', r1')).
    apply IHn; lia.
    inversion H4.

    rewrite Z.twos_complement_mod_smaller_pow in H7 by lia.
    rewrite Z.twos_complement_mod_smaller_pow in H8 by lia.

    cbn -[Z.mul Z.add].
    unfold hddivstep_spec_full'. rewrite !Zselect.Z.zselect_correct.
    rewrite twos_complement_pos_spec.
    rewrite Zmod_odd.

    assert (Z.odd g1 = Z.odd g1').
    rewrite <- (odd_mod2m (machine_wordsize - Z.of_nat n) g1').
    rewrite <- H8.

    rewrite odd_mod2m. reflexivity. lia. lia.
    rewrite <- H5.

    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add oppmod].
    + rewrite Zmod_odd. rewrite twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite twos_complement_opp_spec.
        rewrite Z.twos_complement_two. lia. lia. lia. lia. lia.
        rewrite twos_complement_opp_spec.
        rewrite Z.twos_complement_two. lia. lia. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod_smaller_pow.
        rewrite <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)).
        rewrite H8.
        rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. lia.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite !Z.mod_pull_div. apply f_equal2.
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)).
        rewrite twos_complement_opp_correct.
        rewrite Z.twos_complement_mod_smaller_pow.


        rewrite <- Zplus_mod_idemp_l.
        rewrite Z.mod_pow_same_base_smaller.
        rewrite Zplus_mod_idemp_l.
        push_Zmod. rewrite H7, H8. pull_Zmod.
        apply f_equal2. lia. lia. lia. lia. lia. rewrite Z.mul_comm, Z.pow_mul_base. apply f_equal2. lia. lia. lia. lia.
        apply Z.pow_nonneg. lia.
        apply Z.pow_nonneg. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full by (try rewrite twos_complement_opp_spec; lia).
        rewrite twos_complement_opp_spec by lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full by (try rewrite twos_complement_opp_spec; lia).
        rewrite twos_complement_opp_spec by lia. lia.
    + rewrite !Zmod_odd, g1odd, <- H5, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
      *
        rewrite Z.twos_complement_mod_smaller_pow.
        rewrite <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)).
        rewrite H7.
        rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. lia.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite !Z.mod_pull_div. apply f_equal2.
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)).
        rewrite Z.twos_complement_mod_smaller_pow. assumption. lia.
        rewrite Z.mul_comm, Z.pow_mul_base. apply f_equal2. lia. lia. lia. lia.
        apply Z.pow_nonneg. lia.
        apply Z.pow_nonneg. lia.

      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      * rewrite Z.twos_complement_mod by lia. reflexivity.
      *
        rewrite Z.twos_complement_mod by lia. reflexivity.
    + rewrite !Zmod_odd, g1odd, <- H5, !Z.mul_1_l by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
      *
        rewrite Z.twos_complement_mod_smaller_pow.
        rewrite <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)).
        rewrite H7.
        rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. lia.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite !Z.mod_pull_div. apply f_equal2.
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)).
        rewrite Z.twos_complement_mod_smaller_pow.

        push_Zmod. rewrite H7, H8. pull_Zmod.
        apply f_equal2. lia. lia. lia. rewrite Z.mul_comm, Z.pow_mul_base. apply f_equal2. lia. lia. lia. lia.
        apply Z.pow_nonneg. lia.
        apply Z.pow_nonneg. lia.

      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      * rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
    + rewrite !Zmod_odd, g1odd, <- H5, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
        rewrite Z.twos_complement_two.
        lia. lia. lia.
      *
        rewrite Z.twos_complement_mod_smaller_pow.
        rewrite <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)).
        rewrite H7.
        rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. lia.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite !Z.mod_pull_div. apply f_equal2.
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)).
        rewrite Z.twos_complement_mod_smaller_pow. assumption.
        lia. rewrite Z.mul_comm, Z.pow_mul_base. apply f_equal2. lia. lia. lia. lia.
        apply Z.pow_nonneg. lia.
        apply Z.pow_nonneg. lia.

      *        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      *
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full. lia. lia. lia.
      * rewrite Z.twos_complement_mod by lia. reflexivity.
      *
        rewrite Z.twos_complement_mod by lia. reflexivity.
    + lia.
    + lia.

      Unshelve.
      all: try lia; try assumption.  Qed.


Lemma hddivstep_full_iter_full'_iter m d f g u2 v1 v2 q2 r1 r2 n :
  let '(d1,f1,g1,_,_) :=
      hddivstep_full_iter m d f g v1 r1 n in
  (d1,f1,g1)
  = let '(d2,f2,g2,_,_,_,_) := hddivstep_spec_full'_iter d f g u2 v2 q2 r2 n in
    (d2,f2,g2).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    destruct (hddivstep_full_iter m d f g v1 r1 n) as [[[[?]?]?]?].
    destruct (hddivstep_spec_full'_iter d f g u2 v2 q2 r2 n) as [[[[[[?]?]?]?]?]?].
    inversion IHn.
    unfold hddivstep_spec_full'.
    unfold hddivstep_spec_full.
    destruct (0 <? z4); destruct (Z.odd z6); cbn -[Z.add Z.mul Z.div Z.sub]; reflexivity. Qed.

Lemma hddivstep_full_iter_f_odd m f g v r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_) := hddivstep_full_iter m 1 f g v r n in Z.odd f = true.
Proof.
  induction n.
  - assumption.
  - simpl. unfold hddivstep_spec_full.
    destruct (hddivstep_full_iter m 1 f g v r n) as [[[[d1 f1]g1]v1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption. Qed.

Lemma hddivstep_full'_iter_f_odd d f g u v q r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_,_,_) := hddivstep_spec_full'_iter d f g u v q r n in Z.odd f = true.
Proof.
  induction n.
  - assumption.
  - simpl. unfold hddivstep_spec_full'.
    destruct (hddivstep_spec_full'_iter d f g u v q r n) as [[[[[[d1 f1]g1]u1]v1]q1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption. Qed.

Lemma hddivstep_full'_iter_important_bits d f f0 g g0 u v q r n k
      (Hk : (0 <= n < k)%nat)
      (fodd : Z.odd f = true)
      (fmod : f mod 2 ^ Z.of_nat k = f0 mod 2 ^ Z.of_nat k)
      (gmod : g mod 2 ^ Z.of_nat k = g0 mod 2 ^ Z.of_nat k) :
  let '(d1,f1,g1,u1,v1,q1,r1) :=
      hddivstep_spec_full'_iter d f g u v q r n in
  let '(d2,f2,g2,u2,v2,q2,r2) :=
      hddivstep_spec_full'_iter d f0 g0 u v q r n in
  g1 mod 2 ^ (k - n) = g2 mod 2 ^ (k - n) /\
  f1 mod 2 ^ (k - n) = f2 mod 2 ^ (k - n) /\
  d1 = d2 /\
  (u1,v1,q1,r1) = (u2,v2,q2,r2).
Proof.
  induction n.
  - cbn in *. rewrite !Z.sub_0_r. repeat split; lia.
  - simpl.

    pose proof hddivstep_full'_iter_f_odd d f g u v q r n.
    pose proof hddivstep_full'_iter_f_odd d f0 g0 u v q r n.

    destruct (hddivstep_spec_full'_iter d f g u v q r n) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
    destruct (hddivstep_spec_full'_iter d f0 g0 u v q r n) as [[[[[[d2 f2] g2] u2] v2] q2] r2] eqn:E2.

    specialize (H fodd).
    assert (Z.odd f0 = true).
    { rewrite <- odd_mod2m with (m:=k). rewrite <- fmod. rewrite odd_mod2m. assumption. lia. lia. }

    assert (g1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = g2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            f1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = f2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            d1 = d2 /\ (u1, v1, q1, r1) = (u2, v2, q2, r2)).
    apply IHn. lia.

    destruct H2 as [H3 [H4 [H5 H6]]].

    assert (Z.odd g1 = Z.odd g2 /\ d1 = d2).
    { rewrite <- odd_mod2m with (m:=k - n). rewrite H3.
      rewrite odd_mod2m. split. reflexivity. assumption. lia. lia. }

    unfold hddivstep_spec_full'. destruct H2. rewrite H7, H2.
    inversion H6.

    destruct (0 <? d2); destruct (Z.odd g2) eqn:odd; cbn -[Z.mul Z.add Z.div].
    + split.
      rewrite !Z.mod_pull_div.
      rewrite Z.mul_comm. rewrite Z.pow_mul_base.
      replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
      push_Zmod. rewrite H3, H4. reflexivity. lia.
      apply Z.pow_nonneg. lia.
      apply Z.pow_nonneg. lia.

      split.

      rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)).
      rewrite H3.
      rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia.

      split.

      lia.
      congruence.
    + split.
      rewrite !Z.mod_pull_div.
      rewrite (Z.mul_comm _ 2). rewrite Z.pow_mul_base.
      replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
      push_Zmod. rewrite H3, H4.
      rewrite !Zmod_odd, odd, H2. reflexivity. lia.
      apply Z.pow_nonneg. lia.
      apply Z.pow_nonneg. lia.

      split.

      rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)).
      rewrite H4.
      rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. split. lia. subst.
      rewrite !Zmod_odd, odd, H2. reflexivity.

    + split.
      rewrite !Z.mod_pull_div.
      rewrite (Z.mul_comm _ 2). rewrite Z.pow_mul_base.
      replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
      push_Zmod. rewrite H3, H4.
      rewrite !Zmod_odd, odd, H2. reflexivity. lia.
      apply Z.pow_nonneg. lia.
      apply Z.pow_nonneg. lia.

      split.

      rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)).
      rewrite H4.
      rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. split. lia.

      rewrite !Zmod_odd, odd, H2. reflexivity.
    + split.
      rewrite !Z.mod_pull_div.
      rewrite (Z.mul_comm _ 2). rewrite Z.pow_mul_base.
      replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
      push_Zmod. rewrite H3, H4.
      rewrite !Zmod_odd, odd, H2. reflexivity. lia.
      apply Z.pow_nonneg. lia.
      apply Z.pow_nonneg. lia.

      split.

      rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)).
      rewrite H4.
      rewrite Z.mod_pow_same_base_smaller. reflexivity. lia. lia. lia. lia. split. lia.
      rewrite !Zmod_odd, odd, H2. reflexivity. Qed.

Lemma jump_hddivstep_full_iter m f g v r n
      (fodd : Z.odd f = true)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m)
  :
    let '(d1, f1, g1, v1, r1) := hddivstep_full_iter m 1 f g v r n in
    (d1,2 ^ n * f1,2 ^ n * g1,v1,r1)
  = let '(d1', f1', g1', u1', v1', q1', r1') := hddivstep_spec_full'_iter 1 f g 1 0 0 1 n in
    (d1', (u1' * f + v1' * g), (q1' * f + r1' * g), (u1' * v + v1' * r) mod m, (q1' * v + r1' * r) mod m).
Proof.
  induction n.
  - cbn -[Z.add Z.mul].
    repeat match goal with
           | [ |- (_, _) = (_, _) ] => apply f_equal2; rewrite ?Z.div_1_r, ?Z.mod_small by lia; try lia
           end.
  - cbn -[Z.pow Z.mul Z.add Z.of_nat].
    pose proof hddivstep_full_iter_full'_iter m 1 f g 1 v 0 0 r 1 n.
    pose proof hddivstep_full_iter_f_odd m f g v r n fodd as fodd1.

    destruct (hddivstep_spec_full'_iter 1 f g 1 0 0 1 n) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
    destruct (hddivstep_full_iter m 1 f g v r n) as [[[[d2 f2] g2] v2] r2] eqn:E2.

    replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1).
    rewrite <- Z.pow_mul_base.
    unfold hddivstep_spec_full.
    unfold hddivstep_spec_full'.
    inversion H.
    inversion IHn.
    destruct (0 <? d1); destruct (Z.odd g1) eqn:godd; cbn -[Z.mul Z.add Z.div Z.of_nat];
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2; try (push_Zmod; pull_Zmod; apply f_equal2; lia)
             end; try lia.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_comm.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_div_eq'. subst.

    rewrite Zmod_odd, Z.odd_sub, godd, fodd1; cbn. lia. lia.

    rewrite <- Z.mul_assoc.
    rewrite Z.mul_comm.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_div_eq'. subst.

    rewrite Zmod_odd, godd. cbn. rewrite !Z.add_0_r.
    rewrite Zmod_odd, godd. lia. lia.

    rewrite <- Z.mul_assoc.
    rewrite Z.mul_comm.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_div_eq'. subst.

    rewrite Zmod_odd, godd. rewrite Z.mul_1_l.
    rewrite Zmod_odd, Z.odd_add, godd, fodd1. rewrite Z.sub_0_r. lia. lia.

    rewrite <- Z.mul_assoc.
    rewrite Z.mul_comm.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_div_eq'. subst.

    rewrite Zmod_odd, godd. rewrite !Z.mul_0_l, !Z.add_0_r.
    rewrite Zmod_odd, godd. lia. lia. lia. lia. Qed.

Lemma jump_hddivstep_full m f f0 g g0 v r n
      (fodd : Z.odd f = true)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m)
      (Hf : f mod 2 ^ (Z.of_nat (S n)) = f0 mod 2 ^ (Z.of_nat (S n)))
      (Hg : g mod 2 ^ (Z.of_nat (S n)) = g0 mod 2 ^ (Z.of_nat (S n)))
  :
  hddivstep_full_iter m 1 f g v r n
  = let '(d1', f1', g1', u1', v1', q1', r1') := hddivstep_spec_full'_iter 1 f0 g0 1 0 0 1 n in
    (d1', (u1' * f + v1' * g) / 2 ^ n, (q1' * f + r1' * g) / 2 ^ n, (u1' * v + v1' * r) mod m, (q1' * v + r1' * r) mod m).
Proof.
  assert (f0odd : Z.odd f0 = true).
  { rewrite <- odd_mod2m with (m:=S n). rewrite <- Hf. rewrite odd_mod2m. assumption. lia. lia. }

  pose proof jump_hddivstep_full_iter m f g v r n fodd Hv Hr.
  pose proof hddivstep_full'_iter_important_bits 1 f f0 g g0 1 0 0 1 n (S n) ltac:(lia) fodd Hf Hg.


  destruct (hddivstep_full_iter m 1 f g v r n) as [[[[d1 f1] g1] v1] r1] eqn:E1.
  destruct (hddivstep_spec_full'_iter 1 f g 1 0 0 1 n) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2.
  destruct (hddivstep_spec_full'_iter 1 f0 g0 1 0 0 1 n) as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3.

  destruct H0 as [H1 [H2 [H3 H4]]].

  inversion H.
  inversion H4. subst.

  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H6.
  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H7.
  rewrite Z.div_mul' in *.

  congruence.
  apply Z.pow_nonzero. lia. lia.
  apply Z.pow_nonzero. lia. lia. Qed.

(* TODO: Move thise *)
Lemma fold_right_fold_left_lemma {A B : Type} (f : B -> A -> A) (l s : list B) (a : A) :
  (forall x x' y, f x y = f x' y) -> length l = length s -> fold_left (fun i j => f j i) l a = fold_right f a s.
Proof.
  rewrite <- fold_left_rev_right. revert s a.
  induction l; intros.
  - assert (s = []) by (destruct s; simpl in *; try lia; reflexivity); subst. reflexivity.
  - simpl. rewrite fold_right_snoc. replace s with (rev (rev s)) by (apply rev_involutive).
    destruct (rev s) eqn:E.
    apply (f_equal (@rev B)) in E. rewrite rev_involutive in E. subst. simpl in *. lia.
    simpl. rewrite fold_right_snoc.
    replace (f a a0) with (f b a0). apply IHl. assumption.
    apply (f_equal (@length B)) in E. simpl in *.
    rewrite rev_length in *. lia. apply H. Qed.

Lemma pow_ineq k : (2 <= k)%nat -> k + 2 <= Zpower_nat 2 k.
Proof.
  induction k; intros.
  - lia.
  - destruct k.
    + lia.
    + rewrite Zpower_nat_succ_r.
      * destruct k. simpl. lia. lia. Qed.

Lemma pow_ineq2 k : (3 <= k)%nat -> 2 * k + 2 <= Zpower_nat 2 k.
Proof.
  induction k; intros.
  - lia.
  - destruct k.
    + lia.
    + rewrite Zpower_nat_succ_r.
      * destruct k.
        ** simpl. lia.
        ** destruct k.
           *** simpl. lia.
           *** lia. Qed.

Lemma pow_ineq_Z k : 2 <= k -> k + 2 <= 2 ^ k.
Proof.
  intros. replace k with (Z.of_nat (Z.to_nat k)).
  rewrite <- Zpower_nat_Z. apply pow_ineq. lia. lia. Qed.

Lemma pow_ineq_Z2 k : 3 <= k -> 2 * k + 2 <= 2 ^ k.
Proof.
  intros. replace k with (Z.of_nat (Z.to_nat k)).
  rewrite <- Zpower_nat_Z. apply pow_ineq2. lia. lia. Qed.

Module WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.

  Section __.
    Context (machine_wordsize : Z)
            (n : nat)
            (sat_limbs : nat)
            (word_sat_mul_limbs : nat)
            (m : Z)
            (r' : Z)
            (m' : Z)
            (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
            (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
            (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat n)
            (m_big : 2 ^ machine_wordsize < m).

  (* Converts a wordsized integer to montgomery domain *)
    Definition twosc_word_to_montgomery a :=
      dlet cond := Z.twos_complement_neg machine_wordsize a in
      dlet a_opp := Z.twos_complement_opp machine_wordsize a in
      dlet a_enc := encodemod machine_wordsize n m m' a in
      dlet a_opp_enc := encodemod machine_wordsize n m m' (a_opp) in
      dlet a_opp_enc_opp := oppmod machine_wordsize n m (a_opp_enc) in
      dlet res := select cond a_enc a_opp_enc_opp in res.

  (* Converts a wordsize integer to montgomery domain (without multiplying by R2) *)
    Definition twos_complement_word_to_montgomery_no_encode a :=
      dlet cond := Z.twos_complement_neg machine_wordsize a in
      dlet a_opp := Z.twos_complement_opp machine_wordsize a in
      dlet a_enc := Partition.partition (uweight machine_wordsize) n a in
      dlet a_opp_enc := Partition.partition (uweight machine_wordsize) n a_opp in
      dlet a_opp_enc_opp := oppmod machine_wordsize n m (a_opp_enc) in
                              dlet res := select cond a_enc a_opp_enc_opp in res.

    Lemma twos_complement_word_to_montgomery_no_encode_correct a
          (Hmw : 0 < machine_wordsize)
          (Hn : (1 < n)%nat)
          (* (Hm : 1 < m) *)
          (Ha : 0 <= a < 2 ^ machine_wordsize)
      :
        @eval machine_wordsize n (twos_complement_word_to_montgomery_no_encode a) mod m = Z.twos_complement machine_wordsize a mod m
        /\ valid machine_wordsize n m (twos_complement_word_to_montgomery_no_encode a).
    Proof.
      unfold twos_complement_word_to_montgomery_no_encode.

      assert (valid machine_wordsize n m (Partition.partition (uweight machine_wordsize) n (Z.twos_complement_opp machine_wordsize a))).
      { unfold valid. unfold small. split. unfold eval. rewrite eval_partition.
      rewrite uweight_eq_alt'. rewrite Z.mod_small. reflexivity.
      rewrite twos_complement_opp_correct. pose proof Z.mod_pos_bound (-a) (2^machine_wordsize).

      assert (2 ^ (machine_wordsize) <= 2 ^ (machine_wordsize * Z.of_nat n)).
      apply Z.pow_le_mono_r. lia. nia. lia. apply uwprops. lia.
      unfold eval. rewrite eval_partition.

      rewrite uweight_eq_alt'.
      rewrite twos_complement_opp_correct. pose proof Z.mod_pos_bound (-a) (2^machine_wordsize) ltac:(apply Z.pow_pos_nonneg; lia).
      rewrite Z.mod_pow_same_base_larger.
      pose proof Z.mod_small. lia. nia. lia.

      apply uwprops; lia. }

      (* unfold Z.twos_complement_neg. *)
      rewrite twos_complement_neg_spec.
      rewrite !unfold_Let_In.
      rewrite select_eq with (n:=n).

      unfold Z.twos_complement.
      rewrite Z.twos_complement_cond_equiv.

      destruct (Z.testbit a (machine_wordsize - 1)) eqn:E. cbn -[Partition.partition oppmod]. split.
      replace (@eval machine_wordsize n
                    (oppmod machine_wordsize n m (Partition.partition (uweight machine_wordsize) n (Z.twos_complement_opp machine_wordsize a)))) with
          (@eval machine_wordsize n
            (oppmod machine_wordsize n m (Partition.partition (uweight machine_wordsize) n (Z.twos_complement_opp machine_wordsize a))) * (1 ^ n)).
      rewrite <- r'_correct. push_Zmod; pull_Zmod.
      rewrite Z.pow_mul_l. rewrite Z.mul_comm. rewrite <- Z.mul_assoc. rewrite Z.mul_comm. rewrite (Z.mul_comm (r' ^ _)).
      rewrite <- Zmult_mod_idemp_l.
      rewrite <- eval_from_montgomerymod with (m':=m').

      rewrite eval_oppmod with (r':=r').
      push_Zmod. rewrite eval_from_montgomerymod with (r':=r').
      push_Zmod. unfold eval. rewrite eval_partition. rewrite twos_complement_opp_correct.
      pull_Zmod.
      rewrite uweight_eq_alt'. rewrite Z.mod_pow_same_base_larger.
      rewrite Z.mul_opp_l. rewrite <- Z.mul_assoc. rewrite <- Z.pow_mul_l. rewrite (Z.mul_comm r').
      rewrite PullPush.Z.opp_mod_mod.
      rewrite <- Zmult_mod_idemp_r.
      rewrite PullPush.Z.mod_pow_full. rewrite r'_correct.
      rewrite Z.pow_1_l. pull_Zmod. rewrite Z.mul_1_r.


      destruct (dec (a = 0)).
      subst. rewrite Z.bits_0 in *. inversion E.

      rewrite (Z.mod_opp_small a).
      apply f_equal2. rewrite Z.mod_small.

      all: try assumption; try lia; try nia.

      apply uwprops; lia.

      pose proof oppmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
      apply H0. assumption.

      rewrite Z.pow_1_l. lia. lia.
      pose proof oppmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.

      apply H0. assumption.

      cbn. split.
      unfold eval.
      rewrite eval_partition.
      rewrite uweight_eq_alt.
      rewrite (Z.mod_small a).
      rewrite (Z.mod_small a (2 ^ _)). reflexivity. assumption. nia. lia.

      apply uwprops; lia.

      unfold valid.
      split.
      unfold small.
      unfold eval. rewrite eval_partition.
      rewrite uweight_eq_alt'. rewrite Z.mod_small. reflexivity.
      assert (2 ^ (machine_wordsize) <= 2 ^ (machine_wordsize * Z.of_nat n)).
      { apply Z.pow_le_mono_r. lia. nia. } lia.

      apply uwprops; lia.

      unfold eval. rewrite eval_partition.
      rewrite uweight_eq_alt'. rewrite Z.mod_small. lia.
      assert (2 ^ (machine_wordsize) <= 2 ^ (machine_wordsize * Z.of_nat n)).
      { apply Z.pow_le_mono_r. lia. nia. } lia.
      apply uwprops; lia.

      apply (uweight machine_wordsize).

      rewrite length_partition. reflexivity.

      apply length_small with (lgr:=machine_wordsize).

      pose proof oppmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
      apply H0.
      assumption.
    Qed.

    Lemma eval_twos_complement_word_to_montgomery_no_encode a
          (Hmw : 0 < machine_wordsize)
          (Hn : (1 < n)%nat)
          (Hm : 1 < m)
          (Ha : 0 <= a < 2 ^ machine_wordsize)
      :
        @eval machine_wordsize n (twos_complement_word_to_montgomery_no_encode a) mod m = Z.twos_complement machine_wordsize a mod m.
    Proof. apply twos_complement_word_to_montgomery_no_encode_correct; assumption. Qed.

    Definition twosc_word_mod_m a :=
      dlet cond := Z.twos_complement_neg machine_wordsize a in
      dlet a' := Z.zselect cond a (Z.twos_complement_opp machine_wordsize a) in
      let a'' := extend_to_length 1 n [a'] in
      let a''_opp := oppmod machine_wordsize n m a'' in
      select cond a'' a''_opp.

    Definition outer_loop_body f g (v r : list Z) :=
      let '(_,f1,g1,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_divstep_aux machine_wordsize data) (1,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      dlet f2 := word_sat_mul machine_wordsize sat_limbs u1 f in
      dlet f3 := word_sat_mul machine_wordsize sat_limbs v1 g in
      dlet g2 := word_sat_mul machine_wordsize sat_limbs q1 f in
      dlet g3 := word_sat_mul machine_wordsize sat_limbs r1 g in
      dlet f4 := BYInv.sat_add machine_wordsize word_sat_mul_limbs f2 f3 in
      dlet g4 := BYInv.sat_add machine_wordsize word_sat_mul_limbs g2 g3 in
      dlet f5 := sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs f4 (machine_wordsize - 2) in
      dlet g5 := sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs g4 (machine_wordsize - 2) in
      dlet f6 := firstn sat_limbs f5 in
      dlet g6 := firstn sat_limbs g5 in
      dlet u2 := twos_complement_word_to_montgomery_no_encode u1 in
      dlet v02 := twos_complement_word_to_montgomery_no_encode v1 in
      dlet q2 := twos_complement_word_to_montgomery_no_encode q1 in
      dlet r02 := twos_complement_word_to_montgomery_no_encode r1 in
      dlet v2 := mulmod machine_wordsize n m m' u2 v in
      dlet v3 := mulmod machine_wordsize n m m' v02 r in
      dlet r2 := mulmod machine_wordsize n m m' q2 v in
      dlet r3 := mulmod machine_wordsize n m m' r02 r in
      dlet v4 := addmod machine_wordsize n m v2 v3 in
      dlet r4 := addmod machine_wordsize n m r2 r3 in
      (f6, g6, v4, r4).

    (** Correctness of outer loop body  *)
    Theorem outer_loop_body_correct f g v r
            (fodd : Z.odd (eval_twos_complement machine_wordsize sat_limbs f) = true)
            (n1 : (1 < n)%nat)
            (mw1 : 3 < machine_wordsize)
            (Hf : length f = sat_limbs)
            (Hg : length g = sat_limbs)

            (sat_limbs0 : (0 < sat_limbs)%nat)
            (word_sat_mul_limbs_eq : (word_sat_mul_limbs = 1 + sat_limbs)%nat)
            (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                          eval_twos_complement machine_wordsize sat_limbs f <
                          2 ^ (machine_wordsize * sat_limbs - 2))
            (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                          eval_twos_complement machine_wordsize sat_limbs g <
                          2 ^ (machine_wordsize * sat_limbs - 2))
            (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
            (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize)
            (Hr : valid machine_wordsize n m r)
            (Hv : valid machine_wordsize n m v) :
      let '(f1,g1,v1,r1) := outer_loop_body f g v r in
      (eval_twos_complement machine_wordsize sat_limbs f1,
       eval_twos_complement machine_wordsize sat_limbs g1,
       @eval machine_wordsize n v1 mod m,
       @eval machine_wordsize n r1 mod m)
      =
      let '(_,f1',g1',v1',r1') :=
          hddivstep_full_iter m 1
                            (eval_twos_complement machine_wordsize sat_limbs f)
                            (eval_twos_complement machine_wordsize sat_limbs g)
                            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' v) mod m)
                            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' r) mod m)
                            (Z.to_nat (machine_wordsize - 2)) in
      (Z.twos_complement (machine_wordsize * sat_limbs) f1',
       Z.twos_complement (machine_wordsize * sat_limbs) g1', v1', r1').
    Proof.
      pose proof (pow_ineq_Z2 (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize).
      { apply Zpow_facts.Zpower_gt_1. lia. lia. }
      assert (0 < 2 ^ (machine_wordsize - 1)).
      { apply Z.pow_pos_nonneg. lia. lia. }
      assert (0 < 2 ^ (machine_wordsize - 2)).
      { apply Z.pow_pos_nonneg. lia. lia. }
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1)).
      { rewrite Z.mul_comm, Z.pow_mul_base. apply f_equal2; lia. lia. }
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat sat_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + sat_limbs)) - 1)).
      { rewrite <- Zpower_exp, !Z.pow_mul_base. apply f_equal2; lia. nia. nia. nia. lia. }

      unfold outer_loop_body.
      epose proof twos_complement_word_full_divstep_iter_partially_correct (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

      epose proof twos_complement_word_full_divsteps_partial_bounds (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.

      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      epose proof jump_hddivstep_full
            m
            (eval_twos_complement machine_wordsize sat_limbs f)
            (Z.twos_complement machine_wordsize (nth_default 0 f 0))
            (eval_twos_complement machine_wordsize sat_limbs g)
            (Z.twos_complement machine_wordsize (nth_default 0 g 0))
            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' v) mod m)
            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' r) mod m)
            (Z.to_nat (machine_wordsize - 2)) _ _ _ _ _ _.

      rewrite Z.twos_complement_one in *.
      rewrite Z.twos_complement_zero in *.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))).

      destruct (    fold_left (fun (i : Z * Z * Z * Z * Z * Z * Z) (_ : nat) => twos_complement_word_full_divstep_aux machine_wordsize i)
                              (seq 0 (Z.to_nat (machine_wordsize - 2))) (1, nth_default 0 f 0, nth_default 0 g 0, 1, 0, 0, 1)) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1 .

      destruct (hddivstep_full_iter
                  m 1
                  (eval_twos_complement machine_wordsize sat_limbs f)
                  (eval_twos_complement machine_wordsize sat_limbs g)
                  (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' v) mod m)
                  (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' r) mod m) (Z.to_nat (machine_wordsize - 2)))
        as [[[[d1' f1'] g1'] v1'] r1'] eqn:E2.


      destruct (hddivstep_spec_full'_iter
                  1
                  (Z.twos_complement machine_wordsize (nth_default 0 f 0))
                  (Z.twos_complement machine_wordsize (nth_default 0 g 0))
                  1 0 0 1 (Z.to_nat (machine_wordsize - 2)))
        as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3.

      rewrite !unfold_Let_In.

      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.

      + unfold eval_twos_complement.
        rewrite firstn_eval with (n:=word_sat_mul_limbs).
        rewrite Z.twos_complement_mod.
        rewrite <- Z.twos_complement_twos_complement_smaller_width with (m':=machine_wordsize * Z.of_nat word_sat_mul_limbs).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs
                                                                                              (BYInv.sat_add machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs u1 f)
                                                                                                             (word_sat_mul machine_wordsize sat_limbs v1 g)) (machine_wordsize - 2))).
        rewrite eval_sat_arithmetic_shiftr.
        unfold eval_twos_complement.
        rewrite eval_sat_add.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs v1 g)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs u1 f)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.
        inversion H7.
        inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) by lia. reflexivity. lia. lia.

        all: try assumption; try lia; try nia.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs v1 g)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs u1 f)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.


        pose proof Z.twos_complement_bounds.


        nia. lia. lia. lia. lia. auto. lia. lia. lia. lia. auto.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply length_sat_add.  lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_length. lia.

        apply length_sat_add.  lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_bounds. lia. lia. lia.
        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
      + unfold eval_twos_complement.
        rewrite firstn_eval with (n:=word_sat_mul_limbs).
        rewrite Z.twos_complement_mod.
        rewrite <- Z.twos_complement_twos_complement_smaller_width with (m':=machine_wordsize * Z.of_nat word_sat_mul_limbs).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs
                                   (sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs
                                                          (BYInv.sat_add machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs q1 f)
                                                                         (word_sat_mul machine_wordsize sat_limbs r1 g)) (machine_wordsize - 2))).
        rewrite eval_sat_arithmetic_shiftr.
        unfold eval_twos_complement.
        rewrite eval_sat_add.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs q1 f)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs r1 g)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.
        inversion H7.
        inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) by lia. reflexivity. lia. lia.

        all: try assumption; try lia; try nia.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs q1 f)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs r1 g)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.


        pose proof Z.twos_complement_bounds.


        nia. lia. lia. lia. lia. auto. lia. lia. lia. lia. auto.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply length_sat_add.  lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_length. lia.

        apply length_sat_add.  lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_bounds. lia. lia. lia.
        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
      +


        rewrite <- (Z.mul_1_r (@eval _ _ _)).
        rewrite <- (Z.pow_1_l n).

        rewrite <- r'_correct. push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l. rewrite Z.mul_comm. rewrite <- Z.mul_assoc. rewrite Z.mul_comm. rewrite (Z.mul_comm (r' ^ _)).
        rewrite <- Zmult_mod_idemp_l.
        rewrite <- eval_from_montgomerymod with (m':=m').

        rewrite eval_addmod with (r':=r').
        push_Zmod.
        rewrite !eval_mulmod with (r':=r').

        push_Zmod. rewrite !eval_from_montgomerymod with (r':=r'). push_Zmod.
        rewrite !eval_twos_complement_word_to_montgomery_no_encode.
        pull_Zmod.
        rewrite Z.mul_add_distr_r.
        rewrite <- !Z.mul_assoc.
        rewrite <- Z.pow_mul_l. rewrite (Z.mul_comm r').
        rewrite !Z.mul_assoc.
        rewrite <- Z.mul_add_distr_r.
        rewrite <- Zmult_mod_idemp_r.
        rewrite PullPush.Z.mod_pow_full. rewrite r'_correct.
        rewrite Z.pow_1_l. rewrite Z.mod_1_l. rewrite Z.mul_1_r.


        inversion H7. inversion H5. rewrite !eval_from_montgomerymod with (r':=r'). push_Zmod; pull_Zmod.
        apply f_equal2.

        all: try assumption; try apply twos_complement_word_to_montgomery_no_encode_correct; try lia.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H8.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H8.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.

        pose proof addmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H8.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H9.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H9.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.
     +
        rewrite <- (Z.mul_1_r (@eval _ _ _)).
        rewrite <- (Z.pow_1_l n).

        rewrite <- r'_correct. push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l. rewrite Z.mul_comm. rewrite <- Z.mul_assoc. rewrite Z.mul_comm. rewrite (Z.mul_comm (r' ^ _)).
        rewrite <- Zmult_mod_idemp_l.
        rewrite <- eval_from_montgomerymod with (m':=m').

        rewrite eval_addmod with (r':=r').
        push_Zmod.
        rewrite !eval_mulmod with (r':=r').

        push_Zmod. rewrite !eval_from_montgomerymod with (r':=r'). push_Zmod.
        rewrite !eval_twos_complement_word_to_montgomery_no_encode.
        pull_Zmod.
        rewrite Z.mul_add_distr_r.
        rewrite <- !Z.mul_assoc.
        rewrite <- Z.pow_mul_l. rewrite (Z.mul_comm r').
        rewrite !Z.mul_assoc.
        rewrite <- Z.mul_add_distr_r.
        rewrite <- Zmult_mod_idemp_r.
        rewrite PullPush.Z.mod_pow_full. rewrite r'_correct.
        rewrite Z.pow_1_l. rewrite Z.mod_1_l. rewrite Z.mul_1_r.


        inversion H7. inversion H5. rewrite !eval_from_montgomerymod with (r':=r'). push_Zmod; pull_Zmod.
        apply f_equal2.

        all: try assumption; try apply twos_complement_word_to_montgomery_no_encode_correct; try lia.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H8.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H8.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.

        pose proof addmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H8.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H9.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.

        pose proof mulmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small.
        apply H9.

        apply twos_complement_word_to_montgomery_no_encode_correct; try lia.
        assumption.
     + intros. reflexivity.
     + reflexivity.
     + lia.
     + lia.


Unshelve.
      rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=sat_limbs).
      unfold eval_twos_complement in fodd.
      rewrite Z.twos_complement_odd in fodd.
      rewrite odd_mod2m. assumption.

      lia. nia. lia. assumption.  assumption.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      lia. lia. lia. rewrite Z.twos_complement_one. lia. lia.
      rewrite Z.twos_complement_one. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_one. lia. lia.

      lia. lia. lia. lia.
      apply Hf2.
      destruct f. simpl in *. lia. simpl. left. cbn. reflexivity.
      apply Hg2.
      destruct g. simpl in *. lia. simpl. left. cbn. reflexivity.

      lia.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.
      lia. lia. rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize).
      rewrite odd_mod2m. unfold eval_twos_complement in fodd.
      rewrite Z.twos_complement_odd in fodd. assumption. nia. lia. lia. assumption. assumption.
      lia. lia. lia. lia.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.
      rewrite Z.twos_complement_one. lia. lia.

      rewrite Z.twos_complement_one. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_one. lia. lia.

      assumption. lia.
      apply Z.mod_pos_bound. lia.
      apply Z.mod_pos_bound. lia.

      unfold eval_twos_complement.
      rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize).

      rewrite Z.twos_complement_mod.

      rewrite !Z.twos_complement_mod_smaller_pow. reflexivity. lia. nia. lia. lia. assumption. assumption.

      unfold eval_twos_complement.
      rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize).

      rewrite Z.twos_complement_mod.

      rewrite !Z.twos_complement_mod_smaller_pow. reflexivity. lia. nia. lia. lia. assumption. assumption. Qed.
  End __.
End WordByWordMontgomery.

Module UnsaturatedSolinas.
  Section __.

    Context (limbwidth_num limbwidth_den : Z)
            (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
            (machine_wordsize : Z)
            (s : Z)
            (c : list (Z*Z))
            (n : nat)
            (sat_limbs : nat)
            (word_sat_mul_limbs : nat)
            (idxs : list nat)
            (m_big : 2 ^ machine_wordsize < s - Associational.eval c)
            (len_c : nat)
            (len_idxs : nat)
            (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
            (Hn_nz : n <> 0%nat)
            (Hc : length c = len_c)
            (Hidxs : length idxs = len_idxs).
    
    Notation eval := (Positional.eval (weight (limbwidth_num) (limbwidth_den)) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    Definition word_to_solina a :=
      dlet cond := Z.twos_complement_neg machine_wordsize a in
      dlet a_opp := Z.twos_complement_opp machine_wordsize a in
      dlet a_enc := encodemod limbwidth_num limbwidth_den s c n a in
      dlet a_opp_enc := encodemod limbwidth_num limbwidth_den s c n (a_opp) in
      dlet a_opp_enc_opp := oppmod limbwidth_num limbwidth_den n balance (a_opp_enc) in
      dlet a_opp_enc_opp_carry := carrymod limbwidth_num limbwidth_den s c n idxs a_opp_enc_opp in
      dlet res := select cond a_enc a_opp_enc_opp_carry in res.

    Lemma word_to_solina_length a :
      length (word_to_solina a) = n.
    Proof.
      unfold word_to_solina. 
      rewrite !unfold_Let_In; rewrite length_select with (n:=n);
        unfold carrymod, oppmod, encodemod; auto with distr_length. Qed.

    Hint Resolve word_to_solina_length : distr_length.
    
    Lemma eval_word_to_solina a
          (Hmw : 0 < machine_wordsize)
          (Hn : (1 < n)%nat)
          (Ha : 0 <= a < 2 ^ machine_wordsize) :
      eval (word_to_solina a) mod (s - Associational.eval c) =
      Z.twos_complement machine_wordsize a mod (s - Associational.eval c).
    Proof.
      unfold word_to_solina. 
      rewrite twos_complement_neg_spec.
      rewrite !unfold_Let_In.
      rewrite select_eq with (n:=n).

      unfold Z.twos_complement.
      rewrite Z.twos_complement_cond_equiv.

      destruct (Z.testbit a (machine_wordsize - 1)) eqn:E. cbn -[Partition.partition oppmod].

      rewrite eval_carrymod.
      rewrite eval_oppmod.
      push_Zmod.
      rewrite eval_encodemod.
      pull_Zmod.
      rewrite twos_complement_opp_correct.

      destruct (dec (a = 0)). subst. rewrite Z.bits_0 in E. inversion E.
      pose proof Z.mod_pos_bound a (2 ^ machine_wordsize) ltac:(lia). 
      pose proof Z.mod_pos_bound (- a) (2 ^ machine_wordsize) ltac:(lia). 

      rewrite Z.mod_opp_small.
      rewrite Z.mod_opp_small.
      replace (a mod 2 ^ machine_wordsize - 2 ^ machine_wordsize) with (- (2 ^ machine_wordsize - (a mod 2 ^ machine_wordsize))) by lia.
      rewrite Z.mod_opp_small.
      rewrite Z.mod_small. lia. lia.
      pose proof Z.mod_pos_bound a (2 ^ machine_wordsize) ltac:(lia). lia.  lia.

      rewrite (Z.mod_opp_small a). lia. lia. 
      
      all: try lia; try assumption; unfold encodemod, oppmod; auto with distr_length. 

      simpl.
      pose proof wprops limbwidth_num limbwidth_den limbwidth_good. destruct H.
      rewrite eval_encode. rewrite (Z.mod_small _ (2 ^ _)).
      
      reflexivity.
      all: auto.

      intros. unfold weight. apply Z.pow_nonzero. lia. 
      apply Z.opp_nonneg_nonpos.
      apply Z.div_le_upper_bound. lia. nia. intros. specialize (weight_divides i). lia.

      unfold carrymod; auto with distr_length.
    Qed.
    
    Definition outer_loop_body f g (v r : list Z) :=
      let '(_,f1,g1,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_divstep_aux machine_wordsize data) (1,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      dlet f2 := word_sat_mul machine_wordsize sat_limbs u1 f in
      dlet f3 := word_sat_mul machine_wordsize sat_limbs v1 g in
      dlet g2 := word_sat_mul machine_wordsize sat_limbs q1 f in
      dlet g3 := word_sat_mul machine_wordsize sat_limbs r1 g in
      dlet f4 := BYInv.sat_add machine_wordsize word_sat_mul_limbs f2 f3 in
      dlet g4 := BYInv.sat_add machine_wordsize word_sat_mul_limbs g2 g3 in
      dlet f5 := sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs f4 (machine_wordsize - 2) in
      dlet g5 := sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs g4 (machine_wordsize - 2) in
      dlet f6 := firstn sat_limbs f5 in
      dlet g6 := firstn sat_limbs g5 in
      dlet u2 := word_to_solina u1 in
      dlet v02 := word_to_solina v1 in
      dlet q2 := word_to_solina q1 in
      dlet r02 := word_to_solina r1 in
      dlet v2 := carry_mulmod limbwidth_num limbwidth_den s c n idxs u2 v in
      dlet v3 := carry_mulmod limbwidth_num limbwidth_den s c n idxs v02 r in
      dlet r2 := carry_mulmod limbwidth_num limbwidth_den s c n idxs q2 v in
      dlet r3 := carry_mulmod limbwidth_num limbwidth_den s c n idxs r02 r in
      dlet v4 := addmod limbwidth_num limbwidth_den n v2 v3 in
      dlet v5 := carrymod limbwidth_num limbwidth_den s c n idxs v4 in
      dlet r4 := addmod limbwidth_num limbwidth_den n r2 r3 in
      dlet r5 := carrymod limbwidth_num limbwidth_den s c n idxs r4 in
      (f6, g6, v5, r5).

  (** Correctness of outer loop body  *)
  Theorem outer_loop_body_correct f g v r
          (fodd : Z.odd (eval_twos_complement machine_wordsize sat_limbs f) = true)
          (n1 : (1 < n)%nat)
          (mw1 : 3 < machine_wordsize)
          (Hf : length f = sat_limbs)
          (Hg : length g = sat_limbs)
          (Hv : length v = n)
          (Hr : length r = n)
          (sat_limbs0 : (0 < sat_limbs)%nat)
          (word_sat_mul_limbs_eq : (word_sat_mul_limbs = 1 + sat_limbs)%nat)
          (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                        eval_twos_complement machine_wordsize sat_limbs f <
                        2 ^ (machine_wordsize * sat_limbs - 2))
          (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                        eval_twos_complement machine_wordsize sat_limbs g <
                        2 ^ (machine_wordsize * sat_limbs - 2))
          (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
          (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
    let '(f1,g1,v1,r1) := outer_loop_body f g v r in
    (eval_twos_complement machine_wordsize sat_limbs f1,
     eval_twos_complement machine_wordsize sat_limbs g1,
     eval v1 mod (s - Associational.eval c),
     eval r1 mod (s - Associational.eval c))
    =
    let '(_,f1',g1',v1',r1') :=
        hddivstep_full_iter (s - Associational.eval c) 1
                          (eval_twos_complement machine_wordsize sat_limbs f)
                          (eval_twos_complement machine_wordsize sat_limbs g)
                          (eval v mod (s - Associational.eval c))
                          (eval r mod (s - Associational.eval c))
                          (Z.to_nat (machine_wordsize - 2)) in
    (Z.twos_complement (machine_wordsize * sat_limbs) f1',
     Z.twos_complement (machine_wordsize * sat_limbs) g1', v1', r1').
    Proof.
      pose proof (pow_ineq_Z2 (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize).
      { apply Zpow_facts.Zpower_gt_1. lia. lia. }
      assert (0 < 2 ^ (machine_wordsize - 1)).
      { apply Z.pow_pos_nonneg. lia. lia. }
      assert (0 < 2 ^ (machine_wordsize - 2)).
      { apply Z.pow_pos_nonneg. lia. lia. }
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1)).
      { rewrite Z.mul_comm, Z.pow_mul_base. apply f_equal2; lia. lia. }
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat sat_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + sat_limbs)) - 1)).
      { rewrite <- Zpower_exp, !Z.pow_mul_base. apply f_equal2; lia. nia. nia. nia. lia. }

      unfold outer_loop_body.
      epose proof twos_complement_word_full_divstep_iter_partially_correct (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

      epose proof twos_complement_word_full_divsteps_partial_bounds (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.

      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      epose proof jump_hddivstep_full
            (s - Associational.eval c)
            (eval_twos_complement machine_wordsize sat_limbs f)
            (Z.twos_complement machine_wordsize (nth_default 0 f 0))
            (eval_twos_complement machine_wordsize sat_limbs g)
            (Z.twos_complement machine_wordsize (nth_default 0 g 0))
            (eval v mod (s - Associational.eval c))
            (eval r mod (s - Associational.eval c))
            (Z.to_nat (machine_wordsize - 2)) _ _ _ _ _ _.

      rewrite Z.twos_complement_one in *.
      rewrite Z.twos_complement_zero in *.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))).

      destruct (    fold_left (fun (i : Z * Z * Z * Z * Z * Z * Z) (_ : nat) => twos_complement_word_full_divstep_aux machine_wordsize i)
                              (seq 0 (Z.to_nat (machine_wordsize - 2))) (1, nth_default 0 f 0, nth_default 0 g 0, 1, 0, 0, 1)) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1 .

      destruct (hddivstep_full_iter
                  (s - Associational.eval c) 1
                  (eval_twos_complement machine_wordsize sat_limbs f)
                  (eval_twos_complement machine_wordsize sat_limbs g)
                  (eval v mod (s - Associational.eval c))
                  (eval r mod (s - Associational.eval c))
                  (Z.to_nat (machine_wordsize - 2)))
        as [[[[d1' f1'] g1'] v1'] r1'] eqn:E2.

      destruct (hddivstep_spec_full'_iter
                  1
                  (Z.twos_complement machine_wordsize (nth_default 0 f 0))
                  (Z.twos_complement machine_wordsize (nth_default 0 g 0))
                  1 0 0 1 (Z.to_nat (machine_wordsize - 2)))
        as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3.

      rewrite !unfold_Let_In.

      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.

      + unfold eval_twos_complement.
        rewrite firstn_eval with (n:=word_sat_mul_limbs).
        rewrite Z.twos_complement_mod.
        rewrite <- Z.twos_complement_twos_complement_smaller_width with (m':=machine_wordsize * Z.of_nat word_sat_mul_limbs).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs
                                                                                              (BYInv.sat_add machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs u1 f)
                                                                                                             (word_sat_mul machine_wordsize sat_limbs v1 g)) (machine_wordsize - 2))).
        rewrite eval_sat_arithmetic_shiftr.
        unfold eval_twos_complement.
        rewrite eval_sat_add.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs v1 g)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs u1 f)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.
        inversion H7.
        inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) by lia. reflexivity. lia. lia.

        all: try assumption; try lia; try nia.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs v1 g)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs u1 f)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.


        pose proof Z.twos_complement_bounds.


        nia. lia. lia. lia. lia. auto. lia. lia. lia. lia. auto.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply length_sat_add.  lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_length. lia.

        apply length_sat_add.  lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_bounds. lia. lia. lia.
        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
      + unfold eval_twos_complement.
        rewrite firstn_eval with (n:=word_sat_mul_limbs).
        rewrite Z.twos_complement_mod.
        rewrite <- Z.twos_complement_twos_complement_smaller_width with (m':=machine_wordsize * Z.of_nat word_sat_mul_limbs).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs
                                   (sat_arithmetic_shiftr machine_wordsize word_sat_mul_limbs
                                                          (BYInv.sat_add machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs q1 f)
                                                                         (word_sat_mul machine_wordsize sat_limbs r1 g)) (machine_wordsize - 2))).
        rewrite eval_sat_arithmetic_shiftr.
        unfold eval_twos_complement.
        rewrite eval_sat_add.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_add_full.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs q1 f)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs r1 g)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.
        inversion H7.
        inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) by lia. reflexivity. lia. lia.

        all: try assumption; try lia; try nia.

        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs q1 f)).
        fold (eval_twos_complement machine_wordsize word_sat_mul_limbs (word_sat_mul machine_wordsize sat_limbs r1 g)).
        rewrite word_sat_mul_limbs_eq.
        rewrite !word_sat_mul_correct.


        pose proof Z.twos_complement_bounds.


        nia. lia. lia. lia. lia. auto. lia. lia. lia. lia. auto.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply length_sat_add.  lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_length. lia.

        apply length_sat_add.  lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.

        apply sat_arithmetic_shiftr_bounds. lia. lia. lia.
        apply sat_add_bounds. lia.

        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
        rewrite word_sat_mul_limbs_eq.
        apply word_sat_mul_length. lia. lia. lia. lia.
      +

        rewrite eval_carrymod.
        rewrite eval_addmod.
        push_Zmod. 
        rewrite !eval_carry_mulmod.
        push_Zmod.
        rewrite !eval_word_to_solina.
        
        inversion H7. inversion H5.

        push_Zmod; pull_Zmod. reflexivity.
        all: try lia; auto.
        apply word_to_solina_length.
        apply word_to_solina_length.

        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold addmod, carry_mulmod, mulmod; auto with distr_length.
      +
        rewrite eval_carrymod.
        rewrite eval_addmod.
        push_Zmod. 
        rewrite !eval_carry_mulmod.
        push_Zmod.
        rewrite !eval_word_to_solina.
        
        inversion H7. inversion H5.

        push_Zmod; pull_Zmod. reflexivity.
        all: try lia; auto.
        apply word_to_solina_length.
        apply word_to_solina_length.

        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold addmod, carry_mulmod, mulmod; auto with distr_length.
     + intros. reflexivity.
     + reflexivity.
     + lia.
     + lia.


Unshelve.
      rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=sat_limbs).
      unfold eval_twos_complement in fodd.
      rewrite Z.twos_complement_odd in fodd.
      rewrite odd_mod2m. assumption.

      lia. nia. lia. assumption.  assumption.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      lia. lia. lia. rewrite Z.twos_complement_one. lia. lia.
      rewrite Z.twos_complement_one. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_one. lia. lia.

      lia. lia. lia. lia.
      apply Hf2.
      destruct f. simpl in *. lia. simpl. left. cbn. reflexivity.
      apply Hg2.
      destruct g. simpl in *. lia. simpl. left. cbn. reflexivity.

      lia.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.
      lia. lia. rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize).
      rewrite odd_mod2m. unfold eval_twos_complement in fodd.
      rewrite Z.twos_complement_odd in fodd. assumption. nia. lia. lia. assumption. assumption.
      lia. lia. lia. lia.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.
      rewrite Z.twos_complement_one. lia. lia.

      rewrite Z.twos_complement_one. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_zero. lia. lia.
      rewrite Z.twos_complement_one. lia. lia.

      assumption. lia.
      apply Z.mod_pos_bound. lia.
      apply Z.mod_pos_bound. lia.

      unfold eval_twos_complement.
      rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize).

      rewrite Z.twos_complement_mod.

      rewrite !Z.twos_complement_mod_smaller_pow. reflexivity. lia. nia. lia. lia. assumption. assumption.

      unfold eval_twos_complement.
      rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize).

      rewrite Z.twos_complement_mod.

      rewrite !Z.twos_complement_mod_smaller_pow. reflexivity. lia. nia. lia. lia. assumption. assumption. Qed.
  End __.  
End UnsaturatedSolinas.
