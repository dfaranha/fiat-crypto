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



Module WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.

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
    dlet a_enc := Partition.partition (uweight machine_wordsize) n a in
    dlet a_opp_enc := Partition.partition (uweight machine_wordsize) n a_opp in
    dlet a_opp_enc_opp := oppmod machine_wordsize n m (a_opp_enc) in
    dlet res := select cond a_enc a_opp_enc_opp in res.

  Definition twosc_word_mod_m machine_wordsize n m a :=
    dlet cond := Z.twos_complement_neg machine_wordsize a in
          dlet a' := Z.zselect cond a (Z.twos_complement_opp machine_wordsize a) in
                       let a'' := extend_to_length 1 n [a'] in
                       let a''_opp := oppmod machine_wordsize n m a'' in
                       select cond a'' a''_opp.

End WordByWordMontgomery.

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
              (balance : list Z).

  Definition word_to_solina a :=
    dlet cond := Z.twos_complement_neg machine_wordsize a in
    dlet a_opp := Z.twos_complement_opp machine_wordsize a in
    dlet a_enc := encodemod limbwidth_num limbwidth_den s c n a in
    dlet a_opp_enc := encodemod limbwidth_num limbwidth_den s c n (a_opp) in
    dlet a_opp_enc_opp := oppmod limbwidth_num limbwidth_den n balance (a_opp_enc) in
    dlet a_opp_enc_opp_carry := carrymod limbwidth_num limbwidth_den s c n idxs a_opp_enc_opp in
    dlet res := select cond a_enc a_opp_enc_opp_carry in res.

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
    (f6, g6, v, r).
  End __.
End UnsaturatedSolinas.
  

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
  unfold divstep_spec_full'; cbn -[Z.mul].
  rewrite !Zselect.Z.zselect_correct.
  rewrite !twos_complement_pos_spec, Zmod_odd, Z.twos_complement_odd by lia.
  rewrite Z.twos_complement_mod2, (Zmod_odd g) by lia.
  destruct (0 <? Z.twos_complement machine_wordsize d);
    destruct (Z.odd g) eqn:godd;
    rewrite (Zmod_odd); cbn -[Z.mul];
      rewrite ?godd; cbn -[Z.mul].
  rewrite <- (Z.twos_complement_odd machine_wordsize), !twos_complement_opp_spec by lia;
    rewrite Z.odd_opp, Z.twos_complement_odd, fodd by lia; cbn -[Z.mul].
  all: (repeat apply f_equal2;
        repeat rewrite 1?Z.twos_complement_mod, 1?Z.twos_complement_add_full, 1?Z.twos_complement_one,
        1?Z.arithmetic_shiftr1_spec, 1?twos_complement_opp_spec, 1?Z.twos_complement_zero;
        rewrite ?Z.twos_complement_one, ?twos_complement_opp_spec;
        try apply Z.mod_pos_bound; try apply f_equal2; lia). Qed.









