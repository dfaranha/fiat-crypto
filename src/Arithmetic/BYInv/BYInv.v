Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.ArithmeticShiftr.
Require Import Crypto.Arithmetic.BYInv.Shiftr.
Require Import Crypto.Arithmetic.BYInv.Select.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.TCOpp.
Require Import Crypto.Arithmetic.BYInv.Mod2.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.Divstep.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.TwosComplementPos.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import ListNotations.

(** An implementation of the divsteps2 algorithm from "Fast constant-time gcd computation and modular inversion."
   by D. J. Bernstein et al. See the file inversion-c/readme.txt for generation of C-code.
   For a C-implementation using this generated code to implement modular inversion, see inversion-c/test-inversion.c. **)

Local Coercion Z.of_nat : nat >-> Z.
Local Open Scope Z_scope.

Lemma select_in_bounded machine_wordsize n cond f g
      (f_length : length f = n)
      (g_length : length g = n)
      (f_in_bounded : in_bounded machine_wordsize f)
      (g_in_bounded : in_bounded machine_wordsize g) :
  in_bounded machine_wordsize (Positional.select cond f g).
Proof.
  rewrite (Positional.select_eq Z.to_nat) with (n:=length f) by congruence.
  destruct (dec (cond = 0)); auto.
Qed.

Lemma select_push' n cond a b f : length a = n -> length b = n ->
                                  f (Positional.select cond a b) = Z.zselect cond (f a) (f b).
Proof. intros. apply Positional.select_push; congruence. Qed.

Lemma tc_eval_select_bounds machine_wordsize tc_limbs n cond f g K
      (f_length : length f = n)
      (g_length : length g = n)
      (f_bounds : - K < tc_eval machine_wordsize tc_limbs f < K)
      (g_bounds : - K < tc_eval machine_wordsize tc_limbs g < K) :
  - K < tc_eval machine_wordsize tc_limbs (Positional.select cond f g) < K.
Proof.
  rewrite (Positional.select_eq Z.of_nat) with (n:=n) by assumption. now destruct (dec (cond = 0)).
Qed.

#[global] Hint Resolve length_tc_add length_tc_opp Positional.length_select length_zero arithmetic_shiftr1_length : len.
#[global] Hint Rewrite tc_eval_arithmetic_shiftr1 tc_eval_tc_add tc_eval_select tc_eval_tc_opp tc_opp_mod2 tc_eval_zero : tc.
#[global] Hint Rewrite Z.twos_complement_mod Z.twos_complement_add_full Z.twos_complement_opp'_spec Z.twos_complement_one Z.twos_complement_pos'_spec : Ztc.

Module Export WordByWordMontgomery.

  Import WordByWordMontgomery.WordByWordMontgomery.

  Lemma length_addmod machine_wordsize mont_limbs m :
        0 < machine_wordsize ->
        forall f, length f = mont_limbs -> forall g, length g = mont_limbs -> length (addmod machine_wordsize mont_limbs m f g) = mont_limbs.
  Proof.
    intros.
    unfold addmod, add, Rows.conditional_sub.
    rewrite Positional.length_drop_high_to_length.
    rewrite (surjective_pairing (Rows.sub (uweight machine_wordsize) (S mont_limbs) (let '(v, c) := Rows.add (uweight machine_wordsize) mont_limbs f g in v ++ [c])
                                          (Positional.extend_to_length mont_limbs (S mont_limbs) (Partition.partition (uweight machine_wordsize) mont_limbs m)))).
    rewrite Positional.length_select with (n:=S mont_limbs). lia.
    unfold Rows.sub.
    apply Rows.length_flatten; [apply uwprops; assumption|].
    intros.
    inversion H2. subst.
    simpl.
    rewrite app_length, Rows.length_sum_rows with (n:=length f); auto.
    simpl; lia.
    apply uwprops; assumption.
    inversion H3. subst.
    rewrite map_length, Positional.length_extend_to_length; auto.
    apply length_partition. inversion H4.
    simpl.
    rewrite app_length, Rows.length_sum_rows with (n:=mont_limbs); try assumption.
    simpl; lia.
    apply uwprops; assumption.
  Qed.

  Lemma length_oppmod machine_wordsize mont_limbs m :
        0 < machine_wordsize ->
        forall f, length f = mont_limbs -> length (oppmod machine_wordsize mont_limbs m f) = mont_limbs.
  Proof.
    intros. unfold oppmod, opp, sub. simpl.
    rewrite Rows.length_sum_rows with (n:=mont_limbs). reflexivity. apply uwprops. lia.
    rewrite Rows.length_sum_rows with (n:=mont_limbs). reflexivity. apply uwprops. lia.
    apply Positional.length_zeros. rewrite map_length. assumption.
    rewrite Positional.length_zselect. apply length_partition.
  Qed.

  Lemma addmod_valid machine_wordsize mont_limbs m (r' m' : Z) :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> forall g, valid machine_wordsize mont_limbs m g -> valid machine_wordsize mont_limbs m (addmod machine_wordsize mont_limbs m f g).
  Proof.
    intros.
    epose proof (addmod_correct machine_wordsize mont_limbs m r' m' _ _ _ _ _ _) as [_ h]. apply h; assumption.
    Unshelve. all: try assumption; lia.
  Qed.

  Lemma oppmod_valid machine_wordsize mont_limbs m (r' m' : Z) :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> valid machine_wordsize mont_limbs m (oppmod machine_wordsize mont_limbs m f).
  Proof.
    intros.
    epose proof (oppmod_correct machine_wordsize mont_limbs m r' m' _ _ _ _ _ _) as [_ h]. apply h; assumption.
    Unshelve. all: try assumption; lia.
  Qed.

  Lemma select_valid machine_wordsize mont_limbs m cond f g
        (f_length : length f = mont_limbs)
        (g_length : length g = mont_limbs) :
    valid machine_wordsize mont_limbs m f -> valid machine_wordsize mont_limbs m g -> valid machine_wordsize mont_limbs m (Positional.select cond f g).
  Proof.
    intros. rewrite Positional.select_eq with (n:=mont_limbs) by auto.
    destruct (dec _); auto.
  Qed.

  Lemma zero_valid machine_wordsize mont_limbs m :
    0 < m ->
    valid machine_wordsize mont_limbs m (zero mont_limbs).
  Proof.
    unfold valid, small, WordByWordMontgomery.eval.
    rewrite eval_zero, partition_0; try split; auto; lia.
  Qed.

  Lemma nonzero_zero n :
    nonzeromod (zero n) = 0.
  Proof. unfold nonzero, zero; induction n; auto. Qed.

  #[global] Hint Resolve length_addmod length_oppmod : len.
  #[global] Hint Resolve select_valid zero_valid addmod_valid oppmod_valid : valid.
  #[global] Hint Extern 3 (length _ = _) => auto with len : valid.

  #[global] Hint Resolve arithmetic_shiftr_in_bounded arithmetic_shiftr1_in_bounded tc_add_in_bounded select_in_bounded : in_bounded.
  #[global] Hint Extern 4 (_ < _) => lia : in_bounded.
  #[global] Hint Extern 4 (_ <= _) => lia : in_bounded.
  #[global] Hint Extern 4 (_ <= _ < _) => lia : in_bounded.
  #[global] Hint Extern 3 (length _ = _) => auto with len : in_bounded.

  Section __.

    Context
      (machine_wordsize : Z)
      (tc_limbs : nat)
      (mont_limbs : nat)
      (m : Z)
      (m_bounds : 1 < m < (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs))
      (r' : Z)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m' : Z)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (mw1 : 1 < machine_wordsize)
      (tc_limbs0 : (0 < tc_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat).

    Notation eval := (@WordByWordMontgomery.eval machine_wordsize mont_limbs).
    Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    Notation tc := (Z.twos_complement machine_wordsize).
    Notation divstep_aux := (divstep_aux machine_wordsize tc_limbs mont_limbs m).
    Notation divstep := (divstep machine_wordsize tc_limbs mont_limbs m).
    Notation valid := (valid machine_wordsize mont_limbs m).
    Notation addmod := (addmod machine_wordsize mont_limbs m).
    Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    Notation from_montgomerymod := (from_montgomerymod machine_wordsize mont_limbs m m').
    Notation in_bounded := (in_bounded machine_wordsize).

    #[local]
    Hint Resolve
         (length_addmod machine_wordsize mont_limbs m ltac:(lia))
         (length_oppmod machine_wordsize mont_limbs m ltac:(lia))
      : len.

    #[local]
    Hint Resolve
         (zero_valid machine_wordsize mont_limbs m ltac:(lia))
         (addmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (oppmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      : valid.
    #[local] Hint Resolve (select_in_bounded machine_wordsize tc_limbs) : in_bounded.

    Lemma divstep_iter_d_bounds d f g v r n K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat n))
          (d_bounds : - K < tc d < K) :
      let '(d1,_,_,_,_) := fold_left (fun data i => divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      - K - Z.of_nat n < tc d1 < K + Z.of_nat n.
    Proof.
      induction n; intros.
      - cbn; lia.
      - rewrite seq_snoc, fold_left_app.
        destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
        cbn -[Z.mul Z.add].
        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos'_spec, mod2_odd by lia.
        destruct (0 <? tc d1);
          destruct (Definitions.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
          repeat (rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp'_spec, ?Z.twos_complement_one; try lia).
    Qed.

    Ltac t := repeat match goal with
                     | |- _ => assumption
                     | |- _ < tc_eval (tc_opp _ _ _) < _ => apply tc_eval_tc_opp_bounds
                     | |- _ < tc_eval (Positional.select _ _ _) < _ => simple apply tc_eval_select_bounds with (n:=tc_limbs)
                     | |- _ < tc_eval (zero _) < _ => rewrite tc_eval_zero; lia
                     | |- _ /\ _ => split
                     | |- in_bounded _ => auto with in_bounded
                     | |- length _ = _ =>  auto with len
                     | |- valid _ => auto with valid
                     | |- _ < _ / _ => apply div_lt_lower_bound; lia
                     | |- _ / _ < _ => apply Z.div_lt_upper_bound; lia
                     end.

    Lemma divstep_iter_bounds d f g v r n
          (fodd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) < tc d < 2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(_,f1,g1,v1,r1) :=
        fold_left (fun data i => divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = mont_limbs
      /\ length r1 = mont_limbs
      /\ Z.odd (tc_eval f1) = true
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ valid v1
      /\ valid r1
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      induction n.
      - easy.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r n ((2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)) ltac:(lia) ltac:(lia).
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 n) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize (IHn ltac:(lia)) as [f1_length [g1_length [v1_length [r1_length [f1_odd [f1_bounds [f1_in_bounds [g1_bounds [g1_in_bounds [v1_valid r1_valid]]]]]]]]]].
        unfold divstep_aux. simpl.
        do 4 (split; auto with len).
        rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd; auto with len; try lia.
        destruct (0 <? tc d1);
          destruct (Z.odd (tc_eval g1)) eqn:g'_odd; rewrite ?f1_odd, ?tc_eval_zero; auto; simpl; t.
        all: t.
    Qed.

    Lemma divstep_full d f g v r
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + 1 < tc d < 2 ^ (machine_wordsize - 1) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := (divstep_aux (d, f, g, v, r)) in
      (tc d1, tc_eval f1, tc_eval g1, eval (from_montgomerymod v1) mod m, eval (from_montgomerymod r1) mod m) =
        divstep_vr_mod m (tc d, tc_eval f, tc_eval g, eval (from_montgomerymod v) mod m, eval (from_montgomerymod r) mod m).
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      destruct m_bounds.
      cbn -[tc_add tc_opp Z.mul Z.sub Z.add oppmod].

      rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd, !Zselect.Z.zselect_correct, !eval_addmod with (r':=r'), f_odd; t; try lia.
      destruct (0 <? tc d); destruct (Z.odd (tc_eval g)) eqn:g'_odd;
        cbn -[Z.add Z.mul oppmod]; rewrite !(Positional.select_eq Z.to_nat) with (n:=mont_limbs) by t;
        repeat match goal with
               | |- (_, _) = (_, _) => apply f_equal2; cbn -[Z.add Z.mul oppmod]
               | |- context[tc] => autorewrite with Ztc; try lia
               | |- context[tc_eval (zero _)] => rewrite tc_eval_zero by lia
               | |- _ => pull_Zmod; f_equal; lia
               end; try reflexivity.
      - push_Zmod. rewrite eval_oppmod with (r':=r') by (t; lia). pull_Zmod.
        f_equal; lia.
      - push_Zmod. rewrite eval_from_montgomerymod with (r':=r') (v:=zero _); unfold eval; t; try lia. rewrite eval_zero by lia; fold eval; pull_Zmod.
        f_equal; lia.
      - push_Zmod. rewrite eval_from_montgomerymod with (r':=r') (v:=zero _); unfold eval; t; try lia. rewrite eval_zero by lia; fold eval; pull_Zmod.
        f_equal; lia.
    Qed.

    Lemma divstep_iter_correct d f g v r n
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + Z.of_nat n < tc d < 2 ^ (machine_wordsize - 1) - Z.of_nat n)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval (from_montgomerymod v1) mod m, eval (from_montgomerymod r1) mod m) =
        Nat.iter n (divstep_vr_mod m) (tc d, tc_eval f, tc_eval g, eval (from_montgomerymod v) mod m, eval (from_montgomerymod r) mod m).
    Proof.
      induction n.
      - reflexivity.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r n (2 ^ (machine_wordsize - 1) - Z.of_nat (S n)) ltac:(lia) ltac:(lia).
        pose proof divstep_iter_bounds d f g v r n f_odd f_length g_length v_length r_length ltac:(lia) f_bounds g_bounds v_valid r_valid f_in_bounded g_in_bounded.
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 n) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        destruct H0 as [? [? [? [? [? [? [? [? [? [?]]]]]]]]]].
        rewrite <- IHn by lia.
        apply divstep_full; try assumption; lia.
    Qed.
  End __.
End WordByWordMontgomery.

Module Export UnsaturatedSolinas.

  Import Positional.
  Import Definitions.UnsaturatedSolinas.

  Lemma length_addmod limbwidth_num limbwidth_den n :
    forall f, length f = n -> forall g, length g = n -> length (addmod limbwidth_num limbwidth_den n f g) = n.
  Proof. intros; apply length_add; assumption. Qed.

  Lemma length_oppmod limbwidth_num limbwidth_den n balance :
    length balance = n ->
    forall f, length f = n -> length (oppmod limbwidth_num limbwidth_den n balance f) = n.
  Proof. intros; apply length_opp; assumption. Qed.

  Lemma length_carrymod limbwidth_num limbwidth_den s c n idxs :
    forall f, length f = n ->
         length (carrymod limbwidth_num limbwidth_den s c n idxs f) = n.
  Proof. intros; unfold carrymod; apply length_chained_carries; assumption. Qed.

  #[global] Hint Resolve length_addmod length_carrymod length_oppmod : len.

  Section __.

    Context (limbwidth_num limbwidth_den : Z)
            (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
            (machine_wordsize : Z)
            (s nn: Z)
            (c : list (Z*Z))
            (n : nat)
            (tc_limbs : nat)
            (len_c : nat)
            (idxs : list nat)
            (len_idxs : nat)
            (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
            (Hn_nz : n <> 0%nat)
            (Hc : length c = len_c)
            (Hidxs : length idxs = len_idxs)
            (mw1 : 1 < machine_wordsize)
            (tc_limbs0 : (0 < tc_limbs)%nat)
            (n0 : (0 < n)%nat).

    Local Notation eval := (Positional.eval (weight limbwidth_num limbwidth_den) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    Local Notation divstep_aux := (divstep_aux limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).
    Local Notation divstep := (divstep limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).
    Local Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    Local Notation tc := (Z.twos_complement machine_wordsize).
    Local Notation m := (s - Associational.eval c).
    Local Notation in_bounded := (in_bounded machine_wordsize).

    Local Notation addmod := (addmod limbwidth_num limbwidth_den n).
    Local Notation oppmod := (oppmod limbwidth_num limbwidth_den n balance).
    Local Notation carrymod := (carrymod limbwidth_num limbwidth_den s c n idxs).

    #[local] Hint Resolve (select_in_bounded machine_wordsize tc_limbs) : in_bounded.

    Ltac t := repeat match goal with
                     | |- _ => assumption
                     | |- _ < tc_eval (tc_opp _ _ _) < _ => apply tc_eval_tc_opp_bounds
                     | |- _ < tc_eval (Positional.select _ _ _) < _ => simple apply tc_eval_select_bounds with (n:=tc_limbs)
                     | |- _ < tc_eval (zero _) < _ => rewrite tc_eval_zero; lia
                     | |- _ /\ _ => split
                     | |- in_bounded _ => auto with in_bounded
                     | |- length _ = _ =>  auto with len
                     | |- _ < _ / _ => apply div_lt_lower_bound; lia
                     | |- _ / _ < _ => apply Z.div_lt_upper_bound; lia
                     end.

    Lemma divstep_iter_d_bounds d f g v r k K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat k))
          (d_bounds : - K < tc d < K) :
      let '(d1,_,_,_,_) := fold_left (fun data i => divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      - K - Z.of_nat k < tc d1 < K + Z.of_nat k.
    Proof.
      induction k; intros.
      - cbn; lia.
      - rewrite seq_snoc, fold_left_app.
        destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
        cbn -[Z.mul Z.add].
        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos'_spec, mod2_odd by lia.
        destruct (0 <? tc d1);
          destruct (Definitions.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
          repeat (rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp'_spec, ?Z.twos_complement_one; try lia).
    Qed.

    Lemma divstep_iter_bounds d f g v r k
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat k) < tc d < 2 ^ (machine_wordsize - 1) - 1 - Z.of_nat k)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : forall z, In z g -> 0 <= z < 2 ^ machine_wordsize) :
      let '(_,f1,g1,v1,r1) :=
        fold_left (fun data i => divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = n
      /\ length r1 = n
      /\ Z.odd (tc_eval f1) = true
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      induction k.
      - easy.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r k ((2 ^ (machine_wordsize - 1) - 1 - Z.of_nat k)) ltac:(lia) ltac:(lia).
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 k) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize (IHk ltac:(lia)) as [f1_length [g1_length [v1_length [r1_length [f1_odd [f1_bounds [g1_bounds [f1_in_bounds g1_in_bounds]]]]]]]].
        unfold divstep_aux. simpl.
        do 4 (split; auto 6 with len).
        rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd; auto with len; try lia.
        destruct (0 <? tc d1);
          destruct (Z.odd (tc_eval g1)) eqn:g'_odd; rewrite ?f1_odd, ?tc_eval_zero; auto; simpl; t.
        all: t.
    Qed.

    Lemma divstep_full d f g v r
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + 1 < tc d < 2 ^ (machine_wordsize - 1) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounds : forall z, In z f -> 0 <= z < 2^machine_wordsize)
          (g_in_bounds : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
      let '(d1,f1,g1,v1,r1) := (divstep_aux (d, f, g, v, r)) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        divstep_vr_mod m (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      unfold divstep_aux.
      cbn -[tc_add tc_opp Z.opp Z.mul Z.sub Z.add oppmod addmod select].
      rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd, !Zselect.Z.zselect_correct, !eval_carrymod, !eval_addmod, !eval_select, f_odd, !eval_zero; t; try lia.
      destruct (0 <? tc d); destruct (Z.odd (tc_eval g)) eqn:g'_odd;
        cbn -[Z.add Z.mul oppmod];
        repeat match goal with
               | |- (_, _) = (_, _) => apply f_equal2; cbn -[Z.add Z.mul oppmod]
               | |- context[tc] => autorewrite with Ztc; try lia
               | |- context[tc_eval (zero _)] => rewrite tc_eval_zero by lia
               | |- _ => pull_Zmod; f_equal; lia
               end; try reflexivity.
      - push_Zmod. rewrite eval_carrymod, eval_oppmod by (t; lia).
        pull_Zmod. f_equal. lia.
    Qed.

    Lemma divstep_iter_correct d f g v r k
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + Z.of_nat k < tc d < 2 ^ (machine_wordsize - 1) - Z.of_nat k)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounds : forall z, In z f -> 0 <= z < 2^machine_wordsize)
          (g_in_bounds : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        Nat.iter k (divstep_vr_mod m) (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      induction k.
      - reflexivity.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r k (2 ^ (machine_wordsize - 1) - Z.of_nat (S k)) ltac:(lia) ltac:(lia).
        pose proof divstep_iter_bounds d f g v r k f_odd f_length g_length v_length r_length ltac:(lia) f_bounds g_bounds f_in_bounds g_in_bounds.
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 k) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        destruct H0 as [? [? [? [? [? [? [? [?]]]]]]]].
        rewrite <- IHk by lia.
        apply divstep_full; try assumption; lia.
    Qed.
  End __.
End UnsaturatedSolinas.
