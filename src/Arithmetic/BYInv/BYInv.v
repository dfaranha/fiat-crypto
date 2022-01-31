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

Import ListNotations.

(** An implementation of the divsteps2 algorithm from "Fast constant-time gcd computation and modular inversion."
   by D. J. Bernstein et al. See the file inversion-c/readme.txt for generation of C-code.
   For a C-implementation using this generated code to implement modular inversion, see inversion-c/test-inversion.c. **)

Local Coercion Z.of_nat : nat >-> Z.
Local Open Scope Z_scope.

Module Export WordByWordMontgomery.

  Import WordByWordMontgomery.WordByWordMontgomery.
  Import Positional.

  Lemma divstep_g machine_wordsize tc_limbs mont_limbs m d f g v r
        (mw0 : 0 < machine_wordsize)
        (tc_limbs0 : (0 < tc_limbs)%nat)
        (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
        (Hf : length f = tc_limbs)
        (Hg : length g = tc_limbs)
        (corner_case : Z.twos_complement machine_wordsize d <> - 2 ^ (machine_wordsize - 1))
        (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                      tc_eval machine_wordsize tc_limbs f <
                      2 ^ (machine_wordsize * tc_limbs - 2))
        (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                      tc_eval machine_wordsize tc_limbs g <
                      2 ^ (machine_wordsize * tc_limbs - 2))
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
        (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    tc_eval machine_wordsize tc_limbs g1 =
    snd (divstep_spec
           (Z.twos_complement machine_wordsize d)
           (tc_eval machine_wordsize tc_limbs f)
           (tc_eval machine_wordsize tc_limbs g)).
  Proof.
    set (bw := machine_wordsize * Z.of_nat tc_limbs) in *.

    simpl.
    assert (0 < Z.of_nat tc_limbs) by lia.
    assert (bw0 : 0 < bw) by nia.
    assert (bw1 : 1 < bw) by (destruct (dec (bw = 1)); rewrite ?e in *; simpl in *; lia).
    assert (2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
      by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
    assert (0 < 2 ^ bw) by (apply Z.pow_pos_nonneg; lia).
    assert (2 ^ (bw - 2) <= 2 ^ (bw - 1)) by (apply Z.pow_le_mono; lia).

    Hint Rewrite length_tc_add length_tc_opp length_select : distr_length.

    rewrite tc_eval_arithmetic_shiftr1; distr_length; autorewrite with distr_length; try nia.
    rewrite tc_eval_tc_add; auto; try (autorewrite with distr_length; lia).
    rewrite !tc_eval_select; auto; try (autorewrite with distr_length; lia).
    rewrite tc_eval_tc_opp; auto; try (autorewrite with distr_length; lia).
    rewrite select_push; try (autorewrite with distr_length; lia).

    rewrite tc_opp_mod2; auto.
    unfold divstep_spec.
    rewrite twos_complement_pos'_spec.
    rewrite twos_complement_pos_spec; auto.
    rewrite <- !(tc_eval_mod2 machine_wordsize tc_limbs); auto.
    rewrite !Zmod_odd; auto.

    set (g' := tc_eval machine_wordsize tc_limbs g) in *.
    set (f' := tc_eval machine_wordsize tc_limbs f) in *.
    assert (corner_case_f : f' <> - 2 ^ (bw - 1)) by
        (replace (- _) with (- (2 * 2 ^ (bw - 2))); rewrite ?Pow.Z.pow_mul_base; ring_simplify (bw - 2 + 1); nia).

    destruct (0 <? Z.twos_complement machine_wordsize d);
      destruct (Z.odd g') eqn:g'_odd; rewrite ?fodd, ?eval_zero; auto.
    - simpl; rewrite Z.add_comm; reflexivity.
    - simpl; rewrite tc_eval_zero; auto.
    - rewrite Z.mul_1_l; simpl; reflexivity.
    - simpl; rewrite tc_eval_zero; auto.
    - replace (_ * _) with bw by reflexivity; lia.
    - rewrite twos_complement_pos'_spec.
      fold (tc_eval machine_wordsize tc_limbs
                                 (select (Z.twos_complement_pos machine_wordsize d &' mod2 g) g (tc_opp machine_wordsize tc_limbs f))).
      rewrite tc_eval_select; try apply length_tc_opp; auto.
      destruct (dec (_)); replace (machine_wordsize * _) with bw by reflexivity;
        try rewrite tc_eval_tc_opp; auto; replace (machine_wordsize * _) with bw by reflexivity; lia.
    - rewrite twos_complement_pos'_spec.
      fold (tc_eval machine_wordsize tc_limbs
                                 (select (mod2 (select (Z.twos_complement_pos machine_wordsize d &' mod2 g) g (tc_opp machine_wordsize tc_limbs f)))
                                         (zero tc_limbs) (select (Z.twos_complement_pos machine_wordsize d &' mod2 g) f g))).
      rewrite tc_eval_select; try apply length_zero; try apply length_select; auto.
      destruct (dec (_)); try rewrite tc_eval_zero; try rewrite tc_eval_select;
        replace (machine_wordsize * _) with bw by reflexivity; try lia; destruct (dec (_)); lia.
    - apply tc_add_bounds; repeat (rewrite ?length_tc_opp, ?(length_select tc_limbs), ?length_zero; auto); lia.
  Qed.

  Lemma divstep_d machine_wordsize tc_limbs mont_limbs m d f g v r
        (mw1 : 1 < machine_wordsize)
        (tc_limbs0 : (0 < tc_limbs)%nat)
        (Hg : length g = tc_limbs)
        (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                      Z.twos_complement machine_wordsize d <
                      2 ^ (machine_wordsize - 1) - 1) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    Z.twos_complement machine_wordsize d1 =
    fst (fst (divstep_spec (Z.twos_complement machine_wordsize d)
                           (tc_eval machine_wordsize tc_limbs f)
                           (tc_eval machine_wordsize tc_limbs g))).
  Proof.
    assert (helper0 : 0 < Z.of_nat tc_limbs) by lia.
    assert (mw0 : 0 < machine_wordsize) by lia.
    assert (helper : 1 < 2 ^ machine_wordsize) by (apply Zpow_facts.Zpower_gt_1; lia).
    assert (helper2 : 1 < 2 ^ (machine_wordsize - 1)) by (apply Zpow_facts.Zpower_gt_1; lia).
    assert (helper3 : 2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
      by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).

    simpl; unfold divstep_spec.
    rewrite AddGetCarry.Z.add_get_carry_full_mod.
    rewrite twos_complement_pos'_spec.
    rewrite twos_complement_opp'_spec.
    rewrite twos_complement_pos_spec, <- (tc_eval_mod2 machine_wordsize tc_limbs), Zmod_odd by nia.
    fold (tc_eval machine_wordsize tc_limbs g); set (g' := tc_eval machine_wordsize tc_limbs g) in *.
    destruct ((0 <? Z.twos_complement machine_wordsize d) && (Z.odd g')) eqn:E.
    - apply andb_prop in E. destruct E; rewrite H, H0. simpl Z.b2z; simpl Z.land; cbv [fst].
      unfold Z.zselect. simpl (if _ =? _ then _ else _).
      rewrite twos_complement_opp_correct, Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_mod, twos_complement_zopp, Z.twos_complement_one; try lia.
      rewrite Z.twos_complement_mod, twos_complement_zopp, Z.twos_complement_one; lia.
    - apply andb_false_iff in E.
      destruct E; rewrite H;
        unfold Z.zselect; cbv [fst]; simpl (if _ =? _ then _ else _);
          [destruct (Z.odd g') | rewrite Z.land_0_r; simpl (if _ =? _ then _ else _)];
          rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one; rewrite ?Z.twos_complement_one; lia.
  Qed.

  Lemma divstep_f machine_wordsize tc_limbs mont_limbs m d f g v r
        (mw0 : 0 < machine_wordsize)
        (Hf : length f = tc_limbs)
        (Hg : length g = tc_limbs)
        (corner_case : Z.twos_complement machine_wordsize d <> - 2 ^ (machine_wordsize - 1)) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    tc_eval machine_wordsize tc_limbs f1 =
    snd (fst (divstep_spec (Z.twos_complement machine_wordsize d)
                           (tc_eval machine_wordsize tc_limbs f)
                           (tc_eval machine_wordsize tc_limbs g))).
  Proof.
    destruct tc_limbs. subst.
    unfold tc_eval.
    rewrite !eval0; rewrite Z.mul_0_r.
    replace (Z.twos_complement 0 0) with (-1). unfold divstep_spec.
    destruct (0 <? Z.twos_complement machine_wordsize d); reflexivity. reflexivity.

    unfold divstep_spec. simpl.

    set (n' := S tc_limbs) in *.
    assert (0 < n')%nat by apply Nat.lt_0_succ.
    rewrite twos_complement_pos'_spec.

    rewrite tc_eval_select, twos_complement_pos_spec, <- (tc_eval_mod2 machine_wordsize n'), Zmod_odd; auto.
    fold (tc_eval machine_wordsize n' g).
    destruct (0 <? Z.twos_complement machine_wordsize d); destruct (Z.odd (tc_eval machine_wordsize n' g));
      try reflexivity; lia.
  Qed.

  Theorem divstep_correct machine_wordsize tc_limbs mont_limbs m d f g v r
          (mw1 : 1 < machine_wordsize)
          (tc_limbs0 : (0 < tc_limbs)%nat)
          (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
          (Hf : length f = tc_limbs)
          (Hg : length g = tc_limbs)
          (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                        Z.twos_complement machine_wordsize d <
                        2 ^ (machine_wordsize - 1) - 1)
          (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                        tc_eval machine_wordsize tc_limbs f <
                        2 ^ (machine_wordsize * tc_limbs - 2))
          (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                        tc_eval machine_wordsize tc_limbs g <
                        2 ^ (machine_wordsize * tc_limbs - 2))
          (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
          (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    (Z.twos_complement machine_wordsize d1,
     tc_eval machine_wordsize tc_limbs f1,
     tc_eval machine_wordsize tc_limbs g1) =
    divstep_spec (Z.twos_complement machine_wordsize d)
                 (tc_eval machine_wordsize tc_limbs f)
                 (tc_eval machine_wordsize tc_limbs g).
  Proof.
    assert (0 < machine_wordsize) by lia. simpl.
    apply injective_projections.
    apply injective_projections.
    rewrite <- (divstep_d _ _ mont_limbs m _ _ _ v r); auto.
    rewrite <- (divstep_f _ _ mont_limbs m _ _ _ v r); auto; lia.
    rewrite <- (divstep_g _ _ mont_limbs m _ _ _ v r); auto; lia.
  Qed.

  Lemma divstep_v machine_wordsize tc_limbs mont_limbs m (r' : Z) m' d f g v r
        (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)

        (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
        (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
        (m_big : 1 < m)
        (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
        (Hv2 : valid machine_wordsize mont_limbs m v)
        (Hr2 : valid machine_wordsize mont_limbs m r)
        (mw0 : 0 < machine_wordsize)
        (tc_limbs0 : (0 < tc_limbs)%nat)
        (mont_limbs0 : (0 < mont_limbs)%nat)
        (Hv : length v = mont_limbs)
        (Hr : length r = mont_limbs)
        (Hg : length g = tc_limbs)
        (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                      Z.twos_complement machine_wordsize d <
                      2 ^ (machine_wordsize - 1) - 1) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    @WordByWordMontgomery.eval machine_wordsize mont_limbs
                          (from_montgomerymod machine_wordsize mont_limbs m m' v1) mod m =
    fst (divstep_spec2 m (Z.twos_complement machine_wordsize d)
                       (tc_eval machine_wordsize tc_limbs g)
                       (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                              (from_montgomerymod machine_wordsize mont_limbs m m' v))
                       (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                              (from_montgomerymod machine_wordsize mont_limbs m m' r))).
  Proof.
    assert (tc_limbs <> 0%nat) by lia.
    assert (mont_limbs <> 0%nat) by lia.
    simpl.
    rewrite twos_complement_pos'_spec.

    rewrite twos_complement_pos_spec, <- (tc_eval_mod2 machine_wordsize tc_limbs) by lia.
    rewrite Zmod_odd, (select_eq (uweight machine_wordsize) _ mont_limbs); auto.
    unfold divstep_spec2.
    destruct (0 <? Z.twos_complement machine_wordsize d);
      destruct (Z.odd (tc_eval machine_wordsize tc_limbs g));
      rewrite ?(eval_addmod _ _ _ r'), ?Z.add_diag; auto.
  Qed.

  Lemma nonzero_zero n :
    nonzeromod (zero n) = 0.
  Proof. unfold nonzero, zero; induction n; auto. Qed.

  Lemma zero_valid machine_wordsize n m
        (mw0 : 0 < machine_wordsize)
        (m0 : 0 < m) :
    valid machine_wordsize n m (zero n).
  Proof.
    unfold valid, small, WordByWordMontgomery.eval.
    rewrite eval_zero, partition_0; try split; auto; lia.
  Qed.

  Lemma divstep_r machine_wordsize tc_limbs mont_limbs m (r' : Z) m' d f g v r
        (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
        (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
        (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
        (m_big : 1 < m)
        (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
        (Hv2 : valid machine_wordsize mont_limbs m v)
        (Hr2 : valid machine_wordsize mont_limbs m r)
        (mw0 : 0 < machine_wordsize)
        (tc_limbs0 : (0 < tc_limbs)%nat)
        (mont_limbs0 : (0 < mont_limbs)%nat)
        (Hv : length v = mont_limbs)
        (Hr : length r = mont_limbs)
        (Hf : length f = tc_limbs)
        (Hg : length g = tc_limbs)
        (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                      Z.twos_complement machine_wordsize d <
                      2 ^ (machine_wordsize - 1) - 1)
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    @WordByWordMontgomery.eval machine_wordsize mont_limbs
                          (from_montgomerymod machine_wordsize mont_limbs m m' r1) mod m =
    snd (divstep_spec2 m (Z.twos_complement machine_wordsize d)
                       (tc_eval machine_wordsize tc_limbs g)
                       (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                              (from_montgomerymod machine_wordsize mont_limbs m m' v))
                       (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                              (from_montgomerymod machine_wordsize mont_limbs m m' r))).
  Proof with (auto with zarith).
    assert (tc_limbs0' : (tc_limbs <> 0%nat)) by lia.
    assert (mont_limbs0' : mont_limbs <> 0%nat) by lia.
    unfold divstep_spec2.
    pose proof (oppmod_correct machine_wordsize mont_limbs m r' m' r'_correct m'_correct mw0 m_big (ltac:(lia)) m_small) as H.
    destruct H as [H1 H2].
    assert (zero_valid : valid machine_wordsize mont_limbs m (zero mont_limbs)) by (apply zero_valid; lia).
    pose proof (nonzero_zero mont_limbs) as H3.
    rewrite (nonzeromod_correct machine_wordsize mont_limbs m r' m') in H3
      by (try apply zero_valid; lia).
    cbn -[Z.mul oppmod tc_opp select].
    rewrite select_push; rewrite ?length_tc_opp; auto.
    rewrite tc_opp_mod2; auto.
    rewrite twos_complement_pos'_spec.
    rewrite twos_complement_pos_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs) by lia.
    rewrite !Zmod_odd, !(select_eq (uweight machine_wordsize) _ mont_limbs), fodd;
      try apply length_select; try apply length_zero; auto...
    destruct (0 <? Z.twos_complement machine_wordsize d);
      destruct (Z.odd (tc_eval machine_wordsize tc_limbs g)); cbn -[Z.mul oppmod];
        rewrite (eval_addmod _ _ _ r'); auto with zarith; rewrite <- Zplus_mod_idemp_l, (eval_oppmod _ _ _ r'), Zplus_mod_idemp_l...
    unfold oppmod, WordByWordMontgomery.opp,
    WordByWordMontgomery.sub, Rows.sub_then_maybe_add, Rows.add.
    destruct (Rows.sub (uweight machine_wordsize) mont_limbs (zeros mont_limbs)) eqn:E.
    destruct (Rows.flatten (uweight machine_wordsize) mont_limbs
                           [l; zselect (2 ^ machine_wordsize - 1) (- z) (Partition.partition (uweight machine_wordsize) mont_limbs m)]) eqn:E2.
    simpl.
    inversion E; subst.
    inversion E2.
    apply Rows.length_sum_rows.
    apply (uwprops machine_wordsize mw0).
    apply Rows.length_sum_rows.
    apply (uwprops machine_wordsize mw0).
    apply length_zeros.
    apply map_length.
    rewrite length_zselect.
    apply length_partition.
  Qed.

  Lemma divstep_spec_divstep_spec_full_d m d f g v r :
    fst (fst (divstep_spec d f g)) = fst (fst (fst (fst (divstep_spec_full m d f g v r)))).
  Proof. unfold divstep_spec, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

  Lemma divstep_spec_divstep_spec_full_f m d f g v r :
    snd (fst (divstep_spec d f g)) = snd (fst (fst (fst (divstep_spec_full m d f g v r)))).
  Proof. unfold divstep_spec, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

  Lemma divstep_spec_divstep_spec_full_g m d f g v r :
    snd (divstep_spec d f g) = snd (fst (fst (divstep_spec_full m d f g v r))).
  Proof. unfold divstep_spec, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

  Lemma divstep_spec2_divstep_spec_full_v m d f g v r :
    fst (divstep_spec2 m d g v r) = snd (fst (divstep_spec_full m d f g v r)).
  Proof. unfold divstep_spec2, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

  Lemma divstep_spec2_divstep_spec_full_r m d f g v r :
    snd (divstep_spec2 m d g v r) = snd (divstep_spec_full m d f g v r).
  Proof. unfold divstep_spec2, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

  Theorem divstep_correct_full machine_wordsize tc_limbs mont_limbs m r' m' d f g v r
          (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
          (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
          (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
          (m_big : 1 < m)
          (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
          (mw1 : 1 < machine_wordsize)
          (tc_limbs0 : (0 < tc_limbs)%nat)
          (mont_limbs0 : (0 < mont_limbs)%nat)
          (Hv : length v = mont_limbs)
          (Hr : length r = mont_limbs)
          (Hf : length f = tc_limbs)
          (Hg : length g = tc_limbs)
          (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                        Z.twos_complement machine_wordsize d <
                        2 ^ (machine_wordsize - 1) - 1)
          (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                        tc_eval machine_wordsize tc_limbs f <
                        2 ^ (machine_wordsize * tc_limbs - 2))
          (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                        tc_eval machine_wordsize tc_limbs g <
                        2 ^ (machine_wordsize * tc_limbs - 2))
          (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
          (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize)
          (Hv2 : valid machine_wordsize mont_limbs m v)
          (Hr2 : valid machine_wordsize mont_limbs m r) :
    let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize tc_limbs mont_limbs m d f g v r) in
    (Z.twos_complement machine_wordsize d1,
     tc_eval machine_wordsize tc_limbs f1,
     tc_eval machine_wordsize tc_limbs g1,
     @WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' v1) mod m,
     @WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' r1) mod m) =
    divstep_spec_full m (Z.twos_complement machine_wordsize d)
                      (tc_eval machine_wordsize tc_limbs f)
                      (tc_eval machine_wordsize tc_limbs g)
                      (@WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' v))
                      (@WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' r)).
  Proof.
    assert (0 < machine_wordsize) by lia.
    repeat apply injective_projections.
    rewrite <- divstep_spec_divstep_spec_full_d, <- (divstep_d _ _ mont_limbs m _ _ _ v r); auto.
    rewrite <- divstep_spec_divstep_spec_full_f, <- (divstep_f _ _ mont_limbs m _ _ _ v r); auto; lia.
    rewrite <- divstep_spec_divstep_spec_full_g, <- (divstep_g _ _ mont_limbs m _ _ _ v r); auto; lia.
    rewrite <- divstep_spec2_divstep_spec_full_v;
      rewrite <- (divstep_v _ _ _ _ r' _ _ f _ _ _); auto.
    rewrite <- divstep_spec2_divstep_spec_full_r;
      rewrite <- (divstep_r _ _ _ _ r' _ _ f _ _ _); auto.
  Qed.

End WordByWordMontgomery.

Module Export UnsaturatedSolinas.

  Import Positional.
  Import Definitions.UnsaturatedSolinas.

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
            (Hidxs : length idxs = len_idxs).

    Local Notation eval := (Positional.eval (weight limbwidth_num limbwidth_den) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    Local Notation divstep := (divstep limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).

    (* TODO: generalize this so its not the same proof as for WbW *)
    Lemma divstep_g d f g v r
          (mw0 : 0 < machine_wordsize)
          (tc_limbs0 : (0 < tc_limbs)%nat)
          (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
          (Hf : length f = tc_limbs)
          (Hg : length g = tc_limbs)
          (corner_case : Z.twos_complement machine_wordsize d <> - 2 ^ (machine_wordsize - 1))
          (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                        tc_eval machine_wordsize tc_limbs f <
                        2 ^ (machine_wordsize * tc_limbs - 2))
          (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                        tc_eval machine_wordsize tc_limbs g <
                        2 ^ (machine_wordsize * tc_limbs - 2))
          (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
          (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      tc_eval machine_wordsize tc_limbs g1 =
      snd (divstep_spec
             (Z.twos_complement machine_wordsize d)
             (tc_eval machine_wordsize tc_limbs f)
             (tc_eval machine_wordsize tc_limbs g)).
    Proof.
      set (bw := machine_wordsize * Z.of_nat tc_limbs) in *.

      simpl.
      assert (0 < Z.of_nat tc_limbs) by lia.
      assert (bw0 : 0 < bw) by nia.
      assert (bw1 : 1 < bw) by (destruct (dec (bw = 1)); rewrite ?e in *; simpl in *; lia).
      assert (2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
        by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
      assert (0 < 2 ^ bw) by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ (bw - 2) <= 2 ^ (bw - 1)) by (apply Z.pow_le_mono; lia).

      Hint Rewrite length_tc_add length_tc_opp length_select : distr_length.

      rewrite tc_eval_arithmetic_shiftr1; distr_length; autorewrite with distr_length; try nia.
      rewrite tc_eval_tc_add; auto; try (autorewrite with distr_length; lia).
      rewrite !tc_eval_select; auto; try (autorewrite with distr_length; lia).
      rewrite tc_eval_tc_opp; auto; try (autorewrite with distr_length; lia).
      rewrite select_push; try (autorewrite with distr_length; lia).

      rewrite tc_opp_mod2; auto.
      unfold divstep_spec.
      rewrite twos_complement_pos'_spec.
      rewrite twos_complement_pos_spec; auto.
      rewrite <- !(tc_eval_mod2 machine_wordsize tc_limbs); auto.
      rewrite !Zmod_odd; auto.

      set (g' := tc_eval machine_wordsize tc_limbs g) in *.
      set (f' := tc_eval machine_wordsize tc_limbs f) in *.
      assert (corner_case_f : f' <> - 2 ^ (bw - 1)) by
          (replace (- _) with (- (2 * 2 ^ (bw - 2))); rewrite ?Pow.Z.pow_mul_base; ring_simplify (bw - 2 + 1); nia).

      destruct (0 <? Z.twos_complement machine_wordsize d);
        destruct (Z.odd g') eqn:g'_odd; rewrite ?fodd, ?eval_zero; auto.
      - simpl; rewrite Z.add_comm; reflexivity.
      - simpl; rewrite tc_eval_zero; auto.
      - rewrite Z.mul_1_l; simpl; reflexivity.
      - simpl; rewrite tc_eval_zero; auto.
      - replace (_ * _) with bw by reflexivity; lia.
      - rewrite twos_complement_pos'_spec.
        fold (tc_eval machine_wordsize tc_limbs
                      (select (Z.twos_complement_pos machine_wordsize d &' mod2 g) g (tc_opp machine_wordsize tc_limbs f))).
        rewrite tc_eval_select; try apply length_tc_opp; auto.
        destruct (dec (_)); replace (machine_wordsize * _) with bw by reflexivity;
          try rewrite tc_eval_tc_opp; auto; replace (machine_wordsize * _) with bw by reflexivity; lia.
      - rewrite twos_complement_pos'_spec.
        fold (tc_eval machine_wordsize tc_limbs
                      (select (mod2 (select (Z.twos_complement_pos machine_wordsize d &' mod2 g) g (tc_opp machine_wordsize tc_limbs f)))
                              (zero tc_limbs) (select (Z.twos_complement_pos machine_wordsize d &' mod2 g) f g))).
        rewrite tc_eval_select; try apply length_zero; try apply length_select; auto.
        destruct (dec (_)); try rewrite tc_eval_zero; try rewrite tc_eval_select;
          replace (machine_wordsize * _) with bw by reflexivity; try lia; destruct (dec (_)); lia.
      - apply tc_add_bounds; repeat (rewrite ?length_tc_opp, ?(length_select tc_limbs), ?length_zero; auto); lia.
    Qed.

    Lemma divstep_d d f g v r
          (mw1 : 1 < machine_wordsize)
          (tc_limbs0 : (0 < tc_limbs)%nat)
          (Hg : length g = tc_limbs)
          (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                        Z.twos_complement machine_wordsize d <
                        2 ^ (machine_wordsize - 1) - 1) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      Z.twos_complement machine_wordsize d1 =
      fst (fst (divstep_spec (Z.twos_complement machine_wordsize d)
                             (tc_eval machine_wordsize tc_limbs f)
                             (tc_eval machine_wordsize tc_limbs g))).
    Proof.
      assert (helper0 : 0 < Z.of_nat tc_limbs) by lia.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (helper : 1 < 2 ^ machine_wordsize) by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (helper2 : 1 < 2 ^ (machine_wordsize - 1)) by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (helper3 : 2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
        by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).

      simpl; unfold divstep_spec.
      rewrite AddGetCarry.Z.add_get_carry_full_mod.
      rewrite twos_complement_pos'_spec.
      rewrite twos_complement_opp'_spec.
      rewrite twos_complement_pos_spec, <- (tc_eval_mod2 machine_wordsize tc_limbs), Zmod_odd by nia.
      fold (tc_eval machine_wordsize tc_limbs g); set (g' := tc_eval machine_wordsize tc_limbs g) in *.
      destruct ((0 <? Z.twos_complement machine_wordsize d) && (Z.odd g')) eqn:E.
      - apply andb_prop in E. destruct E; rewrite H, H0. simpl Z.b2z; simpl Z.land; cbv [fst].
        unfold Z.zselect. simpl (if _ =? _ then _ else _).
        rewrite twos_complement_opp_correct, Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_mod, twos_complement_zopp, Z.twos_complement_one; try lia.
        rewrite Z.twos_complement_mod, twos_complement_zopp, Z.twos_complement_one; lia.
      - apply andb_false_iff in E.
        destruct E; rewrite H;
          unfold Z.zselect; cbv [fst]; simpl (if _ =? _ then _ else _);
            [destruct (Z.odd g') | rewrite Z.land_0_r; simpl (if _ =? _ then _ else _)];
            rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one; rewrite ?Z.twos_complement_one; lia.
    Qed.

    Lemma divstep_f d f g v r
          (mw0 : 0 < machine_wordsize)
          (Hf : length f = tc_limbs)
          (Hg : length g = tc_limbs)
          (corner_case : Z.twos_complement machine_wordsize d <> - 2 ^ (machine_wordsize - 1)) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      tc_eval machine_wordsize tc_limbs f1 =
      snd (fst (divstep_spec (Z.twos_complement machine_wordsize d)
                             (tc_eval machine_wordsize tc_limbs f)
                             (tc_eval machine_wordsize tc_limbs g))).
    Proof.
      destruct tc_limbs. simpl. subst.
      unfold tc_eval.
      rewrite !eval0; rewrite Z.mul_0_r.
      replace (Z.twos_complement 0 0) with (-1). unfold divstep_spec.
      destruct (0 <? Z.twos_complement machine_wordsize d); reflexivity. reflexivity.

      unfold divstep_spec.
      cbn -[Z.div Z.mul Z.sub Z.add].

      set (n' := S n0) in *.
      assert (0 < n')%nat by apply Nat.lt_0_succ.
      rewrite twos_complement_pos'_spec.

      rewrite tc_eval_select, twos_complement_pos_spec, <- (tc_eval_mod2 machine_wordsize n'), Zmod_odd; auto.

      fold (tc_eval machine_wordsize n' g).
      destruct (0 <? Z.twos_complement machine_wordsize d); destruct (Z.odd (tc_eval machine_wordsize n' g));
        try reflexivity; lia.
    Qed.

    Theorem divstep_correct d f g v r
            (mw1 : 1 < machine_wordsize)
            (tc_limbs0 : (0 < tc_limbs)%nat)
            (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
            (Hf : length f = tc_limbs)
            (Hg : length g = tc_limbs)
            (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                          Z.twos_complement machine_wordsize d <
                          2 ^ (machine_wordsize - 1) - 1)
            (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                          tc_eval machine_wordsize tc_limbs f <
                          2 ^ (machine_wordsize * tc_limbs - 2))
            (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                          tc_eval machine_wordsize tc_limbs g <
                          2 ^ (machine_wordsize * tc_limbs - 2))
            (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
            (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      (Z.twos_complement machine_wordsize d1,
       tc_eval machine_wordsize tc_limbs f1,
       tc_eval machine_wordsize tc_limbs g1) =
      divstep_spec (Z.twos_complement machine_wordsize d)
                   (tc_eval machine_wordsize tc_limbs f)
                   (tc_eval machine_wordsize tc_limbs g).
    Proof.
      assert (0 < machine_wordsize) by lia. simpl.
      apply injective_projections.
      apply injective_projections.
      rewrite <- (divstep_d _ _ _ v r); auto.
      rewrite <- (divstep_f _ _ _ v r); auto; lia.
      rewrite <- (divstep_g _ _ _ v r); auto; lia.
    Qed.

    Lemma divstep_v d f g v r
          (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
          (mw0 : 0 < machine_wordsize)
          (tc_limbs0 : (0 < tc_limbs)%nat)
          (Hv : length v = n)
          (Hr : length r = n)
          (Hg : length g = tc_limbs)
          (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                        Z.twos_complement machine_wordsize d <
                        2 ^ (machine_wordsize - 1) - 1) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      (eval v1) mod (s - Associational.eval c) =
      fst (divstep_spec2 (s - Associational.eval c)
                         (Z.twos_complement machine_wordsize d)
                         (tc_eval machine_wordsize tc_limbs g)
                         (eval v)
                         (eval r)).
    Proof.
      assert (tc_limbs <> 0%nat) by lia.
      assert (n <> 0%nat) by lia.
      simpl.
      rewrite twos_complement_pos'_spec.

      rewrite twos_complement_pos_spec, <- (tc_eval_mod2 machine_wordsize tc_limbs) by lia.
      rewrite Zmod_odd, (select_eq (uweight machine_wordsize) _ n); auto.
      unfold divstep_spec2.
      destruct (0 <? Z.twos_complement machine_wordsize d);
        destruct (Z.odd (tc_eval machine_wordsize tc_limbs g)); cbn -[Z.mul Z.add];
          rewrite ?eval_carrymod, ?eval_addmod; try (try apply f_equal2; lia); apply length_add; auto.
    Qed.

    Lemma divstep_r d f g v r
          (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
          (mw0 : 0 < machine_wordsize)
          (tc_limbs0 : (0 < tc_limbs)%nat)
          (Hv : length v = n)
          (Hr : length r = n)
          (Hf : length f = tc_limbs)
          (Hg : length g = tc_limbs)
          (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                        Z.twos_complement machine_wordsize d <
                        2 ^ (machine_wordsize - 1) - 1)
          (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      (eval r1) mod (s - Associational.eval c) =
      snd (divstep_spec2 (s - Associational.eval c) (Z.twos_complement machine_wordsize d)
                         (tc_eval machine_wordsize tc_limbs g)
                         (eval v)
                         (eval r)).
    Proof.
      assert (tc_limbs0' : (tc_limbs <> 0%nat)) by lia.
      assert (limbs0' : n <> 0%nat) by lia.
      unfold divstep_spec2.
      cbn -[Z.mul oppmod tc_opp select].
      rewrite select_push; rewrite ?length_tc_opp; auto.
      rewrite tc_opp_mod2; auto.
      rewrite twos_complement_pos'_spec.
      rewrite twos_complement_pos_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs) by lia.
      rewrite !Zmod_odd, !(select_eq (uweight machine_wordsize) _ n), fodd;
        try apply length_select; auto.
      destruct (0 <? Z.twos_complement machine_wordsize d);
        destruct (Z.odd (tc_eval machine_wordsize tc_limbs g)); cbn -[Z.mul oppmod].
      - rewrite eval_carrymod, eval_addmod, <- Zplus_mod_idemp_l, eval_carrymod, eval_oppmod, Zplus_mod_idemp_l; auto with zarith.
        all: unfold addmod, oppmod, carrymod; auto with distr_length.
      - rewrite eval_carrymod, eval_addmod, <- Zplus_mod_idemp_r; auto. unfold Definitions.UnsaturatedSolinas.zeromod.
        rewrite eval_encodemod, Z.mod_0_l, Z.mul_0_l; auto.
        all: unfold addmod, oppmod, carrymod, Definitions.UnsaturatedSolinas.zeromod, encodemod; auto with distr_length.
      - rewrite eval_carrymod, eval_addmod, Z.mul_1_l; auto.
        unfold addmod; auto with distr_length.
      - rewrite eval_carrymod, eval_addmod, <- Zplus_mod_idemp_r; auto. unfold Definitions.UnsaturatedSolinas.zeromod.
        rewrite eval_encodemod, Z.mod_0_l, Z.mul_0_l; auto.
        all: unfold addmod, Definitions.UnsaturatedSolinas.zeromod, encodemod; auto with distr_length.
      - unfold Definitions.UnsaturatedSolinas.zeromod, encodemod; auto with distr_length.
      - unfold carrymod, oppmod; auto with distr_length.
    Qed.

    Lemma divstep_spec_divstep_spec_full_d m d f g v r :
      fst (fst (divstep_spec d f g)) = fst (fst (fst (fst (divstep_spec_full m d f g v r)))).
    Proof. unfold divstep_spec, divstep_spec_full. destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

    Lemma divstep_spec_divstep_spec_full_f m d f g v r :
      snd (fst (divstep_spec d f g)) = snd (fst (fst (fst (divstep_spec_full m d f g v r)))).
    Proof. unfold divstep_spec, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

    Lemma divstep_spec_divstep_spec_full_g m d f g v r :
      snd (divstep_spec d f g) = snd (fst (fst (divstep_spec_full m d f g v r))).
    Proof. unfold divstep_spec, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

    Lemma divstep_spec2_divstep_spec_full_v m d f g v r :
      fst (divstep_spec2 m d g v r) = snd (fst (divstep_spec_full m d f g v r)).
    Proof. unfold divstep_spec2, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

    Lemma divstep_spec2_divstep_spec_full_r m d f g v r :
      snd (divstep_spec2 m d g v r) = snd (divstep_spec_full m d f g v r).
    Proof. unfold divstep_spec2, divstep_spec_full; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

    Theorem divstep_correct_full d f g v r
            (fodd : Z.odd (tc_eval machine_wordsize tc_limbs f) = true)
            (mw1 : 1 < machine_wordsize)
            (tc_limbs0 : (0 < tc_limbs)%nat)
            (Hv : length v = n)
            (Hr : length r = n)
            (Hf : length f = tc_limbs)
            (Hg : length g = tc_limbs)
            (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                          Z.twos_complement machine_wordsize d <
                          2 ^ (machine_wordsize - 1) - 1)
            (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                          tc_eval machine_wordsize tc_limbs f <
                          2 ^ (machine_wordsize * tc_limbs - 2))
            (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) <
                          tc_eval machine_wordsize tc_limbs g <
                          2 ^ (machine_wordsize * tc_limbs - 2))
            (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
            (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
      let '(d1,f1,g1,v1,r1) := (divstep d f g v r) in
      (Z.twos_complement machine_wordsize d1,
       tc_eval machine_wordsize tc_limbs f1,
       tc_eval machine_wordsize tc_limbs g1,
       (eval v1) mod (s - Associational.eval c),
       (eval r1) mod (s - Associational.eval c)) =
      divstep_spec_full (s - Associational.eval c)
                        (Z.twos_complement machine_wordsize d)
                        (tc_eval machine_wordsize tc_limbs f)
                        (tc_eval machine_wordsize tc_limbs g)
                        (eval v)
                        (eval r).
    Proof.
      assert (0 < machine_wordsize) by lia.
      repeat apply injective_projections.
      erewrite <- divstep_spec_divstep_spec_full_d, <- (divstep_d _ _ _ _ _ _ _ _ _); auto.
      erewrite <- divstep_spec_divstep_spec_full_f, <- (divstep_f _ _ _ _ _ _ _ _ _); auto; lia.
      erewrite <- divstep_spec_divstep_spec_full_g, <- (divstep_g _ _ _ _ _ _ _ _ _); auto; lia.
      erewrite <- divstep_spec2_divstep_spec_full_v;
        erewrite <- (divstep_v d f g v r fodd  _ _ _ _ _ _); auto.
      erewrite <- divstep_spec2_divstep_spec_full_r;
        erewrite <- (divstep_r d f g v r fodd _ _ _ _ _ _); auto.
      Unshelve. all: auto; try lia.
    Qed.
  End __.

End UnsaturatedSolinas.
