Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Require Import Crypto.Arithmetic.BYInv.ArithmeticShiftr.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Divstep.
Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.Ones.
Require Import Crypto.Arithmetic.BYInv.TCSignExtend.
Require Import Crypto.Arithmetic.BYInv.TCMul.
Require Import Crypto.Arithmetic.BYInv.Firstn.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementNeg.
Require Import Crypto.Util.ZUtil.TwosComplementPos.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import Positional.
Import ListNotations.
Import Partition.

Local Open Scope Z.
Local Coercion Z.of_nat : nat >-> Z.
Local Notation eval m n f := (Positional.eval (uweight m) n f).

Hint Rewrite length_tc_add arithmetic_shiftr_length word_tc_mul_length : length_distr.

(** Correctness of wordsized hddivstep *)
Theorem twos_complement_word_full_hddivstep_correct
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
      (twos_complement_word_full_hddivstep machine_wordsize d f g u v q r) in
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
        try apply Z.mod_pos_bound; try apply f_equal2; lia).
Qed.

Lemma twos_complement_word_full_hddivsteps_d_bound
      machine_wordsize d f g u v q r n K
      (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - 2 * (Z.of_nat n))
      (mw1 : 2 < machine_wordsize)
      (overflow_d : - K <
                    Z.twos_complement machine_wordsize d <
                    K) :
  let '(d1,_,_,_,_,_,_) :=
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
  - K - 2 * Z.of_nat n <
  Z.twos_complement machine_wordsize d1 <
  K + 2 * Z.of_nat n.
Proof.
  induction n; intros.
  - rewrite Z.add_0_r, Z.sub_0_r in *; cbn. assumption.
  - rewrite seq_snoc, fold_left_app.
    replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in * by lia.
    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
    cbn -[Z.mul Z.add].

    rewrite !Zselect.Z.zselect_correct, twos_complement_pos_spec, Zmod_odd by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
        rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?twos_complement_opp_spec, ?Z.twos_complement_one, ?Z.twos_complement_two; try lia;
          rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?twos_complement_opp_spec, ?Z.twos_complement_one, ?Z.twos_complement_two; try lia.
Qed.

Lemma twos_complement_word_full_hddivsteps_f_odd
      machine_wordsize d f g u v q r n
      (mw0 : 0 < machine_wordsize)
      (fodd : Z.odd f = true) :
  let '(_,f1,_,_,_,_,_) :=
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in
  Z.odd f1 = true.
Proof.
  induction n; [assumption|].
  rewrite seq_snoc, fold_left_app.
  destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
  cbn -[Z.mul Z.add].
  rewrite !Zselect.Z.zselect_correct.
  destruct (dec _); [assumption|].
  rewrite Zmod_odd in *. destruct (Z.odd g1). reflexivity. rewrite Z.land_0_r in n0. contradiction.
Qed.

Lemma div_lt_lower_bound a b c : 0 < b -> b * (a + 1) <= c -> a < c / b.
Proof. intros; enough (a + 1 <= c / b) by lia; apply Z.div_le_lower_bound; assumption. Qed.

Lemma twos_complement_word_full_hddivsteps_bounds
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
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
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
  - cbn -[Z.mul Z.add]; lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_hddivsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_hddivsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct, twos_complement_pos_spec, Zmod_odd by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd, !twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !twos_complement_opp_spec by (try rewrite twos_complement_opp_spec; lia).
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.

      Unshelve. all: lia || assumption.
Qed.

Lemma twos_complement_word_full_hddivsteps_partial_bounds
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
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
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
  - cbn -[Z.mul Z.add]; lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_hddivsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_hddivsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct, twos_complement_pos_spec, Zmod_odd by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd.
      rewrite !twos_complement_opp_odd by (try assumption; lia).  cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !twos_complement_opp_spec by (try rewrite twos_complement_opp_spec; lia).
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia.

      Unshelve. all: lia || assumption.
Qed.

Lemma twos_complement_word_full_hddivsteps_partial_bounds2
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
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
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
  - cbn -[Z.mul Z.add]; lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_hddivsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_hddivsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct, twos_complement_pos_spec, Zmod_odd by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd,!twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !twos_complement_opp_spec
        by (try rewrite twos_complement_opp_spec; lia).
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia.
      Unshelve. all: lia || assumption. Qed.

Theorem twos_complement_word_full_hddivstep_iter_correct
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
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in
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

  induction n; intros.
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_hddivsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_hddivsteps_f_odd machine_wordsize d f g u v q r n _ _.
    epose proof twos_complement_word_full_hddivsteps_bounds machine_wordsize d f g u v q r n K _ _ _ _ _ _ _ _ _ _ _.

    rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
    rewrite <- IHn by lia.
    cbn -[Z.mul Z.add].
    unfold hddivstep_spec_full'.
    rewrite !Zselect.Z.zselect_correct, Z.twos_complement_odd, twos_complement_pos_spec, Zmod_odd by lia.

    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd, twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
      repeat apply f_equal2; try reflexivity.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, twos_complement_opp_spec, Z.twos_complement_two;
          try rewrite ?twos_complement_opp_spec, ?Z.twos_complement_two; lia.
      * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia).
        rewrite Z.twos_complement_mod by lia.
        rewrite Z.twos_complement_add_full by (try rewrite twos_complement_opp_spec; lia).
        rewrite twos_complement_opp_spec by lia. apply f_equal2; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; try rewrite twos_complement_opp_spec; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; try rewrite twos_complement_opp_spec; lia.
    + rewrite !Zmod_odd, Z.twos_complement_odd, g1odd, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end; try reflexivity.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_two;
          try rewrite Z.twos_complement_two; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod; try apply Z.mod_pos_bound; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod; lia.
      * rewrite Z.twos_complement_mod; lia.
    + rewrite !Zmod_odd, Z.twos_complement_odd, g1odd, !Z.mul_1_l by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end; try reflexivity.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_two; try rewrite Z.twos_complement_two; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod, Z.twos_complement_add_full; try apply Z.mod_pos_bound; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
    + rewrite !Zmod_odd, Z.twos_complement_odd, g1odd, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end; try reflexivity.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_two; try rewrite Z.twos_complement_two; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod; try apply Z.mod_pos_bound; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod; lia.
      * rewrite Z.twos_complement_mod; lia.

        Unshelve. all: lia || assumption.
Qed.

Theorem twos_complement_word_full_hddivstep_iter_partially_correct
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
      fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in
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
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_hddivsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_hddivsteps_f_odd machine_wordsize d f g u v q r n _ _.
    epose proof twos_complement_word_full_hddivsteps_partial_bounds machine_wordsize d f g u v q r n K _ _ _ _ _ _ _ _ _.

    rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_hddivstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
    destruct (hddivstep_spec_full'_iter (Z.twos_complement machine_wordsize d) (Z.twos_complement machine_wordsize f)
        (Z.twos_complement machine_wordsize g) (Z.twos_complement machine_wordsize u) (Z.twos_complement machine_wordsize v)
        (Z.twos_complement machine_wordsize q) (Z.twos_complement machine_wordsize r) n) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2 .

    assert ((Z.twos_complement machine_wordsize d1, Z.twos_complement machine_wordsize f1 mod 2 ^ (machine_wordsize - Z.of_nat n),
        Z.twos_complement machine_wordsize g1 mod 2 ^ (machine_wordsize - Z.of_nat n), Z.twos_complement machine_wordsize u1,
        Z.twos_complement machine_wordsize v1, Z.twos_complement machine_wordsize q1, Z.twos_complement machine_wordsize r1) =
        (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1', v1', q1', r1')).
    apply IHn; lia.
    inversion H4.

    rewrite Z.twos_complement_mod_smaller_pow in H7 by lia.
    rewrite Z.twos_complement_mod_smaller_pow in H8 by lia.

    cbn -[Z.mul Z.add].
    unfold hddivstep_spec_full'.
    rewrite !Zselect.Z.zselect_correct, twos_complement_pos_spec, Zmod_odd by lia.

    assert (Z.odd g1 = Z.odd g1').
    { rewrite <- (Z.odd_mod2m (machine_wordsize - Z.of_nat n) g1'), <- H8, Z.odd_mod2m by lia; reflexivity. }
    rewrite <- H5.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd, twos_complement_opp_odd by (try assumption; lia).
      cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, twos_complement_opp_spec, Z.twos_complement_two by
            (try rewrite twos_complement_opp_spec, Z.twos_complement_two; lia); lia.
      *
        rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)) by lia.
        rewrite H8, Z.mod_pow_same_base_smaller; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
        rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
        apply f_equal2; [|reflexivity].
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
            (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
        rewrite twos_complement_opp_correct, Z.twos_complement_mod_smaller_pow, <- Zplus_mod_idemp_l, Z.mod_pow_same_base_smaller, Zplus_mod_idemp_l by lia.
        push_Zmod. rewrite H7, H8. pull_Zmod.
        apply f_equal2; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full,twos_complement_opp_spec; try rewrite twos_complement_opp_spec; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, twos_complement_opp_spec; try rewrite twos_complement_opp_spec; lia.
    + rewrite !Zmod_odd, g1odd, <- H5, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_two;
          try rewrite Z.twos_complement_two; lia.
      * rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)), H7, Z.mod_pow_same_base_smaller; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
        rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
        apply f_equal2; [|reflexivity].
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
            (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
        rewrite Z.twos_complement_mod_smaller_pow; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod; lia.
      * rewrite Z.twos_complement_mod; lia.
    + rewrite !Zmod_odd, g1odd, <- H5, !Z.mul_1_l by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_two;
          try rewrite Z.twos_complement_two; lia.
      * rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)), H7, Z.mod_pow_same_base_smaller; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
        rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
        apply f_equal2; [|reflexivity].
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
            (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
        rewrite Z.twos_complement_mod_smaller_pow by lia.
        push_Zmod. rewrite H7, H8. pull_Zmod.
        apply f_equal2; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
    + rewrite !Zmod_odd, g1odd, <- H5, !Z.mul_0_l, !Z.add_0_r by lia; cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_two;
          try rewrite Z.twos_complement_two; lia.
      * rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)), H7, Z.mod_pow_same_base_smaller; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
        rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
        apply f_equal2; [|reflexivity].
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
            (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
        rewrite Z.twos_complement_mod_smaller_pow; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod; lia.
      * rewrite Z.twos_complement_mod; lia.

      Unshelve.
      all: try lia; try assumption.
Qed.

Lemma hddivstep_full_iter_full'_iter m d f g u2 v1 v2 q2 r1 r2 n :
  let '(d1,f1,g1,_,_) :=
      hddivstep_full_iter m d f g v1 r1 n in
  (d1,f1,g1)
  = let '(d2,f2,g2,_,_,_,_) := hddivstep_spec_full'_iter d f g u2 v2 q2 r2 n in
    (d2,f2,g2).
Proof.
  induction n; simpl.
  - reflexivity.
  - destruct (hddivstep_full_iter m d f g v1 r1 n) as [[[[?]?]?]?].
    destruct (hddivstep_spec_full'_iter d f g u2 v2 q2 r2 n) as [[[[[[?]?]?]?]?]?].
    inversion IHn.
    unfold hddivstep_spec_full'.
    unfold hddivstep_spec_full.
    destruct (0 <? z4); destruct (Z.odd z6); cbn -[Z.add Z.mul Z.div Z.sub]; reflexivity.
Qed.

Lemma hddivstep_full_iter_f_odd m f g v r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_) := hddivstep_full_iter m 1 f g v r n in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold hddivstep_spec_full.
    destruct (hddivstep_full_iter m 1 f g v r n) as [[[[d1 f1]g1]v1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma hddivstep_full'_iter_f_odd d f g u v q r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_,_,_) := hddivstep_spec_full'_iter d f g u v q r n in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold hddivstep_spec_full'.
    destruct (hddivstep_spec_full'_iter d f g u v q r n) as [[[[[[d1 f1]g1]u1]v1]q1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

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
    { rewrite <- Z.odd_mod2m with (m:=k), <- fmod, Z.odd_mod2m; try assumption; lia. }

    assert (g1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = g2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            f1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = f2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            d1 = d2 /\ (u1, v1, q1, r1) = (u2, v2, q2, r2)) by (apply IHn; lia).

    destruct H2 as [H3 [H4 [H5 H6]]].

    assert (Z.odd g1 = Z.odd g2 /\ d1 = d2).
    { rewrite <- Z.odd_mod2m with (m:=k - n), H3, Z.odd_mod2m by lia; split; reflexivity || lia. }

    unfold hddivstep_spec_full'. destruct H2. rewrite H7, H2.
    inversion H6.

    destruct (0 <? d2); destruct (Z.odd g2) eqn:odd; cbn -[Z.mul Z.add Z.div].
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !Z.mod_pull_div, Z.mul_comm, Z.pow_mul_base by (try apply Z.pow_nonneg; lia).
        replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        push_Zmod. rewrite H3, H4. reflexivity.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, Z.mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try reflexivity.
      * rewrite !Z.mod_pull_div, (Z.mul_comm _ 2), Z.pow_mul_base by (try apply Z.pow_nonneg; lia).
        replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        push_Zmod. rewrite H3, H4, !Zmod_odd, odd, H2. reflexivity.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H4, Z.mod_pow_same_base_smaller; lia.
      * rewrite !Zmod_odd, odd, H2; reflexivity.
    + split; [|split;[|split]]; try reflexivity.
      * rewrite !Z.mod_pull_div, (Z.mul_comm _ 2), Z.pow_mul_base by (try apply Z.pow_nonneg; lia).
        replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        push_Zmod. rewrite H3, H4, !Zmod_odd, odd, H2. reflexivity.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H4, Z.mod_pow_same_base_smaller; lia.
      * rewrite !Zmod_odd, odd, H2; reflexivity.
    + split; [|split;[|split]]; try reflexivity.
      * rewrite !Z.mod_pull_div, (Z.mul_comm _ 2), Z.pow_mul_base by (try apply Z.pow_nonneg; lia).
        replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        push_Zmod. rewrite H3, H4, !Zmod_odd, odd, H2. reflexivity.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H4, Z.mod_pow_same_base_smaller; lia.
      * rewrite !Zmod_odd, odd, H2; reflexivity.
Qed.

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

    replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia.
    rewrite <- Z.pow_mul_base by lia.
    unfold hddivstep_spec_full, hddivstep_spec_full'.
    inversion H.
    inversion IHn; subst.
    destruct (0 <? d1); destruct (Z.odd g1) eqn:godd; cbn -[Z.mul Z.add Z.div Z.of_nat];
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2; try (push_Zmod; pull_Zmod; apply f_equal2; lia)
             end; try lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', Zmod_odd, Z.odd_sub, godd, fodd1; cbn; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', !Zmod_odd, godd, Z.add_0_r, godd; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', !Zmod_odd, godd, Z.mul_1_l, Z.odd_add, godd, fodd1, Z.sub_0_r; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', Zmod_odd, godd, Z.mul_0_l, Z.add_0_r, Zmod_odd, godd; lia.
Qed.

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
  { rewrite <- Z.odd_mod2m with (m:=S n), <- Hf, Z.odd_mod2m; try assumption; lia. }

  pose proof jump_hddivstep_full_iter m f g v r n fodd Hv Hr.
  pose proof hddivstep_full'_iter_important_bits 1 f f0 g g0 1 0 0 1 n (S n) ltac:(lia) fodd Hf Hg.

  destruct (hddivstep_full_iter m 1 f g v r n) as [[[[d1 f1] g1] v1] r1] eqn:E1.
  destruct (hddivstep_spec_full'_iter 1 f g 1 0 0 1 n) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2.
  destruct (hddivstep_spec_full'_iter 1 f0 g0 1 0 0 1 n) as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3.
  destruct H0 as [H1 [H2 [H3 H4]]].

  inversion H; inversion H4; subst.

  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H6.
  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H7.
  rewrite Z.div_mul' in * by (apply Z.pow_nonzero; lia).
  congruence.
Qed.

(* TODO: Move thise *)
Lemma fold_right_fold_left_lemma {A B : Type} (f : B -> A -> A) (l s : list B) (a : A) :
  (forall x x' y, f x y = f x' y) -> length l = length s -> fold_left (fun i j => f j i) l a = fold_right f a s.
Proof.
  rewrite <- fold_left_rev_right. revert s a.
  induction l; intros; simpl.
  - assert (s = []) by (destruct s; simpl in *; try lia; reflexivity); subst. reflexivity.
  - rewrite fold_right_snoc. replace s with (rev (rev s)) by (apply rev_involutive).
    destruct (rev s) eqn:E.
    apply (f_equal (@rev B)) in E. rewrite rev_involutive in E. subst. simpl in *. lia.
    simpl. rewrite fold_right_snoc.
    replace (f a a0) with (f b a0). apply IHl. assumption.
    apply (f_equal (@length B)) in E. simpl in *.
    rewrite rev_length in *. lia. apply H.
Qed.

Lemma pow_ineq k : (2 <= k)%nat -> k + 2 <= Zpower_nat 2 k.
Proof. induction k as [|[|[|k]]]; [lia|lia|simpl; lia|rewrite Zpower_nat_succ_r; lia]; intros. Qed.

Lemma pow_ineq_Z k : 2 <= k -> k + 2 <= 2 ^ k.
Proof. intros. replace k with (Z.of_nat (Z.to_nat k)) by lia. rewrite <- Zpower_nat_Z. apply pow_ineq; lia. Qed.

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
           *** lia.
Qed.

Lemma pow_ineq_Z2 k : 3 <= k -> 2 * k + 2 <= 2 ^ k.
Proof.
  intros. replace k with (Z.of_nat (Z.to_nat k)).
  rewrite <- Zpower_nat_Z. apply pow_ineq2. lia. lia.
Qed.

Module WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.

  Section __.
    Context (machine_wordsize : Z)
            (n : nat)
            (sat_limbs : nat)
            (word_tc_mul_limbs : nat)
            (m : Z)
            (r' : Z)
            (m' : Z)
            (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
            (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
            (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat n)
            (m_big : 2 ^ machine_wordsize < m).

    Notation outer_loop_body_hd := (outer_loop_body_hd machine_wordsize n sat_limbs word_tc_mul_limbs m m').

    Lemma twos_complement_word_to_montgomery_no_encode_correct a
          (Hmw : 0 < machine_wordsize)
          (Hn : (1 < n)%nat)
          (* (Hm : 1 < m) *)
          (Ha : 0 <= a < 2 ^ machine_wordsize)
      :
        @eval machine_wordsize n (twos_complement_word_to_montgomery_no_encode machine_wordsize n m a) mod m = Z.twos_complement machine_wordsize a mod m
        /\ valid machine_wordsize n m (twos_complement_word_to_montgomery_no_encode machine_wordsize n m a).
    Proof.
      unfold twos_complement_word_to_montgomery_no_encode.
      assert (2 ^ (machine_wordsize) <= 2 ^ (machine_wordsize * Z.of_nat n)) by
          (apply Z.pow_le_mono_r; nia).
      assert (valid machine_wordsize n m (Partition.partition (uweight machine_wordsize) n (Z.twos_complement_opp machine_wordsize a))).
      { unfold valid, small.
        pose proof Z.mod_pos_bound (-a) (2^machine_wordsize) ltac:(apply Z.pow_pos_nonneg; lia).
        split; unfold eval.
        rewrite eval_partition, uweight_eq_alt', Z.mod_small by
            (try rewrite twos_complement_opp_correct; try apply uwprops; nia); reflexivity.
        rewrite eval_partition, uweight_eq_alt', twos_complement_opp_correct, Z.mod_pow_same_base_larger;
          try apply uwprops; nia. }
      pose proof (Hvalid := oppmod_correct machine_wordsize n m r' m' r'_correct m'_correct ltac:(lia) ltac:(lia) ltac:(lia) m_small).
      rewrite twos_complement_neg_spec, !unfold_Let_In, select_eq with (n:=n); try (try rewrite length_partition; lia);
        try (apply length_small with (lgr:=machine_wordsize); apply Hvalid; assumption); try apply (uweight machine_wordsize).

      unfold Z.twos_complement.
      rewrite Z.twos_complement_cond_equiv by lia.

      destruct (Z.testbit a (machine_wordsize - 1)) eqn:E; cbn -[Partition.partition oppmod]; split.
      - replace (@eval machine_wordsize n
                  (oppmod machine_wordsize n m (Partition.partition (uweight machine_wordsize) n (Z.twos_complement_opp machine_wordsize a)))) with
            (@eval machine_wordsize n
              (oppmod machine_wordsize n m (Partition.partition (uweight machine_wordsize) n (Z.twos_complement_opp machine_wordsize a))) * (1 ^ n)) by (rewrite Z.pow_1_l; lia).

        rewrite <- r'_correct. push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)),  <- Zmult_mod_idemp_l,  <- eval_from_montgomerymod with (m':=m'), eval_oppmod with (r':=r'); try lia; try (try apply Hvalid; assumption).
        push_Zmod. rewrite eval_from_montgomerymod with (r':=r'); try lia; try (try apply Hvalid; assumption).
        push_Zmod. unfold eval; rewrite eval_partition by (apply uwprops; lia).
        rewrite twos_complement_opp_correct. pull_Zmod.
        rewrite uweight_eq_alt', Z.mod_pow_same_base_larger, Z.mul_opp_l, <- Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), PullPush.Z.opp_mod_mod, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, r'_correct, Z.pow_1_l by nia. pull_Zmod. rewrite Z.mul_1_r.
        destruct (dec (a = 0)).
        + subst. rewrite Z.bits_0 in *. inversion E.
        + rewrite (Z.mod_opp_small a) by nia; apply f_equal2; [|reflexivity]; rewrite Z.mod_small; lia.
      - apply Hvalid. assumption.
      - unfold eval. rewrite eval_partition, uweight_eq_alt, (Z.mod_small a), (Z.mod_small a (2 ^ _)); try apply uwprops; lia.
      - unfold valid; split.
        + unfold small.
          unfold eval. rewrite eval_partition, uweight_eq_alt', Z.mod_small; try (apply uwprops; lia); try nia; reflexivity.
        + unfold eval. rewrite eval_partition, uweight_eq_alt', Z.mod_small; try (apply uwprops; lia); try nia; reflexivity.
    Qed.

    Lemma eval_twos_complement_word_to_montgomery_no_encode a
          (Hmw : 0 < machine_wordsize)
          (Hn : (1 < n)%nat)
          (Hm : 1 < m)
          (Ha : 0 <= a < 2 ^ machine_wordsize)
      :
        @eval machine_wordsize n (twos_complement_word_to_montgomery_no_encode machine_wordsize n m a) mod m = Z.twos_complement machine_wordsize a mod m.
    Proof. apply twos_complement_word_to_montgomery_no_encode_correct; assumption. Qed.


    Ltac t := repeat match goal with
                     | |- valid _ _ _ (addmod _ _ _ _ _) => eapply addmod_correct
                     | |- valid _ _ _ (mulmod _ _ _ _ _ _) => eapply mulmod_correct
                     | |- valid _ _ _ (twos_complement_word_to_montgomery_no_encode _ _ _ _) => apply twos_complement_word_to_montgomery_no_encode_correct
                     | |- valid _ _ _ _ => eassumption
                     | |- _ => eassumption || nia
                     end.

    (** Correctness of outer loop body  *)
    Theorem outer_loop_body_hd_correct f g v r
            (fodd : Z.odd (tc_eval machine_wordsize sat_limbs f) = true)
            (n1 : (1 < n)%nat)
            (mw1 : 3 < machine_wordsize)
            (Hf : length f = sat_limbs)
            (Hg : length g = sat_limbs)

            (sat_limbs0 : (0 < sat_limbs)%nat)
            (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + sat_limbs)%nat)
            (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                          tc_eval machine_wordsize sat_limbs f <
                          2 ^ (machine_wordsize * sat_limbs - 2))
            (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                          tc_eval machine_wordsize sat_limbs g <
                          2 ^ (machine_wordsize * sat_limbs - 2))
            (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
            (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize)
            (Hr : valid machine_wordsize n m r)
            (Hv : valid machine_wordsize n m v) :
      let '(f1,g1,v1,r1) := outer_loop_body_hd f g v r in
      (tc_eval machine_wordsize sat_limbs f1,
       tc_eval machine_wordsize sat_limbs g1,
       @eval machine_wordsize n v1 mod m,
       @eval machine_wordsize n r1 mod m)
      =
      let '(_,f1',g1',v1',r1') :=
          hddivstep_full_iter m 1
                            (tc_eval machine_wordsize sat_limbs f)
                            (tc_eval machine_wordsize sat_limbs g)
                            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' v) mod m)
                            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' r) mod m)
                            (Z.to_nat (machine_wordsize - 2)) in
      (Z.twos_complement (machine_wordsize * sat_limbs) f1',
       Z.twos_complement (machine_wordsize * sat_limbs) g1', v1', r1').
    Proof.
      pose proof (pow_ineq_Z2 (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (0 < 2 ^ (machine_wordsize - 1))
        by (apply Z.pow_pos_nonneg; lia).
      assert (0 < 2 ^ (machine_wordsize - 2))
        by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1))
        by (rewrite Z.mul_comm, Z.pow_mul_base by lia; apply f_equal2; lia).
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat sat_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + sat_limbs)) - 1))
        by (rewrite <- Zpower_exp, !Z.pow_mul_base by nia; apply f_equal2; nia).

      unfold outer_loop_body_hd.
      epose proof twos_complement_word_full_hddivstep_iter_partially_correct (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

      epose proof twos_complement_word_full_hddivsteps_partial_bounds (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.

      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      epose proof jump_hddivstep_full
            m
            (tc_eval machine_wordsize sat_limbs f)
            (Z.twos_complement machine_wordsize (nth_default 0 f 0))
            (tc_eval machine_wordsize sat_limbs g)
            (Z.twos_complement machine_wordsize (nth_default 0 g 0))
            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' v) mod m)
            (@eval machine_wordsize n (from_montgomerymod machine_wordsize n m m' r) mod m)
            (Z.to_nat (machine_wordsize - 2)) _ _ _ _ _ _.

      rewrite Z.twos_complement_one, Z.twos_complement_zero in * by lia.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.

      destruct (fold_left (fun (i : Z * Z * Z * Z * Z * Z * Z) (_ : nat) => twos_complement_word_full_hddivstep_aux machine_wordsize i)
                              (seq 0 (Z.to_nat (machine_wordsize - 2))) (1, nth_default 0 f 0, nth_default 0 g 0, 1, 0, 0, 1)) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1 .

      destruct (hddivstep_full_iter
                  m 1
                  (tc_eval machine_wordsize sat_limbs f)
                  (tc_eval machine_wordsize sat_limbs g)
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

      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval with (n:=(1 + sat_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full;
          repeat match goal with
          | |- length _ = _ => autorewrite with length_distr; try lia
          | |- context[In _] => apply arithmetic_shiftr_bounds || apply tc_add_bounds
          | _ => assumption || lia
          end.
        rewrite !word_tc_mul_correct by (assumption || lia).
        inversion H7. inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia.
        rewrite !word_tc_mul_correct; (assumption || nia).
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval with (n:=(1 + sat_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full;
          repeat match goal with
          | |- length _ = _ => autorewrite with length_distr; try lia
          | |- context[In _] => apply arithmetic_shiftr_bounds || apply tc_add_bounds
          | _ => assumption || lia
          end.
        rewrite !word_tc_mul_correct by (assumption || lia).
        inversion H7. inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia.
        rewrite !word_tc_mul_correct; (assumption || nia).
      + rewrite <- (Z.mul_1_r (@eval _ _ _)), <- (Z.pow_1_l n), <- r'_correct by lia.
        push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)), <- Zmult_mod_idemp_l.
        rewrite <- eval_from_montgomerymod with (m':=m'), eval_addmod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_mulmod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_from_montgomerymod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_twos_complement_word_to_montgomery_no_encode by t.
        pull_Zmod.
        rewrite Z.mul_add_distr_r, <- !Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), !Z.mul_assoc, <- Z.mul_add_distr_r, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, r'_correct, Z.pow_1_l, Z.mod_1_l, Z.mul_1_r by lia.
        inversion H7. inversion H5.
        rewrite !eval_from_montgomerymod with (r':=r') by t.
        push_Zmod; pull_Zmod.
        apply f_equal2; lia.
      + rewrite <- (Z.mul_1_r (@eval _ _ _)), <- (Z.pow_1_l n), <- r'_correct by lia.
        push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)), <- Zmult_mod_idemp_l.
        rewrite <- eval_from_montgomerymod with (m':=m'), eval_addmod with (r':=r')by t.
        push_Zmod.
        rewrite !eval_mulmod with (r':=r')by t.
        push_Zmod.
        rewrite !eval_from_montgomerymod with (r':=r')by t.
        push_Zmod.
        rewrite !eval_twos_complement_word_to_montgomery_no_encode by t.
        pull_Zmod.
        rewrite Z.mul_add_distr_r, <- !Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), !Z.mul_assoc, <- Z.mul_add_distr_r, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, r'_correct, Z.pow_1_l, Z.mod_1_l, Z.mul_1_r by lia.
        inversion H7. inversion H5.
        rewrite !eval_from_montgomerymod with (r':=r') by t.
        push_Zmod; pull_Zmod.
        apply f_equal2; lia.

        Unshelve.
        all: lia || rewrite ?Z.twos_complement_one, ?Z.twos_complement_zero; lia || idtac.
        rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=sat_limbs); try lia.
        unfold tc_eval in fodd.
        rewrite Z.twos_complement_odd in fodd.
        rewrite Z.odd_mod2m. assumption.

        lia. nia. assumption.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

        lia.
        apply Hf2.
        destruct f. simpl in *. lia. left. reflexivity.
        apply Hg2.
        destruct g. simpl in *. lia. left. reflexivity.

        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia; lia.
        unfold tc_eval in fodd.
        rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.odd_mod2m by (assumption || lia).
        rewrite Z.twos_complement_odd in fodd; assumption || nia.

        assumption.
        apply Z.mod_pos_bound; lia.
        apply Z.mod_pos_bound; lia.

        unfold tc_eval.
        rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.twos_complement_mod, !Z.twos_complement_mod_smaller_pow; assumption || nia.

        unfold tc_eval.
        rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.twos_complement_mod, !Z.twos_complement_mod_smaller_pow; assumption || nia.
    Qed.
  End __.
End WordByWordMontgomery.

Module UnsaturatedSolinas.

  Import Definitions.UnsaturatedSolinas.

  Section __.

    Context (limbwidth_num limbwidth_den : Z)
            (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
            (machine_wordsize : Z)
            (s : Z)
            (c : list (Z*Z))
            (n : nat)
            (sat_limbs : nat)
            (word_tc_mul_limbs : nat)
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

    Notation word_to_solina := (word_to_solina limbwidth_num limbwidth_den machine_wordsize s c n idxs balance).
    Notation outer_loop_body_hd := (outer_loop_body_hd limbwidth_num limbwidth_den machine_wordsize s c n sat_limbs word_tc_mul_limbs idxs balance).

    Lemma word_to_solina_length a :
      length (word_to_solina a) = n.
    Proof.
      unfold word_to_solina.
      rewrite !unfold_Let_In; rewrite length_select with (n:=n);
        unfold carrymod, oppmod, encodemod; auto with distr_length.
    Qed.

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

    (** Correctness of outer loop body  *)
    Theorem outer_loop_body_hd_correct f g v r
            (fodd : Z.odd (tc_eval machine_wordsize sat_limbs f) = true)
            (n1 : (1 < n)%nat)
            (mw1 : 3 < machine_wordsize)
            (Hf : length f = sat_limbs)
            (Hg : length g = sat_limbs)
            (Hv : length v = n)
            (Hr : length r = n)
            (sat_limbs0 : (0 < sat_limbs)%nat)
            (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + sat_limbs)%nat)
            (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                          tc_eval machine_wordsize sat_limbs f <
                          2 ^ (machine_wordsize * sat_limbs - 2))
            (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                          tc_eval machine_wordsize sat_limbs g <
                          2 ^ (machine_wordsize * sat_limbs - 2))
            (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
            (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
      let '(f1,g1,v1,r1) := outer_loop_body_hd f g v r in
      (tc_eval machine_wordsize sat_limbs f1,
       tc_eval machine_wordsize sat_limbs g1,
       eval v1 mod (s - Associational.eval c),
       eval r1 mod (s - Associational.eval c))
      =
      let '(_,f1',g1',v1',r1') :=
          hddivstep_full_iter (s - Associational.eval c) 1
                            (tc_eval machine_wordsize sat_limbs f)
                            (tc_eval machine_wordsize sat_limbs g)
                            (eval v mod (s - Associational.eval c))
                            (eval r mod (s - Associational.eval c))
                            (Z.to_nat (machine_wordsize - 2)) in
      (Z.twos_complement (machine_wordsize * sat_limbs) f1',
       Z.twos_complement (machine_wordsize * sat_limbs) g1', v1', r1').
    Proof.
      pose proof (pow_ineq_Z2 (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (0 < 2 ^ (machine_wordsize - 1))
        by (apply Z.pow_pos_nonneg; lia).
      assert (0 < 2 ^ (machine_wordsize - 2))
        by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1))
        by (rewrite Z.mul_comm, Z.pow_mul_base by lia; apply f_equal2; lia).
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat sat_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + sat_limbs)) - 1))
        by (rewrite <- Zpower_exp, !Z.pow_mul_base by nia; apply f_equal2; nia).

      unfold outer_loop_body_hd.
      epose proof twos_complement_word_full_hddivstep_iter_partially_correct (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

      epose proof twos_complement_word_full_hddivsteps_partial_bounds (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.

      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      epose proof jump_hddivstep_full
            (s - Associational.eval c)
            (tc_eval machine_wordsize sat_limbs f)
            (Z.twos_complement machine_wordsize (nth_default 0 f 0))
            (tc_eval machine_wordsize sat_limbs g)
            (Z.twos_complement machine_wordsize (nth_default 0 g 0))
            (eval v mod (s - Associational.eval c))
            (eval r mod (s - Associational.eval c))
            (Z.to_nat (machine_wordsize - 2)) _ _ _ _ _ _.

      rewrite Z.twos_complement_one, Z.twos_complement_zero in * by lia.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.

      destruct (    fold_left (fun (i : Z * Z * Z * Z * Z * Z * Z) (_ : nat) => twos_complement_word_full_hddivstep_aux machine_wordsize i)
                              (seq 0 (Z.to_nat (machine_wordsize - 2))) (1, nth_default 0 f 0, nth_default 0 g 0, 1, 0, 0, 1)) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1 .
      destruct (hddivstep_full_iter
                  (s - Associational.eval c) 1
                  (tc_eval machine_wordsize sat_limbs f)
                  (tc_eval machine_wordsize sat_limbs g)
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
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval with (n:=(1 + sat_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full;
          repeat match goal with
                 | |- length _ = _ => autorewrite with length_distr; try lia
                 | |- context[In _] => apply arithmetic_shiftr_bounds || apply tc_add_bounds
                 | _ => assumption || lia
                 end.
        rewrite !word_tc_mul_correct by (assumption || lia).
        inversion H7. inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia.
        rewrite !word_tc_mul_correct; (assumption || nia).
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval with (n:=(1 + sat_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full;
          repeat match goal with
                 | |- length _ = _ => autorewrite with length_distr; try lia
                 | |- context[In _] => apply arithmetic_shiftr_bounds || apply tc_add_bounds
                 | _ => assumption || lia
                 end.
        rewrite !word_tc_mul_correct by (assumption || lia).
        inversion H7. inversion H5.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia.
        rewrite !word_tc_mul_correct; (assumption || nia).
      + rewrite eval_carrymod, eval_addmod; try lia.
        push_Zmod.
        rewrite !eval_carry_mulmod; try lia.
        push_Zmod.
        rewrite !eval_word_to_solina; try lia.

        inversion H7. inversion H5.
        push_Zmod; pull_Zmod. reflexivity.
        apply word_to_solina_length.
        apply word_to_solina_length.
        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold addmod, carry_mulmod, mulmod; auto with distr_length.
      + rewrite eval_carrymod, eval_addmod; try lia.
        push_Zmod.
        rewrite !eval_carry_mulmod; try lia.
        push_Zmod.
        rewrite !eval_word_to_solina; try lia.

        inversion H7. inversion H5.
        push_Zmod; pull_Zmod. reflexivity.
        apply word_to_solina_length.
        apply word_to_solina_length.
        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold carry_mulmod, mulmod; auto with distr_length.
        unfold addmod, carry_mulmod, mulmod; auto with distr_length.

        Unshelve.
        all: lia || rewrite ?Z.twos_complement_one, ?Z.twos_complement_zero; lia || idtac.
        rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=sat_limbs); try lia.
        unfold tc_eval in fodd.
        rewrite Z.twos_complement_odd in fodd.
        rewrite Z.odd_mod2m. assumption.

        lia. nia. assumption.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

        lia.
        apply Hf2.
        destruct f. simpl in *. lia. left. reflexivity.
        apply Hg2.
        destruct g. simpl in *. lia. left. reflexivity.

        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia; lia.
        unfold tc_eval in fodd.
        rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.odd_mod2m by (assumption || lia).
        rewrite Z.twos_complement_odd in fodd; assumption || nia.

        assumption.
        apply Z.mod_pos_bound; lia.
        apply Z.mod_pos_bound; lia.

        unfold tc_eval.
        rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.twos_complement_mod, !Z.twos_complement_mod_smaller_pow; assumption || nia.

        unfold tc_eval.
        rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.twos_complement_mod, !Z.twos_complement_mod_smaller_pow; assumption || nia.
    Qed.
  End __.

End UnsaturatedSolinas.
