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
Require Import Crypto.Arithmetic.BYInv.TCSignBit.
Require Import Crypto.Arithmetic.BYInv.TCSignExtend.
Require Import Crypto.Arithmetic.BYInv.TCMul.
Require Import Crypto.Arithmetic.BYInv.Firstn.
Require Import Crypto.Arithmetic.BYInv.BYInv.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.One.

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
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementNeg.
Require Import Crypto.Util.ZUtil.TwosComplementPos.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.ModExp.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import Positional.
Import ListNotations.
Import Partition.

Local Open Scope Z.
Local Coercion Z.of_nat : nat >-> Z.
Local Notation eval m n := (Positional.eval (uweight m) n).

Hint Rewrite length_tc_add arithmetic_shiftr_length word_tc_mul_length : length_distr.

Require Import Crypto.Arithmetic.BYInv.EvalLemmas.

Ltac splits :=
  repeat match goal with
         | |- (_, _) = _ => apply f_equal2
         end.

(** Correctness of wordsized divstep *)
(* Theorem twos_complement_word_full_divstep_correct *)
(*         machine_wordsize d f g u v q r *)
(*         (fodd : Z.odd f = true) *)
(*         (mw1 : 2 < machine_wordsize) *)
(*         (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 < *)
(*                       Z.twos_complement machine_wordsize d < *)
(*                       2 ^ (machine_wordsize - 1) - 1) *)
(*         (overflow_f : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize f < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_g : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize g < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_u : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize u < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_v : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize v < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_q : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize q < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_r : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize r < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (Hf2 : 0 <= f < 2^machine_wordsize) *)
(*         (Hg2 : 0 <= g < 2^machine_wordsize) : *)
(*   let '(d1,f1,g1,u1,v1,q1,r1) := *)
(*       (twos_complement_word_full_divstep machine_wordsize d f g u v q r) in *)
(*   (Z.twos_complement machine_wordsize d1, *)
(*    Z.twos_complement machine_wordsize f1, *)
(*    Z.twos_complement machine_wordsize g1, *)
(*    Z.twos_complement machine_wordsize u1, *)
(*    Z.twos_complement machine_wordsize v1, *)
(*    Z.twos_complement machine_wordsize q1, *)
(*    Z.twos_complement machine_wordsize r1) = *)
(*   divstep_uvqr ((Z.twos_complement machine_wordsize d), *)
(*                      (Z.twos_complement machine_wordsize f), *)
(*                      (Z.twos_complement machine_wordsize g), *)
(*                      (Z.twos_complement machine_wordsize u), *)
(*                      (Z.twos_complement machine_wordsize v), *)
(*                      (Z.twos_complement machine_wordsize q), *)
(*                      (Z.twos_complement machine_wordsize r)). *)
(* Proof. *)
(*   assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by *)
(*       (rewrite Z.pow_mul_base by lia; apply f_equal2; lia). *)
(*   assert (2 ^ (machine_wordsize - 2) < 2^(machine_wordsize - 1)) by *)
(*       (apply Z.pow_lt_mono_r; lia). *)
(*   assert (2 <= 2 ^ (machine_wordsize - 2)) by *)
(*       (replace 2 with (2 ^ 1) by lia; apply Z.pow_le_mono_r; lia). *)
(*   unfold divstep_uvqr; cbn -[Z.mul Z.add]. *)
(*   rewrite !Zselect.Z.zselect_correct. *)
(*   rewrite !Z.twos_complement_pos_spec, Zmod_odd, Z.twos_complement_odd by lia. *)
(*   destruct (0 <? Z.twos_complement machine_wordsize d); *)
(*     destruct (Z.odd g) eqn:godd; *)
(*     rewrite (Zmod_odd); cbn -[Z.mul Z.add]; *)
(*       rewrite ?godd; cbn -[Z.mul Z.add]. *)
(*   rewrite <- (Z.twos_complement_odd machine_wordsize), !Z.twos_complement_opp_spec by lia; *)
(*     rewrite Z.odd_opp, Z.twos_complement_odd, fodd by lia; cbn -[Z.mul Z.add]. *)
(*   all: (t; repeat rewrite ?Z.twos_complement_mod, 1?Z.twos_complement_add_full, 1?Z.twos_complement_one, *)
(*           1?Z.arithmetic_shiftr1_spec, 1?Z.twos_complement_opp_spec, 1?Z.twos_complement_zero; *)
(*         try apply Z.mod_pos_bound; try apply f_equal2; lia). *)
(* Qed. *)

Lemma twos_complement_word_full_divsteps_d_bound
      machine_wordsize d f g u v q r n K
      (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat n))
      (mw1 : 1 < machine_wordsize)
      (overflow_d : - K <=
                    Z.twos_complement machine_wordsize d <=
                    K) :
  let '(d1,_,_,_,_,_,_) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
  - K - Z.of_nat n <=
  Z.twos_complement machine_wordsize d1 <=
  K + Z.of_nat n.
Proof.
  induction n; intros.
  - rewrite Z.add_0_r, Z.sub_0_r in *; cbn. assumption.
  - rewrite seq_snoc, fold_left_app.
    replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in * by lia.
    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
    cbn -[Z.mul Z.add].

    rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
        rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp_spec, ?Z.twos_complement_one; try lia;
          rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp_spec, ?Z.twos_complement_one; try lia.
Qed.

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
  rewrite Zmod_odd in *. destruct (Z.odd g1). reflexivity. rewrite Z.land_0_r in n0. contradiction.
Qed.

Lemma div_lt_lower_bound a b c : 0 < b -> b * (a + 1) <= c -> a < c / b.
Proof. intros; enough (a + 1 <= c / b) by lia; apply Z.div_le_lower_bound; assumption. Qed.

Lemma twos_complement_word_full_divsteps_bounds
      machine_wordsize d f g u v q r n K
      (HK : 0 < K)
      (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2))
      (mw1 : 1 < machine_wordsize)
      (fodd : Z.odd f = true)

      (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <=
                    Z.twos_complement machine_wordsize d <=
                    2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)
      (* (overflow_f : - 2 ^ (machine_wordsize - 2) < *)
      (*               Z.twos_complement machine_wordsize f < *)
      (*               2 ^ (machine_wordsize - 2)) *)
      (* (overflow_g : - 2 ^ (machine_wordsize - 2) < *)
      (*               Z.twos_complement machine_wordsize g < *)
      (*               2 ^ (machine_wordsize - 2)) *)
      (overflow_u : - K <=
                    Z.twos_complement machine_wordsize u <=
                    K)
      (overflow_v : - K <=
                    Z.twos_complement machine_wordsize v <=
                    K)
      (overflow_q : - K <=
                    Z.twos_complement machine_wordsize q <=
                    K)
      (overflow_r : - K <=
                    Z.twos_complement machine_wordsize r <=
                      K)
      (u_pos : 0 <= u < 2 ^ machine_wordsize)
      (v_pos : 0 <= v < 2 ^ machine_wordsize)
      (q_pos : 0 <= q < 2 ^ machine_wordsize)
      (r_pos : 0 <= r < 2 ^ machine_wordsize) :
  let '(_,f1,g1,u1,v1,q1,r1) :=
      fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in
      (* - 2 ^ (machine_wordsize - 2) < *)
      (* Z.twos_complement machine_wordsize f1 < *)
      (*   2 ^ (machine_wordsize - 2) /\ *)
      (* - 2 ^ (machine_wordsize - 2) < *)
      (* Z.twos_complement machine_wordsize g1 < *)
      (*   2 ^ (machine_wordsize - 2) /\ *)
      - 2 ^ n * K <=
      Z.twos_complement machine_wordsize u1 <=
        2 ^ n * K /\
      - 2 ^ n * K <=
      Z.twos_complement machine_wordsize v1 <=
        2 ^ n * K /\
      - 2 ^ n * K <=
      Z.twos_complement machine_wordsize q1 <=
        2 ^ n * K /\
      - 2 ^ n * K <=
      Z.twos_complement machine_wordsize r1 <=
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

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.

    rewrite seq_snoc, fold_left_app.

    cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

    specialize (IHn ltac:(lia) ltac:(lia)).
    assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

    cbn -[Z.mul Z.add].
    rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd, !Z.twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
      (* rewrite Z.arithmetic_shiftr1_spec. (try apply Z.mod_pos_bound; lia). *)
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !Z.twos_complement_opp_spec by (try rewrite Z.twos_complement_opp_spec; lia).
      assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      (* rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia). *)
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
      (* rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia). *)
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
    + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
      (* rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia). *)
      rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
      repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.

      Unshelve. all: lia || assumption.
Qed.

(* Lemma twos_complement_word_full_divsteps_partial_bounds *)
(*       machine_wordsize d f g u v q r n K *)
(*       (HK : 0 < K) *)
(*       (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2)) *)
(*       (mw1 : 1 < machine_wordsize) *)
(*       (fodd : Z.odd f = true) *)
(*       (u_pos : 0 <= u < 2 ^ machine_wordsize) *)
(*       (v_pos : 0 <= v < 2 ^ machine_wordsize) *)
(*       (q_pos : 0 <= q < 2 ^ machine_wordsize) *)
(*       (r_pos : 0 <= r < 2 ^ machine_wordsize) *)
(*       (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <= *)
(*                     Z.twos_complement machine_wordsize d <= *)
(*                     2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) *)
(*       (overflow_u : - K <= *)
(*                     Z.twos_complement machine_wordsize u <= *)
(*                     K) *)
(*       (overflow_v : - K <= *)
(*                     Z.twos_complement machine_wordsize v <= *)
(*                     K) *)
(*       (overflow_q : - K <= *)
(*                     Z.twos_complement machine_wordsize q <= *)
(*                     K) *)
(*       (overflow_r : - K <= *)
(*                     Z.twos_complement machine_wordsize r <= *)
(*                     K) : *)
(*   let '(_,_,_,u1,v1,q1,r1) := *)
(*       fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize u1 <= *)
(*       2 ^ n * K /\ *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize v1 <= *)
(*       2 ^ n * K /\ *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize q1 <= *)
(*       2 ^ n * K /\ *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize r1 <= *)
(*       2 ^ n * K /\ *)
(*       0 <= u1 < 2 ^ machine_wordsize /\ *)
(*       0 <= v1 < 2 ^ machine_wordsize /\ *)
(*       0 <= q1 < 2 ^ machine_wordsize /\ *)
(*       0 <= r1 < 2 ^ machine_wordsize. *)
(* Proof. *)
(*   assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia). *)

(*   induction n; intros. *)
(*   - cbn -[Z.mul Z.add]; lia. *)
(*   - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia. *)
(*     rewrite <- Z.pow_mul_base in * by lia. *)

(*     epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d. *)
(*     epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _. *)

(*     rewrite seq_snoc, fold_left_app. *)

(*     cbn -[Z.mul Z.add]. *)
(*     destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E. *)

(*     specialize (IHn ltac:(lia) ltac:(lia)). *)
(*     assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by *)
(*         (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia). *)

(*     cbn -[Z.mul Z.add]. *)
(*     rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia. *)
(*     destruct (0 <? Z.twos_complement machine_wordsize d1); *)
(*       destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]. *)
(*     + rewrite Zmod_odd. *)
(*       rewrite !Z.twos_complement_opp_odd by (try assumption; lia).  cbn -[Z.mul Z.add]. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !Z.twos_complement_opp_spec by (try rewrite Z.twos_complement_opp_spec; lia). *)
(*       assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia). *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia. *)
(*     + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia. *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia. *)
(*     + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia. *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia. *)
(*     + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia. *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; lia. *)

(*       Unshelve. all: lia || assumption. *)
(* Qed. *)

(* Lemma twos_complement_word_full_divsteps_partial_bounds2 *)
(*       machine_wordsize d f g u v q r n K *)
(*       (HK : 0 < K) *)
(*       (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2)) *)
(*       (mw1 : 1 < machine_wordsize) *)
(*       (fodd : Z.odd f = true) *)
(*       (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <= *)
(*                     Z.twos_complement machine_wordsize d <= *)
(*                     2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) *)
(*       (overflow_u : - K <= *)
(*                     Z.twos_complement machine_wordsize u <= *)
(*                     K) *)
(*       (overflow_v : - K <= *)
(*                     Z.twos_complement machine_wordsize v <= *)
(*                     K) *)
(*       (overflow_q : - K <= *)
(*                     Z.twos_complement machine_wordsize q <= *)
(*                     K) *)
(*       (overflow_r : - K <= *)
(*                     Z.twos_complement machine_wordsize r <= *)
(*                     K) : *)
(*   let '(_,_,_,u1,v1,q1,r1) := *)
(*       fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r) in *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize u1 <= *)
(*       2 ^ n * K /\ *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize v1 <= *)
(*       2 ^ n * K /\ *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize q1 <= *)
(*       2 ^ n * K /\ *)
(*       - 2 ^ n * K <= *)
(*       Z.twos_complement machine_wordsize r1 <= *)
(*       2 ^ n * K. *)
(* Proof. *)
(*   assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia). *)

(*   induction n; intros. *)
(*   - cbn -[Z.mul Z.add]; lia. *)
(*   - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia. *)
(*     rewrite <- Z.pow_mul_base in * by lia. *)

(*     epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d. *)
(*     epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _. *)

(*     rewrite seq_snoc, fold_left_app. *)

(*     cbn -[Z.mul Z.add]. *)
(*     destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E. *)
(*     specialize (IHn ltac:(lia) ltac:(lia)). *)
(*     assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by *)
(*         (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia). *)

(*     cbn -[Z.mul Z.add]. *)
(*     rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia. *)
(*     destruct (0 <? Z.twos_complement machine_wordsize d1); *)
(*       destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]. *)
(*     + rewrite Zmod_odd,!Z.twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add]. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !Z.twos_complement_opp_spec   *)
(*         by (try rewrite Z.twos_complement_opp_spec; nia). *)
(*       assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia). *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia. *)
(*     + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia. *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia. *)
(*     + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia. *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia. *)
(*     + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r. *)
(*       rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia. *)
(*       repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; lia. *)
(*       Unshelve. all: lia || assumption. Qed. *)

(* Theorem twos_complement_word_full_divstep_iter_correct *)
(*         machine_wordsize d f g u v q r n K *)
(*         (fodd : Z.odd f = true) *)
(*         (HK : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2)) *)
(*         (HK2 : 0 < K) *)
(*         (mw1 : 2 < machine_wordsize) *)
(*         (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <= *)
(*                       Z.twos_complement machine_wordsize d <= *)
(*                       2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) *)
(*         (overflow_f : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize f < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_g : - 2 ^ (machine_wordsize - 2) < *)
(*                       Z.twos_complement machine_wordsize g < *)
(*                       2 ^ (machine_wordsize - 2)) *)
(*         (overflow_u : - K <= *)
(*                       Z.twos_complement machine_wordsize u <= *)
(*                       K) *)
(*         (overflow_v : - K <= *)
(*                       Z.twos_complement machine_wordsize v <= *)
(*                       K) *)
(*         (overflow_q : - K <= *)
(*                       Z.twos_complement machine_wordsize q <= *)
(*                       K) *)
(*         (overflow_r : - K <= *)
(*                       Z.twos_complement machine_wordsize r <= *)
(*                       K) *)
(*         (Hf2 : 0 <= f < 2^machine_wordsize) *)
(*         (Hg2 : 0 <= g < 2^machine_wordsize) *)
(*         (u_pos : 0 <= u < 2 ^ machine_wordsize) *)
(*         (v_pos : 0 <= v < 2 ^ machine_wordsize) *)
(*         (q_pos : 0 <= q < 2 ^ machine_wordsize) *)
(*         (r_pos : 0 <= r < 2 ^ machine_wordsize) : *)
(*   let '(d1,f1,g1,u1,v1,q1,r1) := *)
(*       fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r)  in *)
(*   (Z.twos_complement machine_wordsize d1, *)
(*    Z.twos_complement machine_wordsize f1, *)
(*    Z.twos_complement machine_wordsize g1, *)
(*    Z.twos_complement machine_wordsize u1, *)
(*    Z.twos_complement machine_wordsize v1, *)
(*    Z.twos_complement machine_wordsize q1, *)
(*    Z.twos_complement machine_wordsize r1) = *)
(*     Nat.iter n divstep_uvqr *)
(*              (Z.twos_complement machine_wordsize d, *)
(*                Z.twos_complement machine_wordsize f, *)
(*                Z.twos_complement machine_wordsize g, *)
(*                Z.twos_complement machine_wordsize u, *)
(*                Z.twos_complement machine_wordsize v, *)
(*                Z.twos_complement machine_wordsize q, *)
(*                Z.twos_complement machine_wordsize r). *)
(* Proof. *)
(*   assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia). *)
(*   assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by *)
(*       (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia). *)

(*   induction n; intros. *)
(*   - reflexivity. *)
(*   - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia. *)
(*     rewrite <- Z.pow_mul_base in * by lia. *)

(*     epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d. *)
(*     epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _. *)
(*     epose proof twos_complement_word_full_divsteps_bounds machine_wordsize d f g u v q r n K _ _ _ _ _ _ _ _ _ _ _ _ _. *)
(*     rewrite Nat_iter_S. *)
(*     rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add]. *)
(*     destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E. *)
(*     rewrite <- IHn by lia. *)
(*     cbn -[Z.mul Z.add]. *)
(*     unfold divstep_uvqr. *)
(*     rewrite !Zselect.Z.zselect_correct, Z.twos_complement_odd, Z.twos_complement_pos_spec, Zmod_odd by lia. *)

(*     destruct (0 <? Z.twos_complement machine_wordsize d1); *)
(*       destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]. *)
(*     + rewrite Zmod_odd, Z.twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add]. *)
(*       repeat apply f_equal2; try reflexivity. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_opp_spec, Z.twos_complement_one; *)
(*           try rewrite ?Z.twos_complement_opp_spec, ?Z.twos_complement_one; lia. *)
(*       * rewrite Z.arithmetic_shiftr1_spec by (try apply Z.mod_pos_bound; lia). *)
(*         rewrite Z.twos_complement_mod by lia. *)
(*         rewrite Z.twos_complement_add_full by (try rewrite Z.twos_complement_opp_spec; lia). *)
(*         rewrite Z.twos_complement_opp_spec by lia. apply f_equal2; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; try rewrite Z.twos_complement_opp_spec; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; try rewrite Z.twos_complement_opp_spec; lia. *)
(*     + rewrite !Zmod_odd, g1odd, !Z.add_0_r by lia; cbn -[Z.mul Z.add]. *)
(*       t; try reflexivity. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one; *)
(*           try rewrite Z.twos_complement_one; lia. *)
(*       * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod; try apply Z.mod_pos_bound; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod; lia. *)
(*       * rewrite Z.twos_complement_mod; lia. *)
(*     + rewrite !Zmod_odd, g1odd by lia; cbn -[Z.mul Z.add]. *)
(*       t; try reflexivity. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one; try rewrite Z.twos_complement_one; lia. *)
(*       * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod, Z.twos_complement_add_full; try apply Z.mod_pos_bound; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*     + rewrite !Zmod_odd, g1odd, !Z.add_0_r by lia; cbn -[Z.mul Z.add]. *)
(*       t; try reflexivity. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one; try rewrite Z.twos_complement_one; lia. *)
(*       * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod; try apply Z.mod_pos_bound; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia. *)
(*       * rewrite Z.twos_complement_mod; lia. *)
(*       * rewrite Z.twos_complement_mod; lia. *)

(*         Unshelve. all: try lia. all: try assumption. *)
(* Qed. *)

Theorem twos_complement_word_full_divstep_iter_correct
        machine_wordsize d f g u v q r n K
        (fodd : Z.odd f = true)
        (HK : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2))
        (HK2 : 0 < K)
        (mw1 : 2 < machine_wordsize)
        (nmw : n < machine_wordsize)
        (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <=
                      Z.twos_complement machine_wordsize d <=
                      2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)
        (overflow_u : - K <=
                      Z.twos_complement machine_wordsize u <=
                      K)
        (overflow_v : - K <=
                      Z.twos_complement machine_wordsize v <=
                      K)
        (overflow_q : - K <=
                      Z.twos_complement machine_wordsize q <=
                      K)
        (overflow_r : - K <=
                      Z.twos_complement machine_wordsize r <=
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
    let '(d1',f1',g1',u1',v1',q1',r1') :=
      Nat.iter n divstep_uvqr
               (Z.twos_complement machine_wordsize d,
                 f,
                 g,
                 Z.twos_complement machine_wordsize u,
                 Z.twos_complement machine_wordsize v,
                 Z.twos_complement machine_wordsize q,
                 Z.twos_complement machine_wordsize r) in
  (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1',v1',q1',r1').
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
      (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

  induction n.
  - simpl. splits; try reflexivity; rewrite Z.sub_0_r; rewrite Z.twos_complement_mod'; auto.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    rewrite <- Z.pow_mul_base in * by lia.

    epose proof twos_complement_word_full_divsteps_d_bound _ _ f g u v q r n _ _ _ overflow_d.
    epose proof twos_complement_word_full_divsteps_f_odd machine_wordsize d f g u v q r n _ _.
    epose proof twos_complement_word_full_divsteps_bounds machine_wordsize d f g u v q r n K _ _ _ _ _ _ _ _ _ _ _ _ _.
    rewrite Nat_iter_S.

    rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add].
    destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
    destruct (Nat.iter _ _ _) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2 .

    assert ((Z.twos_complement machine_wordsize d1, Z.twos_complement machine_wordsize f1 mod 2 ^ (machine_wordsize - Z.of_nat n),
        Z.twos_complement machine_wordsize g1 mod 2 ^ (machine_wordsize - Z.of_nat n), Z.twos_complement machine_wordsize u1,
        Z.twos_complement machine_wordsize v1, Z.twos_complement machine_wordsize q1, Z.twos_complement machine_wordsize r1) =
        (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1', v1', q1', r1')).
    apply IHn; lia.
    inversion H4.

    rewrite Z.twos_complement_mod_smaller_pow in H7 by lia.
    rewrite Z.twos_complement_mod_smaller_pow in H8 by lia.

    cbn -[Z.mul Z.add].
    unfold divstep_uvqr.
    rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia.


    assert (Z.odd g1 = Z.odd g1').
    { rewrite <- (Z.odd_mod2m (machine_wordsize - Z.of_nat n) g1'), <- H8, Z.odd_mod2m by lia; reflexivity. }
    rewrite <- H5.
    destruct (0 <? Z.twos_complement machine_wordsize d1);
      destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
    + rewrite Zmod_odd, Z.twos_complement_opp_odd by (try assumption; lia).
      cbn -[Z.mul Z.add].
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_opp_spec, Z.twos_complement_one by
            (try rewrite Z.twos_complement_opp_spec, Z.twos_complement_one; lia); lia.
      *
        rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)) by lia.
        rewrite H8, Z.mod_pow_same_base_smaller; lia.
      * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
        rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
        apply f_equal2; [|reflexivity].
        replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
            (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
        rewrite Z.twos_complement_opp_correct, Z.twos_complement_mod_smaller_pow, <- Zplus_mod_idemp_l, Z.mod_pow_same_base_smaller, Zplus_mod_idemp_l by lia.
        push_Zmod. rewrite H7, H8. pull_Zmod.
        apply f_equal2; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full,Z.twos_complement_opp_spec; try rewrite Z.twos_complement_opp_spec; lia.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_opp_spec; try rewrite Z.twos_complement_opp_spec; lia.
    + rewrite !Zmod_odd, g1odd, !Z.add_0_r by lia; cbn -[Z.mul Z.add]. splits.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one;
          try rewrite Z.twos_complement_one; lia.
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
    + rewrite !Zmod_odd, g1odd by lia; cbn -[Z.mul Z.add]. splits.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one;
          try rewrite Z.twos_complement_one; lia.
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
    + rewrite !Zmod_odd, g1odd, !Z.add_0_r by lia; cbn -[Z.mul Z.add]. splits.
      * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one;
          try rewrite Z.twos_complement_one; lia.
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

(* Lemma divstep_full_iter_full'_iter m d f g u2 v1 v2 q2 r1 r2 n : *)
(*   let '(d1,f1,g1,_,_) := *)
(*       Nat.iter n (divstep_vr_mod m) (d, f, g, v1, r1) in *)
(*   (d1,f1,g1) *)
(*   = let '(d2,f2,g2,_,_,_,_) := Nat.iter n divstep_uvqr (d, f, g, u2, v2, q2, r2) in *)
(*     (d2,f2,g2). *)
(* Proof. *)
(*   induction n; simpl. *)
(*   - reflexivity. *)
(*   - destruct Nat.iter as [[[[?]?]?]?]. *)
(*     destruct Nat.iter as [[[[[[?]?]?]?]?]?]. *)
(*     inversion IHn. *)
(*     unfold divstep_uvqr. *)
(*     unfold divstep_spec_full. *)
(*     destruct (0 <? z4); destruct (Z.odd z6); cbn -[Z.add Z.mul Z.div Z.sub]; reflexivity. *)
(* Qed. *)

(* Lemma divstep_full_iter_f_odd m f g v r n *)
(*   (fodd : Z.odd f = true) : *)
(*   let '(_,f,_,_,_) := divstep_full_iter m 1 f g v r n in Z.odd f = true. *)
(* Proof. *)
(*   induction n; simpl. *)
(*   - assumption. *)
(*   - unfold divstep_spec_full. *)
(*     destruct (divstep_full_iter m 1 f g v r n) as [[[[d1 f1]g1]v1]r1]. *)
(*     destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption. *)
(* Qed. *)

(* Lemma divstep_full'_iter_f_odd d f g u v q r n *)
(*   (fodd : Z.odd f = true) : *)
(*   let '(_,f,_,_,_,_,_) := Nat.iter n divstep_uvqr (d, f, g, u, v, q, r) in *)
(*   Z.odd f = true. *)
(* Proof. *)
(*   induction n; simpl. *)
(*   - assumption. *)
(*   - unfold divstep_uvqr. *)
(*     destruct Nat.iter as [[[[[[d1 f1]g1]u1]v1]q1]r1]. *)
(*     destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption. *)
(* Qed. *)

(* Lemma divstep_full'_iter_important_bits d f f0 g g0 u v q r n k *)
(*       (Hk : (0 <= n < k)%nat) *)
(*       (fodd : Z.odd f = true) *)
(*       (fmod : f mod 2 ^ Z.of_nat k = f0 mod 2 ^ Z.of_nat k) *)
(*       (gmod : g mod 2 ^ Z.of_nat k = g0 mod 2 ^ Z.of_nat k) : *)
(*   let '(d1,f1,g1,u1,v1,q1,r1) := *)
(*       Nat.iter n divstep_uvqr (d, f, g, u, v, q, r) in *)
(*   let '(d2,f2,g2,u2,v2,q2,r2) := *)
(*       Nat.iter n divstep_uvqr (d, f0, g0, u, v, q, r) in *)
(*   g1 mod 2 ^ (k - n) = g2 mod 2 ^ (k - n) /\ *)
(*   f1 mod 2 ^ (k - n) = f2 mod 2 ^ (k - n) /\ *)
(*   d1 = d2 /\ *)
(*   (u1,v1,q1,r1) = (u2,v2,q2,r2). *)
(* Proof. *)
(*   induction n. *)
(*   - cbn in *. rewrite !Z.sub_0_r. repeat split; lia. *)
(*   - simpl. *)

(*     pose proof divstep_full'_iter_f_odd d f g u v q r n. *)
(*     pose proof divstep_full'_iter_f_odd d f0 g0 u v q r n. *)

(*     destruct Nat.iter as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1. *)
(*     destruct (Nat.iter _ _ (_,f0,_,_,_,_,_)) as [[[[[[d2 f2] g2] u2] v2] q2] r2] eqn:E2. *)

(*     specialize (H fodd). *)
(*     assert (Z.odd f0 = true). *)
(*     { rewrite <- Z.odd_mod2m with (m:=k), <- fmod, Z.odd_mod2m; try assumption; lia. } *)

(*     assert (g1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = g2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\ *)
(*             f1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = f2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\ *)
(*             d1 = d2 /\ (u1, v1, q1, r1) = (u2, v2, q2, r2)) by (apply IHn; lia). *)

(*     destruct H2 as [H3 [H4 [H5 H6]]]. *)

(*     assert (Z.odd g1 = Z.odd g2 /\ d1 = d2). *)
(*     { rewrite <- Z.odd_mod2m with (m:=k - n), H3, Z.odd_mod2m by lia; split; reflexivity || lia. } *)

(*     unfold divstep_uvqr. destruct H2. rewrite H7, H2. *)
(*     inversion H6. *)

(*     destruct (0 <? d2); destruct (Z.odd g2) eqn:odd; cbn -[Z.mul Z.add Z.div]. *)
(*     + split; [|split;[|split]]; try lia; try congruence. *)
(*       * rewrite !Z.mod_pull_div, Z.mul_comm, Z.pow_mul_base by (try apply Z.pow_nonneg; lia). *)
(*         replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia. *)
(*         push_Zmod. rewrite H3, H4. reflexivity. *)
(*       * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, Z.mod_pow_same_base_smaller; lia. *)
(*     + split; [|split;[|split]]; try reflexivity. *)
(*       * rewrite !Z.mod_pull_div, (Z.mul_comm _ 2), Z.pow_mul_base by (try apply Z.pow_nonneg; lia). *)
(*         replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia. *)
(*         f_equal. assumption. *)
(*       * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H4, Z.mod_pow_same_base_smaller; lia. *)
(*     + split; [|split;[|split]]; try reflexivity. *)
(*       * rewrite !Z.mod_pull_div, (Z.mul_comm _ 2), Z.pow_mul_base by (try apply Z.pow_nonneg; lia). *)
(*         replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia. *)
(*         f_equal. push_Zmod. rewrite H3, H4. reflexivity. *)
(*       * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H4, Z.mod_pow_same_base_smaller; lia. *)
(*     + split; [|split;[|split]]; try reflexivity. *)
(*       * rewrite !Z.mod_pull_div, (Z.mul_comm _ 2), Z.pow_mul_base by (try apply Z.pow_nonneg; lia). *)
(*         replace (Z.of_nat k - Z.pos (Pos.of_succ_nat n) + 1) with (Z.of_nat k - Z.of_nat n) by lia. *)
(*         f_equal. push_Zmod. assumption.  *)
(*       * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H4, Z.mod_pow_same_base_smaller; lia. *)
(* Qed. *)

(* Lemma important_bits_cor d f f0 g g0 u v q r n k *)
(*       (Hk : (0 <= n < k)%nat) *)
(*       (fodd : Z.odd f = true) *)
(*       (fmod : f mod 2 ^ Z.of_nat k = f0 mod 2 ^ Z.of_nat k) *)
(*       (gmod : g mod 2 ^ Z.of_nat k = g0 mod 2 ^ Z.of_nat k) : *)
(*   Nat.iter n divstep_uvqr (d, f, g, u, v, q, r) = *)
(*     Nat.iter n divstep_uvqr (d, f0, g0, u, v, q, r). *)
(* Proof. *)
(*   pose proof divstep_full'_iter_important_bits d f f0 g g0 u v q r n k Hk fodd fmod gmod. *)


(* Lemma jump_divstep_full_iter m f g v r n *)
(*       (fodd : Z.odd f = true) *)
(*       (Hv : 0 <= v < m) *)
(*       (Hr : 0 <= r < m) *)
(*   : *)
(*     let '(d1, f1, g1, v1, r1) := divstep_full_iter m 1 f g v r n in *)
(*     (d1,2 ^ n * f1,2 ^ n * g1,v1,r1) *)
(*   = let '(d1', f1', g1', u1', v1', q1', r1') := divstep_uvqr_iter 1 f g 1 0 0 1 n in *)
(*     (d1', (u1' * f + v1' * g), (q1' * f + r1' * g), (u1' * v + v1' * r) mod m, (q1' * v + r1' * r) mod m). *)
(* Proof. *)
(*   induction n. *)
(*   - cbn -[Z.add Z.mul]. *)
(*     repeat match goal with *)
(*            | [ |- (_, _) = (_, _) ] => apply f_equal2; rewrite ?Z.div_1_r, ?Z.mod_small by lia; try lia *)
(*            end. *)
(*   - cbn -[Z.pow Z.mul Z.add Z.of_nat]. *)
(*     pose proof divstep_full_iter_full'_iter m 1 f g 1 v 0 0 r 1 n. *)
(*     pose proof divstep_full_iter_f_odd m f g v r n fodd as fodd1. *)

(*     destruct (divstep_uvqr_iter 1 f g 1 0 0 1 n) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1. *)
(*     destruct (divstep_full_iter m 1 f g v r n) as [[[[d2 f2] g2] v2] r2] eqn:E2. *)

(*     replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia. *)
(*     rewrite <- Z.pow_mul_base by lia. *)
(*     unfold divstep_spec_full, divstep_uvqr. *)
(*     inversion H. *)
(*     inversion IHn; subst. *)
(*     destruct (0 <? d1); destruct (Z.odd g1) eqn:godd; cbn -[Z.mul Z.add Z.div Z.of_nat]; *)
(*       repeat match goal with *)
(*              | [ |- (_, _) = (_, _) ] => apply f_equal2; try (push_Zmod; pull_Zmod; apply f_equal2; lia) *)
(*              end; try lia. *)
(*     rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', Zmod_odd, Z.odd_sub, godd, fodd1; cbn; lia. *)
(*     rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', !Zmod_odd, godd, Z.add_0_r, godd; lia. *)
(*     rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', !Zmod_odd, godd, Z.mul_1_l, Z.odd_add, godd, fodd1, Z.sub_0_r; lia. *)
(*     rewrite <- Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc, Z.mul_div_eq', Zmod_odd, godd, Z.mul_0_l, Z.add_0_r, Zmod_odd, godd; lia. *)
(* Qed. *)

(* Lemma jump_divstep_full m f f0 g g0 v r n *)
(*       (fodd : Z.odd f = true) *)
(*       (Hm : 1 < m) *)
(*       (Hv : 0 <= v < m) *)
(*       (Hr : 0 <= r < m) *)
(*       (Hf : f mod 2 ^ (Z.of_nat (S n)) = f0 mod 2 ^ (Z.of_nat (S n))) *)
(*       (Hg : g mod 2 ^ (Z.of_nat (S n)) = g0 mod 2 ^ (Z.of_nat (S n))) *)
(*   : *)
(*   divstep_full_iter m 1 f g v r n *)
(*   = let '(d1', f1', g1', u1', v1', q1', r1') := divstep_uvqr_iter 1 f0 g0 1 0 0 1 n in *)
(*     (d1', (u1' * f + v1' * g) / 2 ^ n, (q1' * f + r1' * g) / 2 ^ n, (u1' * v + v1' * r) mod m, (q1' * v + r1' * r) mod m). *)
(* Proof. *)
(*   assert (f0odd : Z.odd f0 = true). *)
(*   { rewrite <- Z.odd_mod2m with (m:=S n), <- Hf, Z.odd_mod2m; try assumption; lia. } *)

(*   pose proof jump_divstep_full_iter m f g v r n fodd Hv Hr. *)
(*   pose proof divstep_full'_iter_important_bits 1 f f0 g g0 1 0 0 1 n (S n) ltac:(lia) fodd Hf Hg. *)

(*   destruct (divstep_full_iter m 1 f g v r n) as [[[[d1 f1] g1] v1] r1] eqn:E1. *)
(*   destruct (divstep_uvqr_iter 1 f g 1 0 0 1 n) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2. *)
(*   destruct (divstep_uvqr_iter 1 f0 g0 1 0 0 1 n) as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3. *)
(*   destruct H0 as [H1 [H2 [H3 H4]]]. *)

(*   inversion H; inversion H4; subst. *)

(*   apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H6. *)
(*   apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H7. *)
(*   rewrite Z.div_mul' in * by (apply Z.pow_nonzero; lia). *)
(*   congruence. *)
(* Qed. *)

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

(* Definition jump_divstep_vr n mw m '(d, f, g, v, r) := *)
(*   let '(d1, f1, g1, u1, v1, q1, r1) := Nat.iter n divstep_uvqr (d, f mod 2 ^ mw, g mod 2 ^ mw, 1, 0, 0, 1) in *)
(*   let f1' := (u1 * f + v1 * g) / 2 ^ n in *)
(*   let g1' := (q1 * f + r1 * g) / 2 ^ n in *)
(*   let v1' := (u1 * v + v1 * r) mod m in *)
(*   let r1' := (q1 * v + r1 * r) mod m in *)
(*   (d1, f1', g1', v1', r1'). *)

Lemma pow_ineq k : (2 <= k)%nat -> k + 2 <= Zpower_nat 2 k.
Proof. induction k as [|[|[|k]]]; [lia|lia|simpl; lia|rewrite Zpower_nat_succ_r; lia]; intros. Qed.

Lemma pow_ineq_Z k : 2 <= k -> k + 2 <= 2 ^ k.
Proof. intros. replace k with (Z.of_nat (Z.to_nat k)) by lia. rewrite <- Zpower_nat_Z. apply pow_ineq; lia. Qed.

Module WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.
  Import BYInv.WordByWordMontgomery.

  Lemma mulmod_valid machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> forall g, valid machine_wordsize mont_limbs m g -> valid machine_wordsize mont_limbs m (mulmod machine_wordsize mont_limbs m m' f g).
  Proof.
    intros.
    epose proof (mulmod_correct machine_wordsize mont_limbs m r' m' _ _ _ _ _ _) as [_ h]. apply h; assumption.
    Unshelve. all: assumption.
  Qed.

  Lemma length_mulmod machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> forall g, valid machine_wordsize mont_limbs m g -> length (mulmod machine_wordsize mont_limbs m m' f g) = mont_limbs.
  Proof.
    intros.
    unshelve epose proof mulmod_valid machine_wordsize mont_limbs m r' m' _ _ _ _ _ _ f _ g _; try assumption.
    eapply length_small.
    apply H7.
  Qed.

  Lemma twos_complement_word_to_montgomery_no_encode_correct machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    (1 < mont_limbs)%nat ->
    forall a, 0 <= a < 2 ^ machine_wordsize ->
    @WordByWordMontgomery.eval machine_wordsize mont_limbs (twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m a) mod m = Z.twos_complement machine_wordsize a mod m
    /\ valid machine_wordsize mont_limbs m (twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m a).
  Proof.
    intros.
    (* assert (2 < 2 ^ machine_wordsize) by (eapply Z.pow_pos_lt; lia). *)
    assert (2 ^ (machine_wordsize) <= 2 ^ (machine_wordsize * Z.of_nat mont_limbs)) by
      (apply Z.pow_le_mono_r; nia).
    unfold twos_complement_word_to_montgomery_no_encode.
    assert (valid machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs (Z.twos_complement_opp machine_wordsize a))).
    { unfold valid, small.
      pose proof Z.mod_pos_bound (-a) (2^machine_wordsize) ltac:(apply Z.pow_pos_nonneg; lia).
      split; unfold eval.
      rewrite eval_partition, uweight_eq_alt', Z.mod_small by
        (try rewrite Z.twos_complement_opp_correct; try apply uwprops; nia); reflexivity.
      rewrite eval_partition, uweight_eq_alt', Z.twos_complement_opp_correct, Z.mod_pow_same_base_larger;
        try apply uwprops; nia. }
    pose proof (Hvalid := oppmod_correct machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite twos_complement_neg_spec, !unfold_Let_In, select_eq with (n:=mont_limbs); try (try rewrite length_partition; lia);
      try (apply length_small with (lgr:=machine_wordsize); apply Hvalid; assumption); try apply (uweight machine_wordsize).

    unfold Z.twos_complement.
    rewrite Z.twos_complement_cond_equiv by lia.

    destruct (Z.testbit a (machine_wordsize - 1)) eqn:E; cbn -[Partition.partition oppmod]; split.
    - replace (@WordByWordMontgomery.eval machine_wordsize mont_limbs (oppmod machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs (Z.twos_complement_opp machine_wordsize a)))) with
        (@WordByWordMontgomery.eval machine_wordsize mont_limbs (oppmod machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs (Z.twos_complement_opp machine_wordsize a))) * (1 ^ mont_limbs)) by (rewrite Z.pow_1_l; lia).

      rewrite <- H. push_Zmod; pull_Zmod.
      rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)),  <- Zmult_mod_idemp_l,  <- eval_from_montgomerymod with (m':=m'), eval_oppmod with (r':=r'); try lia; try (try apply Hvalid; assumption).
      push_Zmod. rewrite eval_from_montgomerymod with (r':=r'); try lia; try (try apply Hvalid; assumption).
      push_Zmod. unfold eval; rewrite eval_partition by (apply uwprops; lia).
      rewrite Z.twos_complement_opp_correct. pull_Zmod.
      rewrite uweight_eq_alt', Z.mod_pow_same_base_larger, Z.mul_opp_l, <- Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), PullPush.Z.opp_mod_mod, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, H, Z.pow_1_l by nia. pull_Zmod. rewrite Z.mul_1_r.
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

  Lemma eval_twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    (1 < mont_limbs)%nat ->
    forall a, 0 <= a < 2 ^ machine_wordsize ->
    @WordByWordMontgomery.eval machine_wordsize mont_limbs (twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m a) mod m = Z.twos_complement machine_wordsize a mod m.
  Proof. apply twos_complement_word_to_montgomery_no_encode_correct; assumption. Qed.

  Lemma twos_complement_word_to_montgomery_no_encode_valid machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    (1 < mont_limbs)%nat ->
    forall a, 0 <= a < 2 ^ machine_wordsize ->
    valid machine_wordsize mont_limbs m (twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m a).
  Proof. apply twos_complement_word_to_montgomery_no_encode_correct; assumption. Qed.

  Lemma length_twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m :
    0 < machine_wordsize ->
    forall a, length (twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m a) = mont_limbs.
  Proof.
    intros. unfold twos_complement_word_to_montgomery_no_encode. rewrite !unfold_Let_In.
    apply length_select. apply length_partition. apply length_oppmod. assumption. apply length_partition.
  Qed.

  Lemma partition_1 machine_wordsize n : (0 < machine_wordsize) -> (0 < n)%nat -> partition (uweight machine_wordsize) n 1 = one n.
  Proof.
    destruct n.
    - lia.
    - induction n.
      + unfold partition; intros.
        simpl.
        rewrite !uweight_eq_alt'.
        rewrite Z.mul_0_r.
        rewrite Z.pow_0_r.
        rewrite Z.div_1_r.
        rewrite Z.mul_1_r.
        rewrite Z.mod_1_l.
        reflexivity.
        apply Z.pow_gt_1. lia. assumption.
      + intros.
        assert (1 < uweight machine_wordsize (S n)).
        { rewrite uweight_eq_alt'. apply Z.pow_gt_1. lia. nia. }
        assert (1 < uweight machine_wordsize (S (S n))).
        { rewrite uweight_eq_alt'. apply Z.pow_gt_1. lia. nia. }
        rewrite partition_step.
        rewrite Z.mod_small.
        rewrite Z.div_1_l.
        rewrite IHn.
        unfold one.
        simpl. rewrite Nat.sub_0_r.
        all: try lia.
        unfold zeros.
        rewrite <- repeat_cons.
        reflexivity.
  Qed.

  Lemma one_valid machine_wordsize mont_limbs m :
    0 < machine_wordsize ->
    (0 < mont_limbs)%nat ->
    1 < m ->
    valid machine_wordsize mont_limbs m (one mont_limbs).
  Proof.
    intros. unfold valid, small, WordByWordMontgomery.eval.
    rewrite eval_one, partition_1; try split; auto; lia.
  Qed.

  #[global] Hint Resolve mulmod_valid twos_complement_word_to_montgomery_no_encode_valid one_valid : valid.

  #[global] Hint Resolve length_mulmod length_twos_complement_word_to_montgomery_no_encode firstn_length_le word_tc_mul_length arithmetic_shiftr_length length_one length_partition : len.
  #[global] Hint Extern 3 (_ < _) => lia : len.
  #[global] Hint Extern 3 (_ <= _) => lia : len.
  #[global] Hint Extern 3 (_ <= _ < _) => lia : len.
  #[global] Hint Extern 4 (_ < _)%nat => lia : len.
  #[global] Hint Extern 4 (_ <= _)%nat => lia : len.
  #[global] Hint Extern 4 (_ <= _)%nat => progress autorewrite with length_distr; auto with len : len.
  #[global] Hint Extern 3 (valid _ _ _ _) => auto with valid : len.

  #[global] Hint Extern 3 (_ < _) => lia : valid.
  #[global] Hint Extern 3 (_ <= _) => lia : valid.
  #[global] Hint Extern 3 (_ <= _ < _) => lia : valid.
  #[global] Hint Extern 4 (_ < _)%nat => lia : valid.
  #[global] Hint Extern 4 (_ <= _)%nat => lia : valid.

  Lemma partition_in_bounded machine_wordsize limbs a :
    (0 < machine_wordsize) ->
    in_bounded machine_wordsize (partition (uweight machine_wordsize) limbs a).
  Proof.
    intros mw0.
    pose proof uwprops machine_wordsize mw0.
    intros x Hin.
    unfold partition in Hin. apply ListAux.in_map_inv in Hin.
    destruct Hin as [y [Hin]].
    rewrite H0, !uweight_eq_alt by lia. split.
    - apply Z.div_le_lower_bound;
        ring_simplify; try apply Z.mod_pos_bound;
        apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
    - apply Z.div_lt_upper_bound.
      apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
      replace ((_ ^ _) ^ _ * _) with ((2 ^ machine_wordsize) ^ Z.of_nat (S y)).
      apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
      rewrite Z.mul_comm, Pow.Z.pow_mul_base;
        try (replace (Z.of_nat (S y)) with ((Z.of_nat y + 1)) by lia; lia).
  Qed.

  #[global] Hint Resolve firstn_in_bounded partition_in_bounded : in_bounded.

  Section __.

    Context
      (machine_wordsize : Z)
      (tc_limbs : nat)
      (mont_limbs : nat)
      (word_tc_mul_limbs : nat)
      (m : Z)
      (m_bounds : 2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs))
      (r' : Z)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m' : Z)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (mw2 : 2 < machine_wordsize)
      (tc_limbs0 : (0 < tc_limbs)%nat)
      (mont_limbs1 : (1 < mont_limbs)%nat)
      (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + tc_limbs)%nat).

    Notation jump_divstep := (jump_divstep machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    Notation eval := (@WordByWordMontgomery.eval machine_wordsize mont_limbs).
    Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    Notation tc := (Z.twos_complement machine_wordsize).
    Notation divstep_aux := (divstep_aux machine_wordsize tc_limbs mont_limbs m).
    Notation divstep := (divstep machine_wordsize tc_limbs mont_limbs m).
    Notation jump_divstep_aux := (jump_divstep_aux machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    Notation valid := (valid machine_wordsize mont_limbs m).
    Notation tc_wtmne := (twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m).
    Notation mulmod := (mulmod machine_wordsize mont_limbs m m').
    Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    Notation from_montgomerymod := (from_montgomerymod machine_wordsize mont_limbs m m').
    Notation in_bounded := (in_bounded machine_wordsize).
    Notation jumpdivstep_precompmod := (jumpdivstep_precompmod machine_wordsize mont_limbs m).
    Notation partition_precomp := (partition_precomp machine_wordsize mont_limbs m).
    Notation by_inv_jump := (by_inv_jump machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').

    #[local] Hint Resolve
         (length_addmod machine_wordsize mont_limbs m ltac:(lia))
         (length_oppmod machine_wordsize mont_limbs m ltac:(lia))
         (length_mulmod machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (length_twos_complement_word_to_montgomery_no_encode machine_wordsize mont_limbs m ltac:(lia))
      : len.

    #[local] Hint Resolve
         (zero_valid machine_wordsize mont_limbs m ltac:(lia))
         (addmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (oppmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (mulmod_valid machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (twos_complement_word_to_montgomery_no_encode_valid machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia))
      : valid.

    Ltac t := repeat match goal with
                     | |- valid _ => auto with valid
                     | |- length _ = _ => auto with len
                     | |- in_bounded _ => auto with in_bounded
                     | |- _ => assumption
                     | |- _ => lia
                     end.

    Lemma tc_eval_mod2m f :
      tc_eval f mod 2 ^ machine_wordsize = Positional.eval (uweight machine_wordsize) tc_limbs f mod 2 ^ machine_wordsize.
    Proof.
      unfold tc_eval.
      rewrite Z.twos_complement_mod_smaller_pow.  reflexivity. nia.
    Qed.

    (** Correctness of outer loop body  *)
    Theorem jump_divstep_correct d f g v r
            (f_odd : Z.odd (tc_eval f) = true)
            (Hf : length f = tc_limbs)
            (Hg : length g = tc_limbs)
            (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2)) < tc d <
                          2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2))
            (overflow_f : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
            (overflow_g : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
            (Hf2 : in_bounded f)
            (Hg2 : in_bounded g)
            (Hr : valid r)
            (Hv : valid v) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d, f, g, v, r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m)
      = jump_divstep_vr (Z.to_nat (machine_wordsize - 2)) machine_wordsize m
                        (tc d, tc_eval f, tc_eval g, (eval v * r' ^ (Z.of_nat mont_limbs)) mod m, (eval r * r' ^ (Z.of_nat mont_limbs)) mod m).
    Proof.
      pose proof (pow_ineq_Z (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (0 < 2 ^ (machine_wordsize - 1))
        by (apply Z.pow_pos_nonneg; lia).
      assert (0 < 2 ^ (machine_wordsize - 2))
        by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1))
        by (rewrite Z.mul_comm, Z.pow_mul_base by lia; apply f_equal2; lia).
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + tc_limbs)) - 1))
        by (rewrite <- Zpower_exp, !Z.pow_mul_base by nia; apply f_equal2; nia).

      unfold jump_divstep_aux.
      epose proof twos_complement_word_full_divstep_iter_correct (machine_wordsize) d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
      epose proof twos_complement_word_full_divsteps_bounds (machine_wordsize) d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _.

      unfold jump_divstep_vr.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      rewrite Z.twos_complement_one, Z.twos_complement_zero in * by lia.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.

      destruct (    fold_left (fun (i : Z * Z * Z * Z * Z * Z * Z) (_ : nat) => twos_complement_word_full_divstep_aux machine_wordsize i)
                              (seq 0 (Z.to_nat (machine_wordsize - 2))) (d, nth_default 0 f 0, nth_default 0 g 0, 1, 0, 0, 1)) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
      destruct H6 as [u1_bounds [v1_bounds [q1_bounds [r1_bounds [u1_pos [v1_pos [q1_pos r1_pos]]]]]]].

      rewrite !tc_eval_mod2m by t.
      rewrite <- !eval_nth_default_0 by t.

      set (f0 := nth_default 0 f 0) in *.
      set (g0 := nth_default 0 g 0) in *.

      destruct Nat.iter
        as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3.

      assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; nia).

      rewrite !unfold_Let_In by t.

      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.

      + congruence.
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval_small with (n:=(1 + tc_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full, !word_tc_mul_correct; t. inversion H5. reflexivity.
        rewrite !word_tc_mul_correct; t. nia.
        eapply tc_eval_arithmetic_shiftr_bounds; t. nia. nia.
        rewrite tc_eval_tc_add_full, !word_tc_mul_correct, Z.pow_add_r; t. nia. nia.
        rewrite !word_tc_mul_correct; t. nia.
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval_small with (n:=(1 + tc_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full, !word_tc_mul_correct; t. inversion H5. reflexivity.
        rewrite !word_tc_mul_correct; t. nia.
        eapply tc_eval_arithmetic_shiftr_bounds; t. nia. nia.
        rewrite tc_eval_tc_add_full, !word_tc_mul_correct, Z.pow_add_r; t. nia. nia.
        rewrite !word_tc_mul_correct; t. nia.
      + rewrite <- (Z.mul_1_r (eval _)), <- (Z.pow_1_l mont_limbs), <- r'_correct by lia.
        push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)), <- Zmult_mod_idemp_l.
        rewrite <- eval_from_montgomerymod with (m':=m') by t.
        push_Zmod.
        rewrite eval_addmod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_mulmod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_from_montgomerymod with (r':=r') by t.
        push_Zmod.
        rewrite !(eval_twos_complement_word_to_montgomery_no_encode _ _ _ r' m') by t.
        pull_Zmod.
        rewrite Z.mul_add_distr_r, <- !Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), !Z.mul_assoc, <- Z.mul_add_distr_r, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, r'_correct, Z.pow_1_l, Z.mod_1_l, Z.mul_1_r by lia.
        inversion H5.
        push_Zmod; pull_Zmod.
        apply f_equal2; t.
      + rewrite <- (Z.mul_1_r (eval _)), <- (Z.pow_1_l mont_limbs), <- r'_correct by lia.
        push_Zmod; pull_Zmod.
        rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)), <- Zmult_mod_idemp_l.
        rewrite <- eval_from_montgomerymod with (m':=m'), eval_addmod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_mulmod with (r':=r') by t.
        push_Zmod.
        rewrite !eval_from_montgomerymod with (r':=r') by t.
        push_Zmod.
        rewrite !(eval_twos_complement_word_to_montgomery_no_encode _ _ _ r' m') by t.
        pull_Zmod.
        rewrite Z.mul_add_distr_r, <- !Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), !Z.mul_assoc, <- Z.mul_add_distr_r, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, r'_correct, Z.pow_1_l, Z.mod_1_l, Z.mul_1_r by lia.
        inversion H5.
        apply f_equal2; lia.

        Unshelve.
        all: lia || rewrite ?Z.twos_complement_one, ?Z.twos_complement_zero; lia || idtac.
        rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs); try lia.
        unfold tc_eval in f_odd.
        rewrite Z.twos_complement_odd in f_odd.
        rewrite Z.odd_mod2m by lia. assumption. nia. assumption.
        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia. lia.
        apply Hf2. destruct f; simpl in *. lia. left. reflexivity.
        apply Hg2. destruct g; simpl in *. lia. left. reflexivity.

        replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia; lia.
        unfold tc_eval in f_odd.
        rewrite eval_nth_default_0 with (n:=tc_limbs) (m:=machine_wordsize), Z.odd_mod2m by (assumption || lia).
        rewrite Z.twos_complement_odd in f_odd; assumption || nia.
    Qed.

    Lemma jump_divstep_invariants d f g v r
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (f_odd : Z.odd (tc_eval f) = true)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - (machine_wordsize - 2) - 1) < tc d < 2 ^ (machine_wordsize - 1) - (machine_wordsize - 2) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = mont_limbs
      /\ length r1 = mont_limbs
      /\ valid v1
      /\ valid r1
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).

      unfold jump_divstep_aux.

      unshelve epose proof twos_complement_word_full_divsteps_bounds machine_wordsize d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 ltac:(lia) _ ltac:(lia) _ ltac:(nia) ltac:(rewrite Z.twos_complement_one; lia) ltac:(rewrite Z.twos_complement_zero; lia) ltac:(rewrite Z.twos_complement_zero; lia) ltac:(rewrite Z.twos_complement_one; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia).
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia. }
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs), Z.odd_mod2m by (assumption || lia).
        rewrite <- Z.twos_complement_odd with (m:=machine_wordsize * tc_limbs); (assumption || nia). }

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
      destruct (fold_left _ (seq 0 (Z.to_nat _))) as [[[[[[dn fn] gn] un] vn] qn] rn].
      rewrite !word_tc_mul_limbs_eq.

      simpl. repeat (split; t).
    Qed.

    Lemma jump_divstep_invariants2 d f g v r Kd
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (f_odd : Z.odd (tc_eval f) = true)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d,f,g,v,r) in
      Z.odd (tc_eval f1) = true
      /\ - (Kd + (machine_wordsize - 2)) < tc d1 < Kd + (machine_wordsize - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2).
    Proof.
      unshelve epose proof jump_divstep_correct d f g v r _ _ _ _ _ _ _ _ _ _; try assumption; try lia.
      unshelve epose proof jump_divstep_vr_invariants (Z.to_nat (machine_wordsize - 2)) machine_wordsize m (tc d)
               (tc_eval f) (tc_eval g) ((eval v * r' ^ Z.of_nat mont_limbs) mod m) ((eval r * r' ^ Z.of_nat mont_limbs) mod m)
               Kd (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2)) _ _ _ _ _ _ _ _; try assumption; try lia;
        try (apply Z.mod_pos_bound; lia).
      destruct jump_divstep_aux as [[[[d1 f1]g1]v1]r1].
      destruct jump_divstep_vr as [[[[d1' f1']g1']v1']r1'].
      inversion H. subst. repeat (split; easy || lia).
    Qed.

      Lemma jump_divstep_iter_d_bounds d f g v r n K
            (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat n) * (machine_wordsize - 2))
            (d_bounds : - K <= tc d <= K) :
        let '(d1,_,_,_,_) := fold_left (fun data i => jump_divstep_aux data) (seq 0 n) (d,f,g,v,r) in
        - K - Z.of_nat n * (machine_wordsize - 2) <= tc d1 <= K + Z.of_nat n * (machine_wordsize - 2).
      Proof.
        induction n; intros.
        - cbn; lia.
        - rewrite seq_snoc, fold_left_app.
          cbn -[Z.of_nat].
          destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
          specialize (IHn ltac:(lia)).
          unshelve epose proof twos_complement_word_full_divsteps_d_bound machine_wordsize d1 (nth_default 0 f1 0) (nth_default 0 g1 0) 1 0 0 1
                   (Z.to_nat (machine_wordsize - 2))
                   (K + Z.of_nat n * (machine_wordsize - 2)) ltac:(lia) ltac:(lia) ltac:(lia).
          cbn -[Z.of_nat].
          rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
          destruct (fold_left _ (seq 0 (Z.to_nat _))) as [[[[[[dn fn] gn] un] vn] qn] rn].
          cbn -[Z.of_nat].
          nia.
      Qed.

      Lemma firstn_length_le n (f : list Z) :
        (n <= length f)%nat ->
        length (firstn n f) = n.
      Proof.
        intros. rewrite firstn_length, Nat.min_l; auto.
      Qed.

      Lemma jump_divstep_iter_invariants d f g v r n Kd
          (* (n_bounds : (0 < n)%nat) *)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (f_odd : Z.odd (tc_eval f) = true)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - Z.of_nat n * (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) :=
        fold_left (fun data i => jump_divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = mont_limbs
      /\ length r1 = mont_limbs
      /\ Z.odd (tc_eval f1) = true
      /\ - (Kd + Z.of_nat (S n) * (machine_wordsize - 2)) < tc d1 < Kd + Z.of_nat (S n) * (machine_wordsize - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ valid v1
      /\ valid r1
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      induction n.
      - cbn -[Z.add Z.sub Z.of_nat]. repeat (split; try easy); lia.
      - rewrite seq_snoc, fold_left_app. cbn -[Z.add Z.sub Z.of_nat].
        destruct fold_left as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize IHn as [f1_length [g1_length [v1_length [r1_length [f1_odd [d1_bounds [f1_bounds [f1_in_bounds [g1_bounds [g1_in_bounds [v1_valid r1_valid]]]]]]]]]]]. lia.
        unshelve epose proof jump_divstep_invariants d1 f1 g1 v1 r1 _ _ _ _ _ _ _ _ _ _ _ _; try assumption. nia.
        unshelve epose proof jump_divstep_invariants2 d1 f1 g1 v1 r1 (Kd + Z.of_nat (S n) * (machine_wordsize - 2)) _ _ _ _ _ _ _ _ _ _ _ _ _; try assumption. nia.
        destruct jump_divstep_aux as [[[[dn fn] gn] vn] rn].
        repeat (split; try easy).  nia. nia.
    Qed.

    Lemma jump_divstep_iter_correct d f g v r n Kd
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - Z.of_nat n * (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => jump_divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        Nat.iter n (jump_divstep_vr (Z.to_nat (machine_wordsize - 2)) machine_wordsize m) (tc d, tc_eval f, tc_eval g,
                                                                                            (eval v * ((r' ^ Z.of_nat mont_limbs) ^ (Z.of_nat n))) mod m,
                                                                                            (eval r * ((r' ^ Z.of_nat mont_limbs) ^ (Z.of_nat n))) mod m).
    Proof.

      induction n.
      - rewrite !Z.mul_1_r; reflexivity.
      - rewrite Nat_iter_S.
        unshelve epose proof jump_divstep_iter_invariants d f g v r n Kd _ _ _ _ _ _ _ _ _ _ _ _ _; try assumption. lia.
        rewrite seq_snoc, fold_left_app. cbn -[Z.of_nat Z.pow].
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => jump_divstep_aux data) (seq 0 n) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        replace (Z.of_nat (S n)) with (n + 1) by lia.
        rewrite Z.pow_add_r.
        rewrite !Z.mul_assoc.
        rewrite nat_iter_jump_divstep_vr_mul.
        rewrite <- (IHn ltac:(lia)).
        rewrite Z.pow_1_r.
        push_Zmod; pull_Zmod.
        apply jump_divstep_correct.
        specialize (IHn ltac:(lia)).
        inversion IHn.
        all: try easy. lia. lia.
    Qed.

    Lemma partition_valid a :
      0 <= a < m ->
      valid (Partition.partition (uweight machine_wordsize) mont_limbs a).
    Proof.
      unfold valid; split.
      - unfold small.
        replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
        rewrite eval_partition by (apply uwprops; lia).
        rewrite uweight_eq_alt' by assumption.
        rewrite Z.mod_small.
        reflexivity. rewrite Z.pow_mul_r; lia.
      - replace eval with (BYInvJump.eval machine_wordsize mont_limbs) by reflexivity.
        rewrite eval_partition by (apply uwprops; lia).
        rewrite Z.mod_small. lia.
        rewrite uweight_eq_alt'.
        rewrite Z.pow_mul_r; lia.
    Qed.

    Lemma precomp_bound : 0 <= jumpdivstep_precompmod < m.
    Proof.
      unfold jumpdivstep_precompmod.
      apply Z.mod_pos_bound. lia.
    Qed.

    Lemma eval_precomp :
      eval partition_precomp = jumpdivstep_precompmod.
    Proof.
      unfold partition_precomp.
      replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite eval_partition.
      rewrite Z.mod_small. reflexivity.
      rewrite uweight_eq_alt'.
      rewrite Z.pow_mul_r by lia.
      pose proof precomp_bound.
      lia. apply uwprops. lia.
    Qed.

    Lemma precomp_valid : valid partition_precomp.
    Proof.
      unfold partition_precomp.
      apply partition_valid.
      apply precomp_bound.
    Qed.

    Lemma iterations_pos i :
      (0 <= i) -> 0 <= iterations i.
    Proof.
      intros.
      unfold iterations.
      destruct (i <? 46).
      - apply Z_div_pos. lia. lia.
      - apply Z_div_pos. lia. lia.
    Qed.

    Lemma jump_iterations_pos b mw :
      0 <= b -> (0 < mw - 2) -> 0 <= jump_iterations b mw.
    Proof.
      intros.
      unfold jump_iterations.
      unshelve epose proof Z.div_pos (iterations b) (mw - 2) _ _.
      apply iterations_pos.
      assumption. assumption.
      lia.
    Qed.

    Lemma eval_oppmod' a (Ha : valid a)  :
            eval (oppmod a) mod m
            = (-eval a) mod m.
    Proof.
      rewrite <- (Z.mul_1_r (eval (oppmod a))).
      push_Zmod.
      replace 1 with (1 ^ (Z.of_nat mont_limbs)) by (apply Z.pow_1_l; lia).
      rewrite <- r'_correct.
      pull_Zmod.
      rewrite Z.pow_mul_l.
      replace ((eval (oppmod a) * ((2 ^ machine_wordsize) ^ Z.of_nat mont_limbs * r' ^ (Z.of_nat mont_limbs))) mod m) with
        (((eval (oppmod a) * r' ^ (Z.of_nat mont_limbs)) mod m * (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs) mod m).
      rewrite <- eval_from_montgomerymod with (m':=m'); try assumption; try lia; auto with valid.
      rewrite eval_oppmod with (r':=r'); try assumption; try lia.
      push_Zmod.
      rewrite eval_from_montgomerymod with (r':=r'); try assumption; try lia.
      pull_Zmod.
      replace ((- (eval a * r' ^ Z.of_nat mont_limbs) * (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs) mod m)
        with
        (- eval a * (((2 ^ machine_wordsize * r') mod m) ^ Z.of_nat mont_limbs) mod m).
      rewrite r'_correct.
      rewrite Z.pow_1_l by lia.
      rewrite Z.mul_1_r.
      reflexivity.
      push_Zmod; pull_Zmod.
      rewrite Z.pow_mul_l.
      f_equal. lia.
      push_Zmod; pull_Zmod.
      f_equal. lia.
    Qed.

    Lemma eval_mulmod' a b (Ha : valid a) (Hb : valid b) :
            eval (mulmod a b) mod m
            = (eval a * eval b * r' ^ (Z.of_nat mont_limbs)) mod m.
    Proof.
      rewrite <- (Z.mul_1_r (eval (mulmod a b))).
      push_Zmod.
      replace 1 with (1 ^ (Z.of_nat mont_limbs)) by (apply Z.pow_1_l; lia).
      rewrite <- r'_correct.
      pull_Zmod.
      rewrite Z.pow_mul_l.
      replace ((eval (mulmod a b) * ((2 ^ machine_wordsize) ^ Z.of_nat mont_limbs * r' ^ (Z.of_nat mont_limbs))) mod m) with
        (((eval (mulmod a b) * r' ^ (Z.of_nat mont_limbs)) mod m * (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs) mod m).
      rewrite <- eval_from_montgomerymod with (m':=m'); try assumption; try lia; auto with valid.
      rewrite eval_mulmod with (r':=r'); try assumption; try lia.
      push_Zmod.
      rewrite !eval_from_montgomerymod with (r':=r'); try assumption; try lia.
      pull_Zmod.
      replace (((eval a * r' ^ Z.of_nat mont_limbs) * (eval b * r' ^ Z.of_nat mont_limbs) *
                    (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs) mod m)
        with
        (eval a * (eval b * r' ^ Z.of_nat mont_limbs) * (((2 ^ machine_wordsize * r') mod m) ^ Z.of_nat mont_limbs) mod m).
      rewrite r'_correct.
      rewrite Z.pow_1_l by lia.
      f_equal. lia.
      push_Zmod; pull_Zmod.
      rewrite Z.pow_mul_l.
      f_equal. lia.
      push_Zmod; pull_Zmod.
      f_equal. lia.
    Qed.

    Theorem by_inv_jump_spec g
            (g_length : length g = tc_limbs)
            (g_bounds : - 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2))
            (g_in_bounded : in_bounded g)
            (iterations_bouns : 0 <=
  2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - (jump_iterations (Z.log2 m + 1) machine_wordsize + 1) * (machine_wordsize - 2) - 3)
            (m_odd : Z.odd m = true)
            (m_bounds2 : m < 2 ^ (machine_wordsize * tc_limbs - 2)) :
      eval (by_inv_jump g) mod m = by_inv_jump_ref m (tc_eval g) machine_wordsize.
    Proof.
      assert (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)).
      { apply Z.pow_lt_mono_r. lia. nia. lia. }
      unfold by_inv_jump.
      unfold by_inv_jump_ref.
      unfold by_inv_jump_full.
      unfold jumpdivstep_precompmod.
      set (msat := Partition.partition (uweight machine_wordsize) tc_limbs m).
      assert (eval_msat : tc_eval msat = m).
      { unfold msat. unfold tc_eval. rewrite eval_partition. 2: apply uwprops; lia.
        rewrite uweight_eq_alt'.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_small. reflexivity. nia.
        lia. nia. }
      pose proof Z.log2_pos m ltac:(lia).
      pose proof iterations_pos ((Z.log2 m) + 1) ltac:(lia).
      pose proof jump_iterations_pos (Z.log2 m + 1) machine_wordsize ltac:(lia) ltac:(lia).

      unshelve epose proof jump_divstep_iter_correct 1 msat g (zero mont_limbs) (one mont_limbs) (Z.to_nat (jump_iterations (Z.log2 m + 1) machine_wordsize)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.
      rewrite eval_msat. assumption.
      all: auto with len.
      unfold msat; auto with len.
      rewrite Z.twos_complement_one. lia. lia.
      unfold msat.
      auto with in_bounded.

      unshelve epose proof jump_divstep_iter_invariants 1 msat g (zero mont_limbs) (one mont_limbs) (Z.to_nat (jump_iterations (Z.log2 m + 1) machine_wordsize)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: auto with len.
      unfold msat; auto with len.
      rewrite eval_msat. assumption.
      rewrite Z.twos_complement_one. lia. lia.
      unfold msat.
      auto with in_bounded.

      destruct fold_left as [[[[dn fn]gn]vn]rn].
      destruct H4 as [fn_length [gn_length [vn_length [rn_length [fn_odd [dn_bounds [fn_bounds [fn_in_bounds [gn_bounds [gn_in_bounds [vn_valid rn_valid]]]]]]]]]]].

      rewrite nat_iter_jump_divstep_vr_mul in H3.
      rewrite eval_msat in H3.
      rewrite Z.twos_complement_one in H3 by lia.
      replace (eval (zero mont_limbs)) with 0 in H3 by (symmetry; apply eval_zero).
      replace (eval (one mont_limbs)) with 1 in H3 by (symmetry; apply eval_one; lia).
      rewrite Z.mod_0_l, Z.mod_1_l in H3 by lia.
      destruct Nat.iter as [[[[dk fk]gk]vk]rk].
      inversion H3.
      rewrite tc_sign_bit_neg; try assumption; try lia.

      replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite eval_select; auto with len.
      2: { unfold partition_precomp.
           apply length_mulmod with (r':=r').
           assumption.
           assumption. lia. lia. lia. lia.
           apply partition_valid.
           apply precomp_bound.
           assumption. }
      2: { apply length_oppmod. lia.
           apply length_mulmod with (r':=r').
           assumption.
           assumption. lia. lia. lia. lia.
           apply partition_valid.
           apply precomp_bound.
           assumption. }

      destruct (tc_eval fn <? 0).
      - cbn -[Z.mul Z.add mulmod oppmod].
        replace (BYInvJump.eval machine_wordsize mont_limbs ) with eval by reflexivity.
        rewrite eval_oppmod'.
        pull_Zmod; push_Zmod.
        rewrite eval_mulmod'.
        rewrite eval_precomp.
        unfold jumpdivstep_precompmod.

        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H8.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        set (jump_iterations := jump_iterations bits machine_wordsize).
        set (total_iterations := jump_iterations * (machine_wordsize - 2)) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ total_iterations)).

        rewrite !Z.mul_assoc.
        rewrite <- Z.pow_mul_r.
        rewrite <- (Z.mul_assoc _ (r' ^ _)).
        rewrite <- Z.pow_add_r.
        replace (Z.of_nat mont_limbs) with ((Z.of_nat mont_limbs) * 1) at 3 by lia.
        rewrite <- Z.mul_add_distr_l.
        rewrite <- (Z.mul_assoc machine_wordsize).
        rewrite Z.pow_mul_r.
        replace
          ((-
  ((2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)) * pc * vk *
                              r' ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m) with
          ((- pc * vk * (((2 ^ machine_wordsize) * r' mod m) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m).
        rewrite r'_correct.
        rewrite Z.pow_1_l.
        f_equal. lia. clear -H2 mont_limbs1. lia.
        push_Zmod. pull_Zmod.
        rewrite Z.pow_mul_l.
        f_equal. lia. lia. clear -H2 mont_limbs1. lia.
        clear -H2 mont_limbs1. lia.
        lia. lia. assumption. unfold total_iterations.
        clear -H2 mw2. nia. assumption.
        apply precomp_valid.
        assumption.
        apply mulmod_valid with (r':=r').
        assumption.
        assumption.
        lia. lia. lia. lia.
        apply precomp_valid.
        assumption.
      - cbn -[Z.mul Z.add mulmod oppmod].
        replace (BYInvJump.eval machine_wordsize mont_limbs ) with eval by reflexivity.
        rewrite eval_mulmod'.
        rewrite eval_precomp.
        unfold jumpdivstep_precompmod.

        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H8.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        set (jump_iterations := jump_iterations bits machine_wordsize) in *.
        set (total_iterations := jump_iterations * (machine_wordsize - 2)) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ total_iterations)).

        rewrite !Z.mul_assoc.
        rewrite <- Z.pow_mul_r.
        rewrite <- (Z.mul_assoc _ (r' ^ _)).
        rewrite <- Z.pow_add_r.
        replace (Z.of_nat mont_limbs) with ((Z.of_nat mont_limbs) * 1) at 3 by lia.
        rewrite <- Z.mul_add_distr_l.
        rewrite <- (Z.mul_assoc machine_wordsize).
        rewrite Z.pow_mul_r.
        replace
          ((
  ((2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)) * pc * vk *
                              r' ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m) with
          ((pc * vk * (((2 ^ machine_wordsize) * r' mod m) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m).
        rewrite r'_correct.
        rewrite Z.pow_1_l.
        f_equal. lia. clear -H2 mont_limbs1. lia.
        push_Zmod. pull_Zmod.
        rewrite Z.pow_mul_l.
        f_equal. lia. lia. clear -H2 mont_limbs1. lia.
        clear -H2 mont_limbs1. nia.
        lia. lia. assumption. unfold total_iterations.
        clear -H2 mw2. nia. assumption.
        apply precomp_valid.
        assumption.
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
    Notation jump_divstep := (jump_divstep limbwidth_num limbwidth_den machine_wordsize s c n sat_limbs word_tc_mul_limbs idxs balance).

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
      rewrite Z.twos_complement_opp_correct.

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
    (* Theorem outer_loop_body_correct f g v r *)
    (*         (fodd : Z.odd (tc_eval machine_wordsize sat_limbs f) = true) *)
    (*         (n1 : (1 < n)%nat) *)
    (*         (mw1 : 2 < machine_wordsize) *)
    (*         (Hf : length f = sat_limbs) *)
    (*         (Hg : length g = sat_limbs) *)
    (*         (Hv : length v = n) *)
    (*         (Hr : length r = n) *)
    (*         (sat_limbs0 : (0 < sat_limbs)%nat) *)
    (*         (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + sat_limbs)%nat) *)
    (*         (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) < *)
    (*                       tc_eval machine_wordsize sat_limbs f < *)
    (*                       2 ^ (machine_wordsize * sat_limbs - 2)) *)
    (*         (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) < *)
    (*                       tc_eval machine_wordsize sat_limbs g < *)
    (*                       2 ^ (machine_wordsize * sat_limbs - 2)) *)
    (*         (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) *)
    (*         (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) : *)
    (*   let '(f1,g1,v1,r1) := outer_loop_body f g v r in *)
    (*   (tc_eval machine_wordsize sat_limbs f1, *)
    (*    tc_eval machine_wordsize sat_limbs g1, *)
    (*    eval v1 mod (s - Associational.eval c), *)
    (*    eval r1 mod (s - Associational.eval c)) *)
    (*   = *)
    (*   let '(_,f1',g1',v1',r1') := *)
    (*     Nat.iter (Z.to_nat (machine_wordsize - 2)) *)
    (*              (divstep_vr_mod (s - Associational.eval c)) *)
    (*              (1, *)
    (*              tc_eval machine_wordsize sat_limbs f, *)
    (*              tc_eval machine_wordsize sat_limbs g, *)
    (*              eval v mod (s - Associational.eval c), *)
    (*              eval r mod (s - Associational.eval c)) *)
    (*                 in *)
    (*   (Z.twos_complement (machine_wordsize * sat_limbs) f1', *)
    (*    Z.twos_complement (machine_wordsize * sat_limbs) g1', v1', r1'). *)
    (* Proof. *)
    (*   pose proof (pow_ineq_Z (machine_wordsize - 1) ltac:(lia)). *)

    (*   assert (1 < 2 ^ machine_wordsize) *)
    (*     by (apply Zpow_facts.Zpower_gt_1; lia). *)
    (*   assert (0 < 2 ^ (machine_wordsize - 1)) *)
    (*     by (apply Z.pow_pos_nonneg; lia). *)
    (*   assert (0 < 2 ^ (machine_wordsize - 2)) *)
    (*     by (apply Z.pow_pos_nonneg; lia). *)
    (*   assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1)) *)
    (*     by (rewrite Z.mul_comm, Z.pow_mul_base by lia; apply f_equal2; lia). *)
    (*   assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat sat_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + sat_limbs)) - 1)) *)
    (*     by (rewrite <- Zpower_exp, !Z.pow_mul_base by nia; apply f_equal2; nia). *)

    (*   unfold outer_loop_body. *)
    (*   epose proof twos_complement_word_full_divstep_iter_partially_correct (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. *)

    (*   epose proof twos_complement_word_full_divsteps_partial_bounds (machine_wordsize) 1 (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _. *)

    (*   replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia. *)

    (*   epose proof jump_divstep_full *)
    (*         (s - Associational.eval c) *)
    (*         (tc_eval machine_wordsize sat_limbs f) *)
    (*         (Z.twos_complement machine_wordsize (nth_default 0 f 0)) *)
    (*         (tc_eval machine_wordsize sat_limbs g) *)
    (*         (Z.twos_complement machine_wordsize (nth_default 0 g 0)) *)
    (*         (eval v mod (s - Associational.eval c)) *)
    (*         (eval r mod (s - Associational.eval c)) *)
    (*         (Z.to_nat (machine_wordsize - 2)) _ _ _ _ _ _. *)

    (*   rewrite Z.twos_complement_one, Z.twos_complement_zero in * by lia. *)

    (*   rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity. *)

    (*   destruct (    fold_left (fun (i : Z * Z * Z * Z * Z * Z * Z) (_ : nat) => twos_complement_word_full_divstep_aux machine_wordsize i) *)
    (*                           (seq 0 (Z.to_nat (machine_wordsize - 2))) (1, nth_default 0 f 0, nth_default 0 g 0, 1, 0, 0, 1)) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1 . *)
    (*   destruct (divstep_full_iter *)
    (*               (s - Associational.eval c) 1 *)
    (*               (tc_eval machine_wordsize sat_limbs f) *)
    (*               (tc_eval machine_wordsize sat_limbs g) *)
    (*               (eval v mod (s - Associational.eval c)) *)
    (*               (eval r mod (s - Associational.eval c)) *)
    (*               (Z.to_nat (machine_wordsize - 2))) *)
    (*     as [[[[d1' f1'] g1'] v1'] r1'] eqn:E2. *)

    (*   destruct (divstep_uvqr_iter *)
    (*               1 *)
    (*               (Z.twos_complement machine_wordsize (nth_default 0 f 0)) *)
    (*               (Z.twos_complement machine_wordsize (nth_default 0 g 0)) *)
    (*               1 0 0 1 (Z.to_nat (machine_wordsize - 2))) *)
    (*     as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3. *)

    (*   rewrite !unfold_Let_In. *)

    (*   repeat match goal with *)
    (*          | [ |- (_, _) = (_, _) ] => apply f_equal2 *)
    (*          end. *)
    (*   + rewrite word_tc_mul_limbs_eq in *. *)
    (*     rewrite firstn_tc_eval with (n:=(1 + sat_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full; *)
    (*       repeat match goal with *)
    (*              | |- length _ = _ => autorewrite with length_distr; try lia *)
    (*              | |- context[In _] => apply arithmetic_shiftr_bounds || apply tc_add_bounds *)
    (*              | _ => assumption || lia *)
    (*              end. *)
    (*     rewrite !word_tc_mul_correct by (assumption || lia). *)
    (*     inversion H7. inversion H5. *)
    (*     replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia. *)
    (*     rewrite !word_tc_mul_correct; (assumption || nia). *)
    (*   + rewrite word_tc_mul_limbs_eq in *. *)
    (*     rewrite firstn_tc_eval with (n:=(1 + sat_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full; *)
    (*       repeat match goal with *)
    (*              | |- length _ = _ => autorewrite with length_distr; try lia *)
    (*              | |- context[In _] => apply arithmetic_shiftr_bounds || apply tc_add_bounds *)
    (*              | _ => assumption || lia *)
    (*              end. *)
    (*     rewrite !word_tc_mul_correct by (assumption || lia). *)
    (*     inversion H7. inversion H5. *)
    (*     replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia. *)
    (*     rewrite !word_tc_mul_correct; (assumption || nia). *)
    (*   + rewrite eval_carrymod, eval_addmod; try lia. *)
    (*     push_Zmod. *)
    (*     rewrite !eval_carry_mulmod; try lia. *)
    (*     push_Zmod. *)
    (*     rewrite !eval_word_to_solina; try lia. *)

    (*     inversion H7. inversion H5. *)
    (*     push_Zmod; pull_Zmod. reflexivity. *)
    (*     apply word_to_solina_length. *)
    (*     apply word_to_solina_length. *)
    (*     unfold carry_mulmod, mulmod; auto with distr_length. *)
    (*     unfold carry_mulmod, mulmod; auto with distr_length. *)
    (*     unfold addmod, carry_mulmod, mulmod; auto with distr_length. *)
    (*   + rewrite eval_carrymod, eval_addmod; try lia. *)
    (*     push_Zmod. *)
    (*     rewrite !eval_carry_mulmod; try lia. *)
    (*     push_Zmod. *)
    (*     rewrite !eval_word_to_solina; try lia. *)

    (*     inversion H7. inversion H5. *)
    (*     push_Zmod; pull_Zmod. reflexivity. *)
    (*     apply word_to_solina_length. *)
    (*     apply word_to_solina_length. *)
    (*     unfold carry_mulmod, mulmod; auto with distr_length. *)
    (*     unfold carry_mulmod, mulmod; auto with distr_length. *)
    (*     unfold addmod, carry_mulmod, mulmod; auto with distr_length. *)

    (*     Unshelve. *)
    (*     all: lia || rewrite ?Z.twos_complement_one, ?Z.twos_complement_zero; lia || idtac. *)
    (*     rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=sat_limbs); try lia. *)
    (*     unfold tc_eval in fodd. *)
    (*     rewrite Z.twos_complement_odd in fodd. *)
    (*     rewrite Z.odd_mod2m. assumption. *)

    (*     lia. nia. assumption. *)
    (*     replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia. *)

    (*     lia. *)
    (*     apply Hf2. *)
    (*     destruct f. simpl in *. lia. left. reflexivity. *)
    (*     apply Hg2. *)
    (*     destruct g. simpl in *. lia. left. reflexivity. *)

    (*     replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia; lia. *)
    (*     unfold tc_eval in fodd. *)
    (*     rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.odd_mod2m by (assumption || lia). *)
    (*     rewrite Z.twos_complement_odd in fodd; assumption || nia. *)

    (*     assumption. *)
    (*     apply Z.mod_pos_bound; lia. *)
    (*     apply Z.mod_pos_bound; lia. *)

    (*     unfold tc_eval. *)
    (*     rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.twos_complement_mod, !Z.twos_complement_mod_smaller_pow; assumption || nia. *)

    (*     unfold tc_eval. *)
    (*     rewrite eval_nth_default_0 with (n:=sat_limbs) (m:=machine_wordsize), Z.twos_complement_mod, !Z.twos_complement_mod_smaller_pow; assumption || nia. *)
    (* Qed. *)
  End __.

End UnsaturatedSolinas.
