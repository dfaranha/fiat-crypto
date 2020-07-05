Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.Zselect.

Require Import Crypto.Util.LetIn.

Import Notations.

Local Open Scope Z_scope.

Ltac solve_testbit :=
    repeat (match goal with
            | _ => rewrite unfold_Let_In, Zselect.Z.zselect_correct
            | [ |- context[Z.sign_extend _ _ _] ] => unfold Z.sign_extend
            | [ |- context[Z.ones_at _ _ ] ] => unfold Z.ones_at
            | [ |- context[Z.sign_bit _ _] ] => rewrite Z.sign_bit_testbit
            | [ |- context[Z.testbit (_ >> _)] ] => rewrite Z.shiftr_spec
            | [ |- context[Z.testbit (_ |' _)] ] => rewrite Z.lor_spec
            | [ |- context[Z.testbit (_ &' _)] ] => rewrite Z.land_spec
            | [ |- context[Z.testbit (_ << _)] ] => rewrite Z.shiftl_spec
            | [ |- context[Z.testbit (Z.ones _ )] ] => rewrite Z.ones_spec_full
            | [ |- context[Z.testbit 0 _] ] => rewrite Z.bits_0
            | [ |- context[Z.testbit (2 ^ ?m) ?m] ] => rewrite Z.pow2_bits_true
            | [ |- context[Z.testbit (2 ^ ?m) ?i] ] => rewrite Z.pow2_bits_false by lia
            | [ |- context[Z.testbit ?a (?m - 1)] ] =>
              let E := fresh in destruct (Z.testbit a (m - 1)) eqn:E; simpl
            | [ |- context[_ - ?a + ?a] ] => rewrite Z.sub_simpl_r
            | [ |- context[Z_lt_dec ?a ?b] ] =>
              destruct (Z_lt_dec a b)
            | [ |- context[?a <? ?b] ] =>
              let E := fresh in
              destruct (a <? b) eqn:E; [rewrite Z.ltb_lt in E|rewrite Z.ltb_ge in E]
            | [ |- context[?a <=? ?b] ] =>
              let E := fresh in
              destruct (a <=? b) eqn:E; [rewrite Z.leb_le in E|rewrite Z.leb_gt in E]
            | [ |- context[?a =? ?b] ] =>
              let E := fresh in
              destruct (a =? b) eqn:E; [rewrite Z.eqb_eq in E; subst|rewrite Z.eqb_neq in E]
            | [ |- Z.testbit ?a ?i = false] =>
              match goal with
              | [ H: 0 <= a < 2 ^ ?m |- _ ] =>
                assert (2 ^ m <= 2 ^ i) by (apply Z.pow_le_mono_r; lia)
              end;
              apply Z.bits_above_log2; [lia|apply Log2.Z.log2_lt_pow2_alt; lia]
            | [ |- context[_ && false] ] => rewrite andb_false_r
            end; simpl; subst);
    try reflexivity; try discriminate; try lia.
