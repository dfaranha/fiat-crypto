Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.

Lemma length_one n (Hn : (0 < n)%nat) :
  length (one n) = n.
Proof. unfold one; simpl; rewrite length_zeros; lia. Qed.

Hint Rewrite length_one : distr_length.

Lemma eval_one n machine_wordsize
      (Hn : (0 < n)%nat)
      (Hmw : 0 <= machine_wordsize) :
  eval (uweight machine_wordsize) n (one n) = 1.
Proof.
  unfold one. destruct n. lia.
  rewrite eval_cons, uweight_eval_shift, uweight_0, uweight_1 by (try rewrite length_zeros; lia).
  replace (S n - 1)%nat with n by lia. rewrite eval_zeros; lia.
Qed.
