Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.Decidable.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma tc_eval_select machine_wordsize n cond f g
      (Hf : length f = n)
      (Hg : length g = n) :
  tc_eval machine_wordsize n (select cond f g) = if dec (cond = 0)
                                                    then (tc_eval machine_wordsize n f)
                                                    else (tc_eval machine_wordsize n g).
Proof. unfold tc_eval; rewrite eval_select; auto; destruct (dec (cond = 0)); auto. Qed.
