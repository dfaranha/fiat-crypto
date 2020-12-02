Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Testbit.

Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.

Local Open Scope Z_scope.

Module Z.
  Lemma ones_at_spec_full m k i
        (Hk : 0 <= k) :
    Z.testbit (Z.ones_at m k) i = if (i <? 0) then false else (m <=? i) && (i <? m + k).
  Proof. unfold Z.ones_at; Z.solve_testbit. Qed.

  Hint Rewrite ones_at_spec_full : testbit_rewrite.

  Lemma ones_at_0 m : Z.ones_at m 0 = 0.
  Proof. Z.solve_using_testbit. Qed.
End Z.
