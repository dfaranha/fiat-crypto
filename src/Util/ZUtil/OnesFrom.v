Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Testbit.

Require Import Crypto.Util.ZUtil.Tactics.BruteForceIneq.

Local Open Scope Z_scope.

Module Z.
  Lemma ones_from_spec m k i
        (Hk : 0 <= k)
        (Hi : 0 <= i) :
    Z.testbit (Z.ones_from m k) i = ((m - k) <=? i) && (i <? m).
  Proof. unfold Z.ones_from; rewrite Z.shiftl_spec, Z.ones_spec_full; brute_force_ineq. Qed.

  Lemma ones_from_0 m : Z.ones_from m 0 = 0.
  Proof. unfold Z.ones_from, Z.ones. apply Z.shiftl_0_l. Qed.
End Z.
