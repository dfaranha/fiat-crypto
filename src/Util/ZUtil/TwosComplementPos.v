Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.

Local Open Scope Z_scope.

Module Z.

  Lemma twos_complement_pos_spec m a
        (mw0 : 0 < m)
        (a_bound : - 2 ^ (m - 1) < Z.twos_complement m a < 2 ^ (m - 1)) :
    Z.twos_complement_pos m a = Z.b2z (0 <? Z.twos_complement m a).
  Proof.
    replace (0 <? Z.twos_complement m a) with (- Z.twos_complement m a <? 0) by
        (destruct (0 <? Z.twos_complement m a) eqn:?; destruct (- Z.twos_complement m a <? 0) eqn:?;
                  rewrite ?Z.ltb_lt in *; rewrite ?Z.ltb_ge in *; try reflexivity; lia).
    unfold Z.twos_complement_pos; pose proof Z.twos_complement_opp_bound m a ltac:(lia).
    rewrite <- Z.twos_complement_opp_spec, Rewriter.Util.LetIn.unfold_Let_In, Z.twos_complement_neg_equiv by lia.
    rewrite Z.sign_bit_testbit, Z.twos_complement_cond_equiv, Bool.negb_involutive; lia. Qed.


  Lemma twos_complement_pos'_pos m a :
    Z.twos_complement_pos' m a = Z.twos_complement_pos m a.
  Proof. unfold Z.twos_complement_pos'. rewrite Z.twos_complement_opp'_opp. reflexivity. Qed.

  Lemma twos_complement_pos'_spec m a
        (mw0 : 0 < m)
        (a_bound : - 2 ^ (m - 1) < Z.twos_complement m a < 2 ^ (m - 1)) :
    Z.twos_complement_pos' m a = Z.b2z (0 <? Z.twos_complement m a).
  Proof. rewrite twos_complement_pos'_pos; now apply twos_complement_pos_spec. Qed.

End Z.
