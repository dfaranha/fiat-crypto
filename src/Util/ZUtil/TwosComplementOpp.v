Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.AddGetCarry.

Local Open Scope Z_scope.

Section Z.

  Lemma twos_complement_opp_bound m a (Hm : 0 <= m) :
    0 <= Z.twos_complement_opp m a < 2 ^ m.
  Proof. unfold Z.twos_complement_opp; apply Z.mod_pos_bound.
         apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma twos_complement_opp_correct m a :
    (Z.twos_complement_opp m a) = - a mod 2 ^ m.
  Proof. unfold Z.twos_complement_opp, Z.lnot_modulo, Z.lnot.
         rewrite Zplus_mod_idemp_l, <- Z.sub_1_r; apply f_equal2; lia.
  Qed.

  Lemma twos_complement_zopp a m (Hm : 0 < m) (corner_case : Z.twos_complement m a <> - 2 ^ (m - 1)) :
    Z.twos_complement m (- a) = - Z.twos_complement m a.
  Proof.
    pose proof Z.twos_complement_bounds m a Hm.
    apply Z.twos_complement_spec; [lia|split]; [|lia].
    rewrite (PullPush.Z.opp_mod_mod (Z.twos_complement _ _)), Z.twos_complement_mod' by lia;
      apply PullPush.Z.opp_mod_mod.
  Qed.

  Lemma twos_complement_opp_spec m a
        (Hm : 0 < m) (corner_case : Z.twos_complement m a <> - 2 ^ (m - 1)) :
    Z.twos_complement m (Z.twos_complement_opp m a) = - (Z.twos_complement m a).
  Proof.
    apply Z.twos_complement_spec; [lia|split]; [|pose proof Z.twos_complement_bounds m a Hm; lia].
    now rewrite <- twos_complement_zopp, twos_complement_opp_correct, Z.twos_complement_mod', Z.mod_mod by (try apply Z.pow_nonzero; lia).
  Qed.

  Lemma twos_complement_opp_odd m a (Hm : 0 < m) (aodd : Z.odd a = true) :
    Z.odd (Z.twos_complement_opp m a) = true.
  Proof.
    unfold Z.twos_complement_opp, Z.lnot_modulo, Z.lnot.
    rewrite Zplus_mod_idemp_l.
    replace (Z.pred (- a) + 1) with (-a) by lia.
    now rewrite Z.odd_mod2m, Z.odd_opp by assumption.
  Qed.

  Lemma twos_complement_opp'_spec m a :
    Z.twos_complement_opp' m a = Z.twos_complement_opp m a.
  Proof.
    unfold Z.twos_complement_opp', Z.twos_complement_opp.
    destruct (Z_lt_dec m 0).
    - rewrite !Z.pow_neg_r, !Zmod_0_r by assumption; reflexivity.
    - rewrite Z.add_get_carry_full_mod; auto with zarith.
  Qed.

End Z.
