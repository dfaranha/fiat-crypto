Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.

Import Positional.

Module UnsaturatedSolinas.

  Lemma length_addmod limbwidth_num limbwidth_den n :
    forall f, length f = n -> forall g, length g = n -> length (addmod limbwidth_num limbwidth_den n f g) = n.
  Proof. intros; apply length_add; assumption. Qed.

  Lemma length_oppmod limbwidth_num limbwidth_den n balance :
    length balance = n ->
    forall f, length f = n -> length (oppmod limbwidth_num limbwidth_den n balance f) = n.
  Proof. intros; apply length_opp; assumption. Qed.

  Lemma length_carrymod limbwidth_num limbwidth_den s c n idxs :
    forall f, length f = n ->
         length (carrymod limbwidth_num limbwidth_den s c n idxs f) = n.
  Proof. intros; unfold carrymod; apply length_chained_carries; assumption. Qed.

  Lemma length_mulmod weight s c n f g :
    length (mulmod weight s c n f g) = n.
  Proof. intros; unfold mulmod; apply Positional.length_from_associational. Qed.

  Lemma length_carry_mulmod limbwidth_num limbwidth_den s c n idxs :
    forall f, length f = n ->
         forall g, length g = n ->
    length (carry_mulmod limbwidth_num limbwidth_den s c n idxs f g) = n.
  Proof. intros. unfold carry_mulmod. apply Positional.length_chained_carries. apply length_mulmod. Qed.

  Lemma length_encodemod limbwidth_num limbwidth_den s c n a :
    length (encodemod limbwidth_num limbwidth_den s c n a) = n.
  Proof. unfold encodemod. apply Positional.length_encode. Qed.

End UnsaturatedSolinas.
