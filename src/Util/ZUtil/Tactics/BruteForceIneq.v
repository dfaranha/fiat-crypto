Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Ltac brute_force_ineq :=
  repeat match goal with
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
           destruct (a =? b) eqn:E; [rewrite Z.eqb_eq in E|rewrite Z.eqb_neq in E]
         end;
  try reflexivity; try lia.
