(** * Push-Button Synthesis of Bernstein-Yang Inversion: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Lists.List.

Import
  Language.Wf.Compilers
  Language.Compilers
  Language.API.Compilers.
Import Compilers.API.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Definition msat bitwidth n m := Partition.partition (uweight bitwidth) n m. (* m in saturated representation *)

Derive reified_msat_gen
       SuchThat (is_reification_of reified_msat_gen msat)
       As reified_msat_gen_correct.
Proof.
  Time cache_reify ().
  Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification msat (proj1 reified_msat_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_msat_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_msat_gen_correct) : interp_gen_cache.
Local Opaque reified_msat_gen. (* needed for making [autorewrite] not take a very long time *)

Module Export WordByWordMontgomery.
  Import Definitions.WordByWordMontgomery.

  Derive reified_outer_loop_body_gen
         SuchThat (is_reification_of reified_outer_loop_body_gen outer_loop_body)
         As reified_outer_loop_body_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification outer_loop_body (proj1 reified_outer_loop_body_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_outer_loop_body_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_outer_loop_body_gen_correct) : interp_gen_cache.
  Local Opaque reified_outer_loop_body_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification divstep (proj1 reified_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)
End WordByWordMontgomery.

Module Export UnsaturatedSolinas.
  Import Definitions.UnsaturatedSolinas.

  Derive reified_outer_loop_body_gen
         SuchThat (is_reification_of reified_outer_loop_body_gen outer_loop_body)
         As reified_outer_loop_body_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification outer_loop_body (proj1 reified_outer_loop_body_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_outer_loop_body_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_outer_loop_body_gen_correct) : interp_gen_cache.
  Local Opaque reified_outer_loop_body_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification divstep (proj1 reified_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)
End UnsaturatedSolinas.
