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
Require Import Crypto.Arithmetic.BYInv.
Require Import Crypto.Arithmetic.BYInvJump.
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

Definition asr machine_wordsize n k f := sat_arithmetic_shiftr machine_wordsize n f k.

Derive reified_asr_gen
       SuchThat (is_reification_of reified_asr_gen asr)
       As reified_asr_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification sat_arithmetic_shiftr (proj1 reified_asr_gen_correct) : reify_cache_gen.
Hint Rewrite (proj1 reified_asr_gen_correct) : interp_gen_cache.
Local Opaque reified_asr_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_word_sat_mul_gen
       SuchThat (is_reification_of reified_word_sat_mul_gen word_sat_mul)
       As reified_word_sat_mul_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification word_sat_mul (proj1 reified_word_sat_mul_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_word_sat_mul_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_word_sat_mul_gen_correct) : interp_gen_cache.
Local Opaque reified_word_sat_mul_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_twos_complement_word_full_divstep_gen
       SuchThat (is_reification_of reified_twos_complement_word_full_divstep_gen twos_complement_word_full_divstep)
       As reified_twos_complement_word_full_divstep_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification twos_complement_word_full_divstep (proj1 reified_twos_complement_word_full_divstep_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_twos_complement_word_full_divstep_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_twos_complement_word_full_divstep_gen_correct) : interp_gen_cache.
Local Opaque reified_twos_complement_word_full_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_sat_add_gen
       SuchThat (is_reification_of reified_sat_add_gen BYInv.sat_add)
       As reified_sat_add_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification BYInv.sat_add (proj1 reified_sat_add_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_sat_add_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_sat_add_gen_correct) : interp_gen_cache.
Local Opaque reified_sat_add_gen. (* needed for making [autorewrite] not take a very long time *)

Module Export WordByWordMontgomery.
  Import BYInv.WordByWordMontgomery.
  Import BYInvJump.WordByWordMontgomery.

  Derive reified_outer_loop_body_gen
         SuchThat (is_reification_of reified_outer_loop_body_gen outer_loop_body)
         As reified_outer_loop_body_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification outer_loop_body (proj1 reified_outer_loop_body_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_outer_loop_body_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_outer_loop_body_gen_correct) : interp_gen_cache.
  Local Opaque reified_outer_loop_body_gen. (* needed for making [autorewrite] not take a very long time *)  
  
  Derive reified_twos_complement_word_to_montgomery_no_encode_gen
         SuchThat (is_reification_of reified_twos_complement_word_to_montgomery_no_encode_gen twos_complement_word_to_montgomery_no_encode)
         As reified_twos_complement_word_to_montgomery_no_encode_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification twos_complement_word_to_montgomery_no_encode (proj1 reified_twos_complement_word_to_montgomery_no_encode_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_twos_complement_word_to_montgomery_no_encode_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_twos_complement_word_to_montgomery_no_encode_gen_correct) : interp_gen_cache.
  Local Opaque reified_twos_complement_word_to_montgomery_no_encode_gen.

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
  Import BYInv.UnsaturatedSolinas.
  Import BYInvJump.UnsaturatedSolinas.

  Derive reified_outer_loop_body_gen
         SuchThat (is_reification_of reified_outer_loop_body_gen outer_loop_body)
         As reified_outer_loop_body_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification outer_loop_body (proj1 reified_outer_loop_body_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_outer_loop_body_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_outer_loop_body_gen_correct) : interp_gen_cache.
  Local Opaque reified_outer_loop_body_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_word_to_solina_gen
         SuchThat (is_reification_of reified_word_to_solina_gen word_to_solina)
         As reified_word_to_solina_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification word_to_solina (proj1 reified_word_to_solina_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_word_to_solina_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_word_to_solina_gen_correct) : interp_gen_cache.
  Local Opaque reified_word_to_solina_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification divstep (proj1 reified_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)
End UnsaturatedSolinas.
