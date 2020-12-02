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

Definition partition bitwidth n a := Partition.partition (uweight bitwidth) n a. (* similar to encode except it does not inject into Montgomery domain *)

Derive reified_partition_gen
       SuchThat (is_reification_of reified_partition_gen partition)
       As reified_partition_gen_correct.
Proof.
  Time cache_reify ().
  Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification partition (proj1 reified_partition_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_partition_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_partition_gen_correct) : interp_gen_cache.
Local Opaque reified_partition_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_eval_twos_complement_gen
         SuchThat (is_reification_of reified_eval_twos_complement_gen tc_eval)
         As reified_eval_twos_complement_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification tc_eval (proj1 reified_eval_twos_complement_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_eval_twos_complement_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_eval_twos_complement_gen_correct) : interp_gen_cache.
  Local Opaque reified_eval_twos_complement_gen. (* needed for making [autorewrite] not take a very long time *)

Module Export WordByWordMontgomery.
  Import Definitions.WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.

  Derive reified_update_fg_gen
         SuchThat (is_reification_of reified_update_fg_gen update_fg)
         As reified_update_fg_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification update_fg (proj1 reified_update_fg_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_update_fg_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_update_fg_gen_correct) : interp_gen_cache.
  Local Opaque reified_update_fg_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_update_vr_gen
         SuchThat (is_reification_of reified_update_vr_gen update_vr)
         As reified_update_vr_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification update_vr (proj1 reified_update_vr_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_update_vr_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_update_vr_gen_correct) : interp_gen_cache.
  Local Opaque reified_update_vr_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_inner_loop_gen
         SuchThat (is_reification_of reified_inner_loop_gen inner_loop)
         As reified_inner_loop_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification inner_loop (proj1 reified_inner_loop_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_inner_loop_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_inner_loop_gen_correct) : interp_gen_cache.
  Local Opaque reified_inner_loop_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_inner_loop_hd_gen
         SuchThat (is_reification_of reified_inner_loop_hd_gen inner_loop_hd)
         As reified_inner_loop_hd_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification inner_loop_hd (proj1 reified_inner_loop_hd_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_inner_loop_hd_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_inner_loop_hd_gen_correct) : interp_gen_cache.
  Local Opaque reified_inner_loop_hd_gen. (* needed for making [autorewrite] not take a very long time *)

  (* this got too slow after generalizing d in jumpdivstep

  Derive reified_jump_divstep_gen
         SuchThat (is_reification_of reified_jump_divstep_gen jump_divstep)
         As reified_jump_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification jump_divstep (proj1 reified_jump_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_jump_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_jump_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_jump_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_jump_divstep_hd_gen
         SuchThat (is_reification_of reified_jump_divstep_hd_gen jump_divstep_hd)
         As reified_jump_divstep_hd_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification jump_divstep_hd (proj1 reified_jump_divstep_hd_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_jump_divstep_hd_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_jump_divstep_hd_gen_correct) : interp_gen_cache.
  Local Opaque reified_jump_divstep_hd_gen. (* needed for making [autorewrite] not take a very long time *)

  *)

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

  Derive reified_update_fg_gen
         SuchThat (is_reification_of reified_update_fg_gen update_fg)
         As reified_update_fg_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification update_fg (proj1 reified_update_fg_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_update_fg_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_update_fg_gen_correct) : interp_gen_cache.
  Local Opaque reified_update_fg_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_update_vr_gen
         SuchThat (is_reification_of reified_update_vr_gen update_vr)
         As reified_update_vr_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification update_vr (proj1 reified_update_vr_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_update_vr_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_update_vr_gen_correct) : interp_gen_cache.
  Local Opaque reified_update_vr_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_inner_loop_gen
         SuchThat (is_reification_of reified_inner_loop_gen inner_loop)
         As reified_inner_loop_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification inner_loop (proj1 reified_inner_loop_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_inner_loop_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_inner_loop_gen_correct) : interp_gen_cache.
  Local Opaque reified_inner_loop_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_inner_loop_hd_gen
         SuchThat (is_reification_of reified_inner_loop_hd_gen inner_loop_hd)
         As reified_inner_loop_hd_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification inner_loop_hd (proj1 reified_inner_loop_hd_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_inner_loop_hd_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_inner_loop_hd_gen_correct) : interp_gen_cache.
  Local Opaque reified_inner_loop_hd_gen. (* needed for making [autorewrite] not take a very long time *)

  (* this got too slow after generalizing d in jumpdivstep

  Derive reified_jump_divstep_gen
         SuchThat (is_reification_of reified_jump_divstep_gen jump_divstep)
         As reified_jump_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification jump_divstep (proj1 reified_jump_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_jump_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_jump_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_jump_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_jump_divstep_hd_gen
         SuchThat (is_reification_of reified_jump_divstep_hd_gen jump_divstep_hd)
         As reified_jump_divstep_hd_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification jump_divstep_hd (proj1 reified_jump_divstep_hd_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_jump_divstep_hd_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_jump_divstep_hd_gen_correct) : interp_gen_cache.
  Local Opaque reified_jump_divstep_hd_gen. (* needed for making [autorewrite] not take a very long time *)

  *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification divstep (proj1 reified_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)
End UnsaturatedSolinas.
