(** * Push-Button Synthesis of Word-By-Word Montgomery: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Inv.
Require Import Crypto.Arithmetic.JumpDivstep.
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

Module Export WordByWordMontgomeryInversion.
  Import WordByWordMontgomery.WordByWordMontgomery.
  Import WordByWordMontgomery.

  Definition iterations bits := if bits <? 46 then (49 * bits + 80) / 17 else (49 * bits + 57) / 17.
  (* m in saturated representation *)
  Definition msat bitwidth n m := encode_no_reduce (uweight bitwidth) n m. 
  (* Precomputed value for the inversion algorithm in the montgomery domain (not sure where to put this) *)
  Definition precompmod bitwidth n m m' :=
    let bits := (Z.log2 m) + 1 in
    let i := iterations bits in
    let k := (m + 1) / 2 in
    let precomp := (Z.sq_and_multiply_mod k i m) in
    encodemod bitwidth n m m' precomp.
  Definition jumpprecompmod bitwidth n m m' :=
    let bits := (Z.log2 m) + 1 in
    let jump_iterations := ((iterations bits) / (bitwidth - 2)) + 1 in
    let total_iterations := jump_iterations * (bitwidth - 2) in
    let k := (m + 1) / 2 in
    let precomp := (Z.sq_and_multiply_mod k total_iterations m) in
    let RN := (Z.sq_and_multiply_mod 2 (bitwidth * (Z.of_nat n) * (jump_iterations + 1)) m) in
    let res := (RN * precomp) mod m in
    encodemod bitwidth n m m' res.
  Definition jumpprecompmodalt bitwidth n m m' :=
    let bits := (Z.log2 m) + 1 in
    let jump_iterations := ((iterations bits) / bitwidth) + 1 in
    let total_iterations := jump_iterations * (bitwidth - 2) in
    let k := (m + 1) / 2 in
    let precomp := (Z.sq_and_multiply_mod k total_iterations m) in
    let RN := (Z.sq_and_multiply_mod 2 (bitwidth * (Z.of_nat n) * jump_iterations) m) in
    let res := (RN * precomp) mod m in
    encodemod bitwidth n m m' res.  
  Definition shiftr62 machine_wordsize n f := sat_arithmetic_shiftr machine_wordsize n f 62. 

  Derive reified_shiftr62_gen
         SuchThat (is_reification_of reified_shiftr62_gen shiftr62)
         As reified_shiftr62_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification shiftr62 (proj1 reified_shiftr62_gen_correct) : reify_cache_gen.
  Hint Rewrite (proj1 reified_shiftr62_gen_correct) : interp_gen_cache.
  Local Opaque reified_shiftr62_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sat64_mul_gen
         SuchThat (is_reification_of reified_sat64_mul_gen sat64_mul)
         As reified_sat64_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification sat64_mul (proj1 reified_sat64_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_sat64_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_sat64_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_sat64_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_twos_complement_word_full_divstep_gen
         SuchThat (is_reification_of reified_twos_complement_word_full_divstep_gen twos_complement_word_full_divstep)
         As reified_twos_complement_word_full_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification twos_complement_word_full_divstep (proj1 reified_twos_complement_word_full_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_twos_complement_word_full_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_twos_complement_word_full_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_twos_complement_word_full_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sat_add_gen
         SuchThat (is_reification_of reified_sat_add_gen Inv.sat_add)
         As reified_sat_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification Inv.sat_add (proj1 reified_sat_add_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_sat_add_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_sat_add_gen_correct) : interp_gen_cache.
  Local Opaque reified_sat_add_gen. (* needed for making [autorewrite] not take a very long time *)    

  Derive reified_twos_complement_word_to_montgomery_no_encode_gen
         SuchThat (is_reification_of reified_twos_complement_word_to_montgomery_no_encode_gen twos_complement_word_to_montgomery_no_encode)
         As reified_twos_complement_word_to_montgomery_no_encode_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification twos_complement_word_to_montgomery_no_encode (proj1 reified_twos_complement_word_to_montgomery_no_encode_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_twos_complement_word_to_montgomery_no_encode_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_twos_complement_word_to_montgomery_no_encode_gen_correct) : interp_gen_cache.
  Local Opaque reified_twos_complement_word_to_montgomery_no_encode_gen. 

  Derive reified_jumpprecomp_gen
         SuchThat (is_reification_of reified_jumpprecomp_gen jumpprecompmod)
         As reified_jumpprecomp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification jumpprecompmod (proj1 reified_jumpprecomp_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_jumpprecomp_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_jumpprecomp_gen_correct) : interp_gen_cache.
  Local Opaque reified_jumpprecomp_gen. (* needed for making [autorewrite] not take a very long time *)
  
  Derive reified_precomp_gen
         SuchThat (is_reification_of reified_precomp_gen precompmod)
         As reified_precomp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification precompmod (proj1 reified_precomp_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_precomp_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_precomp_gen_correct) : interp_gen_cache.
  Local Opaque reified_precomp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification divstep (proj1 reified_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

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
End WordByWordMontgomeryInversion.
