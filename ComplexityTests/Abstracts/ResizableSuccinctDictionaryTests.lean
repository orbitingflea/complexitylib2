/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

/-!
# Formal Abstract Tests: Word-Granular Resizable Word-RAM, Dynamic Array, and Succinct Dictionary

Non-vacuity and concrete evaluation checks for
`ComplexityAbstracts.ResizableSuccinctDictionaryAbstract`.
-/

namespace ComplexityTests.Abstracts.ResizableSuccinctDictionaryTests

open scoped ENNReal
open ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

/-! ## Concrete Evaluations of Model & Space Functions -/

example : arrayPackedWords 64 5 100 = 8 := by decide
example : arrayActiveWords 64 5 100 = 9 := by decide
example : 100 * 5 ≤ arrayActiveWords 64 5 100 * 64 ∧
    arrayActiveWords 64 5 100 * 64 < 100 * 5 + 2 * 64 :=
  resizableArray_space_tight (by decide) (by decide) (by decide) 100

example : targetCap 100 0 = 0 := by decide
example : targetCap 100 10 = 20 := by decide
example : EpochValid 10 (targetCap 100 10) := ⟨by decide, by decide⟩
example : logLogFactor 4 = 1 := by decide
example : optBits 8 4 2 = 9 := by decide

/-- Sample dynamic dictionary operation sequence (`insert 0 3`, `insert 1 2`, `delete 0`, `query 1`)
on `Fin 4` with value bound `V = 8` and **no capacity cap**. -/
def sampleOps : List (DynamicOp 4) :=
  [ .insert ⟨0, by decide⟩ 3,
    .insert ⟨1, by decide⟩ 2,
    .delete ⟨0, by decide⟩,
    .query ⟨1, by decide⟩ ]

lemma validDictSeq_sampleOps : ValidDictSeq 8 (emptyDict 4) sampleOps :=
  ⟨(by decide : 3 < 8), (by decide : 2 < 8), trivial, trivial, trivial⟩

example : (runDict (emptyDict 4) sampleOps) ⟨0, by decide⟩ = none := by decide
example : (runDict (emptyDict 4) sampleOps) ⟨1, by decide⟩ = some 2 := by decide
example : (dictDom (runDict (emptyDict 4) sampleOps)).card = 1 := by decide
example : runEpochInit 8 (emptyDict 4) 0 sampleOps = 1 := by decide
example : maxEpochCap 8 (emptyDict 4) 0 sampleOps = 2 := by decide

/-! ## Non-Vacuity of Headline Theorems -/

private lemma fit_epochPeakWords_sampleOps :
    ∀ N ≤ maxEpochCap 8 (emptyDict 4) 0 sampleOps, 10 + epochPeakWords 4 8 64 N < 2 ^ 64 := by
  intro N hN
  have hN2 : N ≤ 2 := hN
  interval_cases N <;> decide

/-- Non-vacuity of `resizableSuccinctDynamicDictionary` on `sampleOps` at
`(U, V, w) = (4, 8, 64)`. -/
theorem nonvacuous_resizableSuccinctDynamicDictionary :
    ∃ (r C_init C_op C_space C_word : ℕ) (hr : 256 ≤ r) (p_init p_op : RProgram r)
      (ν_init ν_final : PMF (RState r)) (T_ops : ℝ≥0∞),
      C_space = 1355 ∧
      C_word = 380 ∧
      RandFaultFreeDemonic 64 p_init ⟨fun _ => 0, fun _ => 0, 10⟩ ∧
      (∀ adv, expectedTimeDemonic 64 adv p_init ⟨fun _ => 0, fun _ => 0, 10⟩ ≤ C_init) ∧
      (∀ x_init ∈ ν_init.support,
        RBounded 64 x_init ∧
        x_init.frontier = 10 + compactedEpochWords 4 8 64 0 0 ∧
        x_init.frontier = 10 + 4) ∧
      ExecResizableDynDictOps hr 8 64 p_op 10 ⟨fun _ => 0, fun _ => 0, 10⟩
        (emptyDict 4) 0 sampleOps ν_init ν_final T_ops ∧
      (C_init : ℝ≥0∞) + T_ops ≤ ((C_init + sampleOps.length * C_op : ℕ) : ℝ≥0∞) := by
  obtain ⟨r, C_init, C_op, C_space, C_word, hr, hcs, hcw, hmain⟩ :=
    resizableSuccinctDynamicDictionary
  obtain ⟨p_init, p_op, hbase⟩ := hmain 4 8 64
  let x₀ : RState r := ⟨fun _ => 0, fun _ => 0, 10⟩
  have hx₀_bdd : RBounded 64 x₀ :=
    ⟨⟨fun _ => (by decide : 0 < 2 ^ 64), fun _ => (by decide : 0 < 2 ^ 64)⟩,
      (by decide : 10 < 2 ^ 64), fun _ _ => rfl⟩
  obtain ⟨ν_init, ν_final, T_ops, hff, hinit_time, hinit, hexec, htime⟩ :=
    hbase 10 (by decide) (by decide) (by decide)
      x₀ hx₀_bdd rfl sampleOps fit_epochPeakWords_sampleOps validDictSeq_sampleOps
  exact ⟨r, C_init, C_op, C_space, C_word, hr, p_init, p_op, ν_init, ν_final, T_ops,
    hcs, hcw, hff, hinit_time,
    fun x hx => ⟨(hinit x hx).1, (hinit x hx).2.1, (hinit x hx).2.2.1⟩,
    hexec, htime⟩

/-- Non-vacuity of `unbounded_seq_expected_amortized` on `sampleOps` at `(U, V, w) = (4, 8, 64)`. -/
theorem nonvacuous_unbounded_seq_expected_amortized :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ) (_hr : 256 ≤ r),
      C_space = 1355 ∧
      C_word = 380 ∧
      let s_final := runDict (emptyDict 4) sampleOps
      let n_final := (dictDom s_final).card
      let n_init_final := runEpochInit 8 (emptyDict 4) 0 sampleOps
      let N_final := targetCap 4 n_init_final
      EpochValid n_final N_final ∧
      N_final ≤ 4 ∧
      (∀ u v, s_final u = some v → v < 8) ∧
      compactedEpochWords 4 8 64 N_final n_final ≤
        succinctWords C_space C_word 4 8 64 n_final ∧
      64 * compactedEpochWords 4 8 64 N_final n_final ≤
        optBits 4 8 n_final + C_space * n_final * logLogFactor n_final + (C_word + 1) * 64 ∧
      2 * rebuildUnitCost * ((n_final - n_init_final) + (n_init_final - n_final)) ≤
        sampleOps.length * resizableChargeVal := by
  obtain ⟨r, rebuildUnitCost, resizableChargeVal, C_space, C_word,
    hr, hcs, hcw, hseq⟩ := unbounded_seq_expected_amortized
  let x₀ : RState r := ⟨fun _ => 0, fun _ => 0, 10⟩
  have hx₀_bdd : RBounded 64 x₀ :=
    ⟨⟨fun _ => (by decide : 0 < 2 ^ 64), fun _ => (by decide : 0 < 2 ^ 64)⟩,
      (by decide : 10 < 2 ^ 64), fun _ _ => rfl⟩
  have h := hseq 4 8 64 10 (by decide) (by decide) (by decide)
    x₀ hx₀_bdd rfl sampleOps fit_epochPeakWords_sampleOps validDictSeq_sampleOps
  dsimp only at h
  obtain ⟨hepoch, hN, hval, hwords, hbits, hpot, _⟩ := h
  exact ⟨r, rebuildUnitCost, resizableChargeVal, C_space, C_word,
    hr, hcs, hcw, hepoch, hN, hval, hwords, hbits, hpot⟩

/-- Non-vacuity of `dictionary_client_memory_reuse` at `(U, V, w) = (4, 8, 64)` on `sampleOps`. -/
theorem nonvacuous_dictionary_client_memory_reuse :
    ∃ (r : ℕ) (hr : 256 ≤ r) (x_dict x_dealloc x_reused : RState r),
      RBounded 64 x_dict ∧
      x_dict.frontier =
        10 + compactedEpochWords 4 8 64
          (targetCap 4 (runEpochInit 8 (emptyDict 4) 0 sampleOps))
          (dictDom (runDict (emptyDict 4) sampleOps)).card ∧
      SeqOutputCorrect hr 8 (emptyDict 4) sampleOps x_dict.regs ∧
      ExecRProgramDemonic 64
        (deallocProgram ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩)
        x_dict x_dealloc 3 ∧
      RBounded 64 x_dealloc ∧
      x_dealloc.frontier = 10 ∧
      RBounded 64 x_reused ∧
      x_reused.frontier = 10 + 5 ∧
      (∀ a, 10 ≤ a → a < 10 + 5 → x_reused.mem a = 0) := by
  obtain ⟨r, hr, hreuse⟩ := dictionary_client_memory_reuse
  obtain ⟨_, hsub⟩ := hreuse 4 8 64 (by decide) (by decide) (by decide)
  let x₀ : RState r := ⟨fun _ => 0, fun _ => 0, 10⟩
  have hx₀_bdd : RBounded 64 x₀ :=
    ⟨⟨fun _ => (by decide : 0 < 2 ^ 64), fun _ => (by decide : 0 < 2 ^ 64)⟩,
      (by decide : 10 < 2 ^ 64), fun _ _ => rfl⟩
  obtain ⟨x_dict, x_dealloc, x_reused, hd_bdd, hd_fr, _, hd_out, _, hexec_de, hde_bdd, hde_fr,
    hre_bdd, hre_fr, _, hre_zero⟩ :=
    hsub 10 5 x₀ sampleOps fit_epochPeakWords_sampleOps (by decide) hx₀_bdd rfl
      validDictSeq_sampleOps
  exact ⟨r, hr, x_dict, x_dealloc, x_reused, hd_bdd, hd_fr, hd_out, hexec_de,
    hde_bdd, hde_fr, hre_bdd, hre_fr, hre_zero⟩

end ComplexityTests.Abstracts.ResizableSuccinctDictionaryTests
