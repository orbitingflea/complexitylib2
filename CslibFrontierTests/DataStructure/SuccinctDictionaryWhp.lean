/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhp
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec

/-!
# With-High-Probability Fixed-Capacity Succinct Dynamic Dictionary Tests

This module provides test cases exercising the with-high-probability succinct dynamic
dictionary on the Word-RAM:
1. Positive space and parameter bounds via `succinctDictionaryWhp_exists`.
2. Sequential composition and whole-sequence execution under `seq_whp_ofFn`.
-/

@[expose] public section

namespace CslibFrontierTests.SuccinctDictionaryWhp

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp
open scoped ENNReal

/-- Concrete exercise of `succinctDictionaryWhp_exists`. -/
theorem test_succinctDictionaryWhp_concrete
    (hfit : Fits 16 (0 + (whpSpace 1 16 16 16 8 + 2 * 16))) :
    ∃ (spaceWords initTime timeBound : ℕ) (pFail : ℝ≥0∞),
      pFail ≤ (max 8 1 : ℝ≥0∞)⁻¹ ^ 1 ∧
      spaceWords ≤ Dynamic.succinctWords (whpSpaceFactor 1) whpSpaceConst 16 16 16 8 ∧
      timeBound ≤ whpTimeBound 1 ∧
      initTime ≤ whpInitFactor 1 * (whpSpace 1 16 16 16 8 + 1) := by
  have hnU : 8 ≤ 16 := by decide
  have hw : 1 ≤ 16 := by decide
  have hV : Fits 16 16 := by decide
  obtain ⟨sp, initT, tBdd, pF, hFail, hSp, hTime, hInit, _⟩ :=
    succinctDictionaryWhp_exists 1 16 16 16 8 0 hnU hw hV hfit
  exact ⟨sp, initT, tBdd, pF, hFail, hSp, hTime, hInit⟩

/-- Exercise of sequential composition `seq_whp_ofFn` on `SuccinctWhp.impl`:
execution over a single query operation completes with probability at least `1 - failureProb`. -/
theorem test_seq_whp_single_op
    (hfit : Fits 16 (0 + (whpSpace 1 16 16 16 8 + 2 * 16))) :
    let C := impl 1 16 16 16 8 0 (by decide) (by decide) hfit
    ∃ (ν₀ : PMF (C.Seed × Data rWhp))
      (τ_final : PMF (WhpSeqOutcome C.Seed (Dynamic.spec 16 16 8) rWhp)),
      RandHaltsWithin 16 ((subroutineCode 1 16 16 16 8).initFresh.program
        (subroutineCode 1 16 16 16 8).output)
        ⟨0, Data.init []⟩ (C.initTime + 1) ∧
      C.ExecWhpSteps (subroutineCode 1 16 16 16 8).output [.query ⟨0, by decide⟩]
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty 16, p.2⟩) τ_final ∧
      1 - ((1 : ℕ) : ℝ≥0∞) * C.failureProb ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ C.worstCaseTime ∧
            tr.transcript =
              ((Dynamic.spec 16 16 8).run (Dictionary.empty 16) [.query ⟨0, by decide⟩]).2} := by
  intro C
  have hx : (Data.init [] : Data rWhp).Bounded 16 := Data.Bounded.init (by simp [InputFits])
  have hz : ∀ a ∈ (Block.mk 0 C.space).footprint, (Data.init [] : Data rWhp).mem a = 0 := by
    intro a ha
    simp [Data.init]
  have hv : (Dynamic.spec 16 16 8).ValidHistory (Dictionary.empty 16) [.query ⟨0, by decide⟩] := by
    refine ⟨by simp [Dynamic.valid], trivial⟩
  obtain ⟨ν₀, τ_final, hhalts, _, _, hex, _, _, hsucc⟩ :=
    C.seq_whp_ofFn (subroutineCode 1 16 16 16 8).output [.query ⟨0, by decide⟩] hx
      (by simp [Data.init]) (fun j => Fin.elim0 j) hz hv
  refine ⟨ν₀, τ_final, hhalts, hex, ?_⟩
  have hlen : [Dynamic.Op.query (⟨0, by decide⟩ : Fin 16)].length = 1 := rfl
  simpa only [hlen, Nat.cast_one] using hsucc

end CslibFrontierTests.SuccinctDictionaryWhp

end
