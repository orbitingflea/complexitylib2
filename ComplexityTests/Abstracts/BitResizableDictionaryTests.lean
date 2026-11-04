/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.BitResizableDictionaryAbstract

/-!
# Formal Abstract Tests: Capacity-Unbounded Succinct Dictionary (`BitResizableDictionaryAbstract`)

Non-vacuity and concrete evaluation checks for
`ComplexityAbstracts.BitResizableDictionaryAbstract`.
-/

namespace ComplexityTests.Abstracts.BitResizableDictionaryTests

open scoped ENNReal
open ComplexityAbstracts.BitResizableDictionaryAbstract

/-! ## Concrete Bitwise, Memory, and Succinct Space Quantity Evaluations -/

example : ceilDiv 0 64 = 0 := by decide
example : ceilDiv 1 64 = 1 := by decide
example : ceilDiv 64 64 = 1 := by decide
example : ceilDiv 65 64 = 2 := by decide

example : logLogFactor 0 = 1 := by decide
example : logLogFactor 4 = 1 := by decide
example : logLogFactor 16 = 2 := by decide

example : optBits 16 8 0 = 0 := by decide
example : optBits 16 8 2 = 13 := by decide
example : optBits 4 4 4 = 8 := by decide

example : bucketBits 0 = 0 := by decide
example : quotientBits 16 0 = 4 := by decide
example : valBits 8 = 3 := by decide
example : itemBits 16 8 0 = 7 := by decide
example : itemBits 4 4 4 = 4 := by decide

example : targetCap 16 0 = 0 := by decide
example : targetCap 16 3 = 6 := by decide
example : targetCap 4 3 = 4 := by decide

example : EpochInv 16 0 0 := Or.inl ⟨rfl, rfl⟩
example : EpochInv 16 4 2 := by
  exact Or.inr ⟨by decide, by decide, by decide, by decide⟩

example : getBit 64 (fun q => if q = 0 then 5 else 0) 0 = true := by decide
example : getBit 64 (fun q => if q = 0 then 5 else 0) 1 = false := by decide
example : getBit 64 (fun q => if q = 0 then 5 else 0) 2 = true := by decide
example : getField 64 (fun q => if q = 0 then 5 else 0) 0 3 = 5 := by decide
example : clearRangeMem 64 (fun _ => 7) 1 3 0 = 1 := by decide

/-! ## Sample Valid Operation Sequence and Dictionary Semantics -/

abbrev k0 : Fin 4 := ⟨0, by decide⟩
abbrev k1 : Fin 4 := ⟨1, by decide⟩
abbrev k2 : Fin 4 := ⟨2, by decide⟩

/-- Six-operation sequence (`insert 1 3`, `insert 2 1`, `query 1`, `delete 1`, `query 1`,
`query 2`) on `Fin 4` with value bound `V = 4`. -/
def sampleOps : List (DictOp 4) :=
  [ .insert k1 3
  , .insert k2 1
  , .query k1
  , .delete k1
  , .query k1
  , .query k2 ]

theorem validDictHistory_sampleOps : ValidDictHistory 4 (emptyDict 4) sampleOps := by
  dsimp only [ValidDictHistory, validDictOp, sampleOps]
  refine ⟨by decide, by decide, trivial, trivial, trivial, trivial, trivial⟩

example : decodeQueryRegs ⟨fun _ => 0, fun _ => 0, 0⟩ = none := rfl
example : decodeQueryRegs ⟨fun i => if i.val = 1 then 1 else 7, fun _ => 0, 0⟩ = some 7 := rfl

/-- Zeroed 12-register `Data 12` state at word width `w = 64`. -/
def zeroData12 : Data 12 :=
  ⟨fun _ => 0, fun _ => 0, 0⟩

theorem wellFormed_zeroData12 : zeroData12.WellFormed 64 := by
  dsimp only [Data.WellFormed, zeroData12]
  refine ⟨fun _ => by decide, fun _ => by decide, by decide, fun i _ => ?_⟩
  simp [getBit]

/-! ## Headline Theorem Non-Vacuity (`U = 4, V = 4, w = 64`) -/

theorem optBits_bound_4_4_64 :
    ∀ N' ≤ 4, optBits 4 4 N' + 680 * N' * logLogFactor N' + 218 * 64 < 2 ^ 64 := by
  intro N' hN'
  interval_cases N' <;> decide

/-- Concrete instantiation of `bitResizableDictionary` at `(U, V, w) = (4, 4, 64)`, verifying that
all hypotheses (`4 ≤ w`, `U < 2 ^ w`, `V ≤ 2 ^ w`, `zeroData12.WellFormed 64`,
`∀ N' ≤ 4, dictBitSize N' N' < 2 ^ 64`, and `ValidDictHistory 4 (emptyDict 4) sampleOps`) are
simultaneously satisfiable and produce an initial execution trace of `sampleOps` in `21` init
instructions with initial footprint `4 * 64 = 256` bits. -/
theorem bitResizableDictionary_nonvacuous_4_4_64 :
    ∃ (EpochSeed : ℕ → Type)
      (epochSeedPMF : ∀ N, PMF (EpochSeed N))
      (_ : ∀ N, Nonempty (EpochSeed N))
      (Companion : Type)
      (emptyCompanion : Companion)
      (DictInv : ∀ N, EpochSeed N → DictState 4 → Companion → Data 12 → Prop)
      (totalPotential : ℕ → DictState 4 → Companion → ℕ)
      (stepOverhead : ∀ N, EpochSeed N → DictState 4 → DictOp 4 → ℕ)
      (dictBitSize : ℕ → ℕ → ℕ)
      (initCode : EpochSeed 0 → Code 12),
      dictBitSize 0 0 = 256 ∧
      (∀ N n_t, dictBitSize N (n_t + 1) = dictBitSize N n_t + itemBits 4 4 N) ∧
      (∀ θ₀ : EpochSeed 0,
        ∃ B_tot : ℕ,
          DemonicExecWithin 64 (initCode θ₀) zeroData12
            (fun y₀ =>
              DictInv 0 θ₀ (emptyDict 4) emptyCompanion y₀ ∧
              y₀.bitSize = 256 ∧
              ExecTrace 4 4 64 EpochSeed epochSeedPMF Companion DictInv
                totalPotential stepOverhead sampleOps 0 θ₀ (emptyDict 4)
                emptyCompanion y₀ B_tot ∧
              ∃ ts : List ℕ, ts.length = 6 ∧ ts.sum ≤ B_tot)
            21) := by
  obtain ⟨EpochSeed, epochSeedPMF, hne, Companion, emptyCompanion, DictInv,
    totalPotential, stepOverhead, dictBitSize, initCode, _clientCode,
    hd0, hstep_sz, hopt_le, _hspace, _hstep, hseq, _hreuse⟩ :=
    bitResizableDictionary (U := 4) (V := 4) (w := 64) (by decide) (by decide) (by decide)
  have hfit_all : ∀ N' ≤ 4, dictBitSize N' N' < 2 ^ 64 := by
    intro N' hN'
    exact lt_of_le_of_lt (hopt_le N' N' (epochInv_self hN')) (optBits_bound_4_4_64 N' hN')
  refine ⟨EpochSeed, epochSeedPMF, hne, Companion, emptyCompanion, DictInv,
    totalPotential, stepOverhead, dictBitSize, initCode, hd0, hstep_sz, fun θ₀ => ?_⟩
  exact hseq hfit_all θ₀ wellFormed_zeroData12 rfl sampleOps validDictHistory_sampleOps

end ComplexityTests.Abstracts.BitResizableDictionaryTests
