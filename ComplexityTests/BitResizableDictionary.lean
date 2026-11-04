/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Dictionary.BitResizable.Client

/-!
# Bit-resizable succinct dictionary tests

Concrete evaluations, non-vacuity checks, and axiom guards for the capacity-unbounded bit-resizable
succinct dictionary (`Cslib.DataStructure.Dictionary.BitResizable`).
-/

public section

namespace ComplexityTests.BitResizableDictionary

open scoped ENNReal
open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.BitResizable

/-! ## Concrete Specification and Resource Evaluations -/

example : Dynamic.optBits 4 4 0 = 0 := by decide
example : Dynamic.optBits 4 4 2 = 7 := by decide
example : Dynamic.logLogFactor 2 = 1 := by decide
example : Dynamic.logLogFactor 16 = 2 := by decide
example : dictBitSize 4 4 64 0 0 = 256 := by decide

/-- Sample operation history (`insert 0 2`, `insert 1 3`, `query 0`, `delete 0`, `query 0`,
`query 1`) on `Fin 4` with `V = 4`. -/
def sampleOps : List (Dynamic.Op 4) :=
  [ .insert ⟨0, by decide⟩ 2,
    .insert ⟨1, by decide⟩ 3,
    .query ⟨0, by decide⟩,
    .delete ⟨0, by decide⟩,
    .query ⟨0, by decide⟩,
    .query ⟨1, by decide⟩ ]

lemma validHistory_sampleOps :
    (BitResizable.spec 4 4).ValidHistory (Dynamic.empty 4) sampleOps := by
  refine ⟨by decide, by decide, trivial, trivial, trivial, trivial, trivial⟩

lemma fits_dictBitSize_4_4_64 (N' : ℕ) (hN' : N' ≤ 4) :
    Fits 64 (dictBitSize 4 4 64 N' N') := by
  have hepoch : EpochInv 4 N' N' := by
    rcases Nat.eq_zero_or_pos N' with rfl | hpos
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hpos, le_rfl, by omega, hN'⟩
  have h1 : dictBitSize 4 4 64 N' N' ≤
      Dynamic.optBits 4 4 N' + 680 * N' * Dynamic.logLogFactor N' + 218 * 64 :=
    dictBitSize_le_optBits (by decide) (by decide) hepoch
  have h2 : Dynamic.optBits 4 4 N' + 680 * N' * Dynamic.logLogFactor N' + 218 * 64 < 2 ^ 64 := by
    interval_cases N' <;> decide
  exact lt_of_le_of_lt h1 h2

/-- Initial empty `BitRAM.Data 12` state at word width `64`. -/
def zeroData12 : BitRAM.Data 12 :=
  ⟨fun _ => 0, fun _ => 0, 0⟩

lemma wellFormed_zeroData12 : zeroData12.WellFormed 64 :=
  ⟨fun _ => fits_zero 64, BitMemory.wellFormed_empty 64⟩

/-- Non-vacuity of `seq_transition_from_empty` on `sampleOps` at `(U, V, w) = (4, 4, 64)`. -/
theorem nonvacuous_seq_transition_from_empty :
    ∀ θ₀ : Succinct.QuotHashSeed 4 0,
      ∃ B_tot : ℕ,
        BitRAM.DemonicExecWithin 64 (initDictCode 4 4 64 θ₀) zeroData12
          (fun y₀ =>
            DictInv 4 4 64 0 θ₀ (Dynamic.empty 4) Companion.empty y₀ ∧
            y₀.bitSize = 4 * 64 ∧
            ExecTrace 4 4 64 sampleOps 0 θ₀ (Dynamic.empty 4) Companion.empty y₀ B_tot ∧
            ∃ ts : List ℕ, ts.length = sampleOps.length ∧ ts.sum ≤ B_tot)
          21 := fun θ₀ =>
  seq_transition_from_empty (by decide) (by decide) (by decide)
    fits_dictBitSize_4_4_64 θ₀ wellFormed_zeroData12 rfl sampleOps validHistory_sampleOps

/-! ## Axiom Guards -/

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.dictBitSize_le_optBits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dictBitSize_le_optBits

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.DictInv.space_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DictInv.space_tight

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.init_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms init_transition

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.step_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_transition

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.tsum_stepOverhead_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tsum_stepOverhead_le

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.seq_transition_from_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms seq_transition_from_empty

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.delete_reuses_released_bits_subroutine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms delete_reuses_released_bits_subroutine

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.dict_subroutine_with_delete_reuse_from_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dict_subroutine_with_delete_reuse_from_empty

end ComplexityTests.BitResizableDictionary
