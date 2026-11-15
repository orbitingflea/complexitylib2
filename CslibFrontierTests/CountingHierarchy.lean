/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Aggregation
import CslibFrontier.Computability.Complexity.Classes.Oracle.BinarySearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! Ordinary module clients: short-index counts, restricted sums, signed cancellation, and
adaptive composition, independently of real feasibility. -/

public section

namespace CslibFrontierTests.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- A test predicate selects indices beginning with true when the instance does not. -/
def selected (x : List Bool × List Bool) : Bool :=
  x.2.headD false && !x.1.headD false

private theorem selected_level (a : ℕ) :
    selected ∈ CountingFunction a (encPair encBits encBits) encBool :=
  CountingFunction.of_polyTime (by unfold selected; fun_prop)

/-- Tags select different fixed languages, including the documented empty-word behavior. -/
example : [false, true] ∈ taggedUnion {w | w.headD false = true} {w | w.headD true = false} ∧
    [true, false] ∈ taggedUnion {w | w.headD false = true} {w | w.headD true = false} ∧
    [] ∉ taggedUnion {w | w.headD false = true} {w | w.headD true = false} := by
  simp [taggedUnion]

/-- A fixed finite family shares an oracle even when its members are queried adaptively. -/
example (a : ℕ) : ∃ A ∈ CountingLevel a encBits,
    ∀ i : Bool, ComputableInPolyTimeWithOracle A
      (fun w : List Bool => if i then w.tail else w) encBits encBits := by
  apply CountingFunction.exists_common_oracle
  intro i
  apply CountingFunction.of_polyTime
  cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- Exponentially many indices are accepted by one fixed evaluator. -/
example (a : ℕ) :
    (fun w => acceptCount selected w w.length) ∈ CountingFunction (a + 1) encBits encNat :=
  CountingFunction.count_bits Decoder.bits (selected_level a) (by fun_prop)

example : acceptCount selected [] 3 = 4 := by decide
example : acceptCount selected [true] 3 = 0 := by decide
example : acceptCount selected [] 0 = 0 := by decide

/-- The upper endpoint of the binary search is needed even at width zero. -/
example : acceptCount (fun _ : List Bool × List Bool => true) [] 0 = 1 := by decide
example : acceptCount (fun _ : List Bool × List Bool => true) [] 4 = 16 := by decide

/-- Count recovery includes the maximum count and the singleton width-zero domain. -/
example : ((BinarySearch.step 16)^[5] (0, 5)).1 = 16 := by decide
example : ((BinarySearch.step 1)^[1] (0, 1)).1 = 1 := by decide
example : ((BinarySearch.step 0)^[1] (0, 1)).1 = 0 := by decide

private def inRange (x : List Bool × List Bool) : Bool :=
  decide (BitString.binaryValue x.2 < BitString.binaryValue x.1)

private def indexValue (x : List Bool × List Bool) : ℕ := BitString.binaryValue x.2

private theorem range_level (a : ℕ) :
    inRange ∈ CountingFunction a (encPair encBits encBits) encBool :=
  CountingFunction.of_polyTime (by unfold inRange; fun_prop)

private theorem index_level (a : ℕ) :
    indexValue ∈ CountingFunction a (encPair encBits encBits) encNat :=
  CountingFunction.of_polyTime (by unfold indexValue; fun_prop)

/-- A binary interval restriction shares the fixed evaluator oracle with the summand. -/
example (a : ℕ) :
    (fun w => ∑ i : Fin w.length → Bool,
      if inRange (w, List.ofFn i) then indexValue (w, List.ofFn i) else 0) ∈
        CountingFunction (a + 1) encBits encNat :=
  CountingFunction.sum_bits_restrict Decoder.bits (index_level a) (range_level a) (by fun_prop)

example : (∑ i : Fin 2 → Bool,
    if inRange ([true, true], List.ofFn i) then indexValue ([true, true], List.ofFn i)
      else 0) = 3 := by decide

example : (∑ i : Fin 0 → Bool,
    if inRange ([], List.ofFn i) then indexValue ([], List.ofFn i) else 0) = 0 := by decide

private def signed (x : List Bool × List Bool) : ℤ :=
  if x.2.headD false then 1 else -1

private theorem signed_level (a : ℕ) :
    signed ∈ CountingFunction a (encPair encBits encBits) encIntBin :=
  CountingFunction.of_polyTime (by unfold signed; fun_prop)

/-- Signed sums count the two parts and subtract at the same successor level. -/
example (a : ℕ) :
    (fun w => ∑ i : Fin w.length → Bool, signed (w, List.ofFn i)) ∈
      CountingFunction (a + 1) encBits encIntBin :=
  CountingFunction.sum_bits_int Decoder.bits (signed_level a) (by fun_prop)

example : (∑ i : Fin 3 → Bool, signed ([], List.ofFn i)) = 0 := by decide
example : (∑ i : Fin 0 → Bool, signed ([], List.ofFn i)) = -1 := by decide

open Classical in
/-- The language conversion adds one level after existential choice. -/
example (a : ℕ) :
    {w : List Bool | ∃ i : List Bool, i.length = w.length ∧ selected (w, i) = true} ∈
      CountingLevel (a + 2) encBits := by
  simpa only [decide_eq_true_eq] using
    CountingFunction.decision
      (CountingFunction.exists_bits Decoder.bits (selected_level a) (by fun_prop))

/-- Same-level calls can be chained adaptively without increasing their level. -/
example (a : ℕ) {f g : List Bool → List Bool}
    (hf : f ∈ CountingFunction a encBits encBits)
    (hg : g ∈ CountingFunction a encBits encBits) :
    (fun w => g (f w)) ∈ CountingFunction a encBits encBits := CountingFunction.comp hg hf

end CslibFrontierTests.CountingHierarchy
