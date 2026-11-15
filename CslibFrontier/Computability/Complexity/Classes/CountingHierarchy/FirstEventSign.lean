/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.BoundedSearch

/-!
# Three-way selection at a bounded first event

`firstEventSign` returns `1` if the first event satisfies the positive test, otherwise `-1`
if it satisfies the negative test, and otherwise `0`. Positive has priority when both tests
hold. The operation is generic: the test names do not assert any relation to an integer's sign.

Three uniform F_a Boolean evaluators and a polynomial-time binary endpoint give an
F_(a+2) signed binary output. The first-event quantifiers are those of `firstEventTest`;
no CRT, approximation or manuscript-specific parameters occur in the operation.

## Main definitions

* `Cslib.Complexity.firstEventSign`: positive-priority three-way first-event selection.

## Main results

* `Cslib.Complexity.firstEventSign_mem_CountingFunction`: the two-level computational bound.
* `Cslib.Complexity.firstEventSign_eq_one_iff`: positive-test semantics.
* `Cslib.Complexity.firstEventSign_eq_neg_one_iff`: negative-test semantics with positive priority.
* `Cslib.Complexity.firstEventSign_eq_zero_iff`: neither first-event test holds.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Select `1`, `-1`, or `0` using tests at the first event below `r x`.
The positive test takes priority if both tests hold. This operation alone does not recover
an integer's sign; an application must establish what its tests mean. -/
@[expose] noncomputable def firstEventSign {α : Type}
    (event positive negative : α × ℕ → Bool) (r : α → ℕ) (x : α) : ℤ :=
  if firstEventTest event positive r x then 1 else
    if firstEventTest event negative r x then -1 else 0

/-- The positive first-event test characterizes output one, regardless of the negative test. -/
theorem firstEventSign_eq_one_iff {α : Type} (event positive negative : α × ℕ → Bool)
    (r : α → ℕ) (x : α) :
    firstEventSign event positive negative r x = 1 ↔
      ∃ i < r x, event (x, i) = true ∧ positive (x, i) = true ∧
        ∀ j < i, event (x, j) = false := by
  rw [← firstEventTest_eq_true_iff]
  cases hp : firstEventTest event positive r x <;>
    cases hn : firstEventTest event negative r x <;> simp [firstEventSign, hp, hn]

/-- Output minus one requires the negative first-event test and failure of the positive one. -/
theorem firstEventSign_eq_neg_one_iff {α : Type} (event positive negative : α × ℕ → Bool)
    (r : α → ℕ) (x : α) :
    firstEventSign event positive negative r x = -1 ↔
      (¬ ∃ i < r x, event (x, i) = true ∧ positive (x, i) = true ∧
        ∀ j < i, event (x, j) = false) ∧
      ∃ i < r x, event (x, i) = true ∧ negative (x, i) = true ∧
        ∀ j < i, event (x, j) = false := by
  simp only [← firstEventTest_eq_true_iff]
  cases hp : firstEventTest event positive r x <;>
    cases hn : firstEventTest event negative r x <;> simp [firstEventSign, hp, hn]

/-- Output zero means that neither test accepts the first event, including when no event exists. -/
theorem firstEventSign_eq_zero_iff {α : Type} (event positive negative : α × ℕ → Bool)
    (r : α → ℕ) (x : α) :
    firstEventSign event positive negative r x = 0 ↔
      (¬ ∃ i < r x, event (x, i) = true ∧ positive (x, i) = true ∧
        ∀ j < i, event (x, j) = false) ∧
      ¬ ∃ i < r x, event (x, i) = true ∧ negative (x, i) = true ∧
        ∀ j < i, event (x, j) = false := by
  simp only [← firstEventTest_eq_true_iff]
  cases hp : firstEventTest event positive r x <;>
    cases hn : firstEventTest event negative r x <;> simp [firstEventSign, hp, hn]

/-- Three uniform F_a Boolean evaluators give signed binary first-event selection in F_(a+2).
No semantic sign-correctness premise is needed for this computational certificate. -/
theorem firstEventSign_mem_CountingFunction {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) {event positive negative : α × ℕ → Bool} {r : α → ℕ}
    (hevent : event ∈ CountingFunction a (encPair enc encNat) encBool)
    (hpositive : positive ∈ CountingFunction a (encPair enc encNat) encBool)
    (hnegative : negative ∈ CountingFunction a (encPair enc encNat) encBool)
    (hr : ComputableInPolyTime r enc encNat) :
    firstEventSign event positive negative r ∈ CountingFunction (a + 2) enc encIntBin :=
  CountingFunction.ite (firstEventTest_mem_CountingFunction D hevent hpositive hr)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1))
    (CountingFunction.ite (firstEventTest_mem_CountingFunction D hevent hnegative hr)
      (CountingFunction.of_polyTime (ComputableInPolyTime.const (-1)))
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 0)))

end Cslib.Complexity
