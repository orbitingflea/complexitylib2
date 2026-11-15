/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Quantification and first-event tests on binary intervals

An interval endpoint can have exponential value but polynomial binary length. Existential
and universal quantification cost one function level; testing a property of the first event
costs two. These rules use one evaluator for all indices, including nested indices.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace CountingFunction

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

open Classical in
/-- Existential quantification over a short binary interval costs one function level. -/
theorem exists_range (D : Decoder enc) {V : α × ℕ → Bool} {r : α → ℕ}
    (hV : V ∈ CountingFunction a (encPair enc encNat) encBool)
    (hr : ComputableInPolyTime r enc encNat) :
    (fun x => decide (∃ i < r x, V (x, i) = true)) ∈
      CountingFunction (a + 1) enc encBool := by
  have hsum := sum_range D (map hV
    (ComputableInPolyTime.of_finite Bool.toNat)) hr
  have h := map hsum (g := fun n : ℕ => decide (0 < n)) (by fun_prop)
  convert h using 1
  funext x
  congr 1
  apply propext
  rw [Finset.sum_pos_iff]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨i, hi, htrue⟩
    exact ⟨i, hi, by simp only [htrue, Bool.toNat_true]; omega⟩
  · rintro ⟨i, hi, hpos⟩
    refine ⟨i, hi, ?_⟩
    cases hvi : V (x, i) <;> simp_all

open Classical in
/-- Universal quantification over a short binary interval also costs one function level. -/
theorem forall_range (D : Decoder enc) {V : α × ℕ → Bool} {r : α → ℕ}
    (hV : V ∈ CountingFunction a (encPair enc encNat) encBool)
    (hr : ComputableInPolyTime r enc encNat) :
    (fun x => decide (∀ i < r x, V (x, i) = true)) ∈
      CountingFunction (a + 1) enc encBool := by
  have hnot := map hV ComputableInPolyTime.bool_not
  have h := map (exists_range D hnot hr) ComputableInPolyTime.bool_not
  convert h using 1
  funext x
  simp only [← decide_not, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false]

end CountingFunction

open Classical in
/-- Does the first event below a binary endpoint satisfy the supplied test?
Both event and test are uniform evaluators, not input-dependent families of programs. -/
noncomputable def firstEventTest {α : Type} (event test : α × ℕ → Bool)
    (r : α → ℕ) (x : α) : Bool :=
  decide (∃ i < r x, event (x, i) = true ∧ test (x, i) = true ∧
    ∀ j < i, event (x, j) = false)

open Classical in
/-- Semantic characterization of the first-event operation, including empty intervals. -/
theorem firstEventTest_eq_true_iff {α : Type} (event test : α × ℕ → Bool)
    (r : α → ℕ) (x : α) :
    firstEventTest event test r x = true ↔
      ∃ i < r x, event (x, i) = true ∧ test (x, i) = true ∧
        ∀ j < i, event (x, j) = false := by
  simp only [firstEventTest, decide_eq_true_eq]

/-- A test at the first event on a short binary interval uses two function levels.
The inner universal test and outer existential test have fixed uniform evaluators. -/
theorem firstEventTest_mem_CountingFunction {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) {event test : α × ℕ → Bool} {r : α → ℕ}
    (hevent : event ∈ CountingFunction a (encPair enc encNat) encBool)
    (htest : test ∈ CountingFunction a (encPair enc encNat) encBool)
    (hr : ComputableInPolyTime r enc encNat) :
    firstEventTest event test r ∈ CountingFunction (a + 2) enc encBool := by
  classical
  have hnot : (fun x => !(event x)) ∈ CountingFunction a (encPair enc encNat) encBool :=
    CountingFunction.map hevent ComputableInPolyTime.bool_not
  have hprevious :
      (fun x : (α × ℕ) × ℕ => !(event (x.1.1, x.2))) ∈
        CountingFunction a (encPair (encPair enc encNat) encNat) encBool :=
    CountingFunction.preprocess hnot (g := fun x : (α × ℕ) × ℕ => (x.1.1, x.2))
      (by fun_prop)
  have hfirst := CountingFunction.forall_range (Decoder.pair D Decoder.nat)
    hprevious (ComputableInPolyTime.snd _ _)
  have hguard := CountingFunction.map
    (CountingFunction.prod (CountingFunction.mono (Nat.le_succ a) hevent)
      (CountingFunction.prod (CountingFunction.mono (Nat.le_succ a) htest) hfirst))
    (g := fun p : Bool × Bool × Bool => p.1 && (p.2.1 && p.2.2)) (by fun_prop)
  have h := CountingFunction.exists_range D hguard hr
  change (fun x => decide (∃ i < r x, event (x, i) = true ∧ test (x, i) = true ∧
    ∀ j < i, event (x, j) = false)) ∈ CountingFunction (a + 2) enc encBool
  simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    and_assoc] using h

end Cslib.Complexity
