/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event

/-!
# Total probability with two cases

Split the outcomes of a random first stage `p` by a set `pre`. If the continuation `kernel`
reaches `event` with probability at most `a₁` from the supported outcomes in `pre` and at most
`a₂` from the other supported outcomes, then `p.bind kernel` reaches `event` with probability at
most `P(pre) * a₁ + P(preᶜ) * a₂`. This refines `toOuterMeasure_bind_failure_le`, which bounds the
second case by `1` and drops the factor `P(pre)`. It is the step of an induction on a budget in
which an outcome outside `pre` does not end the run but uses more of the budget, as when a search
repeats a failed attempt.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_bind_le_mul_add_mul`: the bound in `ℝ≥0∞`.
* `Cslib.Probability.PMF.toOuterMeasure_bind_toReal_le_mul_add_mul`: the bound in `ℝ`, for
  nonnegative `a₁` and `a₂`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- **Total probability with two cases.** If the continuation reaches `event` with probability at
most `a₁` after a supported outcome in `pre` and at most `a₂` after any other supported outcome,
then the bind reaches `event` with probability at most `P(pre) * a₁ + P(preᶜ) * a₂`. -/
theorem toOuterMeasure_bind_le_mul_add_mul (p : PMF α) (kernel : α → PMF β) (pre : Set α)
    (event : Set β) {a₁ a₂ : ℝ≥0∞}
    (hpre : ∀ a ∈ p.support, a ∈ pre → (kernel a).toOuterMeasure event ≤ a₁)
    (hnot : ∀ a ∈ p.support, a ∉ pre → (kernel a).toOuterMeasure event ≤ a₂) :
    (p.bind kernel).toOuterMeasure event ≤
      p.toOuterMeasure pre * a₁ + p.toOuterMeasure preᶜ * a₂ := by
  classical
  have e₁ : p.toOuterMeasure pre * a₁ = ∑' a, pre.indicator p a * a₁ := by
    rw [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right]
  have e₂ : p.toOuterMeasure preᶜ * a₂ = ∑' a, preᶜ.indicator p a * a₂ := by
    rw [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right]
  rw [e₁, e₂, ← tsum_add, PMF.toOuterMeasure_bind_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases hs : a ∈ p.support
  · by_cases ha : a ∈ pre
    · simp only [Set.indicator_of_mem ha, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ha),
        zero_mul, add_zero]
      exact mul_le_mul_of_nonneg_left (hpre a hs ha) zero_le
    · simp only [Set.indicator_of_notMem ha, Set.indicator_of_mem (Set.mem_compl ha), zero_mul,
        zero_add]
      exact mul_le_mul_of_nonneg_left (hnot a hs ha) zero_le
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

/-- **Total probability with two cases**, in `ℝ`: if the continuation reaches `event` with
probability at most `a₁ ≥ 0` after a supported outcome in `pre` and at most `a₂ ≥ 0` after any
other supported outcome, then the bind reaches `event` with probability at most
`P(pre) * a₁ + P(preᶜ) * a₂`. -/
theorem toOuterMeasure_bind_toReal_le_mul_add_mul (p : PMF α) (kernel : α → PMF β) (pre : Set α)
    (event : Set β) {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂)
    (hpre : ∀ a ∈ p.support, a ∈ pre → ((kernel a).toOuterMeasure event).toReal ≤ a₁)
    (hnot : ∀ a ∈ p.support, a ∉ pre → ((kernel a).toOuterMeasure event).toReal ≤ a₂) :
    ((p.bind kernel).toOuterMeasure event).toReal ≤
      (p.toOuterMeasure pre).toReal * a₁ + (p.toOuterMeasure preᶜ).toReal * a₂ := by
  have hle := toOuterMeasure_bind_le_mul_add_mul p kernel pre event
    (fun a hs ha => (ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) h₁).mpr
      (hpre a hs ha))
    (fun a hs ha => (ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) h₂).mpr
      (hnot a hs ha))
  have ht₁ : p.toOuterMeasure pre * ENNReal.ofReal a₁ ≠ ⊤ :=
    ENNReal.mul_ne_top (toOuterMeasure_ne_top _ _) ENNReal.ofReal_ne_top
  have ht₂ : p.toOuterMeasure preᶜ * ENNReal.ofReal a₂ ≠ ⊤ :=
    ENNReal.mul_ne_top (toOuterMeasure_ne_top _ _) ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ht₁, ht₂⟩) hle
  rwa [ENNReal.toReal_add ht₁ ht₂, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal h₁, ENNReal.toReal_ofReal h₂] at h

end Cslib.Probability.PMF
