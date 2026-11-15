/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The fundamental theorem of calculus on a left half-line

For an integrable `f : ℝ → E` that is continuous at `x`, the improper integral
`y ↦ ∫ t in Iic y, f t` has derivative `f x` at `x` (`MeasureTheory.hasDerivAt_integral_Iic`):
it differs from `y ↦ ∫ t in 0..y, f t` by a constant.

## Main results

* `MeasureTheory.hasDerivAt_integral_Iic`: the fundamental theorem of calculus for
  `∫ t in Iic y, f t`.
-/

public section

open Set

namespace MeasureTheory

/-- The **fundamental theorem of calculus on `(-∞, x]`**: for an integrable `f` continuous at `x`,
`y ↦ ∫ t in Iic y, f t` has derivative `f x` at `x`. -/
theorem hasDerivAt_integral_Iic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} {x : ℝ} (hint : Integrable f) (hf : ContinuousAt f x) :
    HasDerivAt (fun y => ∫ t in Iic y, f t) (f x) x := by
  have h : (fun y => ∫ t in Iic y, f t) = fun y => (∫ t in Iic 0, f t) + ∫ t in 0..y, f t := by
    funext y
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn,
      add_sub_cancel]
  rw [h]
  refine (intervalIntegral.integral_hasDerivAt_right (hint.intervalIntegrable)
    ⟨univ, Filter.univ_mem, ?_⟩ hf).const_add _
  rw [Measure.restrict_univ]
  exact hint.aestronglyMeasurable

end MeasureTheory
