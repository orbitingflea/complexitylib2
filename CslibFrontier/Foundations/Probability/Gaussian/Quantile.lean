/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.CDF
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import CslibFrontier.Foundations.MeasureTheory.Integral.IntegralEqImproper
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The standard Gaussian quantile function

The cdf `Φ` of a nondegenerate real Gaussian is differentiable with derivative the Gaussian
density (`hasDerivAt_cdf_gaussianReal`), hence smooth. The standard Gaussian cdf `Φ` is a strictly
increasing bijection from `ℝ` onto `(0, 1)`; its inverse `Φ⁻¹ : (0, 1) → ℝ` is the *standard
Gaussian quantile function* `gaussianQuantile`. It is continuous on `(0, 1)` with derivative
`1 / φ (Φ⁻¹ α)`, for the standard Gaussian density `φ` (`hasDerivAt_gaussianQuantile`), and so it
is smooth on `(0, 1)` (`contDiffOn_gaussianQuantile`).

## Main definitions

* `ProbabilityTheory.gaussianQuantile`: the standard Gaussian quantile function `Φ⁻¹`.

## Main results

* `ProbabilityTheory.hasDerivAt_cdf_gaussianReal`: the derivative of a Gaussian cdf is the
  Gaussian density.
* `ProbabilityTheory.contDiff_cdf_gaussianReal`: a nondegenerate Gaussian cdf is smooth.
* `ProbabilityTheory.cdf_gaussianQuantile`, `ProbabilityTheory.gaussianQuantile_cdf`: `Φ` and
  `Φ⁻¹` are inverse bijections between `ℝ` and `(0, 1)`.
* `ProbabilityTheory.gaussianQuantile_half`: `Φ⁻¹ (1 / 2) = 0`.
* `ProbabilityTheory.strictMonoOn_gaussianQuantile`,
  `ProbabilityTheory.continuousAt_gaussianQuantile`,
  `ProbabilityTheory.continuousOn_gaussianQuantile`,
  `ProbabilityTheory.hasDerivAt_gaussianQuantile`,
  `ProbabilityTheory.contDiffOn_gaussianQuantile`: regularity of `Φ⁻¹` on `(0, 1)`.
-/

public section

open MeasureTheory Set Filter
open scoped NNReal ContDiff

namespace ProbabilityTheory

/-- The **derivative of a Gaussian cdf** is the Gaussian density. -/
theorem hasDerivAt_cdf_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (cdf (gaussianReal μ v)) (gaussianPDFReal μ v x) x := by
  rw [funext (cdf_gaussianReal_eq_integral μ hv)]
  exact hasDerivAt_integral_Iic (integrable_gaussianPDFReal μ v)
    (continuous_gaussianPDFReal μ v).continuousAt

/-- The cdf of a nondegenerate real Gaussian is smooth. -/
theorem contDiff_cdf_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ContDiff ℝ ∞ (cdf (gaussianReal μ v)) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun x => (hasDerivAt_cdf_gaussianReal μ hv x).differentiableAt,
    ?_⟩
  rw [funext fun x => (hasDerivAt_cdf_gaussianReal μ hv x).deriv]
  exact contDiff_gaussianPDFReal μ v

local notation "Φ" => cdf (gaussianReal 0 1)

/-- The **standard Gaussian quantile function** `Φ⁻¹`, the inverse of the standard Gaussian cdf
`Φ : ℝ → (0, 1)`. It is meant for `α ∈ (0, 1)`, where `Φ (Φ⁻¹ α) = α`
(`cdf_gaussianQuantile`); its values outside `(0, 1)` are unspecified. -/
noncomputable def gaussianQuantile (α : ℝ) : ℝ :=
  Function.invFun Φ α

/-- `Φ⁻¹ (Φ x) = x`. -/
@[simp]
theorem gaussianQuantile_cdf (x : ℝ) : gaussianQuantile (Φ x) = x :=
  Function.leftInverse_invFun (strictMono_cdf_gaussianReal 0 one_ne_zero).injective x

/-- `Φ (Φ⁻¹ α) = α` for `α ∈ (0, 1)`. -/
theorem cdf_gaussianQuantile {α : ℝ} (hα : α ∈ Ioo 0 1) : Φ (gaussianQuantile α) = α := by
  refine Function.invFun_eq (mem_range_of_exists_le_of_exists_ge
    (continuous_cdf_gaussianReal 0 one_ne_zero) ?_ ?_)
  · obtain ⟨x, hx⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
      (Iio_mem_nhds hα.1)).exists
    exact ⟨x, hx.le⟩
  · obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
      (Ioi_mem_nhds hα.2)).exists
    exact ⟨x, hx.le⟩

/-- `Φ⁻¹ (1 / 2) = 0`. -/
theorem gaussianQuantile_half : gaussianQuantile 2⁻¹ = 0 := by
  rw [← cdf_gaussianReal_zero_zero one_ne_zero, gaussianQuantile_cdf]

/-- `Φ⁻¹` is strictly increasing on `(0, 1)`. -/
theorem strictMonoOn_gaussianQuantile : StrictMonoOn gaussianQuantile (Ioo 0 1) := by
  intro α hα β hβ h
  rw [← cdf_gaussianQuantile hα, ← cdf_gaussianQuantile hβ] at h
  exact (strictMono_cdf_gaussianReal 0 one_ne_zero).lt_iff_lt.1 h

/-- `Φ⁻¹` is continuous at every `α ∈ (0, 1)`. -/
theorem continuousAt_gaussianQuantile {α : ℝ} (hα : α ∈ Ioo 0 1) :
    ContinuousAt gaussianQuantile α := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds strictMonoOn_gaussianQuantile.monotoneOn
    (Ioo_mem_nhds hα.1 hα.2) ?_
  have : gaussianQuantile '' Ioo 0 1 = univ := by
    refine eq_univ_of_forall fun x => ⟨Φ x, ⟨cdf_pos ?_ x, cdf_lt_one ?_ x⟩,
      gaussianQuantile_cdf x⟩ <;>
    exact gaussianReal_absolutelyContinuous' 0 one_ne_zero
  rw [this]
  exact univ_mem

/-- `Φ⁻¹` is continuous on `(0, 1)`. -/
theorem continuousOn_gaussianQuantile : ContinuousOn gaussianQuantile (Ioo 0 1) :=
  fun _ hα => (continuousAt_gaussianQuantile hα).continuousWithinAt

/-- The **derivative of `Φ⁻¹`**: `(Φ⁻¹)' α = 1 / φ (Φ⁻¹ α)` for `α ∈ (0, 1)`, where `φ` is the
standard Gaussian density. -/
theorem hasDerivAt_gaussianQuantile {α : ℝ} (hα : α ∈ Ioo 0 1) :
    HasDerivAt gaussianQuantile (gaussianPDFReal 0 1 (gaussianQuantile α))⁻¹ α :=
  (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).of_local_left_inverse
    (continuousAt_gaussianQuantile hα) (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'
    (eventually_of_mem (Ioo_mem_nhds hα.1 hα.2) fun _ hβ => cdf_gaussianQuantile hβ)

/-- `Φ⁻¹` is smooth on `(0, 1)`: its derivative `1 / φ ∘ Φ⁻¹` is `Cⁿ` whenever `Φ⁻¹` is. -/
theorem contDiffOn_gaussianQuantile : ContDiffOn ℝ ∞ gaussianQuantile (Ioo 0 1) := by
  refine contDiffOn_infty.2 fun n => ?_
  induction n with
  | zero => exact contDiffOn_zero.2 continuousOn_gaussianQuantile
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun α hα => (hasDerivAt_gaussianQuantile hα).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine ContDiffOn.congr ?_ fun α hα => (hasDerivAt_gaussianQuantile hα).deriv
    exact ((contDiff_gaussianPDFReal 0 1).comp_contDiffOn ih).inv
      fun _ _ => (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'

end ProbabilityTheory
