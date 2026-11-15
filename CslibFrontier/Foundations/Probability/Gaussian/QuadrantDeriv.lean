/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `QuadrantDeriv.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant
public import CslibFrontier.Foundations.Probability.Gaussian.Quantile
public import Mathlib.LinearAlgebra.Matrix.PosDef
import CslibFrontier.Foundations.Analysis.Calculus.FDeriv.Partial
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosDef
import CslibFrontier.Foundations.MeasureTheory.Integral.IntegralEqImproper
import CslibFrontier.Foundations.Probability.Gaussian.Real

/-!
# Derivatives and `ρ`-concavity of the Gaussian quadrant probability

For `|ρ| < 1` write `s = √(1 - ρ²)`, `t = Φ⁻¹ α` and `t' = Φ⁻¹ β`. We compute the first and second
partial derivatives of the Gaussian quadrant probability `Λ_ρ(α, β)` on `(0, 1)²`.

The starting point is the conditional form, in the book's coordinates `(t, t')`,
`P[z ≤ t, z' ≤ t'] = ∫_{x ≤ t} φ(x) Φ((t' - ρx) / s) dx`
(`measureReal_correlatedGaussian_setOf_le_and_le`): given `z = x`, the second coordinate `z'` is
Gaussian with mean `ρx` and variance `s²`. Differentiating in `t` and changing variables by `Φ⁻¹`
(`ProbabilityTheory.gaussianQuantile`, with `(Φ⁻¹)' = 1 / φ ∘ Φ⁻¹`) gives
[O'Donnell, Exercise 11.19 (d)][ODonnell2014]:
`∂Λ_ρ / ∂α = Φ((t' - ρt) / s)` and `∂Λ_ρ / ∂β = Φ((t - ρt') / s)`.

Differentiating once more gives [O'Donnell, Exercise 11.28][ODonnell2014]:

* (a) `∂²Λ_ρ / ∂α² = -(ρ / s) (1 / φ(t)) φ((t' - ρt) / s)`, and symmetrically in `β`;
* (b) `∂²Λ_ρ / ∂β∂α = (1 / s) (1 / φ(t')) φ((t' - ρt) / s)` (the book's `d²/dα dβ`), which
  equals
  `∂²Λ_ρ / ∂α∂β = (1 / s) (1 / φ(t)) φ((t - ρt') / s)`
  (`gaussianPDFReal_mul_gaussianPDFReal_comm`);
* (c) the `ρ`-Hessian `H_ρ Λ_ρ = (H Λ_ρ) ∘ [[1, ρ], [ρ, 1]]` has determinant `0` on `(0, 1)²`;
* (d) for `ρ ∈ (0, 1)` the diagonal second derivatives are negative, so `H_ρ Λ_ρ` is negative
  semidefinite at every point of `(0, 1)²`.

The book defines `ρ`-concavity for `C²` functions. For `|ρ| < 1`, `Λ_ρ` is `C^∞` on `(0, 1)²`
(`contDiffOn_gaussianQuadrant`): continuous first partials make `Λ_ρ` Fréchet differentiable
(`hasFDerivAt_gaussianQuadrant`), and its derivative is built from `Φ` and `Φ⁻¹`, both smooth.
The first partials are in turn Fréchet differentiable with the second partials above as
components (`hasFDerivAt_deriv_gaussianQuadrant_left`, `hasFDerivAt_deriv_gaussianQuadrant_right`),
so `rhoHessian`, built from iterated `deriv`s, is the `ρ`-Hessian of the `C²` function `Λ_ρ`, and
part (d) is its `ρ`-concavity. [O'Donnell, Exercise 11.29][ODonnell2014], the Mossel–Neeman
semigroup argument for the one-dimensional Two-Function Borell Isoperimetric Theorem, is not
proved.

## Main definitions

* `ProbabilityTheory.rhoHessian`: the `ρ`-Hessian `H_ρ F` of a function of two variables.

## Main results

* `ProbabilityTheory.measureReal_correlatedGaussian_setOf_le_and_le`: the conditional formula for
  `P[z ≤ t, z' ≤ t']`.
* `ProbabilityTheory.hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_left`,
  `ProbabilityTheory.hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_right`: its
  partial derivatives in `t` and `t'`.
* `ProbabilityTheory.hasDerivAt_gaussianQuadrant_left`,
  `ProbabilityTheory.hasDerivAt_gaussianQuadrant_right`,
  `ProbabilityTheory.hasFDerivAt_gaussianQuadrant`: Exercise 11.19 (d), as partial and as Fréchet
  derivatives.
* `ProbabilityTheory.hasDerivAt_gaussianQuadrant_left_left`,
  `ProbabilityTheory.hasDerivAt_gaussianQuadrant_right_right`: Exercise 11.28 (a).
* `ProbabilityTheory.hasDerivAt_gaussianQuadrant_left_right`,
  `ProbabilityTheory.hasDerivAt_gaussianQuadrant_right_left`,
  `ProbabilityTheory.gaussianPDFReal_mul_gaussianPDFReal_comm`: Exercise 11.28 (b).
* `ProbabilityTheory.hasFDerivAt_deriv_gaussianQuadrant_left`,
  `ProbabilityTheory.hasFDerivAt_deriv_gaussianQuadrant_right`,
  `ProbabilityTheory.contDiffOn_gaussianQuadrant`: the first partials are Fréchet differentiable,
  and `Λ_ρ` is `C^∞` on `(0, 1)²`.
* `ProbabilityTheory.rhoHessian_gaussianQuadrant`,
  `ProbabilityTheory.det_rhoHessian_gaussianQuadrant`: Exercise 11.28 (c).
* `ProbabilityTheory.deriv_gaussianQuadrant_left_left_neg`,
  `ProbabilityTheory.deriv_gaussianQuadrant_right_right_neg`,
  `ProbabilityTheory.negSemidef_rhoHessian_gaussianQuadrant`,
  `ProbabilityTheory.dotProduct_mulVec_rhoHessian_gaussianQuadrant_nonpos`: Exercise 11.28 (d).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Set Filter
open scoped ContDiff

namespace ProbabilityTheory

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-! ### Preliminaries -/

private theorem sqrt_one_sub_sq_pos {ρ : ℝ} (hρ : |ρ| < 1) : 0 < √(1 - ρ ^ 2) :=
  sqrt_pos.2 (sub_pos.2 ((sq_lt_one_iff_abs_lt_one ρ).2 hρ))

/-- A set integral against the standard Gaussian is a set integral against its density. -/
private theorem setIntegral_gaussianReal (f : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, f x ∂gaussianReal 0 1 = ∫ x in s, φ x * f x := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, restrict_withDensity hs,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-! ### The quadrant probability in the book's coordinates -/

/-- **The conditional formula for the bivariate Gaussian cdf**: for `|ρ| < 1` and a
`ρ`-correlated pair `(z, z')`, `P[z ≤ t, z' ≤ t'] = ∫_{x ≤ t} φ(x) Φ((t' - ρx) / √(1 - ρ²)) dx`,
since `z'` given `z = x` is Gaussian with mean `ρx` and variance `1 - ρ²`. -/
theorem measureReal_correlatedGaussian_setOf_le_and_le {ρ : ℝ} (hρ : |ρ| < 1) (t t' : ℝ) :
    (correlatedGaussian ρ).real {p | p.1 ≤ t ∧ p.2 ≤ t'} =
      ∫ x in Iic t, φ x * Φ ((t' - ρ * x) / √(1 - ρ ^ 2)) := by
  have hs := sqrt_one_sub_sq_pos hρ
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ t ∧ p.2 ≤ t'} :=
    (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
  have hinner : ∀ x, gaussianReal 0 1 (Prod.mk x ⁻¹'
      ((fun g : ℝ × ℝ => (g.1, ρ * g.1 + √(1 - ρ ^ 2) * g.2)) ⁻¹' {p | p.1 ≤ t ∧ p.2 ≤ t'})) =
      (Iic t).indicator (fun x => ENNReal.ofReal (Φ ((t' - ρ * x) / √(1 - ρ ^ 2)))) x := by
    intro x
    by_cases hx : x ≤ t
    · rw [indicator_of_mem (mem_Iic.2 hx), ofReal_cdf]
      congr 1
      ext y
      simp only [mem_preimage, mem_ofPred_eq, hx, true_and, mem_Iic, le_div_iff₀ hs]
      constructor <;> intro h <;> linarith
    · rw [indicator_of_notMem (by simpa using hx), ← measure_empty (μ := gaussianReal 0 1)]
      congr 1
      ext y
      simp only [mem_preimage, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]
  rw [measureReal_def, correlatedGaussian_def, Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Iic, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun _ => cdf_nonneg _ _)
    ((measurable_cdf _).comp (by fun_prop)).aestronglyMeasurable,
    setIntegral_gaussianReal _ measurableSet_Iic]

/-- The partial derivative of `P[z ≤ t, z' ≤ t']` in `t` is `φ(t) Φ((t' - ρt) / √(1 - ρ²))`, for
`|ρ| < 1` and a `ρ`-correlated pair `(z, z')`. -/
theorem hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_left {ρ : ℝ} (hρ : |ρ| < 1)
    (t t' : ℝ) :
    HasDerivAt (fun t => (correlatedGaussian ρ).real {p | p.1 ≤ t ∧ p.2 ≤ t'})
      (φ t * Φ ((t' - ρ * t) / √(1 - ρ ^ 2))) t := by
  simp_rw [measureReal_correlatedGaussian_setOf_le_and_le hρ]
  have hc : Continuous fun x => Φ ((t' - ρ * x) / √(1 - ρ ^ 2)) :=
    (continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)
  refine hasDerivAt_integral_Iic ?_ ((continuous_gaussianPDFReal 0 1).mul hc).continuousAt
  refine (integrable_gaussianPDFReal 0 1).mul_bdd hc.aestronglyMeasurable (c := 1)
    (ae_of_all _ fun x => ?_)
  rw [norm_of_nonneg (cdf_nonneg _ _)]
  exact cdf_le_one _ _

/-- The partial derivative of `P[z ≤ t, z' ≤ t']` in `t'` is `φ(t') Φ((t - ρt') / √(1 - ρ²))`,
for `|ρ| < 1` and a `ρ`-correlated pair `(z, z')`. -/
theorem hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_right {ρ : ℝ} (hρ : |ρ| < 1)
    (t t' : ℝ) :
    HasDerivAt (fun t' => (correlatedGaussian ρ).real {p | p.1 ≤ t ∧ p.2 ≤ t'})
      (φ t' * Φ ((t - ρ * t') / √(1 - ρ ^ 2))) t' := by
  have h : ∀ t', (correlatedGaussian ρ).real {p | p.1 ≤ t ∧ p.2 ≤ t'} =
      (correlatedGaussian ρ).real {p | p.1 ≤ t' ∧ p.2 ≤ t} := fun t' => by
    rw [← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, gaussianQuadrant_comm hρ.le]
  simp_rw [h]
  exact hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_left hρ t' t

/-! ### Exercise 11.19 (d): first derivatives -/

/-- `Λ_ρ(α, β) = P[z ≤ Φ⁻¹ α, z' ≤ Φ⁻¹ β]` for `α, β ∈ (0, 1)`. -/
private theorem gaussianQuadrant_eq_measureReal_quantile (ρ : ℝ) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) : gaussianQuadrant ρ α β = (correlatedGaussian ρ).real
      {p | p.1 ≤ gaussianQuantile α ∧ p.2 ≤ gaussianQuantile β} := by
  conv_lhs => rw [← cdf_gaussianQuantile hα, ← cdf_gaussianQuantile hβ]
  exact gaussianQuadrant_cdf_cdf ρ _ _

/-- **The derivative of `Λ_ρ` in `α`** [O'Donnell, Exercise 11.19 (d)][ODonnell2014]: for
`|ρ| < 1` and `α, β ∈ (0, 1)`, `∂Λ_ρ(α, β) / ∂α = Φ((t' - ρt) / √(1 - ρ²))`, where `t = Φ⁻¹ α`
and `t' = Φ⁻¹ β`. -/
theorem hasDerivAt_gaussianQuadrant_left {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) :
    HasDerivAt (fun α => gaussianQuadrant ρ α β)
      (Φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2))) α := by
  have h := (hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_left hρ (gaussianQuantile α)
    (gaussianQuantile β)).comp α (hasDerivAt_gaussianQuantile hα)
  have hφ := (gaussianPDFReal_pos 0 1 (gaussianQuantile α) one_ne_zero).ne'
  rw [mul_right_comm, mul_inv_cancel₀ hφ, one_mul] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hα.1 hα.2] with α' hα'
  exact gaussianQuadrant_eq_measureReal_quantile ρ hα' hβ

/-- **The derivative of `Λ_ρ` in `β`** [O'Donnell, Exercise 11.19 (d)][ODonnell2014]: for
`|ρ| < 1` and `α, β ∈ (0, 1)`, `∂Λ_ρ(α, β) / ∂β = Φ((t - ρt') / √(1 - ρ²))`, where `t = Φ⁻¹ α`
and `t' = Φ⁻¹ β`. -/
theorem hasDerivAt_gaussianQuadrant_right {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) :
    HasDerivAt (fun β => gaussianQuadrant ρ α β)
      (Φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2))) β := by
  simp_rw [gaussianQuadrant_comm hρ.le α]
  exact hasDerivAt_gaussianQuadrant_left hρ hβ hα

/-- [O'Donnell, Exercise 11.19 (d)][ODonnell2014]: `∂Λ_ρ(α, β) / ∂α = Φ((t' - ρt) / √(1 - ρ²))`
for `|ρ| < 1` and `α, β ∈ (0, 1)`, where `t = Φ⁻¹ α` and `t' = Φ⁻¹ β`. -/
theorem deriv_gaussianQuadrant_left {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) :
    deriv (fun α => gaussianQuadrant ρ α β) α =
      Φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)) :=
  (hasDerivAt_gaussianQuadrant_left hρ hα hβ).deriv

/-- [O'Donnell, Exercise 11.19 (d)][ODonnell2014]: `∂Λ_ρ(α, β) / ∂β = Φ((t - ρt') / √(1 - ρ²))`
for `|ρ| < 1` and `α, β ∈ (0, 1)`, where `t = Φ⁻¹ α` and `t' = Φ⁻¹ β`. -/
theorem deriv_gaussianQuadrant_right {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) :
    deriv (fun β => gaussianQuadrant ρ α β) β =
      Φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)) :=
  (hasDerivAt_gaussianQuadrant_right hρ hα hβ).deriv

/-! ### Exercise 11.28 (a), (b): second derivatives -/

/-- The chain rule for `α ↦ Φ((a Φ⁻¹(α) + c) / s)`. -/
private theorem hasDerivAt_cdf_affine_gaussianQuantile {α : ℝ} (hα : α ∈ Ioo 0 1) (a c s : ℝ) :
    HasDerivAt (fun α => Φ ((a * gaussianQuantile α + c) / s))
      (φ ((a * gaussianQuantile α + c) / s) * (a * (φ (gaussianQuantile α))⁻¹ / s)) α :=
  (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp α
    ((((hasDerivAt_gaussianQuantile hα).const_mul a).add_const c).div_const s)

/-- **The second derivative of `Λ_ρ` in `α`** [O'Donnell, Exercise 11.28 (a)][ODonnell2014]: for
`|ρ| < 1` and `α, β ∈ (0, 1)`,
`∂²Λ_ρ(α, β) / ∂α² = -(ρ / √(1 - ρ²)) (1 / φ(t)) φ((t' - ρt) / √(1 - ρ²))`, where `t = Φ⁻¹ α`
and `t' = Φ⁻¹ β`. -/
theorem hasDerivAt_gaussianQuadrant_left_left {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    HasDerivAt (fun α => deriv (fun α => gaussianQuadrant ρ α β) α)
      (-(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile α))⁻¹ *
        φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2))) α := by
  have h := hasDerivAt_cdf_affine_gaussianQuantile hα (-ρ) (gaussianQuantile β) √(1 - ρ ^ 2)
  have he : ∀ x, -ρ * x + gaussianQuantile β = gaussianQuantile β - ρ * x := fun _ => by ring
  simp only [he] at h
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hα.1 hα.2] with α' hα'
  exact deriv_gaussianQuadrant_left hρ hα' hβ

/-- **The mixed second derivative of `Λ_ρ`** [O'Donnell, Exercise 11.28 (b)][ODonnell2014]: for
`|ρ| < 1` and `α, β ∈ (0, 1)`,
`∂/∂β (∂Λ_ρ(α, β) / ∂α) = (1 / √(1 - ρ²)) (1 / φ(t')) φ((t' - ρt) / √(1 - ρ²))`, where
`t = Φ⁻¹ α` and `t' = Φ⁻¹ β`. -/
theorem hasDerivAt_gaussianQuadrant_left_right {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    HasDerivAt (fun β => deriv (fun α => gaussianQuadrant ρ α β) α)
      ((√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile β))⁻¹ *
        φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2))) β := by
  have h := hasDerivAt_cdf_affine_gaussianQuantile hβ 1 (-(ρ * gaussianQuantile α))
    √(1 - ρ ^ 2)
  have he : ∀ x, 1 * x + -(ρ * gaussianQuantile α) = x - ρ * gaussianQuantile α :=
    fun _ => by ring
  simp only [he] at h
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hβ.1 hβ.2] with β' hβ'
  exact deriv_gaussianQuadrant_left hρ hα hβ'

/-- **The second derivative of `Λ_ρ` in `β`** [O'Donnell, Exercise 11.28 (a)][ODonnell2014]: for
`|ρ| < 1` and `α, β ∈ (0, 1)`,
`∂²Λ_ρ(α, β) / ∂β² = -(ρ / √(1 - ρ²)) (1 / φ(t')) φ((t - ρt') / √(1 - ρ²))`, where `t = Φ⁻¹ α`
and `t' = Φ⁻¹ β`. -/
theorem hasDerivAt_gaussianQuadrant_right_right {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    HasDerivAt (fun β => deriv (fun β => gaussianQuadrant ρ α β) β)
      (-(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile β))⁻¹ *
        φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2))) β := by
  simp_rw [gaussianQuadrant_comm hρ.le α]
  exact hasDerivAt_gaussianQuadrant_left_left hρ hβ hα

/-- **The other mixed second derivative of `Λ_ρ`** [O'Donnell, Exercise 11.28 (b)][ODonnell2014]:
for `|ρ| < 1` and `α, β ∈ (0, 1)`,
`∂/∂α (∂Λ_ρ(α, β) / ∂β) = (1 / √(1 - ρ²)) (1 / φ(t)) φ((t - ρt') / √(1 - ρ²))`, where
`t = Φ⁻¹ α` and `t' = Φ⁻¹ β`. It equals the other mixed derivative
(`gaussianPDFReal_mul_gaussianPDFReal_comm`). -/
theorem hasDerivAt_gaussianQuadrant_right_left {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    HasDerivAt (fun α => deriv (fun β => gaussianQuadrant ρ α β) β)
      ((√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile α))⁻¹ *
        φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2))) α := by
  have h : (fun α => deriv (fun β => gaussianQuadrant ρ α β) β) =
      fun α => deriv (fun β => gaussianQuadrant ρ β α) β := by
    funext α
    simp_rw [gaussianQuadrant_comm hρ.le α]
  rw [h]
  exact hasDerivAt_gaussianQuadrant_left_right hρ hβ hα

/-- **Symmetry of the bivariate Gaussian density**: for `|ρ| < 1` and `s = √(1 - ρ²)`,
`φ(t) φ((t' - ρt) / s) = φ(t') φ((t - ρt') / s)`; both are `s` times the density of a
`ρ`-correlated pair at `(t, t')`. This makes the two mixed derivatives of `Λ_ρ` equal
[O'Donnell, Exercise 11.28 (b)][ODonnell2014]. -/
theorem gaussianPDFReal_mul_gaussianPDFReal_comm {ρ : ℝ} (hρ : |ρ| < 1) (t t' : ℝ) :
    φ t * φ ((t' - ρ * t) / √(1 - ρ ^ 2)) = φ t' * φ ((t - ρ * t') / √(1 - ρ ^ 2)) := by
  have hs := (sqrt_one_sub_sq_pos hρ).ne'
  have hs2 : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 :=
    sq_sqrt (sub_pos.2 ((sq_lt_one_iff_abs_lt_one ρ).2 hρ)).le
  simp only [gaussianPDFReal_def, mul_mul_mul_comm _ (rexp _), ← Real.exp_add]
  congr 2
  field_simp
  rw [hs2]
  ring

/-! ### Joint differentiability and smoothness -/

/-- **`Λ_ρ` is jointly differentiable on `(0, 1)²`** [O'Donnell, Exercise 11.19 (d)][ODonnell2014]:
for `|ρ| < 1` and `α, β ∈ (0, 1)`, the Fréchet derivative of `(α, β) ↦ Λ_ρ(α, β)` at `(α, β)` is
`(u, v) ↦ Φ((t' - ρt) / √(1 - ρ²)) u + Φ((t - ρt') / √(1 - ρ²)) v`, where `t = Φ⁻¹ α` and
`t' = Φ⁻¹ β`. -/
theorem hasFDerivAt_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) :
    HasFDerivAt (Function.uncurry (gaussianQuadrant ρ))
      (Φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        Φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) (α, β) := by
  have hU := prod_mem_nhds (Ioo_mem_nhds hα.1 hα.2) (Ioo_mem_nhds hβ.1 hβ.2)
  have := continuousAt_gaussianQuantile hα
  have := continuousAt_gaussianQuantile hβ
  have := continuous_cdf_gaussianReal 0 one_ne_zero
  refine (hasStrictFDerivAt_uncurry_of_hasDerivAt
    (f₁ := fun α β => Φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)))
    (f₂ := fun α β => Φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)))
    (u := (α, β)) ?_ ?_ (by fun_prop) (by fun_prop)).hasFDerivAt
  · filter_upwards [hU] with v hv using hasDerivAt_gaussianQuadrant_left hρ hv.1 hv.2
  · filter_upwards [hU] with v hv using hasDerivAt_gaussianQuadrant_right hρ hv.1 hv.2

/-- **The Fréchet derivative of `∂Λ_ρ / ∂α`** [O'Donnell, Exercise 11.28 (a), (b)][ODonnell2014]:
for `|ρ| < 1` and `α, β ∈ (0, 1)`, `(α, β) ↦ ∂Λ_ρ(α, β) / ∂α` is differentiable at `(α, β)`, with
the partial derivatives `hasDerivAt_gaussianQuadrant_left_left` and
`hasDerivAt_gaussianQuadrant_left_right` as its components. -/
theorem hasFDerivAt_deriv_gaussianQuadrant_left {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    HasFDerivAt (fun p : ℝ × ℝ => deriv (fun α => gaussianQuadrant ρ α p.2) p.1)
      ((-(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile α))⁻¹ *
          φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2))) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile β))⁻¹ *
          φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2))) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) (α, β) := by
  have hU := prod_mem_nhds (Ioo_mem_nhds hα.1 hα.2) (Ioo_mem_nhds hβ.1 hβ.2)
  have := continuousAt_gaussianQuantile hα
  have := continuousAt_gaussianQuantile hβ
  refine (hasStrictFDerivAt_uncurry_of_hasDerivAt
    (f := fun α β => deriv (fun α => gaussianQuadrant ρ α β) α)
    (f₁ := fun α β => -(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile α))⁻¹ *
      φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)))
    (f₂ := fun α β => (√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile β))⁻¹ *
      φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)))
    (u := (α, β)) ?_ ?_ ?_ ?_).hasFDerivAt
  · filter_upwards [hU] with v hv using hasDerivAt_gaussianQuadrant_left_left hρ hv.1 hv.2
  · filter_upwards [hU] with v hv using hasDerivAt_gaussianQuadrant_left_right hρ hv.1 hv.2
  all_goals fun_prop (disch := exact (gaussianPDFReal_pos _ _ _ one_ne_zero).ne')

/-- **The Fréchet derivative of `∂Λ_ρ / ∂β`** [O'Donnell, Exercise 11.28 (a), (b)][ODonnell2014]:
for `|ρ| < 1` and `α, β ∈ (0, 1)`, `(α, β) ↦ ∂Λ_ρ(α, β) / ∂β` is differentiable at `(α, β)`, with
the partial derivatives `hasDerivAt_gaussianQuadrant_right_left` and
`hasDerivAt_gaussianQuadrant_right_right` as its components. -/
theorem hasFDerivAt_deriv_gaussianQuadrant_right {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    HasFDerivAt (fun p : ℝ × ℝ => deriv (fun β => gaussianQuadrant ρ p.1 β) p.2)
      (((√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile α))⁻¹ *
          φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2))) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile β))⁻¹ *
          φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2))) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) (α, β) := by
  have hU := prod_mem_nhds (Ioo_mem_nhds hα.1 hα.2) (Ioo_mem_nhds hβ.1 hβ.2)
  have := continuousAt_gaussianQuantile hα
  have := continuousAt_gaussianQuantile hβ
  refine (hasStrictFDerivAt_uncurry_of_hasDerivAt
    (f := fun α β => deriv (fun β => gaussianQuadrant ρ α β) β)
    (f₁ := fun α β => (√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile α))⁻¹ *
      φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)))
    (f₂ := fun α β => -(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile β))⁻¹ *
      φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)))
    (u := (α, β)) ?_ ?_ ?_ ?_).hasFDerivAt
  · filter_upwards [hU] with v hv using hasDerivAt_gaussianQuadrant_right_left hρ hv.1 hv.2
  · filter_upwards [hU] with v hv using hasDerivAt_gaussianQuadrant_right_right hρ hv.1 hv.2
  all_goals fun_prop (disch := exact (gaussianPDFReal_pos _ _ _ one_ne_zero).ne')

/-- **`Λ_ρ` is smooth on `(0, 1)²`**: for `|ρ| < 1`, `(α, β) ↦ Λ_ρ(α, β)` is `C^∞` on the open
square, since its Fréchet derivative (`hasFDerivAt_gaussianQuadrant`) is built from
`Φ`, `Φ⁻¹` and the coordinates, all smooth there. In particular `Λ_ρ` is `C²`, as the book's
definition of `ρ`-concavity [O'Donnell, Exercise 11.28][ODonnell2014] requires. -/
theorem contDiffOn_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| < 1) :
    ContDiffOn ℝ ∞ (Function.uncurry (gaussianQuadrant ρ)) (Ioo 0 1 ×ˢ Ioo 0 1) := by
  have hQ₁ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gaussianQuantile p.1) (Ioo 0 1 ×ˢ Ioo 0 1) :=
    contDiffOn_gaussianQuantile.comp contDiffOn_fst fun _ hp => hp.1
  have hQ₂ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gaussianQuantile p.2) (Ioo 0 1 ×ˢ Ioo 0 1) :=
    contDiffOn_gaussianQuantile.comp contDiffOn_snd fun _ hp => hp.2
  have hΦ := contDiff_cdf_gaussianReal 0 one_ne_zero
  refine (contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_Ioo)).2
    ⟨fun p hp => (hasFDerivAt_gaussianQuadrant hρ hp.1 hp.2).differentiableAt
      |>.differentiableWithinAt, ?_⟩
  refine ContDiffOn.congr ?_ fun p hp => (hasFDerivAt_gaussianQuadrant hρ hp.1 hp.2).fderiv
  exact ((hΦ.comp_contDiffOn ((hQ₂.sub (contDiffOn_const.mul hQ₁)).div_const _)).smul
    contDiffOn_const).add
    ((hΦ.comp_contDiffOn ((hQ₁.sub (contDiffOn_const.mul hQ₂)).div_const _)).smul contDiffOn_const)

/-! ### Exercise 11.28 (c), (d): the `ρ`-Hessian and `ρ`-concavity -/

/-- The **`ρ`-Hessian** `H_ρ F = (H F) ∘ [[1, ρ], [ρ, 1]]` of `F : ℝ → ℝ → ℝ` at `(x, y)`
[O'Donnell, Exercise 11.28][ODonnell2014]: the Hessian of `F` with its off-diagonal entries
multiplied by `ρ`. The partial derivatives are iterated `deriv`s; entry `(0, 1)` is
`∂/∂x (∂F/∂y)` and entry `(1, 0)` is `∂/∂y (∂F/∂x)`. It is meaningful when `F` is twice
differentiable near `(x, y)`. -/
noncomputable def rhoHessian (ρ : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![deriv (fun x => deriv (fun x => F x y) x) x, ρ * deriv (fun x => deriv (fun y => F x y) y) x;
    ρ * deriv (fun y => deriv (fun x => F x y) x) y, deriv (fun y => deriv (fun y => F x y) y) y]

/-- The defining formula of `rhoHessian`. -/
theorem rhoHessian_def (ρ : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    rhoHessian ρ F x y =
      !![deriv (fun x => deriv (fun x => F x y) x) x,
        ρ * deriv (fun x => deriv (fun y => F x y) y) x;
        ρ * deriv (fun y => deriv (fun x => F x y) x) y,
        deriv (fun y => deriv (fun y => F x y) y) y] := by
  rw [rhoHessian]

/-- **The `ρ`-Hessian of `Λ_ρ`** [O'Donnell, Exercise 11.28][ODonnell2014]: for `|ρ| < 1` and
`α, β ∈ (0, 1)`, with `s = √(1 - ρ²)`, `t = Φ⁻¹ α` and `t' = Φ⁻¹ β`, the entries of `H_ρ Λ_ρ` are
`-(ρ / s) φ((t' - ρt) / s) / φ(t)`, `(ρ / s) φ((t - ρt') / s) / φ(t)`,
`(ρ / s) φ((t' - ρt) / s) / φ(t')` and `-(ρ / s) φ((t - ρt') / s) / φ(t')`. -/
theorem rhoHessian_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) :
    rhoHessian ρ (gaussianQuadrant ρ) α β =
      !![-(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile α))⁻¹ *
          φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)),
        ρ * ((√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile α))⁻¹ *
          φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)));
        ρ * ((√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile β))⁻¹ *
          φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2))),
        -(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile β))⁻¹ *
          φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2))] := by
  rw [rhoHessian, (hasDerivAt_gaussianQuadrant_left_left hρ hα hβ).deriv,
    (hasDerivAt_gaussianQuadrant_right_left hρ hα hβ).deriv,
    (hasDerivAt_gaussianQuadrant_left_right hρ hα hβ).deriv,
    (hasDerivAt_gaussianQuadrant_right_right hρ hα hβ).deriv]

/-- [O'Donnell, Exercise 11.28 (c)][ODonnell2014]: `det (H_ρ Λ_ρ) = 0` on `(0, 1)²`, for
`|ρ| < 1`. -/
theorem det_rhoHessian_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1)
    (hβ : β ∈ Ioo 0 1) : (rhoHessian ρ (gaussianQuadrant ρ) α β).det = 0 := by
  rw [rhoHessian_gaussianQuadrant hρ hα hβ, Matrix.det_fin_two_of]
  ring

/-- [O'Donnell, Exercise 11.28 (d)][ODonnell2014]: `∂²Λ_ρ / ∂α² < 0` on `(0, 1)²` for
`ρ ∈ (0, 1)`. -/
theorem deriv_gaussianQuadrant_left_left_neg {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    deriv (fun α => deriv (fun α => gaussianQuadrant ρ α β) α) α < 0 := by
  have hρ : |ρ| < 1 := abs_lt.2 ⟨by linarith, hρ1⟩
  rw [(hasDerivAt_gaussianQuadrant_left_left hρ hα hβ).deriv, neg_mul, neg_mul, neg_lt_zero]
  have := sqrt_one_sub_sq_pos hρ
  have := gaussianPDFReal_pos 0 1 (gaussianQuantile α) one_ne_zero
  have := gaussianPDFReal_pos 0 1
    ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)) one_ne_zero
  positivity

/-- [O'Donnell, Exercise 11.28 (d)][ODonnell2014]: `∂²Λ_ρ / ∂β² < 0` on `(0, 1)²` for
`ρ ∈ (0, 1)`. -/
theorem deriv_gaussianQuadrant_right_right_neg {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    deriv (fun β => deriv (fun β => gaussianQuadrant ρ α β) β) β < 0 := by
  simp_rw [gaussianQuadrant_comm (abs_lt.2 ⟨by linarith, hρ1⟩).le α]
  exact deriv_gaussianQuadrant_left_left_neg hρ0 hρ1 hβ hα

/-- **`H_ρ Λ_ρ` is negative semidefinite** [O'Donnell, Exercise 11.28 (d)][ODonnell2014]: for
`ρ ∈ (0, 1)` and `α, β ∈ (0, 1)`, `-H_ρ Λ_ρ(α, β)` is positive semidefinite. Since `Λ_ρ` is
`C^∞` on `(0, 1)²` (`contDiffOn_gaussianQuadrant`), this is the `ρ`-concavity of `Λ_ρ` there. -/
theorem negSemidef_rhoHessian_gaussianQuadrant {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {α β : ℝ}
    (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    (-rhoHessian ρ (gaussianQuadrant ρ) α β).PosSemidef := by
  have hρ : |ρ| < 1 := abs_lt.2 ⟨by linarith, hρ1⟩
  have hdet := det_rhoHessian_gaussianQuadrant hρ hα hβ
  have h00 := deriv_gaussianQuadrant_left_left_neg hρ0 hρ1 hα hβ
  have h11 := deriv_gaussianQuadrant_right_right_neg hρ0 hρ1 hα hβ
  -- The two off-diagonal entries agree by the symmetry of the bivariate density.
  have hsymm : (rhoHessian ρ (gaussianQuadrant ρ) α β) 0 1 =
      (rhoHessian ρ (gaussianQuadrant ρ) α β) 1 0 := by
    have hA := (gaussianPDFReal_pos 0 1 (gaussianQuantile α) one_ne_zero).ne'
    have hB := (gaussianPDFReal_pos 0 1 (gaussianQuantile β) one_ne_zero).ne'
    have hid := gaussianPDFReal_mul_gaussianPDFReal_comm hρ (gaussianQuantile α)
      (gaussianQuantile β)
    rw [rhoHessian_gaussianQuadrant hρ hα hβ]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have hAB : (φ (gaussianQuantile α))⁻¹ *
        φ ((gaussianQuantile α - ρ * gaussianQuantile β) / √(1 - ρ ^ 2)) =
        (φ (gaussianQuantile β))⁻¹ *
          φ ((gaussianQuantile β - ρ * gaussianQuantile α) / √(1 - ρ ^ 2)) := by
      rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hA hB]
      linear_combination -hid
    simp only [mul_assoc, hAB]
  set M := rhoHessian ρ (gaussianQuadrant ρ) α β
  have hM : -M = !![-M 0 0, -M 0 1; -M 0 1, -M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsymm]
  rw [hM]
  refine Matrix.posSemidef_fin_two (by simpa [M, rhoHessian] using h00.le)
    (by simpa [M, rhoHessian] using h11.le) ?_
  rw [Matrix.det_fin_two, ← hsymm] at hdet
  nlinarith

open Matrix in
/-- [O'Donnell, Exercise 11.28 (d)][ODonnell2014]: for `ρ ∈ (0, 1)` and `α, β ∈ (0, 1)`, the
quadratic form of `H_ρ Λ_ρ(α, β)` is nonpositive: `v ⬝ᵥ (H_ρ Λ_ρ(α, β) *ᵥ v) ≤ 0`. -/
theorem dotProduct_mulVec_rhoHessian_gaussianQuadrant_nonpos {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {α β : ℝ} (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (rhoHessian ρ (gaussianQuadrant ρ) α β *ᵥ v) ≤ 0 := by
  have h := (negSemidef_rhoHessian_gaussianQuadrant hρ0 hρ1 hα hβ).dotProduct_mulVec_nonneg v
  rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg, neg_nonneg] at h
  exact h

end ProbabilityTheory
