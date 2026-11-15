/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv

/-! # Tests for the derivatives and `ρ`-concavity of the Gaussian quadrant probability

The quantile `Φ⁻¹`: its sign below `1 / 2`, continuity, and derivative `√(2π)` at `1 / 2`. The
bivariate formula at `ρ = 0`, which factors as `Φ(t) Φ(t')`. The first derivative
`∂Λ_ρ / ∂α = Φ(0) = 1 / 2` at `α = β = 1 / 2`; consistency with `Λ_0(α, β) = αβ` at `ρ = 0`;
the second derivative `-ρ / √(1 - ρ²)` and the mixed derivative `1 / √(1 - ρ²)` at
`α = β = 1 / 2`; the Fréchet derivatives of `Λ_ρ` and of `∂Λ_ρ / ∂α` at `(1 / 2, 1 / 2)` and
the `C²` regularity of `Λ_ρ` on `(0, 1)²`; the density symmetry; an entry of the `ρ`-Hessian, its
vanishing determinant, and the negative semidefiniteness of `H_{1/2} Λ_{1/2}` at
`(1 / 2, 1 / 2)`. -/

public section

namespace CslibFrontierTests.GaussianQuadrantDeriv

open MeasureTheory ProbabilityTheory Real Set

/-- `1 / 2 ∈ (0, 1)`. -/
theorem half_mem : (2⁻¹ : ℝ) ∈ Ioo 0 1 := by norm_num

/-- `|1 / 2| < 1`. -/
theorem abs_half_lt_one : |(1 / 2 : ℝ)| < 1 := by norm_num [abs_of_pos]

/-- `φ 0 = 1 / √(2π)`. -/
theorem gaussianPDFReal_zero : gaussianPDFReal 0 1 0 = (√(2 * π))⁻¹ := by
  simp [gaussianPDFReal_def]

/-- `Φ⁻¹ (Φ 1) = 1`. -/
example : gaussianQuantile (cdf (gaussianReal 0 1) 1) = 1 := gaussianQuantile_cdf 1

/-- `Φ⁻¹` is negative below `1 / 2`, by strict monotonicity. -/
example : gaussianQuantile 4⁻¹ < 0 := by
  rw [← gaussianQuantile_half]
  exact strictMonoOn_gaussianQuantile (by norm_num) half_mem (by norm_num)

/-- `Φ⁻¹` is continuous at `1 / 3`. -/
example : ContinuousAt gaussianQuantile 3⁻¹ := continuousAt_gaussianQuantile (by norm_num)

/-- At `ρ = 0` the bivariate formula factors: `P[z ≤ t, z' ≤ t'] = Φ(t) Φ(t')`. -/
example (t t' : ℝ) :
    (correlatedGaussian 0).real {p | p.1 ≤ t ∧ p.2 ≤ t'} =
      cdf (gaussianReal 0 1) t * cdf (gaussianReal 0 1) t' := by
  rw [measureReal_correlatedGaussian_setOf_le_and_le (by norm_num)]
  simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sqrt_one, div_one]
  rw [integral_mul_const, cdf_gaussianReal_eq_integral 0 one_ne_zero t]

/-- `(Φ⁻¹)' (1 / 2) = √(2π)`. -/
example : HasDerivAt gaussianQuantile √(2 * π) 2⁻¹ := by
  have h := hasDerivAt_gaussianQuantile half_mem
  rwa [gaussianQuantile_half, gaussianPDFReal_zero, inv_inv] at h

/-- At `α = β = 1 / 2` (so `t = t' = 0`), `∂Λ_ρ / ∂α = Φ(0) = 1 / 2`. -/
example {ρ : ℝ} (hρ : |ρ| < 1) : HasDerivAt (fun α => gaussianQuadrant ρ α 2⁻¹) 2⁻¹ 2⁻¹ := by
  have h := hasDerivAt_gaussianQuadrant_left hρ half_mem half_mem
  rwa [gaussianQuantile_half, mul_zero, sub_zero, zero_div,
    cdf_gaussianReal_zero_zero one_ne_zero] at h

/-- The same derivative in `β`. -/
example {ρ : ℝ} (hρ : |ρ| < 1) : deriv (fun β => gaussianQuadrant ρ 2⁻¹ β) 2⁻¹ = 2⁻¹ := by
  rw [deriv_gaussianQuadrant_right hρ half_mem half_mem, gaussianQuantile_half, mul_zero,
    sub_zero, zero_div, cdf_gaussianReal_zero_zero one_ne_zero]

/-- At `ρ = 0` the formula gives `∂Λ_0 / ∂α = Φ(Φ⁻¹ β) = β`. -/
example {α β : ℝ} (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    deriv (fun α => gaussianQuadrant 0 α β) α = β := by
  rw [deriv_gaussianQuadrant_left (by norm_num) hα hβ]
  simp [cdf_gaussianQuantile hβ]

/-- Consistency with `Λ_0(α, β) = αβ`: differentiating `αβ` instead recovers the formula's
value `Φ((Φ⁻¹ β - 0) / 1)` at `ρ = 0`. -/
example {α β : ℝ} (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 1) :
    cdf (gaussianReal 0 1) ((gaussianQuantile β - 0 * gaussianQuantile α) / √(1 - 0 ^ 2)) =
      β := by
  rw [← deriv_gaussianQuadrant_left (by norm_num) hα hβ]
  have h : (fun α => gaussianQuadrant 0 α β) =ᶠ[nhds α] fun α => α * β := by
    filter_upwards [Ioo_mem_nhds hα.1 hα.2] with a ha
    exact gaussianQuadrant_zero ha.1.le ha.2.le hβ.1.le hβ.2.le
  rw [h.deriv_eq, (hasDerivAt_mul_const β).deriv]

/-- At `α = β = 1 / 2`, `∂²Λ_ρ / ∂α² = -ρ / √(1 - ρ²)`. -/
example {ρ : ℝ} (hρ : |ρ| < 1) :
    deriv (fun α => deriv (fun α => gaussianQuadrant ρ α 2⁻¹) α) 2⁻¹ = -(ρ / √(1 - ρ ^ 2)) := by
  rw [(hasDerivAt_gaussianQuadrant_left_left hρ half_mem half_mem).deriv, gaussianQuantile_half,
    mul_zero, sub_zero, zero_div, gaussianPDFReal_zero]
  have : (√(2 * π))⁻¹ ≠ 0 := by positivity
  field_simp

/-- At `α = β = 1 / 2`, the mixed derivative `∂/∂β (∂Λ_ρ / ∂α)` is `1 / √(1 - ρ²)`. -/
example {ρ : ℝ} (hρ : |ρ| < 1) :
    HasDerivAt (fun β => deriv (fun α => gaussianQuadrant ρ α β) 2⁻¹) (√(1 - ρ ^ 2))⁻¹ 2⁻¹ := by
  have h := hasDerivAt_gaussianQuadrant_left_right hρ half_mem half_mem
  have : (√(2 * π))⁻¹ ≠ 0 := by positivity
  rwa [gaussianQuantile_half, mul_zero, sub_zero, zero_div, gaussianPDFReal_zero,
    mul_assoc, inv_mul_cancel₀ this, mul_one] at h

/-- At `(1 / 2, 1 / 2)` the Fréchet derivative of `Λ_ρ` is `(u, v) ↦ (u + v) / 2`. -/
example {ρ : ℝ} (hρ : |ρ| < 1) :
    HasFDerivAt (Function.uncurry (gaussianQuadrant ρ))
      ((2⁻¹ : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2⁻¹ : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (2⁻¹, 2⁻¹) := by
  have h := hasFDerivAt_gaussianQuadrant hρ half_mem half_mem
  rwa [gaussianQuantile_half, mul_zero, sub_zero, zero_div,
    cdf_gaussianReal_zero_zero one_ne_zero] at h

/-- At `(1 / 2, 1 / 2)` the Fréchet derivative of `∂Λ_ρ / ∂α` is
`(u, v) ↦ (-ρ u + v) / √(1 - ρ²)`. -/
example {ρ : ℝ} (hρ : |ρ| < 1) :
    HasFDerivAt (fun p : ℝ × ℝ => deriv (fun α => gaussianQuadrant ρ α p.2) p.1)
      ((-(ρ / √(1 - ρ ^ 2))) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (√(1 - ρ ^ 2))⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) (2⁻¹, 2⁻¹) := by
  have h := hasFDerivAt_deriv_gaussianQuadrant_left hρ half_mem half_mem
  have : (√(2 * π))⁻¹ ≠ 0 := by positivity
  rwa [gaussianQuantile_half, mul_zero, sub_zero, zero_div, gaussianPDFReal_zero, mul_assoc,
    inv_mul_cancel₀ this, mul_one, mul_assoc, inv_mul_cancel₀ this, mul_one] at h

/-- `Λ_ρ` is `C²` on `(0, 1)²`, as the book's definition of `ρ`-concavity requires. -/
example {ρ : ℝ} (hρ : |ρ| < 1) :
    ContDiffOn ℝ 2 (Function.uncurry (gaussianQuadrant ρ)) (Ioo 0 1 ×ˢ Ioo 0 1) :=
  contDiffOn_infty.1 (contDiffOn_gaussianQuadrant hρ) 2

/-- The symmetry of the bivariate density at `ρ = 1 / 2`, `t = 1`, `t' = 0`. -/
example : gaussianPDFReal 0 1 1 * gaussianPDFReal 0 1 ((0 - 1 / 2 * 1) / √(1 - (1 / 2) ^ 2)) =
    gaussianPDFReal 0 1 0 * gaussianPDFReal 0 1 ((1 - 1 / 2 * 0) / √(1 - (1 / 2) ^ 2)) :=
  gaussianPDFReal_mul_gaussianPDFReal_comm abs_half_lt_one 1 0

/-- An off-diagonal entry of `H_{1/2} Λ_{1/2}` at `(1 / 2, 1 / 2)`: `ρ / √(1 - ρ²)`. -/
example : rhoHessian (1 / 2) (gaussianQuadrant (1 / 2)) 2⁻¹ 2⁻¹ 0 1 =
    1 / 2 * (√(1 - (1 / 2) ^ 2))⁻¹ := by
  rw [rhoHessian_gaussianQuadrant abs_half_lt_one half_mem half_mem, gaussianQuantile_half]
  have : (√(2 * π))⁻¹ ≠ 0 := by positivity
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, sub_zero, zero_div,
    gaussianPDFReal_zero]
  rw [mul_assoc _ (√(2 * π))⁻¹⁻¹, inv_mul_cancel₀ this, mul_one]

/-- **Exercise 11.28 (c)** at a point: `det (H_{1/2} Λ_{1/2})(1 / 2, 1 / 2) = 0`. -/
example : (rhoHessian (1 / 2) (gaussianQuadrant (1 / 2)) 2⁻¹ 2⁻¹).det = 0 :=
  det_rhoHessian_gaussianQuadrant abs_half_lt_one half_mem half_mem

/-- **Exercise 11.28 (d)** at a point: `H_{1/2} Λ_{1/2}` is negative semidefinite at
`(1 / 2, 1 / 2)`. -/
example : (-rhoHessian (1 / 2) (gaussianQuadrant (1 / 2)) 2⁻¹ 2⁻¹).PosSemidef :=
  negSemidef_rhoHessian_gaussianQuadrant (by norm_num) (by norm_num) half_mem half_mem

open Matrix in
/-- **Exercise 11.28 (d)** at a point, as a quadratic form, along the direction `(1, -1)`. -/
example : ![1, -1] ⬝ᵥ (rhoHessian (1 / 2) (gaussianQuadrant (1 / 2)) 2⁻¹ 2⁻¹ *ᵥ ![1, -1]) ≤ 0 :=
  dotProduct_mulVec_rhoHessian_gaussianQuadrant_nonpos (by norm_num) (by norm_num) half_mem
    half_mem _

/-- **Exercise 11.28 (d)** at a point: `∂²Λ_{1/2} / ∂β² < 0` at `(1 / 2, 1 / 2)`. -/
example : deriv (fun β => deriv (fun β => gaussianQuadrant (1 / 2) 2⁻¹ β) β) 2⁻¹ < 0 :=
  deriv_gaussianQuadrant_right_right_neg (by norm_num) (by norm_num) half_mem half_mem

end CslibFrontierTests.GaussianQuadrantDeriv
