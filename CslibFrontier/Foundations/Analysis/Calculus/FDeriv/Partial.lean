/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Calculus/FDeriv/Partial.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Partial derivatives of a real function of two real variables

If `f : ℝ → ℝ → ℝ` has partial derivatives `f₁` and `f₂` near `u`, given as `HasDerivAt`
statements, and they are continuous at `u`, then `(x, y) ↦ f x y` is strictly differentiable at
`u` with derivative `f₁ u.1 u.2 • fst + f₂ u.1 u.2 • snd`
(`hasStrictFDerivAt_uncurry_of_hasDerivAt`). This is the scalar form of Mathlib's
`hasStrictFDerivAt_uncurry_coprod`.

## Main results

* `hasStrictFDerivAt_uncurry_of_hasDerivAt`: continuous partial derivatives give a strict
  Fréchet derivative.
-/

public section

open Filter Topology

/-- If `f : ℝ → ℝ → ℝ` has partial derivatives `f₁` and `f₂` in a neighbourhood of `u`, continuous
at `u`, then `(x, y) ↦ f x y` is strictly differentiable at `u` with derivative
`f₁ u.1 u.2 • fst + f₂ u.1 u.2 • snd`. -/
theorem hasStrictFDerivAt_uncurry_of_hasDerivAt {f f₁ f₂ : ℝ → ℝ → ℝ} {u : ℝ × ℝ}
    (df₁ : ∀ᶠ v in 𝓝 u, HasDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
    (df₂ : ∀ᶠ v in 𝓝 u, HasDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (fun v : ℝ × ℝ => f₁ v.1 v.2) u)
    (cf₂ : ContinuousAt (fun v : ℝ × ℝ => f₂ v.1 v.2) u) :
    HasStrictFDerivAt (fun v : ℝ × ℝ => f v.1 v.2)
      (f₁ u.1 u.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + f₂ u.1 u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      u := by
  have hc := (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous
  have h := hasStrictFDerivAt_uncurry_coprod
    (f₁ := fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (f₁ x y))
    (f₂ := fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (f₂ x y))
    (df₁.mono fun _ hv => hv.hasFDerivAt) (df₂.mono fun _ hv => hv.hasFDerivAt)
    (hc.continuousAt.comp cf₁) (hc.continuousAt.comp cf₂)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
  simp [Function.HasUncurry.uncurry, mul_comm]
