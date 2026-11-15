/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Probability.IID.Birthday
import CslibFrontier.Probability.PMF.Coin

/-!
# Tests for the birthday collision bounds

Checks for `CslibFrontier/Probability/IID/Birthday.lean` as a `module` client with an ordinary
import: the exact collision probability of two fair coins; the upper bound on distinctness for
every law, with more samples than points (three samples from a two-point set, where the
hypothesis of the Theorem B.1(ii) bound cannot be dropped) and with fewer (two samples from a
four-point set); the first lower bound for a biased coin and for every law on a four-point set;
the second lower bound for a point mass; and the Theorem B.1(ii) bound on a four-point set.

Outside `namespace Cslib.Probability.PMF` the uniform law is written
`Cslib.Probability.PMF.uniformOfFintype`: there the bare `PMF.uniformOfFintype` is a deprecated
Mathlib name with a different argument.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ProbabilityBirthday

open Cslib.Probability.PMF

/-- Two fair coins collide with probability exactly `1 / 2`. -/
example : ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 2).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 / 2 := by
  have hc := toOuterMeasure_toReal_add_compl (iid (Cslib.Probability.PMF.uniformOfFintype Bool) 2)
    {x | Function.Injective x}
  change _ + ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 2).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 at hc
  have h2 : ((2 : ℕ).descFactorial 2 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 2 := by
    norm_num [Nat.descFactorial]
  rw [iid_uniformOfFintype_injective, Fintype.card_bool, h2] at hc
  linarith

/-- Three samples of any law on a two-point set are never distinct. -/
theorem iid_bool_three_injective (μ : PMF Bool) :
    ((iid μ 3).toOuterMeasure {x | Function.Injective x}).toReal = 0 := by
  refine le_antisymm ?_ ENNReal.toReal_nonneg
  have e : ((Fintype.card Bool).descFactorial 3 : ℝ) / (Fintype.card Bool : ℝ) ^ 3 = 0 := by
    norm_num [Fintype.card_bool, Nat.descFactorial]
  exact e ▸ iid_injective_le_descFactorial_div_pow μ 3

/-- Two samples of any law on a four-point set are distinct with probability at most `3 / 4`. -/
example (μ : PMF (Fin 4)) :
    ((iid μ 2).toOuterMeasure {x | Function.Injective x}).toReal ≤ 3 / 4 := by
  have e :
      ((Fintype.card (Fin 4)).descFactorial 2 : ℝ) / (Fintype.card (Fin 4) : ℝ) ^ 2 = 3 / 4 := by
    norm_num [Fintype.card_fin, Nat.descFactorial]
  exact e ▸ iid_injective_le_descFactorial_div_pow μ 2

/-- The hypothesis of the Theorem B.1(ii) bound cannot be dropped: for three samples from a
two-point set (`2 * 3 > 2 + 2`) the collision probability is `1`, above `1 - exp (-3)`. -/
example : ¬ ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal ≤
      1 - Real.exp (-(((3 : ℕ) : ℝ) * ((3 : ℕ) - 1) / Fintype.card Bool)) := by
  have hc := toOuterMeasure_toReal_add_compl (iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3)
    {x | Function.Injective x}
  change _ + ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 at hc
  rw [iid_bool_three_injective] at hc
  have := Real.exp_pos (-(((3 : ℕ) : ℝ) * ((3 : ℕ) - 1) / Fintype.card Bool))
  intro h
  linarith

/-- The first lower bound for a non-uniform law: two flips of a coin with bias `1 / 3` agree with
probability at least `1 - exp (-1 / 2)`. -/
example : 1 - Real.exp (-(1 / 2)) ≤
    ((iid (coin ⟨1 / 3, by norm_num, by norm_num⟩) 2).toOuterMeasure
      {x | ¬ Function.Injective x}).toReal := by
  convert one_sub_exp_neg_le_iid_not_injective (coin ⟨1 / 3, by norm_num, by norm_num⟩) 2 using 4
  norm_num [Fintype.card_bool]

/-- Five samples of any law on a four-point set contain two equal samples with probability at
least `1 - exp (-5 / 2)`. -/
example (μ : PMF (Fin 4)) : 1 - Real.exp (-(5 / 2)) ≤
    ((iid μ 5).toOuterMeasure {x | ¬ Function.Injective x}).toReal := by
  convert one_sub_exp_neg_le_iid_not_injective μ 5 using 4
  norm_num [Fintype.card_fin]

/-- The second lower bound for a non-uniform law: a point mass on a two-point set, `k = 2`. -/
example : min ((2 : ℝ) * (2 - 1) / (4 * 2)) 0.63 ≤
    ((iid (PMF.pure true) 2).toOuterMeasure {x | ¬ Function.Injective x}).toReal := by
  simpa [Fintype.card_bool] using min_le_iid_not_injective (PMF.pure true) 2

/-- The Theorem B.1(ii) bound for two uniform samples from a four-point set. -/
example : ((iid (Cslib.Probability.PMF.uniformOfFintype (Fin 4)) 2).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal ≤
      1 - Real.exp (-(((2 : ℕ) : ℝ) * ((2 : ℕ) - 1) / 4)) := by
  simpa [Fintype.card_fin] using
    iid_uniformOfFintype_not_injective_le_one_sub_exp_neg (α := Fin 4) (k := 2) (by simp)

end CslibFrontierTests.ProbabilityBirthday
