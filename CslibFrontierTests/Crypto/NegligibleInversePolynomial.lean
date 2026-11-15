/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Tests for inverse-polynomial characterizations and Boneh–Shoup §2.3.1 examples

Checked instances of the Definition 2.5 and Theorem 2.11 equivalences, the Example 2.10 negligible
(`2 ^ (-√n)`, `n ^ (-log n)`) and non-negligible (`1 / (1000 n ^ 4 + n ^ 2 log n)`, `1 / n ^ 100`)
functions, the hypothesis probes for `PolynomiallyBounded.not_negligible_inv`,
`negligible_inv_pow_log`, and Theorem 2.11, and the piecewise function of Example 2.11 (`1 / n` on
even `n` and `2 ^ (-n)` on odd `n`) with its natural inverse (`n` on even `n` and `2 ^ n` on odd
`n`) from [BonehShoup2023], v0.6, §2.3.1, pp. 28–29.
-/

public section

namespace CslibFrontierTests.Crypto.NegligibleInversePolynomial

open Filter Topology Cslib Cslib.Crypto
open scoped NNReal

/-! ### Theorem 2.11 and Definition 2.5 equivalences applied in both directions -/

example : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ((2 : ℝ≥0) ^ n)⁻¹ < 1 / (n : ℝ≥0) ^ k :=
  negligible_iff_eventually_lt_inv_pow.mp negligible_inv_two_pow

example : Negligible (fun _ : ℕ => (0 : ℝ≥0)) :=
  negligible_iff_eventually_lt_inv_pow.mpr fun k => by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    exact one_div_pos.mpr (pow_pos (by exact_mod_cast hn1) k)

example : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ((2 : ℝ≥0) ^ n)⁻¹ ≤ 1 / (n : ℝ≥0) ^ k :=
  negligible_iff_eventually_le_inv_pow.mp negligible_inv_two_pow

example : Negligible (fun _ : ℕ => (0 : ℝ≥0)) :=
  negligible_iff_eventually_le_inv_pow.mpr fun _ => Eventually.of_forall fun _ => zero_le

example : ∀ p : ℕ → ℕ, PolynomiallyBounded p → (∀ n, 0 < p n) →
    ∀ᶠ n : ℕ in atTop, (((2 : ℝ≥0) ^ n)⁻¹ : ℝ) ≤ 1 / (p n : ℝ) :=
  negligible_iff_eventually_le_inv_polynomial.mp negligible_inv_two_pow

example : Negligible (fun _ : ℕ => (0 : ℝ≥0)) :=
  negligible_iff_eventually_le_inv_polynomial.mpr fun _ _ _ =>
    Eventually.of_forall fun _ => by positivity

example : ∀ᶠ n : ℕ in atTop, (((2 : ℝ≥0) ^ n)⁻¹ : ℝ) < 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
  negligible_iff_eventually_lt_inv_rpow.mp negligible_inv_two_pow (3 / 2) (by norm_num)

example : Negligible (fun _ : ℕ => (0 : ℝ≥0)) :=
  negligible_iff_eventually_lt_inv_rpow.mpr fun c _ => by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    exact one_div_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn1) c)

example : Tendsto (fun n : ℕ => (((2 : ℝ≥0) ^ n)⁻¹ : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)) atTop (𝓝 0) :=
  negligible_iff_tendsto_mul_rpow.mp negligible_inv_two_pow (3 / 2) (by norm_num)

example : Negligible (fun _ : ℕ => (0 : ℝ≥0)) :=
  negligible_iff_tendsto_mul_rpow.mpr fun _ _ => by simp

-- Theorem 2.11 on a signed real-valued function (-1)^n * 2^(-n)
example :
    (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
      |(-1 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹| < 1 / (n : ℝ) ^ c) ↔
    (∀ c : ℝ, 0 < c → Tendsto
      (fun n : ℕ => (-1 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ c) atTop (𝓝 0)) :=
  eventually_abs_lt_inv_rpow_iff_tendsto_mul_rpow

/-! ### Example 2.10 negligible functions and `fun_prop` integration -/

example : PolynomiallyLowerBounded (fun n => Nat.sqrt (2 * n + 1)) := by
  fun_prop (disch := positivity)

example : Negligible (fun n =>
    ((n + 1 : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ Nat.sqrt n)⁻¹ + (1 : ℝ≥0) / 2 ^ Nat.sqrt n) := by
  fun_prop

example : Negligible (fun n =>
    (n : ℝ≥0) ^ 2 * ((2 : ℝ≥0) ^ Real.sqrt (n : ℝ))⁻¹ +
      (2 : ℝ≥0) ^ (-Real.sqrt (n : ℝ))) := by
  fun_prop

example : Negligible (fun n => ((2 : ℝ≥0) ^ Nat.sqrt (2 * n + 1))⁻¹) := by
  fun_prop (disch := positivity)

example : Negligible (fun n => (1 : ℝ≥0) / 2 ^ Nat.sqrt (2 * n + 1)) := by
  fun_prop (disch := positivity)

example : Negligible (fun n =>
    ((n ^ 3 + 5 : ℕ) : ℝ≥0) / 2 ^ Nat.sqrt (2 * n + 1) +
      (2 : ℝ≥0) ^ (-Real.sqrt (n : ℝ))) := by
  fun_prop (disch := positivity)

example : Negligible (fun n => ((n : ℝ≥0) ^ n)⁻¹) :=
  negligible_inv_pow_of_tendsto_atTop tendsto_id

example : Negligible (fun n => (1 : ℝ≥0) / (n : ℝ≥0) ^ n) := by
  simpa only [one_div] using negligible_inv_pow_of_tendsto_atTop (f := fun n : ℕ => n) tendsto_id

example : Negligible (fun n => ((n : ℝ≥0) ^ (n : ℝ))⁻¹) :=
  negligible_inv_rpow_of_tendsto_atTop tendsto_natCast_atTop_atTop

example : Negligible (fun n => (n : ℝ≥0) ^ (-(n : ℝ))) :=
  negligible_rpow_neg_of_tendsto_atTop tendsto_natCast_atTop_atTop

example : Negligible (fun n =>
    (n : ℝ≥0) * ((n : ℝ≥0) ^ Nat.log 2 n)⁻¹ +
      (1 : ℝ≥0) / (n : ℝ≥0) ^ Nat.log 2 n) := by
  fun_prop (disch := decide)

example : Negligible (fun n =>
    ((n + 3 : ℕ) : ℝ≥0) * ((n : ℝ≥0) ^ Real.log (n : ℝ))⁻¹ +
      (n : ℝ≥0) ^ (-Real.log (n : ℝ))) := by
  fun_prop

/-! ### Example 2.10 non-negligible functions (`1 / n ^ 100`, `1 / (1000 n ^ 4 + n ^ 2 log n)`) -/

example : ¬ Negligible (fun n => ((n : ℝ≥0) ^ 100)⁻¹) := not_negligible_inv_pow 100

example : ¬ Negligible (fun n => (1 : ℝ≥0) / n ^ 100) := by
  simpa only [one_div] using not_negligible_inv_pow 100

/-- **Example 2.10** ([BonehShoup2023], p. 28), natural logarithm base `b`:
`1 / (1000 * n ^ 4 + n ^ 2 * Nat.log b n)` is not negligible. -/
theorem not_negligible_one_div_quartic_add_sq_mul_log (b : ℕ) :
    ¬ Negligible (fun n => (1 : ℝ≥0) / (1000 * n ^ 4 + n ^ 2 * Nat.log b n : ℕ)) := by
  simpa only [one_div] using PolynomiallyBounded.not_negligible_inv (by fun_prop)
    ((eventually_ge_atTop 1).frequently.mono fun n hn => by positivity)

/-- **Example 2.10** ([BonehShoup2023], p. 28), real logarithm:
`1 / (1000 * n ^ 4 + n ^ 2 * Real.toNNReal (Real.log n))` is not negligible. -/
theorem not_negligible_one_div_quartic_add_sq_mul_realLog :
    ¬ Negligible (fun n => (1 : ℝ≥0) /
      (1000 * (n : ℝ≥0) ^ 4 + (n : ℝ≥0) ^ 2 * Real.toNNReal (Real.log (n : ℝ)))) := by
  simpa only [one_div] using PolynomiallyBoundedNNReal.not_negligible_inv (by fun_prop)
    ((eventually_ge_atTop 1).frequently.mono fun n hn => by
      have : (0 : ℝ≥0) < n := by exact_mod_cast hn
      positivity)

example : ¬ Negligible (fun n => (1 : ℝ≥0) / (1000 * n ^ 4 + n ^ 2 * Nat.log 2 n : ℕ)) :=
  not_negligible_one_div_quartic_add_sq_mul_log 2

/-! ### General non-negligibility lemmas and hypothesis probes -/

example : ¬ Negligible (fun _ : ℕ => (1 / 2 : ℝ≥0)) :=
  not_negligible_of_frequently_ge (by norm_num) (Eventually.of_forall fun _ => le_rfl).frequently

example : ¬ Negligible (fun _ : ℕ => (1 / 2 : ℝ≥0)) :=
  not_negligible_of_eventually_ge (by norm_num) (Eventually.of_forall fun _ => le_rfl)

example : ¬ Negligible (fun _ : ℕ => (1 : ℝ≥0)) :=
  not_negligible_of_eventually_eq_one (Eventually.of_forall fun _ => rfl)

example : ¬ Negligible (fun n : ℕ => (n + 1 : ℝ≥0)⁻¹) :=
  PolynomiallyBoundedNNReal.not_negligible_inv (by fun_prop)
    (Eventually.of_forall fun _ => by positivity).frequently

example : ¬ Negligible (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)⁻¹) :=
  PolynomiallyBounded.not_negligible_inv (p := fun n => n + 1) (by fun_prop)
    (Eventually.of_forall fun n => Nat.succ_pos n).frequently

-- Probe 1: Without `∃ᶠ n in atTop, 0 < p n`, a polynomially bounded `p` can have a negligible
-- reciprocal in Lean (`0⁻¹ = 0`), even if `0 < p n` at finitely many inputs (`p 0 = 1`).
example : PolynomiallyBounded (fun n : ℕ => if n = 0 then 1 else 0) ∧
    0 < (if (0 : ℕ) = 0 then 1 else 0) ∧
    Negligible (fun n : ℕ => ((if n = 0 then 1 else 0 : ℕ) : ℝ≥0)⁻¹) := by
  refine ⟨by fun_prop, by decide, ?_⟩
  rw [(PolynomiallyBounded.ite (fun n => n = 0) (.const 1) (.const 0)).negligible_inv_iff]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : n ≠ 0 := by omega
  simp [hne]

-- Probe 2: In `negligible_inv_pow_log`, the hypothesis `1 < b` is needed: at `b = 1` (or `b = 0`),
-- `Nat.log b n = 0` so `((n : ℝ≥0) ^ Nat.log b n)⁻¹ = 1`, which is not negligible.
example : ¬ Negligible (fun n : ℕ => ((n : ℝ≥0) ^ Nat.log 1 n)⁻¹) := by
  simpa only [Nat.log_one_left, pow_zero, inv_one] using not_negligible_const one_ne_zero

-- Probe 3: In Theorem 2.11 / Definition 2.5, holding at one `c > 0` (e.g. `c = 1/2` for `1 / n`)
-- does not make `1 / n` negligible; universal quantification over all `c > 0` is required.
example : (∀ᶠ n : ℕ in atTop, (((1 : ℝ≥0) / n : ℝ≥0) : ℝ) < 1 / (n : ℝ) ^ (1 / 2 : ℝ)) ∧
    ¬ Negligible (fun n : ℕ => (1 : ℝ≥0) / n) := by
  refine ⟨?_, by simpa only [one_div, pow_one] using not_negligible_inv_pow 1⟩
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hlt : (n : ℝ) ^ (1 / 2 : ℝ) < (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hn1 (by norm_num : (1 / 2 : ℝ) < 1)
  push_cast
  exact one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hn0 _) hlt

/-! ### Example 2.11 ([BonehShoup2023], p. 29) -/

/-- The piecewise function of [BonehShoup2023], Example 2.11 (p. 29): `1 / n` on even `n` and
`1 / 2 ^ n` on odd `n`. At `n = 0` (which is even), `(1 : ℝ≥0) / 0 = 0`. -/
noncomputable def evenInvOddTwoPow (n : ℕ) : ℝ≥0 :=
  if Even n then (1 : ℝ≥0) / n else (1 : ℝ≥0) / 2 ^ n

/-- The natural-valued inverse `1 / f` of `evenInvOddTwoPow`: `n` on even `n` and `2 ^ n` on odd
`n`. Its cast to `ℝ≥0` equals `(evenInvOddTwoPow n)⁻¹` at every `n : ℕ`, including `n = 0`. -/
def evenIdOddTwoPow (n : ℕ) : ℕ :=
  if Even n then n else 2 ^ n

@[simp]
theorem evenInvOddTwoPow_apply (n : ℕ) :
    evenInvOddTwoPow n = if Even n then (1 : ℝ≥0) / n else (1 : ℝ≥0) / 2 ^ n := by
  unfold evenInvOddTwoPow; rfl

@[simp]
theorem evenIdOddTwoPow_apply (n : ℕ) :
    evenIdOddTwoPow n = if Even n then n else 2 ^ n := by
  unfold evenIdOddTwoPow; rfl

@[simp]
theorem inv_evenInvOddTwoPow (n : ℕ) :
    (evenInvOddTwoPow n)⁻¹ = (evenIdOddTwoPow n : ℝ≥0) := by
  simp only [evenInvOddTwoPow_apply, evenIdOddTwoPow_apply, one_div]
  split_ifs <;> simp

@[simp]
theorem inv_cast_evenIdOddTwoPow (n : ℕ) :
    (evenIdOddTwoPow n : ℝ≥0)⁻¹ = evenInvOddTwoPow n := by
  rw [← inv_evenInvOddTwoPow, inv_inv]

/-- **Example 2.11** ([BonehShoup2023], p. 29), first claim: `evenInvOddTwoPow` is not
negligible. -/
theorem not_negligible_evenInvOddTwoPow : ¬ Negligible evenInvOddTwoPow := by
  refine not_negligible_of_frequently_inv_le (P := fun n => (n : ℝ≥0)) (by fun_prop) ?_
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨2 * (N + 1), by omega, by positivity, ?_⟩
  have heven : Even (2 * (N + 1)) := ⟨N + 1, by ring⟩
  simp [heven]

/-- **Example 2.11** ([BonehShoup2023], p. 29), second claim (natural form): `evenIdOddTwoPow` is
not polynomially bounded. -/
theorem not_polynomiallyBounded_evenIdOddTwoPow :
    ¬ PolynomiallyBounded evenIdOddTwoPow := by
  intro hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp hp.eventually_lt_two_pow
  have hlt := hN (2 * N + 1) (by omega)
  have hodd : ¬ Even (2 * N + 1) := Nat.not_even_two_mul_add_one N
  simp [hodd] at hlt

/-- **Example 2.11** ([BonehShoup2023], p. 29), second claim (`ℝ≥0` reciprocal form):
`fun n => (evenInvOddTwoPow n)⁻¹` is not polynomially bounded in `ℝ≥0`. -/
theorem not_polynomiallyBoundedNNReal_inv_evenInvOddTwoPow :
    ¬ PolynomiallyBoundedNNReal (fun n => (evenInvOddTwoPow n)⁻¹) := by
  rintro ⟨p, hp, hle⟩
  refine not_polynomiallyBounded_evenIdOddTwoPow (hp.mono_of_le fun n => ?_)
  have h : (evenInvOddTwoPow n)⁻¹ ≤ p n := hle n
  rw [inv_evenInvOddTwoPow] at h
  exact_mod_cast h

/-- **Example 2.11** ([BonehShoup2023], p. 29), third claim (natural form): `evenIdOddTwoPow` is
not super-poly (its reciprocal in `ℝ≥0` is not negligible). -/
theorem not_negligible_inv_evenIdOddTwoPow :
    ¬ Negligible (fun n => (evenIdOddTwoPow n : ℝ≥0)⁻¹) := by
  simpa only [inv_cast_evenIdOddTwoPow] using not_negligible_evenInvOddTwoPow

/-- **Example 2.11** ([BonehShoup2023], p. 29), third claim (`ℝ≥0` reciprocal form):
`fun n => (evenInvOddTwoPow n)⁻¹` is not super-poly (`((evenInvOddTwoPow n)⁻¹)⁻¹` is not
negligible). -/
theorem not_negligible_inv_inv_evenInvOddTwoPow :
    ¬ Negligible (fun n => ((evenInvOddTwoPow n)⁻¹)⁻¹) := by
  simpa only [inv_inv] using not_negligible_evenInvOddTwoPow

example : evenIdOddTwoPow 0 = 0 ∧ evenIdOddTwoPow 1 = 2 ∧
    evenIdOddTwoPow 2 = 2 ∧ evenIdOddTwoPow 3 = 8 ∧ evenIdOddTwoPow 4 = 4 := by
  simp only [evenIdOddTwoPow_apply]
  decide

example : evenInvOddTwoPow 0 = 0 ∧ evenInvOddTwoPow 2 = 1 / 2 ∧ evenInvOddTwoPow 3 = 1 / 8 := by
  refine ⟨by simp, ?_, ?_⟩
  · have : Even 2 := by decide
    simp [this]
  · have : ¬ Even 3 := by decide
    simp [this]
    norm_num

end CslibFrontierTests.Crypto.NegligibleInversePolynomial
