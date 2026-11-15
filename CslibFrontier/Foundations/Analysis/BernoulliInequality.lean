/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/MeanInequalitiesPow.lean)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Forms of Bernoulli's inequality

For `p ≤ 1` and `n : ℕ`, `(1 - p) ^ n * (1 + n * p) ≤ 1`
(`Real.one_sub_pow_mul_one_add_mul_le_one`). By induction on `n`, each factor `1 - p ≥ 0` decreases
`(1 + (n + 1) * p)` below `(1 + n * p) / (1 - p)` because `(n + 1) * p ^ 2 ≥ 0`. For `0 ≤ p ≤ 1`
this bounds `(1 - p) ^ n` from above by `1 / (1 + n * p)`.

The homogeneous form is the tangent-line inequality for `x ↦ x ^ (n + 1)` on `[0, ∞)`:
`y ^ (n + 1) + (n + 1) * y ^ n * (x - y) ≤ x ^ (n + 1)` for `0 ≤ x` and `0 ≤ y`
(`Real.pow_add_mul_sub_le_pow`). For `0 < y` it is Mathlib's `one_add_mul_le_pow` at `x / y - 1`,
multiplied by `y ^ (n + 1)`.

## Main results

* `Real.one_sub_pow_mul_one_add_mul_le_one`: `(1 - p) ^ n * (1 + n * p) ≤ 1` for `p ≤ 1`.
* `Real.one_sub_pow_le_one_div_one_add_mul`: `(1 - p) ^ n ≤ 1 / (1 + n * p)` for `0 ≤ p ≤ 1`.
* `Real.pow_add_mul_sub_le_pow`: `y ^ (n + 1) + (n + 1) * y ^ n * (x - y) ≤ x ^ (n + 1)` for
  `0 ≤ x` and `0 ≤ y`.
-/

public section

namespace Real

/-- A multiplicative form of Bernoulli's inequality: `(1 - p) ^ n (1 + n p) ≤ 1` for `p ≤ 1`. -/
theorem one_sub_pow_mul_one_add_mul_le_one {p : ℝ} (hp : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    have hnon := mul_nonneg (pow_nonneg (sub_nonneg.mpr hp) n)
      (mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg p))
    nlinarith

/-- For `0 ≤ p ≤ 1`, `(1 - p) ^ n ≤ 1 / (1 + n p)`. -/
theorem one_sub_pow_le_one_div_one_add_mul {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ 1 / (1 + (n : ℝ) * p) :=
  (le_div_iff₀ (by positivity)).mpr (one_sub_pow_mul_one_add_mul_le_one hp₁ n)

/-- The tangent-line inequality for `x ↦ x ^ (n + 1)` on `[0, ∞)`, a homogeneous form of
Bernoulli's inequality: `y ^ (n + 1) + (n + 1) y ^ n (x - y) ≤ x ^ (n + 1)` for `0 ≤ x` and
`0 ≤ y`. -/
theorem pow_add_mul_sub_le_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    y ^ (n + 1) + (n + 1) * y ^ n * (x - y) ≤ x ^ (n + 1) := by
  rcases hy.eq_or_lt with rfl | hy
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [zero_pow hn.ne', pow_nonneg hx]
  · have hb := one_add_mul_le_pow (a := x / y - 1) (by linarith [div_nonneg hx hy.le]) (n + 1)
    have hyn : 0 < y ^ (n + 1) := pow_pos hy _
    rw [show 1 + (x / y - 1) = x / y by ring, div_pow, le_div_iff₀ hyn] at hb
    push_cast at hb
    calc y ^ (n + 1) + (n + 1) * y ^ n * (x - y)
        = (1 + (n + 1) * (x / y - 1)) * y ^ (n + 1) := by
          field_simp
          ring
      _ ≤ x ^ (n + 1) := hb

end Real
