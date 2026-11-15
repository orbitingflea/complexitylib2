/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Falling factorials against the exponential

Bounds on the ratio `(n)_k / n ^ k = n.descFactorial k / n ^ k`, which is the probability that `k`
independent uniform samples from a set of size `n` are distinct. Writing the ratio as the product
`∏_{i < k} (n - i) / n` (`Nat.cast_descFactorial_div_pow`) and comparing factor by factor with
`exp (-i / n)` gives an upper bound valid for all `n` and `k`, and comparing with `exp (-2 i / n)`
gives a lower bound when `0 < n` and `2 k ≤ n + 2`, using the scalar inequality
`exp (-x) ≤ 1 - x / 2` on `[0, 1]`.

`CslibFrontier.Probability.IID.Birthday` turns these into bounds on the collision probability of
independent samples.

## Main results

* `Real.exp_neg_le_one_sub_div_two`: `exp (-x) ≤ 1 - x / 2` for `x ∈ [0, 1]`.
* `Nat.cast_descFactorial_div_pow`: `(n)_k / n ^ k = ∏_{i < k} (n - i) / n` in any semifield.
* `Nat.descFactorial_div_pow_le_exp`: `(n)_k / n ^ k ≤ exp (-k (k - 1) / (2 n))`.
* `Nat.exp_le_descFactorial_div_pow`: `exp (-k (k - 1) / n) ≤ (n)_k / n ^ k` for `0 < n` and
  `2 k ≤ n + 2`.
-/

public section

open Finset

namespace Real

/-- `exp (-x) ≤ 1 - x / 2` for `x ∈ [0, 1]`. -/
theorem exp_neg_le_one_sub_div_two {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : exp (-x) ≤ 1 - x / 2 :=
  (exp_neg_le_one_sub_add_sq_div_two h0).trans (by nlinarith)

end Real

namespace Nat

/-- `(n)_k / n ^ k = ∏_{i < k} (n - i) / n` in any semifield, with truncated subtraction. -/
theorem cast_descFactorial_div_pow {K : Type*} [Semifield K] (n k : ℕ) :
    (n.descFactorial k : K) / (n : K) ^ k = ∏ i ∈ range k, (((n - i : ℕ) : K) / n) := by
  rw [descFactorial_eq_prod_range, cast_prod, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range]

/-- Gauss's summation formula `∑_{i < k} i = k (k - 1) / 2`, cast to `ℝ`. -/
private theorem sum_range_cast (k : ℕ) : ∑ i ∈ range k, (i : ℝ) = k * (k - 1) / 2 := by
  rw [← Nat.cast_sum, Finset.sum_range_id, ← Nat.choose_two_right, Nat.cast_choose_two]

/-- `(n)_k / n ^ k ≤ exp (-k (k - 1) / (2 n))`, for all `n` and `k`: at `n = 0` both sides are `1`
for `k = 0` and the left side is `0` otherwise, and for `k > n` the left side is `0`. -/
theorem descFactorial_div_pow_le_exp (n k : ℕ) :
    (n.descFactorial k : ℝ) / (n : ℝ) ^ k ≤ Real.exp (-(k * (k - 1) / (2 * n))) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rcases k with _ | k
    · simp
    · rw [zero_descFactorial_succ]; simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : Real.exp (-(k * (k - 1) / (2 * n))) = ∏ i ∈ range k, Real.exp (-(i / n)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, sum_range_cast]
    congr 1; ring
  rw [cast_descFactorial_div_pow, e]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  rcases le_or_gt i n with h | h
  · rw [cast_sub h, sub_div, div_self hn'.ne']
    exact Real.one_sub_le_exp_neg _
  · rw [Nat.sub_eq_zero_of_le h.le, cast_zero, zero_div]
    exact (Real.exp_pos _).le

/-- `exp (-k (k - 1) / n) ≤ (n)_k / n ^ k` when `0 < n` and `2 k ≤ n + 2`, that is, when every
factor `1 - i / n` with `i < k` has `2 i / n ≤ 1`. -/
theorem exp_le_descFactorial_div_pow {n k : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n + 2) :
    Real.exp (-(k * (k - 1) / n)) ≤ (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : Real.exp (-(k * (k - 1) / n)) = ∏ i ∈ range k, Real.exp (-(2 * (i / n))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      sum_range_cast]
    congr 1; ring
  rw [cast_descFactorial_div_pow, e]
  refine Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i hi => ?_
  have hin : 2 * i ≤ n := by have := Finset.mem_range.1 hi; omega
  rw [cast_sub (by omega : i ≤ n), sub_div, div_self hn'.ne']
  have h1 : 2 * ((i : ℝ) / n) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hn']; exact_mod_cast hin
  linarith [Real.exp_neg_le_one_sub_div_two (by positivity) h1]

end Nat
