/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Negligible.Dyadic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Inverse-polynomial characterizations and examples of negligible functions

Equivalent forms of `Cslib.Crypto.Negligible`, subexponential decay bounds, and inverse-polynomial
non-negligibility criteria from [BonehShoup2023], v0.6, §2.3.1 (printed pp. 28–29).

`Negligible ε` is defined as superpolynomial decay
`∀ k : ℕ, Tendsto (fun n => n ^ k * ε n) atTop (𝓝 0)` over `ℕ → ℝ≥0`. This module proves its
equivalence with the inverse-polynomial comparisons of Definition 2.5 (`ε n < 1 / n ^ k`,
`ε n ≤ 1 / n ^ k`, and `ε n ≤ 1 / p n` for positive polynomially bounded `p : ℕ → ℕ`), with
Definition 2.5's real-exponent condition
`∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, (ε n : ℝ) < 1 / (n : ℝ) ^ c`, and with Theorem 2.11's
real-exponent limit condition
`∀ c : ℝ, 0 < c → Tendsto (fun n => (ε n : ℝ) * (n : ℝ) ^ c) atTop (𝓝 0)`, as well as Theorem 2.11
directly for signed functions `f : ℕ → ℝ` (`eventually_abs_lt_inv_rpow_iff_tendsto_mul_rpow`).

For the negligible functions of Example 2.10 (`2 ^ (-√n)` and `n ^ (-log n)`, alongside `2 ^ (-n)`
in `CslibFrontier.Crypto.Negligible.Dyadic`), `PolynomiallyLowerBounded.sqrt` registers `Nat.sqrt`
as a polynomially lower-bounded parameter schedule, and `negligible_inv_pow_of_tendsto_atTop` and
`negligible_inv_rpow_of_tendsto_atTop` prove `((n : ℝ≥0) ^ f n)⁻¹` negligible whenever `f` tends to
infinity, covering both natural and real square-root and logarithmic exponents.

For the remark after Definition 2.7 ("if `f` is a poly-bounded function, then `1 / f` is definitely
not a negligible function"), `PolynomiallyBoundedNNReal.not_negligible_inv` and
`PolynomiallyBounded.not_negligible_inv` show that the reciprocal of any frequently positive
polynomially bounded function is not negligible, and `negligible_inv_iff` shows that under total
division (`(0 : ℝ≥0)⁻¹ = 0`) the reciprocal is negligible if and only if the function is eventually
zero. This yields `not_negligible_inv_pow` for `((n : ℝ≥0) ^ k)⁻¹`, and
`PolynomiallyBoundedNNReal.toNNReal_log` bounds `Real.toNNReal (Real.log (p n : ℝ))` for
polynomially bounded `p : ℕ → ℕ`. Concrete instances from Examples 2.10 and 2.11 (including
`1 / (1000 n ^ 4 + n ^ 2 log n)` and the piecewise function equal to `1 / n` on even `n` and
`2 ^ (-n)` on odd `n`) are checked in `CslibFrontierTests.Crypto.NegligibleInversePolynomial`.

## Main results

* `Cslib.Crypto.negligible_iff_eventually_lt_inv_pow`,
  `Cslib.Crypto.negligible_iff_eventually_le_inv_pow`,
  `Cslib.Crypto.negligible_iff_eventually_le_inv_polynomial`: natural-exponent inverse-polynomial
  characterizations of `Negligible`.
* `Cslib.Crypto.negligible_iff_eventually_lt_inv_rpow`,
  `Cslib.Crypto.negligible_iff_tendsto_mul_rpow`,
  `Cslib.Crypto.eventually_abs_lt_inv_rpow_iff_tendsto_mul_rpow`: real-exponent characterizations
  (Definition 2.5 and Theorem 2.11).
* `Cslib.Crypto.PolynomiallyLowerBounded.sqrt`,
  `Cslib.Crypto.negligible_inv_two_pow_of_polynomiallyLowerBounded`,
  `Cslib.Crypto.negligible_inv_two_pow_sqrt`, `Cslib.Crypto.negligible_inv_two_rpow_sqrt`,
  `Cslib.Crypto.negligible_two_rpow_neg_sqrt`: square-root schedule closure and `2 ^ (-√n)`
  (Example 2.10).
* `Cslib.Crypto.negligible_inv_rpow_of_tendsto_atTop`,
  `Cslib.Crypto.negligible_rpow_neg_of_tendsto_atTop`,
  `Cslib.Crypto.negligible_inv_pow_of_tendsto_atTop`,
  `Cslib.Crypto.negligible_inv_pow_log`, `Cslib.Crypto.negligible_inv_rpow_log`,
  `Cslib.Crypto.negligible_rpow_neg_log`: superpolynomial decay of `n ^ (-f n)` when `f n → ∞`,
  and `n ^ (-log n)` (Example 2.10).
* `Cslib.Crypto.PolynomiallyBoundedNNReal.toNNReal_log`,
  `Cslib.Crypto.not_negligible_of_frequently_ge`, `Cslib.Crypto.not_negligible_of_eventually_ge`,
  `Cslib.Crypto.not_negligible_of_eventually_eq_one`,
  `Cslib.Crypto.not_negligible_of_frequently_inv_le`,
  `Cslib.Crypto.PolynomiallyBoundedNNReal.not_negligible_inv`,
  `Cslib.Crypto.PolynomiallyBoundedNNReal.negligible_inv_iff`,
  `Cslib.PolynomiallyBounded.not_negligible_inv`,
  `Cslib.PolynomiallyBounded.negligible_inv_iff`,
  `Cslib.Crypto.not_negligible_inv_pow`: non-negligibility of inverse polynomials (Remark after
  Definition 2.7 and Example 2.10).

## Deviations from [BonehShoup2023]

* Functions are indexed by `ℕ` rather than `ℤ_{≥ 1}`, and `Negligible` has codomain `ℝ≥0` (since
  advantages and probabilities are nonnegative); `eventually_abs_lt_inv_rpow_iff_tendsto_mul_rpow`
  also states Theorem 2.11 directly for signed `f : ℕ → ℝ`.
* Definition 2.6 ("`f` is super-poly if `1 / f` is negligible", p. 28) is not given a separate
  named predicate: across the library it is written directly as `Negligible (fun n => (f n)⁻¹)` or
  `Negligible (fun n => 1 / f n)`. Because `(0 : ℝ≥0)⁻¹ = 0` in Lean, a wrapper `SuperPoly f`
  defined as `Negligible (fun n => (f n)⁻¹)` would hold for `f = 0`.
* For the same reason (`0⁻¹ = 0`), the remark after Definition 2.7 (p. 29) that `1 / f` is not
  negligible for polynomially bounded `f` requires the positivity hypothesis
  `∃ᶠ n in atTop, 0 < f n`, which `negligible_inv_iff` shows is both necessary and sufficient.
* In Example 2.10 (p. 28), `n ^ (-log n)` is provided for both the discrete logarithm `Nat.log b n`
  with `1 < b` (`negligible_inv_pow_log`, false for `b ≤ 1` where `Nat.log b n = 0`) and the real
  logarithm `Real.log (n : ℝ)` (`negligible_inv_rpow_log`, `negligible_rpow_neg_log`).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], v0.6, §2.3.1,
  pp. 28–29.
-/

public section

open Filter Topology
open scoped NNReal

namespace Cslib.Crypto

/-! ### Theorem 2.11 and Definition 2.5 equivalences -/

private theorem tendsto_inv_natCast_nnreal :
    Tendsto (fun n : ℕ => (n : ℝ≥0)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- Definition 2.5 ([BonehShoup2023], p. 28) with natural exponents in `ℝ≥0` (strict inequality):
`ε` is negligible if and only if for every natural exponent `k`, `ε n < 1 / n ^ k` eventually. -/
theorem negligible_iff_eventually_lt_inv_pow {ε : ℕ → ℝ≥0} :
    Negligible ε ↔ ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ε n < 1 / (n : ℝ≥0) ^ k := by
  constructor
  · intro hε k
    filter_upwards [(hε k).eventually_lt_const zero_lt_one, eventually_ge_atTop 1] with n hn hn1
    have hpos : (0 : ℝ≥0) < (n : ℝ≥0) ^ k := pow_pos (by exact_mod_cast hn1) k
    rw [lt_div_iff₀ hpos, mul_comm]
    exact hn
  · intro h k
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_natCast_nnreal
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [h (k + 1), eventually_ge_atTop 1] with n hn hn1
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hpos : (0 : ℝ≥0) < (n : ℝ≥0) ^ (k + 1) := pow_pos (by exact_mod_cast hn1) _
    have hmul : ε n * (n : ℝ≥0) ^ (k + 1) ≤ 1 := ((lt_div_iff₀ hpos).mp hn).le
    calc
      (n : ℝ≥0) ^ k * ε n = (ε n * (n : ℝ≥0) ^ (k + 1)) * (n : ℝ≥0)⁻¹ := by
        rw [pow_succ, ← mul_assoc, mul_comm ((n : ℝ≥0) ^ k), mul_assoc, mul_inv_cancel₀ hn0,
          mul_one]
      _ ≤ 1 * (n : ℝ≥0)⁻¹ := mul_le_mul_of_nonneg_right hmul zero_le
      _ = (n : ℝ≥0)⁻¹ := one_mul _

/-- Definition 2.5 ([BonehShoup2023], p. 28) with natural exponents in `ℝ≥0` (non-strict
inequality): `ε` is negligible if and only if for every natural exponent `k`, `ε n ≤ 1 / n ^ k`
eventually. -/
theorem negligible_iff_eventually_le_inv_pow {ε : ℕ → ℝ≥0} :
    Negligible ε ↔ ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ε n ≤ 1 / (n : ℝ≥0) ^ k := by
  refine ⟨fun hε k => (negligible_iff_eventually_lt_inv_pow.mp hε k).mono fun _ => le_of_lt,
    fun h => negligible_iff_eventually_lt_inv_pow.mpr fun k => ?_⟩
  filter_upwards [h (k + 1), eventually_ge_atTop 2] with n hn hn2
  refine hn.trans_lt ?_
  rw [one_div, one_div]
  exact inv_strictAnti₀ (pow_pos (by exact_mod_cast (by omega : 0 < n)) k)
    (pow_lt_pow_right₀ (by exact_mod_cast hn2) (Nat.lt_succ_self k))

/-- Two-way form of `Negligible.eventually_le_inv_polynomial`: `ε` is negligible if and only if it
is eventually bounded by the reciprocal of every positive polynomially bounded natural function. -/
theorem negligible_iff_eventually_le_inv_polynomial {ε : ℕ → ℝ≥0} :
    Negligible ε ↔ ∀ p : ℕ → ℕ, PolynomiallyBounded p → (∀ n, 0 < p n) →
      ∀ᶠ n : ℕ in atTop, (ε n : ℝ) ≤ 1 / (p n : ℝ) := by
  refine ⟨fun hε p hp hpos => hε.eventually_le_inv_polynomial hp hpos, fun h => ?_⟩
  refine negligible_iff_eventually_le_inv_pow.mpr fun k => ?_
  have hp : PolynomiallyBounded (fun n => (n + 1) ^ k) := by fun_prop
  have hpos : ∀ n, 0 < (n + 1) ^ k := fun n => Nat.pow_pos (Nat.succ_pos n)
  filter_upwards [h _ hp hpos, eventually_ge_atTop 1] with n hn _
  apply NNReal.coe_le_coe.mp
  push_cast at hn ⊢
  refine hn.trans ?_
  gcongr
  linarith

/-- **Definition 2.5** ([BonehShoup2023], p. 28): `ε` is negligible if and only if for every real
`c > 0`, `(ε n : ℝ) < 1 / (n : ℝ) ^ c` eventually. -/
theorem negligible_iff_eventually_lt_inv_rpow {ε : ℕ → ℝ≥0} :
    Negligible ε ↔ ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (ε n : ℝ) < 1 / (n : ℝ) ^ c := by
  constructor
  · intro hε c hc
    filter_upwards [negligible_iff_eventually_lt_inv_pow.mp hε ⌈c⌉₊,
      eventually_ge_atTop 1] with n hn hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn' : (ε n : ℝ) < 1 / (n : ℝ) ^ ⌈c⌉₊ := by exact_mod_cast hn
    refine hn'.trans_le ?_
    rw [← Real.rpow_natCast]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) c)
      (Real.rpow_le_rpow_of_exponent_le hnR (Nat.le_ceil c))
  · intro h
    refine negligible_iff_eventually_lt_inv_pow.mpr fun k => ?_
    filter_upwards [h ((k + 1 : ℕ) : ℝ) (by positivity), eventually_ge_atTop 1] with n hn hn1
    rw [Real.rpow_natCast] at hn
    apply NNReal.coe_lt_coe.mp
    push_cast
    refine hn.trans_le ?_
    exact one_div_le_one_div_of_le (pow_pos (by exact_mod_cast hn1) k)
      (pow_le_pow_right₀ (by exact_mod_cast hn1) (Nat.le_succ k))

/-- **Theorem 2.11** ([BonehShoup2023], p. 28) for `ε : ℕ → ℝ≥0`: `ε` is negligible if and only if
for every real `c > 0`, `ε n * n ^ c → 0` as `n → ∞`. -/
theorem negligible_iff_tendsto_mul_rpow {ε : ℕ → ℝ≥0} :
    Negligible ε ↔
      ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => (ε n : ℝ) * (n : ℝ) ^ c) atTop (𝓝 0) := by
  constructor
  · intro hε c hc
    have hlim := negligible_iff_coe.mp hε ⌈c⌉₊
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => mul_nonneg (NNReal.coe_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) c)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    rw [mul_comm ((n : ℝ) ^ ⌈c⌉₊), ← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (Nat.le_ceil c))
      (NNReal.coe_nonneg _)
  · intro h
    refine negligible_iff_eventually_lt_inv_rpow.mpr fun c hc => ?_
    filter_upwards [(h c hc).eventually_lt_const zero_lt_one,
      eventually_ge_atTop 1] with n hn hn1
    have hpos : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by exact_mod_cast hn1) c
    exact (lt_div_iff₀ hpos).mpr hn

/-- **Theorem 2.11** ([BonehShoup2023], p. 28) for real-valued `f : ℕ → ℝ`: Definition 2.5
(`∀ c > 0`, eventually `|f n| < 1 / n ^ c`) is equivalent to `∀ c > 0`, `lim (f n * n ^ c) = 0`. -/
theorem eventually_abs_lt_inv_rpow_iff_tendsto_mul_rpow {f : ℕ → ℝ} :
    (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, |f n| < 1 / (n : ℝ) ^ c) ↔
      (∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => f n * (n : ℝ) ^ c) atTop (𝓝 0)) := by
  let ε : ℕ → ℝ≥0 := fun n => ⟨|f n|, abs_nonneg _⟩
  have h1 : (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, |f n| < 1 / (n : ℝ) ^ c) ↔ Negligible ε :=
    negligible_iff_eventually_lt_inv_rpow (ε := ε) |>.symm
  rw [h1, negligible_iff_tendsto_mul_rpow]
  refine forall₂_congr fun c _ => ?_
  rw [tendsto_zero_iff_abs_tendsto_zero (f := fun n : ℕ => f n * (n : ℝ) ^ c)]
  refine tendsto_congr fun n => ?_
  change |f n| * (n : ℝ) ^ c = |f n * (n : ℝ) ^ c|
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) c)]

/-! ### Example 2.10 negligible functions (`2 ^ (-√n)` and `n ^ (-log n)`) -/

/-- Natural square roots preserve a polynomial lower bound (`n ≤ (√n + 1) ^ 2`). -/
@[fun_prop]
protected theorem PolynomiallyLowerBounded.sqrt {g : ℕ → ℕ} (hg : PolynomiallyLowerBounded g) :
    PolynomiallyLowerBounded (fun n => Nat.sqrt (g n)) :=
  PolynomiallyLowerBounded.comp
    ⟨1, 2, fun m => by simpa only [one_mul, sq] using (Nat.lt_succ_sqrt m).le⟩ hg

/-- Reindexing `((2 : ℝ≥0) ^ g n)⁻¹` along any polynomially lower-bounded schedule `g` is
negligible. -/
@[fun_prop]
theorem negligible_inv_two_pow_of_polynomiallyLowerBounded {g : ℕ → ℕ}
    (hg : PolynomiallyLowerBounded g) :
    Negligible (fun n => ((2 : ℝ≥0) ^ g n)⁻¹) :=
  negligible_inv_two_pow.comp_polynomiallyLowerBounded hg

/-- **Example 2.10** ([BonehShoup2023], p. 28), natural square root: `((2 : ℝ≥0) ^ Nat.sqrt n)⁻¹`
is negligible. -/
theorem negligible_inv_two_pow_sqrt : Negligible (fun n => ((2 : ℝ≥0) ^ Nat.sqrt n)⁻¹) :=
  negligible_inv_two_pow_of_polynomiallyLowerBounded (.sqrt .id)

/-- **Example 2.10** ([BonehShoup2023], p. 28), real square root: `((2 : ℝ≥0) ^ Real.sqrt n)⁻¹`
is negligible. -/
@[fun_prop]
theorem negligible_inv_two_rpow_sqrt :
    Negligible (fun n => ((2 : ℝ≥0) ^ Real.sqrt (n : ℝ))⁻¹) := by
  refine negligible_of_le negligible_inv_two_pow_sqrt fun n => ?_
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast (sq (Nat.sqrt n) ▸ Nat.sqrt_le n)
  rw [← NNReal.rpow_natCast]
  exact inv_anti₀ (NNReal.rpow_pos two_pos)
    (NNReal.rpow_le_rpow_of_exponent_le one_le_two hsqrt)

/-- **Example 2.10** ([BonehShoup2023], p. 28), negative real square-root exponent:
`(2 : ℝ≥0) ^ (-Real.sqrt n)` is negligible. -/
@[fun_prop]
theorem negligible_two_rpow_neg_sqrt :
    Negligible (fun n => (2 : ℝ≥0) ^ (-Real.sqrt (n : ℝ))) := by
  simpa only [NNReal.rpow_neg] using negligible_inv_two_rpow_sqrt

/-- For any real exponent `f : ℕ → ℝ` tending to infinity, `((n : ℝ≥0) ^ f n)⁻¹` is negligible. -/
theorem negligible_inv_rpow_of_tendsto_atTop {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Negligible (fun n => ((n : ℝ≥0) ^ f n)⁻¹) := by
  refine negligible_iff_eventually_le_inv_pow.mpr fun k => ?_
  filter_upwards [hf.eventually_ge_atTop (k : ℝ), eventually_ge_atTop 1] with n hfn hn1
  have hn0 : (0 : ℝ≥0) < n := by exact_mod_cast hn1
  rw [one_div, ← NNReal.rpow_natCast]
  exact inv_anti₀ (NNReal.rpow_pos hn0)
    (NNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hfn)

/-- For any real exponent `f : ℕ → ℝ` tending to infinity, `(n : ℝ≥0) ^ (-f n)` is negligible. -/
theorem negligible_rpow_neg_of_tendsto_atTop {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Negligible (fun n => (n : ℝ≥0) ^ (-f n)) := by
  simpa only [NNReal.rpow_neg] using negligible_inv_rpow_of_tendsto_atTop hf

/-- For any natural exponent `f : ℕ → ℕ` tending to infinity, `((n : ℝ≥0) ^ f n)⁻¹` is
negligible. -/
theorem negligible_inv_pow_of_tendsto_atTop {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Negligible (fun n => ((n : ℝ≥0) ^ f n)⁻¹) := by
  simpa only [Function.comp_apply, NNReal.rpow_natCast] using
    negligible_inv_rpow_of_tendsto_atTop (tendsto_natCast_atTop_atTop.comp hf)

/-- **Example 2.10** ([BonehShoup2023], p. 28), natural logarithm: for `1 < b`,
`((n : ℝ≥0) ^ Nat.log b n)⁻¹` is negligible. -/
@[fun_prop]
theorem negligible_inv_pow_log {b : ℕ} (hb : 1 < b) :
    Negligible (fun n => ((n : ℝ≥0) ^ Nat.log b n)⁻¹) :=
  negligible_inv_pow_of_tendsto_atTop (Nat.tendsto_log_atTop hb)

/-- **Example 2.10** ([BonehShoup2023], p. 28), real logarithm: `((n : ℝ≥0) ^ Real.log n)⁻¹`
is negligible. -/
@[fun_prop]
theorem negligible_inv_rpow_log :
    Negligible (fun n => ((n : ℝ≥0) ^ Real.log (n : ℝ))⁻¹) :=
  negligible_inv_rpow_of_tendsto_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Example 2.10** ([BonehShoup2023], p. 28), negative real logarithm exponent:
`(n : ℝ≥0) ^ (-Real.log n)` is negligible. -/
@[fun_prop]
theorem negligible_rpow_neg_log :
    Negligible (fun n => (n : ℝ≥0) ^ (-Real.log (n : ℝ))) :=
  negligible_rpow_neg_of_tendsto_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-! ### Non-negligibility of inverse polynomials -/

/-- Real logarithms of polynomially bounded natural functions are polynomially bounded in `ℝ≥0`
(`Real.toNNReal (Real.log (p n)) ≤ p n`). -/
@[fun_prop]
protected theorem PolynomiallyBoundedNNReal.toNNReal_log {p : ℕ → ℕ}
    (hp : PolynomiallyBounded p) :
    PolynomiallyBoundedNNReal (fun n => Real.toNNReal (Real.log (p n : ℝ))) := by
  refine ⟨p, hp, fun n => ?_⟩
  rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_natCast]
  rcases Nat.eq_zero_or_pos (p n) with h0 | hpos
  · simp [h0]
  · exact (Real.log_le_sub_one_of_pos (by exact_mod_cast hpos)).trans (by linarith)

/-- A function that frequently takes values at least a positive constant `c` is not negligible. -/
theorem not_negligible_of_frequently_ge {ε : ℕ → ℝ≥0} {c : ℝ≥0} (hc : c ≠ 0)
    (h : ∃ᶠ n in atTop, c ≤ ε n) : ¬ Negligible ε := by
  intro hε
  have ht : Tendsto ε atTop (𝓝 0) := by simpa only [pow_zero, one_mul] using hε 0
  exact h ((ht.eventually_lt_const (pos_iff_ne_zero.mpr hc)).mono fun _ => not_le_of_gt)

/-- A function that is eventually at least a positive constant `c` is not negligible. -/
theorem not_negligible_of_eventually_ge {ε : ℕ → ℝ≥0} {c : ℝ≥0} (hc : c ≠ 0)
    (h : ∀ᶠ n in atTop, c ≤ ε n) : ¬ Negligible ε :=
  not_negligible_of_frequently_ge hc h.frequently

/-- A function that is eventually equal to `1` is not negligible. -/
theorem not_negligible_of_eventually_eq_one {f : ℕ → ℝ≥0}
    (hf : ∀ᶠ n in atTop, f n = 1) : ¬ Negligible f :=
  not_negligible_of_eventually_ge one_ne_zero (hf.mono fun _ hn => hn.symm.le)

/-- A function that is frequently bounded below by the reciprocal of positive values of a
polynomially bounded `ℝ≥0` function is not negligible. -/
theorem not_negligible_of_frequently_inv_le {ε P : ℕ → ℝ≥0} (hP : PolynomiallyBoundedNNReal P)
    (h : ∃ᶠ n in atTop, 0 < P n ∧ (P n)⁻¹ ≤ ε n) : ¬ Negligible ε := by
  intro hε
  refine not_negligible_of_frequently_ge one_ne_zero ?_ (hε.polynomiallyBoundedNNReal_mul hP)
  refine h.mono fun n ⟨hpos, hle⟩ => ?_
  calc
    (1 : ℝ≥0) = P n * (P n)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
    _ ≤ P n * ε n := mul_le_mul_of_nonneg_left hle zero_le

/-- **Remark after Definition 2.7** ([BonehShoup2023], p. 29): if `P` is a polynomially bounded
`ℝ≥0` function that is frequently positive, its reciprocal `(P n)⁻¹` is not negligible. -/
theorem PolynomiallyBoundedNNReal.not_negligible_inv {P : ℕ → ℝ≥0}
    (hP : PolynomiallyBoundedNNReal P) (hpos : ∃ᶠ n in atTop, 0 < P n) :
    ¬ Negligible (fun n => (P n)⁻¹) :=
  not_negligible_of_frequently_inv_le hP (hpos.mono fun _ hn => ⟨hn, le_rfl⟩)

/-- Under Lean's total division `(0 : ℝ≥0)⁻¹ = 0`, the reciprocal of a polynomially bounded
`ℝ≥0` function `P` is negligible if and only if `P` is eventually zero. -/
theorem PolynomiallyBoundedNNReal.negligible_inv_iff {P : ℕ → ℝ≥0}
    (hP : PolynomiallyBoundedNNReal P) :
    Negligible (fun n => (P n)⁻¹) ↔ ∀ᶠ n in atTop, P n = 0 := by
  constructor
  · intro hneg
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, 0 < P n := by
      rw [Filter.not_eventually] at hnot
      exact hnot.mono fun n hn => pos_iff_ne_zero.mpr hn
    exact hP.not_negligible_inv hfreq hneg
  · intro hz
    exact negligible_zero.congr' (hz.mono fun n hn => by simp [hn])

/-- Inverse powers `((n : ℝ≥0) ^ k)⁻¹` are not negligible for any natural exponent `k`
([BonehShoup2023], Example 2.10, p. 28). -/
theorem not_negligible_inv_pow (k : ℕ) : ¬ Negligible (fun n => ((n : ℝ≥0) ^ k)⁻¹) := by
  have hP : PolynomiallyBoundedNNReal (fun n => (n : ℝ≥0) ^ k) := by fun_prop
  refine hP.not_negligible_inv ((eventually_ge_atTop 1).frequently.mono fun n hn => ?_)
  exact pow_pos (by exact_mod_cast hn) k

end Cslib.Crypto

namespace Cslib.PolynomiallyBounded

open Filter Cslib.Crypto
open scoped NNReal

/-- **Remark after Definition 2.7** ([BonehShoup2023], p. 29): if `p : ℕ → ℕ` is polynomially
bounded and frequently positive, `(p n : ℝ≥0)⁻¹` is not negligible. -/
theorem not_negligible_inv {p : ℕ → ℕ} (hp : PolynomiallyBounded p)
    (hpos : ∃ᶠ n in atTop, 0 < p n) : ¬ Negligible (fun n => (p n : ℝ≥0)⁻¹) :=
  (PolynomiallyBoundedNNReal.natCast hp).not_negligible_inv
    (hpos.mono fun _ hn => by exact_mod_cast hn)

/-- For a polynomially bounded `p : ℕ → ℕ`, `(p n : ℝ≥0)⁻¹` is negligible if and only if `p` is
eventually zero. -/
theorem negligible_inv_iff {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ≥0)⁻¹) ↔ ∀ᶠ n in atTop, p n = 0 := by
  rw [(PolynomiallyBoundedNNReal.natCast hp).negligible_inv_iff]
  simp only [Nat.cast_eq_zero]

end Cslib.PolynomiallyBounded
