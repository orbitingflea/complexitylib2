/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.DyadicCircle
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Chinese remaindering on the rational circle

For pairwise coprime positive integer moduli, normalized CRT coefficients sum to the
represented integer divided by the product, modulo one. The product is a mathematical
quantity in the correctness proof. The rounding operation only receives the coefficient
fractions and its precision, and never constructs the represented integer or product.

This generalizes the mathematical CRT and rounding steps of Section 2 of
[OpenAI2026CountingHierarchy]. Moduli need not be prime. The local inverse congruences
are an access interface for modular arithmetic; the circle identity is proved here.

## Main definitions

* `Cslib.crtCofactor`: the product omitting one modulus.
* `Cslib.crtCoefficient`: the canonical coefficient from a supplied modular inverse.

## Main results

* `Cslib.crt_circle_identity`: the CRT identity modulo one.
* `Cslib.crt_dyadicCircleApprox_close`: its dyadic approximation error.

## References

* [OpenAI2026CountingHierarchy], Section 2, equations `crt-circle-identity` and `crt-circle-error`.
-/

public section

namespace Cslib

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mathematical CRT cofactor, the product of all moduli except at index `i`. -/
@[expose] def crtCofactor (m : ι → ℤ) (i : ι) : ℤ := ∏ j ∈ univ.erase i, m j

/-- Multiplying the omitted modulus back into its cofactor recovers the full product. -/
theorem mul_crtCofactor (m : ι → ℤ) (i : ι) : m i * crtCofactor m i = ∏ j, m j := by
  exact mul_prod_erase _ _ (mem_univ i)

/-- Canonical CRT coefficient. The argument `u` is an inverse of the cofactor modulo `m`;
its computation is deliberately separate from this residue operation. -/
@[expose] def crtCoefficient (m u n : ℤ) : ℤ := (n * u) % m

/-- CRT coefficients lie in the canonical residue interval for positive moduli. -/
theorem crtCoefficient_mem {m : ℤ} (hm : 0 < m) (u n : ℤ) :
    0 ≤ crtCoefficient m u n ∧ crtCoefficient m u n < m :=
  ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩

/-- A supplied modular inverse yields the local CRT congruence for the coefficient. -/
theorem crtCoefficient_modEq (m u n a : ℤ) (hu : a * u ≡ 1 [ZMOD m]) :
    crtCoefficient m u n * a ≡ n [ZMOD m] := by
  calc
    crtCoefficient m u n * a ≡ (n * u) * a [ZMOD m] :=
      (Int.mod_modEq _ _).mul_right a
    _ ≡ n * 1 [ZMOD m] := by
      convert hu.mul_left n using 1; ring
    _ = n := mul_one n

/-- CRT circle identity for arbitrary pairwise coprime positive integer moduli.
Only the individual coefficient congruences are supplied; divisibility by the entire
product and the identity modulo one are conclusions of the proof. -/
theorem crt_circle_identity (m c : ι → ℤ) (n : ℤ)
    (hm : ∀ i, 0 < m i) (hcop : Pairwise fun i j => IsCoprime (m i) (m j))
    (hc : ∀ i, c i * crtCofactor m i ≡ n [ZMOD m i]) :
    ∃ z : ℤ, (∑ i, (c i : ℚ) / m i) - (n : ℚ) / (∏ i, m i : ℤ) = z := by
  let T : ℤ := ∑ i, c i * crtCofactor m i
  have hdiv : (∏ i, m i) ∣ T - n := by
    apply Fintype.prod_dvd_of_coprime hcop
    intro i
    have heq : T - n = (∑ j ∈ univ.erase i, c j * crtCofactor m j) +
        (c i * crtCofactor m i - n) := by
      dsimp only [T]
      rw [← sum_erase_add _ _ (mem_univ i)]
      ring
    rw [heq]
    apply dvd_add
    · apply dvd_sum
      intro j hj
      apply dvd_mul_of_dvd_right
      exact dvd_prod_of_mem m (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, mem_univ i⟩)
    · exact (hc i).symm.dvd
  obtain ⟨z, hz⟩ := hdiv
  have hP : (∏ i, m i : ℤ) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => (hm i).ne'
  have hsum : (∑ i, (c i : ℚ) / m i) = (T : ℚ) / (∏ i, m i : ℤ) := by
    simp only [T, Int.cast_sum, Int.cast_mul, sum_div]
    apply sum_congr rfl
    intro i _
    rw [← mul_crtCofactor m i, Int.cast_mul]
    have hi : (m i : ℚ) ≠ 0 := by exact_mod_cast (hm i).ne'
    have hco : (crtCofactor m i : ℚ) ≠ 0 := by
      have := mul_crtCofactor m i
      exact_mod_cast (right_ne_zero_of_mul (this ▸ hP))
    field_simp
  refine ⟨z, ?_⟩
  rw [hsum, ← sub_div]
  have hzq : (T : ℚ) - n = (∏ i, m i : ℤ) * (z : ℚ) := by exact_mod_cast hz
  rw [hzq, mul_div_cancel_left₀ _ (by exact_mod_cast hP)]

/-- Dyadic rounding of normalized CRT coefficients approximates the represented integer
modulo the product, for every sign of the integer. The precision condition is explicit. -/
theorem crt_dyadicCircleApprox_close (m c : ι → ℤ) (n : ℤ) (B : ℕ)
    (hm : ∀ i, 0 < m i) (hcop : Pairwise fun i j => IsCoprime (m i) (m j))
    (hc : ∀ i, c i * crtCofactor m i ≡ n [ZMOD m i]) {ε : ℚ}
    (hε : Fintype.card ι / (2 : ℚ) ^ B < ε) :
    CircleClose ε (dyadicCircleApprox B fun i => (c i : ℚ) / m i)
      ((n : ℚ) / (∏ i, m i : ℤ)) :=
  dyadicCircleApprox_close B _ (crt_circle_identity m c n hm hcop hc) hε

end Cslib
