/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.CRTSign
public import CslibFrontier.Foundations.NumberTheory.PrimeWindowBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# First-flag sign correctness at the manuscript's prime cutoff

For magnitude bound `m` and excluded prime bound `L`, put `Z = max 16 (max m L)` and
`Y = 2 * Z ^ 4`. The indices are exactly the primes `L < p ≤ Y`, with integer moduli `p`.
Their positivity, pairwise coprimality, product bounds and the dyadic precision estimate
discharge the numerical hypotheses of `Cslib.crt_firstCircleFlag_sign` at threshold `1/6`,
error `1/1024`, flag margin `1/8`, precision `Y.size + 10` and cutoff `Y * Y.size + 1`.

This is a mathematical step of [OpenAI2026CountingHierarchy], Section 2, Proposition 2.6
(Sign from residues). The theorems assume local weighted-coefficient congruences. They do
not compute the coefficients or prove the proposition's complexity-class bound. The represented
integer and the full prime product are used only in correctness statements and proofs.

## Main definitions

* `Cslib.PrimeWindowSign.cutoff`: the prime cutoff `2 * (max 16 (max m L)) ^ 4`.
* `Cslib.PrimeWindowSign.primes`: the primes above `L` and at most the cutoff.
* `Cslib.PrimeWindowSign.modulus`: the integer value of a prime index.

## Main results

* `Cslib.PrimeWindowSign.firstCircleFlag_sign_of_coefficients`: first-flag existence and sign
  correctness from weighted coefficients, with every numerical hypothesis discharged.
* `Cslib.PrimeWindowSign.not_flag_zero_of_coefficients`: zero has no flag.

## References

* [OpenAI2026CountingHierarchy], Section 2, proof of Sign from residues.
-/

public section

namespace Cslib.PrimeWindowSign

open Finset

/-- The prime cutoff for the magnitude bound `m` and excluded prime bound `L`. -/
@[expose] def cutoff (m L : ℕ) : ℕ := 2 * (max 16 (max m L)) ^ 4

/-- The prime window excludes `L` and includes the upper cutoff. -/
@[expose] def primes (m L : ℕ) : Finset ℕ := Nat.primesLE (cutoff m L) \ Nat.primesLE L

/-- A prime index, cast to the integer modulus required by the CRT API. -/
@[expose] def modulus (m L : ℕ) (p : primes m L) : ℤ := p.val

/-- Every index of the sign-recovery window is a prime. -/
theorem prime (m L : ℕ) (p : primes m L) : p.val.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp p.property).1

/-- Every modulus in the sign-recovery window is positive. -/
theorem modulus_pos (m L : ℕ) (p : primes m L) : 0 < modulus m L p := by
  change (0 : ℤ) < (p.val : ℤ)
  exact_mod_cast (prime m L p).pos

/-- Distinct prime indices give pairwise coprime integer moduli. -/
theorem moduli_pairwise_coprime (m L : ℕ) :
    Pairwise fun p q : primes m L => IsCoprime (modulus m L p) (modulus m L q) := by
  intro p q hpq
  exact ((Nat.coprime_primes (prime m L p) (prime m L q)).mpr
    (Subtype.coe_ne_coe.mpr hpq)).isCoprime

private theorem prod_modulus_eq (m L : ℕ) :
    (∏ p : primes m L, modulus m L p) = (∏ p ∈ primes m L, p : ℕ) := by
  change (∏ p : primes m L, (p.val : ℤ)) = (∏ p ∈ primes m L, p : ℕ)
  rw [Finset.prod_coe_sort, Nat.cast_prod]

/-- Precision `Y.size + 10` gives total rounding error strictly below `1/1024`. -/
theorem precision_error_lt (m L : ℕ) :
    (Fintype.card (primes m L) : ℚ) / (2 : ℚ) ^ ((cutoff m L).size + 10) < 1 / 1024 := by
  have hcard : #(primes m L) ≤ cutoff m L :=
    (Finset.card_le_card Finset.sdiff_subset).trans (Nat.card_primesLE_le _)
  have hlt : (#(primes m L) : ℚ) < (2 : ℚ) ^ (cutoff m L).size := by
    exact_mod_cast hcard.trans_lt (Nat.lt_size_self _)
  rw [Fintype.card_coe, div_lt_iff₀ (by positivity), pow_add]
  norm_num
  nlinarith

/-- The magnitude hypothesis implies the strict starting bound for the CRT doubling argument. -/
theorem magnitude_lt (m L : ℕ) (X : ℤ) (hX : |X| ≤ (2 : ℤ) ^ m) :
    |(X : ℚ)| < (1 / 6 : ℚ) * (∏ p : primes m L, modulus m L p : ℤ) := by
  have hZ : 16 ≤ max 16 (max m L) := le_max_left _ _
  have hm : m ≤ max 16 (max m L) := (le_max_left m L).trans (le_max_right _ _)
  have hL : L ≤ max 16 (max m L) := (le_max_right m L).trans (le_max_right _ _)
  have hprod := Nat.six_mul_two_pow_lt_prod_primesLE_sdiff hZ hL hm
  have hprodq : (6 : ℚ) * 2 ^ m < (∏ p ∈ primes m L, p : ℕ) := by
    exact_mod_cast hprod
  have hXq : |(X : ℚ)| ≤ (2 : ℚ) ^ m := by exact_mod_cast hX
  rw [prod_modulus_eq, Int.cast_natCast]
  nlinarith

/-- The manuscript doubling limit is large enough to reach the magnitude window. -/
theorem product_cutoff_le (m L : ℕ) :
    (1 / 6 : ℚ) * (∏ p : primes m L, modulus m L p : ℤ) ≤
      (2 : ℚ) ^ (cutoff m L * (cutoff m L).size + 1) := by
  have hprod := Nat.prod_primesLE_sdiff_le_two_pow (cutoff m L) L
  have hprodq : (∏ p ∈ primes m L, p : ℕ) ≤ (2 : ℚ) ^
      (cutoff m L * (cutoff m L).size) := by exact_mod_cast hprod
  rw [prod_modulus_eq, Int.cast_natCast, pow_succ]
  have hp : (0 : ℚ) ≤ (∏ p ∈ primes m L, p : ℕ) := by positivity
  nlinarith

/-- Mathematical first-flag correctness from supplied weighted coefficients.
The local congruences are the sole component-specific premise: all prime-window, magnitude,
precision and cutoff conditions are proved here. No computational bound is claimed. -/
theorem firstCircleFlag_sign_of_coefficients (m L : ℕ)
    (c : ℕ → primes m L → ℤ) (X : ℤ) (hbound : |X| ≤ (2 : ℤ) ^ m) (hX : X ≠ 0)
    (hc : ∀ k ≤ cutoff m L * (cutoff m L).size + 1, ∀ p,
      c k p * crtCofactor (modulus m L) p ≡ (2 : ℤ) ^ k * X [ZMOD modulus m L p]) :
    ∃ k ≤ cutoff m L * (cutoff m L).size + 1,
      FirstCircleFlag (1 / 8)
        (fun j => crtCircleApprox (modulus m L) ((cutoff m L).size + 10) (c j)) k ∧
      (0 < X ↔ crtCircleApprox (modulus m L) ((cutoff m L).size + 10) (c k) < 1 / 2) ∧
      (X < 0 ↔ 1 / 2 < crtCircleApprox (modulus m L) ((cutoff m L).size + 10) (c k)) := by
  apply crt_firstCircleFlag_sign (modulus m L) c X ((cutoff m L).size + 10)
    (cutoff m L * (cutoff m L).size + 1) (a := 1 / 6) (ε := 1 / 1024)
    (modulus_pos m L) (moduli_pairwise_coprime m L) hc hX (magnitude_lt m L X hbound)
    (product_cutoff_le m L) (precision_error_lt m L) <;> norm_num

/-- Any supplied coefficients representing zero yield no flag, at the manuscript precision. -/
theorem not_flag_zero_of_coefficients (m L : ℕ) (c : primes m L → ℤ)
    (hc : ∀ p, c p * crtCofactor (modulus m L) p ≡ 0 [ZMOD modulus m L p]) :
    ¬ CircleFlag (1 / 8) (crtCircleApprox (modulus m L) ((cutoff m L).size + 10) c) :=
  crtCircleApprox_not_flag_zero (modulus m L) c ((cutoff m L).size + 10)
    (modulus_pos m L) (moduli_pairwise_coprime m L) hc (precision_error_lt m L) (by norm_num)

end Cslib.PrimeWindowSign
