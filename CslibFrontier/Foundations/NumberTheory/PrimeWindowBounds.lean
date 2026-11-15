/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (general mathematics, intended for Mathlib)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Nat.BinarySize
public import CslibFrontier.Foundations.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit prime products above an excluded cutoff

The existing elementary prime-count estimate suffices at the exact manuscript cutoff
`Y = 2 * Z ^ 4`, `16 ≤ Z`: first obtain `4 * Z` primes at most `Y`, and then remove the at most
`Z` primes at most the excluded cutoff. Every remaining prime contributes a factor at least two.
This uses `Nat.le_card_primesLE_mul_log`, whose original source credit remains in PrimeCounting.
The general window lemmas apply to any cutoffs. The later corollaries give the exact cutoff
and binary-width estimates used in Proposition 2.6 (“Sign from residues”, Section 2) of
*Existential–universal real sentences in the counting hierarchy*, manuscript revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These are numerical corollaries of the existing
counting bound, using a different proof from the manuscript's binomial argument.
They do not assert the proposition's computational sign-recovery conclusion.
The width bounds concern ordinary binary lengths, without asserting computational certificates.

## Main results

* `Nat.sub_le_card_primesLE_sdiff_of_mul_log_le`: a prime-window cardinality bound.
* `Nat.two_pow_card_le_prod_primesLE_sdiff`, `Nat.prod_primesLE_sdiff_le_two_pow`:
  lower and upper product bounds for arbitrary windows.
* `Nat.three_mul_le_card_primesLE_sdiff`, `Nat.six_mul_two_pow_lt_prod_primesLE_sdiff`:
  enough primes and a sufficiently large product at the cutoff `2 * Z ^ 4`.
* `Nat.size_two_mul_pow_four_le`, `Nat.size_prime_window_doubling_index_le`:
  explicit binary-width bounds for the cutoff and doubling indices.
-/

public section

open Finset

namespace Nat

/-- Membership in a prime window is exactly primality and its two range tests. -/
theorem mem_primesLE_sdiff_primesLE_iff {p Y L : ℕ} :
    p ∈ Nat.primesLE Y \ Nat.primesLE L ↔ p.Prime ∧ L < p ∧ p ≤ Y := by
  by_cases hp : p.Prime <;> simp [Finset.mem_sdiff, Nat.mem_primesLE, hp, and_comm]

/-- Removing the primes at most `L` loses at most `L` of an explicit prime-count lower bound. -/
theorem sub_le_card_primesLE_sdiff_of_mul_log_le {w Y L : ℕ}
    (hY : (w + 1) * (2 * Nat.log 2 (w + 1) + 4) ≤ Y) :
    w - L ≤ #(Nat.primesLE Y \ Nat.primesLE L) := by
  have hcount := (Nat.le_card_primesLE_mul_log w).trans
    (Finset.card_le_card (Nat.primesLE_mono hY))
  have hsmall := Nat.card_primesLE_le L
  have hsplit := Finset.card_le_card_sdiff_add_card
    (s := Nat.primesLE Y) (t := Nat.primesLE L)
  omega

/-- Each prime in a window contributes a factor at least two, including the empty window. -/
theorem two_pow_card_le_prod_primesLE_sdiff (Y L : ℕ) :
    2 ^ #(Nat.primesLE Y \ Nat.primesLE L) ≤
      ∏ p ∈ Nat.primesLE Y \ Nat.primesLE L, p :=
  Finset.pow_card_le_prod _ _ _ fun _ hp =>
    Nat.two_le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1

/-- The upper prime-product bound in the manuscript, with binary length `Nat.size`. -/
theorem prod_primesLE_sdiff_le_two_pow (Y L : ℕ) :
    (∏ p ∈ Nat.primesLE Y \ Nat.primesLE L, p) ≤ 2 ^ (Y * Y.size) := by
  have hcard : #(Nat.primesLE Y \ Nat.primesLE L) ≤ Y :=
    (Finset.card_le_card Finset.sdiff_subset).trans (Nat.card_primesLE_le Y)
  calc
    (∏ p ∈ Nat.primesLE Y \ Nat.primesLE L, p)
        ≤ (2 ^ Y.size) ^ #(Nat.primesLE Y \ Nat.primesLE L) :=
      Finset.prod_le_pow_card _ _ _ fun p hp =>
        (Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).trans (Nat.lt_size_self Y).le
    _ ≤ (2 ^ Y.size) ^ Y := Nat.pow_le_pow_right (by positivity) hcard
    _ = 2 ^ (Y * Y.size) := by rw [← pow_mul, Nat.mul_comm Y.size Y]

/-- The existing elementary prime-count cutoff for `4Z` lies below `2Z⁴` when `Z ≥ 16`. -/
theorem four_mul_prime_count_cutoff_le {Z : ℕ} (hZ : 16 ≤ Z) :
    (4 * Z + 1) * (2 * Nat.log 2 (4 * Z + 1) + 4) ≤ 2 * Z ^ 4 := by
  have hfirst : 4 * Z + 1 ≤ 5 * Z := by omega
  have hsecond : 2 * Nat.log 2 (4 * Z + 1) + 4 ≤ 10 * Z := by
    have := Nat.log_le_self 2 (4 * Z + 1)
    omega
  have hsquare : 25 ≤ Z ^ 2 := by nlinarith
  calc
    (4 * Z + 1) * (2 * Nat.log 2 (4 * Z + 1) + 4)
        ≤ (5 * Z) * (10 * Z) := Nat.mul_le_mul hfirst hsecond
    _ = (2 * 25) * Z ^ 2 := by ring
    _ ≤ (2 * Z ^ 2) * Z ^ 2 :=
      Nat.mul_le_mul_right (Z ^ 2) (Nat.mul_le_mul_left 2 hsquare)
    _ = 2 * Z ^ 4 := by ring

/-- There are at least `4Z` primes at most the manuscript's prime cutoff. -/
theorem four_mul_le_card_primesLE_two_mul_pow_four {Z : ℕ} (hZ : 16 ≤ Z) :
    4 * Z ≤ #(Nat.primesLE (2 * Z ^ 4)) :=
  (Nat.le_card_primesLE_mul_log (4 * Z)).trans
    (Finset.card_le_card (Nat.primesLE_mono (four_mul_prime_count_cutoff_le hZ)))

/-- Excluding all primes at most any `L ≤ Z` leaves at least `3Z` primes. -/
theorem three_mul_le_card_primesLE_sdiff {Z L : ℕ} (hZ : 16 ≤ Z) (hL : L ≤ Z) :
    3 * Z ≤ #(Nat.primesLE (2 * Z ^ 4) \ Nat.primesLE L) := by
  have := sub_le_card_primesLE_sdiff_of_mul_log_le (L := L)
    (four_mul_prime_count_cutoff_le hZ)
  omega

/-- The product of primes `L < p ≤ 2Z⁴` is at least `2^(3Z)` for `L ≤ Z` and `Z ≥ 16`. -/
theorem two_pow_three_mul_le_prod_primesLE_sdiff {Z L : ℕ}
    (hZ : 16 ≤ Z) (hL : L ≤ Z) :
    2 ^ (3 * Z) ≤ ∏ p ∈ Nat.primesLE (2 * Z ^ 4) \ Nat.primesLE L, p := by
  calc
    2 ^ (3 * Z) ≤ 2 ^ #(Nat.primesLE (2 * Z ^ 4) \ Nat.primesLE L) :=
      Nat.pow_le_pow_right (by decide) (three_mul_le_card_primesLE_sdiff hZ hL)
    _ ≤ ∏ p ∈ Nat.primesLE (2 * Z ^ 4) \ Nat.primesLE L, p :=
      two_pow_card_le_prod_primesLE_sdiff _ _

/-- For `m ≤ Z`, the prime product exceeds six times the maximum allowed integer magnitude. -/
theorem six_mul_two_pow_lt_prod_primesLE_sdiff {Z L m : ℕ}
    (hZ : 16 ≤ Z) (hL : L ≤ Z) (hm : m ≤ Z) :
    6 * 2 ^ m < ∏ p ∈ Nat.primesLE (2 * Z ^ 4) \ Nat.primesLE L, p := by
  calc
    6 * 2 ^ m < 8 * 2 ^ m :=
      Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
    _ = 2 ^ (m + 3) := by rw [pow_add]; norm_num; ring
    _ ≤ 2 ^ (3 * Z) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ ∏ p ∈ Nat.primesLE (2 * Z ^ 4) \ Nat.primesLE L, p :=
      two_pow_three_mul_le_prod_primesLE_sdiff hZ hL

/-- `2Z⁴` has binary length at most `4 size Z + 3`, using only existing size arithmetic. -/
theorem size_two_mul_pow_four_le (Z : ℕ) :
    (2 * Z ^ 4).size ≤ 4 * Z.size + 3 := by
  have hmul := Nat.size_mul_le 2 (Z ^ 4)
  have hpow := Nat.size_pow_le Z 4
  have htwo : Nat.size 2 = 2 := by decide
  omega

/-- The sign-recovery prime cutoff has binary length linear in the lengths of its input bounds. -/
theorem size_sign_prime_cutoff_le (m L : ℕ) :
    (2 * (max 16 (max m L)) ^ 4).size ≤ 4 * max 5 (max m.size L.size) + 3 := by
  have hmono : Monotone Nat.size := fun _ _ h => Nat.size_le_size h
  have hmax : (max 16 (max m L)).size = max 5 (max m.size L.size) := by
    rw [hmono.map_max, hmono.map_max]
    rfl
  simpa only [hmax] using size_two_mul_pow_four_le (max 16 (max m L))

/-- The doubling range has binary width linear in the width of `Z`. -/
theorem size_prime_window_doubling_index_le {Z k : ℕ}
    (hk : k ≤ (2 * Z ^ 4) * (2 * Z ^ 4).size + 1) :
    k.size ≤ 8 * Z.size + 8 := by
  have := size_mul_size_add_one_le hk
  have := size_two_mul_pow_four_le Z
  omega

/-- The dyadic precision exponent itself is linear in the binary width of `Z`. -/
theorem prime_window_precision_le (Z : ℕ) :
    (2 * Z ^ 4).size + 10 ≤ 4 * Z.size + 13 := by
  have := size_two_mul_pow_four_le Z
  omega

/-- The precision exponent also has an explicit binary-width bound. -/
theorem size_prime_window_precision_le (Z : ℕ) :
    ((2 * Z ^ 4).size + 10).size ≤ 4 * Z.size + 8 := by
  have := Nat.size_add_le (2 * Z ^ 4).size 10
  have := Nat.size_le_self (2 * Z ^ 4).size
  have := size_two_mul_pow_four_le Z
  have : Nat.size 10 = 4 := by decide
  omega

/-- The width allowance `2 * Y.size + 11` for a rounded sum is linear in `Z.size`. -/
theorem prime_window_sum_width_le (Z : ℕ) :
    2 * (2 * Z ^ 4).size + 11 ≤ 8 * Z.size + 17 := by
  have := size_two_mul_pow_four_le Z
  omega

end Nat
