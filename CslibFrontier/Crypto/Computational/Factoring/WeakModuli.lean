/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
public import CslibFrontier.Crypto.Computational.RSAAttacks
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Mathlib.Data.Nat.Sqrt

/-!
# Weak RSA moduli: shared primes and close primes

Two ways in which badly generated RSA moduli `n = p * q` are factored without solving a hard
problem, after [BonehShoup2023], Section 16.4.2, pp. 698–699.

* **Shared prime.** Two moduli `p * q₁` and `p * q₂` with a common prime `p` and distinct
  primes `q₁ ≠ q₂` reveal `p` as their gcd (`gcd_mul_mul_of_prime_ne`,
  `RSADesc.gcd_modulus_eq_of_p_eq`). The book observes this for keys generated on devices that
  have little entropy when they choose `p`. The attack is `Nat.gcd`, which
  `Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd` computes in polynomial time.
* **Close primes** (Section 16.4.2.1). If `|p - q| < 2 * n ^ (1 / 4)`, the bound in which the
  chain (16.11) ends, then `A = (p + q) / 2` satisfies `|A - √n| < 1 / 2` (Lemma 16.4,
  `abs_add_div_two_sub_sqrt_mul_lt_half`). Since also `√n ≤ A`, when `p + q` is even `A` is an
  integer and therefore `A = ⌈√n⌉` (`ceilSqrt_mul_eq_add_div_two`). From `p + q = 2 * A` and
  `p * q = n` the factors follow by solving a quadratic equation, which is what `factorOfTotient`
  from `RSAAttacks.lean` does given `n + 1 - (p + q) = (p - 1) * (q - 1)`. `fermatFactor n`
  composes the two steps, and `fermatFactor_mul_eq` shows that it returns `(p, q)`. The book
  does not name this algorithm; the name `fermatFactor` is ours. It is the first step of Fermat's
  factoring method only: it tries `A = ⌈√n⌉` and does not search over larger `A`. It is
  computable in polynomial time (`computableInPolyTime_fermatFactor`), so moduli with close
  factors are factored by a polynomial-time function.

## Main definitions

* `Cslib.Crypto.fermatFactor`: the close-prime attack, `factorOfTotient n (n + 1 - 2 * ⌈√n⌉)`.

## Main results

* `Cslib.Crypto.gcd_mul_mul_of_prime_ne`, `Cslib.Crypto.RSADesc.gcd_modulus_eq_of_p_eq`: moduli
  sharing one prime factor are factored by their gcd.
* `Cslib.Crypto.abs_add_div_two_sub_sqrt_mul_lt_half`: Lemma 16.4 over `ℝ`.
* `Cslib.Crypto.abs_sub_lt_two_mul_rpow_iff`: the closeness bound `|p - q| < 2 * (p * q) ^ (1 / 4)`
  is the polynomial inequality `(p - q) ^ 4 < 16 * (p * q)`, so it can be checked by `norm_num`.
* `Cslib.Crypto.ceilSqrt_mul_eq_add_div_two`: step 1 of the attack, `⌈√(p * q)⌉ = (p + q) / 2`.
* `Cslib.Crypto.fermatFactor_mul_eq`, `Cslib.Crypto.RSADesc.fermatFactor_eq`: `fermatFactor`
  recovers the factors of a modulus with close factors.
* `Cslib.Crypto.computableInPolyTime_fermatFactor`: `fermatFactor` is computable in polynomial
  time on binary naturals.

## Implementation notes

`⌈√n⌉` is written as `if n = 0 then 0 else (n - 1).sqrt + 1`, the function on naturals that
`Turing.MultiTapeTM.ComputableInPolyTime.binary_ceilSqrt` certifies in polynomial time.
`computableInPolyTime_fermatFactor` certifies the whole of `fermatFactor`, with `factorOfTotient`
unfolded, from the polynomial-time certificates for arithmetic, the test `n = 0` and `Nat.sqrt` on
binary naturals; it does not need a separate certificate for `factorOfTotient`.

The book assumes that `p` and `q` are odd primes. The statements on naturals need only that
`p + q` is even: positivity of `p` and `q` follows from the closeness bound, and primality is not
used. `RSADesc.fermatFactor_eq` replaces evenness of `p + q` by `p ≠ 2` and `q ≠ 2`. The closeness
hypothesis and the conclusion of Lemma 16.4 are stated over `ℝ` exactly as in the book; the book
leaves the proof of Lemma 16.4 as an exercise, and the proof here uses
`(p + q) / 2 - √n = ((p - q) / 2) ^ 2 / ((p + q) / 2 + √n)` and `(p + q) / 2 ≥ √n`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 16.4.2, pp. 698–699 (shared primes on p. 698; Lemma 16.4 and the factoring algorithm
  of Section 16.4.2.1 on p. 699).
-/

public section

namespace Cslib.Crypto

/-! ### Shared primes -/

/-- **Shared prime factor** ([BonehShoup2023], Section 16.4.2, p. 698): moduli `p * q₁` and
`p * q₂` with distinct primes `q₁ ≠ q₂` have gcd `p`. The common factor `p` need not be prime.
The attack is `Nat.gcd`, which `Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd` computes in
polynomial time on binary naturals. -/
theorem gcd_mul_mul_of_prime_ne {p q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) :
    Nat.gcd (p * q₁) (p * q₂) = p := by
  rw [Nat.gcd_mul_left, (Nat.coprime_primes hq₁ hq₂).2 hne, mul_one]

/-- Two RSA moduli with the same first prime and different second primes are both factored by
their gcd ([BonehShoup2023], Section 16.4.2, p. 698), which
`Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd` computes in polynomial time. -/
theorem RSADesc.gcd_modulus_eq_of_p_eq (desc₁ desc₂ : RSADesc) (hp : desc₁.p = desc₂.p)
    (hq : desc₁.q ≠ desc₂.q) : Nat.gcd desc₁.modulus desc₂.modulus = desc₁.p := by
  rw [RSADesc.modulus, RSADesc.modulus, ← hp]
  exact gcd_mul_mul_of_prime_ne desc₁.hq desc₂.hq hq

/-! ### Close primes -/

/-- **Lemma 16.4** of [BonehShoup2023] (Section 16.4.2.1, p. 699): for positive reals `p`, `q`
with `|p - q| < 2 * (p * q) ^ (1 / 4)`, the arithmetic mean `A = (p + q) / 2` satisfies
`|A - √(p * q)| < 1 / 2`. This is the printed statement "if `|p − q| < 2n^{1/4}` then
`|A − √n| < 1/2`" with `n = p * q` substituted. The book states it for the factors of an RSA
modulus `n = p * q`; nothing beyond positivity is used. -/
theorem abs_add_div_two_sub_sqrt_mul_lt_half {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : |p - q| < 2 * (p * q) ^ (1 / 4 : ℝ)) : |(p + q) / 2 - Real.sqrt (p * q)| < 1 / 2 := by
  have hpq : 0 < p * q := mul_pos hp hq
  set s := Real.sqrt (p * q) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hpq
  have hs2 : s ^ 2 = p * q := Real.sq_sqrt hpq.le
  have ht : ((p * q) ^ (1 / 4 : ℝ)) ^ 2 = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpq.le, hs_def, Real.sqrt_eq_rpow]
    norm_num
  have hd : (p - q) ^ 2 < 4 * s := by
    have h2 := pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero
    rw [sq_abs, mul_pow, ht] at h2
    linarith
  have hA : s ≤ (p + q) / 2 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (p - q)]⟩
  exact abs_lt.2 ⟨by linarith, by nlinarith⟩

/-- The closeness bound of Lemma 16.4 and (16.11), `|p - q| < 2 * (p * q) ^ (1 / 4)`, is the
polynomial inequality `(p - q) ^ 4 < 16 * (p * q)` (for `0 ≤ p * q`). On concrete numbers the
right-hand side is decided by `norm_num`. -/
theorem abs_sub_lt_two_mul_rpow_iff {p q : ℝ} (h : 0 ≤ p * q) :
    |p - q| < 2 * (p * q) ^ (1 / 4 : ℝ) ↔ (p - q) ^ 4 < 16 * (p * q) := by
  have ht4 : ((p * q) ^ (1 / 4 : ℝ)) ^ 4 = p * q := by
    rw [one_div, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
    exact Real.rpow_inv_natCast_pow h (by norm_num)
  rw [← pow_lt_pow_iff_left₀ (abs_nonneg _) (by positivity) four_ne_zero,
    Even.pow_abs (by decide), mul_pow, ht4]
  norm_num

/-- The closeness bound forces both natural factors to be positive: when `p * q = 0` its right-hand
side is `2 * 0 ^ (1 / 4) = 0`. -/
private theorem pos_of_abs_sub_lt_two_mul_rpow {p q : ℕ}
    (hclose : |(p : ℝ) - q| < 2 * ((p : ℝ) * q) ^ (1 / 4 : ℝ)) : 0 < p ∧ 0 < q := by
  have hpq : p * q ≠ 0 := fun h0 => by
    rw [← Nat.cast_mul, h0, Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero] at hclose
    exact lt_irrefl _ ((abs_nonneg _).trans_lt hclose)
  exact (mul_ne_zero_iff.1 hpq).imp Nat.pos_of_ne_zero Nat.pos_of_ne_zero

/-- **Step 1 of the close-prime attack** ([BonehShoup2023], Section 16.4.2.1, p. 699): if
`p + q` is even and `|p - q| < 2 * (p * q) ^ (1 / 4)`, then `⌈√(p * q)⌉ = (p + q) / 2`. The
ceiling square root is written as the natural-number function
`if n = 0 then 0 else (n - 1).sqrt + 1` that `binary_ceilSqrt` certifies. The book assumes odd
primes `p`, `q`; neither primality nor oddness beyond the parity of `p + q` is needed (positivity
follows from the closeness bound), and without that parity the conclusion fails (`p = 3`,
`q = 2`). -/
theorem ceilSqrt_mul_eq_add_div_two {p q : ℕ} (hpq : Even (p + q))
    (hclose : |(p : ℝ) - q| < 2 * ((p : ℝ) * q) ^ (1 / 4 : ℝ)) :
    (if p * q = 0 then 0 else (p * q - 1).sqrt + 1) = (p + q) / 2 := by
  obtain ⟨hp, hq⟩ := pos_of_abs_sub_lt_two_mul_rpow hclose
  rw [ite_eq_right (Nat.mul_pos hp hq).ne']
  obtain ⟨A, hA⟩ : ∃ A, p + q = 2 * A := ⟨(p + q) / 2, (Nat.two_mul_div_two_of_even hpq).symm⟩
  rw [hA, Nat.mul_div_cancel_left A two_pos]
  have hA1 : 1 ≤ A := by omega
  have hAR : ((p : ℝ) + q) / 2 = A := by
    have h : ((p + q : ℕ) : ℝ) = ((2 * A : ℕ) : ℝ) := by rw [hA]
    push_cast at h
    linarith
  have hlemma := abs_add_div_two_sub_sqrt_mul_lt_half (Nat.cast_pos.2 hp) (Nat.cast_pos.2 hq) hclose
  rw [hAR] at hlemma
  replace hlemma := (abs_lt.1 hlemma).2
  have hlow : (A - 1) ^ 2 < p * q := by
    have h1 : ((A - 1 : ℕ) : ℝ) < Real.sqrt ((p : ℝ) * q) := by
      push_cast [Nat.cast_sub hA1]
      linarith
    have h2 := (Real.lt_sqrt (Nat.cast_nonneg _)).1 h1
    exact_mod_cast h2
  have hhigh : p * q ≤ A ^ 2 := by nlinarith [four_mul_le_sq_add p q]
  have hsqrt : A - 1 = (p * q - 1).sqrt := by
    refine Nat.eq_sqrt'.2 ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel hA1]
    omega
  omega

/-- The two steps of the close-prime attack of [BonehShoup2023], Section 16.4.2.1, p. 699, on a
modulus `n`: compute `A = ⌈√n⌉`, written `if n = 0 then 0 else (n - 1).sqrt + 1`, and solve
`p + q = 2 * A`, `p * q = n` with `factorOfTotient`, which receives `n + 1 - 2 * A` in the place
of `φ(n) = n + 1 - (p + q)`.

The book does not name the algorithm; the name `fermatFactor` is ours. It is a single step of
Fermat's factoring method, with no search over `A`: Fermat's method would go on to try
`A = ⌈√n⌉ + 1, ⌈√n⌉ + 2, …`, while `fermatFactor` stops at `A = ⌈√n⌉` and factors `n` only when
its factors are close (`fermatFactor_mul_eq`). -/
@[expose] def fermatFactor (n : ℕ) : ℕ × ℕ :=
  factorOfTotient n (n + 1 - 2 * (if n = 0 then 0 else (n - 1).sqrt + 1))

/-- **The close-prime attack recovers close factors** ([BonehShoup2023], Section 16.4.2.1,
p. 699): for naturals `q ≤ p` with `p + q` even and `|p - q| < 2 * (p * q) ^ (1 / 4)`,
`fermatFactor (p * q) = (p, q)`. Primality of `p` and `q` is not needed, and their positivity
follows from the closeness bound. -/
theorem fermatFactor_mul_eq {p q : ℕ} (hqp : q ≤ p) (hpq : Even (p + q))
    (hclose : |(p : ℝ) - q| < 2 * ((p : ℝ) * q) ^ (1 / 4 : ℝ)) :
    fermatFactor (p * q) = (p, q) := by
  obtain ⟨hp, hq⟩ := pos_of_abs_sub_lt_two_mul_rpow hclose
  rw [fermatFactor, ceilSqrt_mul_eq_add_div_two hpq hclose,
    Nat.two_mul_div_two_of_even hpq, ← factorOfTotient_eq hq hqp]
  congr 1
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
  rw [show (a + 1) * (b + 1) + 1 = a * b + (a + 1 + (b + 1)) by ring, Nat.add_sub_cancel,
    Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- **The close-prime attack on an RSA modulus** ([BonehShoup2023], Section 16.4.2.1,
p. 699): if both primes are odd and `|p - q| < 2 * (p * q) ^ (1 / 4)`,
`fermatFactor` returns the factorization `(max p q, min p q)`. -/
theorem RSADesc.fermatFactor_eq (desc : RSADesc) (hp : desc.p ≠ 2) (hq : desc.q ≠ 2)
    (hclose : |(desc.p : ℝ) - desc.q| < 2 * ((desc.p : ℝ) * desc.q) ^ (1 / 4 : ℝ)) :
    fermatFactor desc.modulus = (max desc.p desc.q, min desc.p desc.q) := by
  have hpq : Even (desc.p + desc.q) := (desc.hp.odd_of_ne_two hp).add_odd (desc.hq.odd_of_ne_two hq)
  rcases le_total desc.q desc.p with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact fermatFactor_mul_eq h hpq hclose
  · rw [max_eq_right h, min_eq_left h, RSADesc.modulus, mul_comm]
    rw [abs_sub_comm, mul_comm (desc.p : ℝ)] at hclose
    exact fermatFactor_mul_eq h (add_comm desc.p desc.q ▸ hpq) hclose

/-! ### Efficiency -/

open Turing.MultiTapeTM in
/-- The single Fermat step `fermatFactor` is computable in polynomial time on binary naturals.
Together with `fermatFactor_mul_eq`, a modulus with close factors is factored by a polynomial-time
function. The proof unfolds `fermatFactor` and `factorOfTotient`, and `fun_prop` composes the
certificates for arithmetic, the test `n = 0` and `Nat.sqrt` on binary naturals. -/
theorem computableInPolyTime_fermatFactor :
    ComputableInPolyTime fermatFactor encNat (encPair encNat encNat) := by
  unfold fermatFactor factorOfTotient
  fun_prop

end Cslib.Crypto
