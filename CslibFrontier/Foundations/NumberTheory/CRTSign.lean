/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.CRTCircle
public import CslibFrontier.Foundations.NumberTheory.DoublingSign
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Integer sign correctness from weighted CRT residues

`crtCircleApprox` consumes only moduli, weighted residues and a precision. The integer
being represented and the full modulus product occur only in correctness statements.
For pairwise coprime positive moduli, numerical magnitude and cutoff bounds, and sufficient
precision, `crt_firstCircleFlag_sign` proves that a nonzero integer has a first flag whose
side of one half gives its sign. `crtCircleApprox_not_flag_zero` handles zero.

This is the mathematical sign-recovery layer of Section 2 of
[OpenAI2026CountingHierarchy], used in Appendix A's sign step. The theorem is generic in
moduli and all numerical parameters. It does not establish a prime-window product bound,
certify computation of the weighted residues, or claim membership in a complexity class.

## Main definitions

* `Cslib.crtCircleApprox`: dyadic approximation from weighted residues alone.

## Main results

* `Cslib.crt_firstCircleFlag_sign`: first-flag correctness for nonzero integers.
* `Cslib.crtCircleApprox_not_flag_zero`: zero cannot be flagged.

## References

* [OpenAI2026CountingHierarchy], Section 2, proof of Sign from residues; Appendix A,
  Accounting for the oracle levels (only the mathematical sign step is formalized here).
-/

public section

namespace Cslib

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Approximate the normalized weighted CRT residue sum modulo one.
No represented integer or full product is an input to this operation. -/
@[expose] def crtCircleApprox (m : ι → ℤ) (B : ℕ) (c : ι → ℤ) : ℚ :=
  dyadicCircleApprox B fun i => (c i : ℚ) / m i

/-- A zero represented integer cannot produce a flag, for any valid weighted CRT residues. -/
theorem crtCircleApprox_not_flag_zero (m c : ι → ℤ) (B : ℕ) {ε t : ℚ}
    (hm : ∀ i, 0 < m i) (hcop : Pairwise fun i j => IsCoprime (m i) (m j))
    (hc : ∀ i, c i * crtCofactor m i ≡ 0 [ZMOD m i])
    (hprec : Fintype.card ι / (2 : ℚ) ^ B < ε) (hε : ε < t) :
    ¬ CircleFlag t (crtCircleApprox m B c) := by
  have h := crt_dyadicCircleApprox_close m c 0 B hm hcop hc hprec
  simp only [Int.cast_zero, zero_div] at h
  exact h.not_flag_zero hε

/-- Integer first-flag correctness from local weighted CRT congruences.
The magnitude bound is `|X| < a Π`, and the cutoff is `a Π ≤ 2ᴷ`; integrality of a
nonzero `X` supplies the missing lower magnitude bound. Neither `X` nor `Π` is algorithm data.
The local congruences can be supplied by `crtCoefficient_modEq` and modular multiplication. -/
theorem crt_firstCircleFlag_sign (m : ι → ℤ) (c : ℕ → ι → ℤ) (X : ℤ) (B K : ℕ)
    {a ε t : ℚ} (hm : ∀ i, 0 < m i)
    (hcop : Pairwise fun i j => IsCoprime (m i) (m j))
    (hc : ∀ k ≤ K, ∀ i, c k i * crtCofactor m i ≡ (2 : ℤ) ^ k * X [ZMOD m i])
    (hX : X ≠ 0) (hmag : |(X : ℚ)| < a * (∏ i, m i : ℤ))
    (hcut : a * (∏ i, m i : ℤ) ≤ (2 : ℚ) ^ K)
    (hprec : Fintype.card ι / (2 : ℚ) ^ B < ε)
    (ht : 0 < t) (hε : ε < t) (hlo : t + ε ≤ a) (hhi : 2 * a + ε ≤ 1 / 2) :
    ∃ k ≤ K, FirstCircleFlag t (fun j => crtCircleApprox m B (c j)) k ∧
      (0 < X ↔ crtCircleApprox m B (c k) < 1 / 2) ∧
      (X < 0 ↔ 1 / 2 < crtCircleApprox m B (c k)) := by
  have hP : (0 : ℚ) < (∏ i, m i : ℤ) := by
    exact_mod_cast prod_pos fun i _ => hm i
  let q : ℚ := (X : ℚ) / (∏ i, m i : ℤ)
  have hstart : |q| < a := by
    rw [show |q| = |(X : ℚ)| / (∏ i, m i : ℤ) by
      dsimp only [q]; rw [abs_div, abs_of_pos hP]]
    exact (div_lt_iff₀ hP).mpr hmag
  have hXunit : (1 : ℚ) ≤ |(X : ℚ)| := by
    have hi : 1 ≤ |X| := by
      have := abs_pos.mpr hX
      omega
    exact_mod_cast hi
  have hend : a ≤ |(2 : ℚ) ^ K * q| := by
    dsimp only [q]
    rw [abs_mul, abs_of_pos (pow_pos (by norm_num) K), abs_div, abs_of_pos hP,
      ← mul_div_assoc]
    apply (le_div_iff₀ hP).mpr
    exact hcut.trans (le_mul_of_one_le_right (by positivity) hXunit)
  have happrox : ∀ k ≤ K, CircleClose ε (crtCircleApprox m B (c k))
      ((2 : ℚ) ^ k * q) := by
    intro k hk
    have h := crt_dyadicCircleApprox_close m (c k) ((2 : ℤ) ^ k * X) B hm hcop
      (hc k hk) hprec
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_assoc, q,
      crtCircleApprox] using h
  obtain ⟨k, hk, hf, hs⟩ := firstCircleFlag_sign (fun j => crtCircleApprox m B (c j))
    hstart hend ht hε hlo hhi (fun j _ => dyadicCircleApprox_mem B _) happrox
  have hpos : 0 < q ↔ 0 < X := by
    dsimp only [q]
    rw [lt_div_iff₀ hP, zero_mul]
    exact Int.cast_pos
  have hneg : q < 0 ↔ X < 0 := by
    dsimp only [q]
    rw [div_lt_iff₀ hP, zero_mul]
    exact Int.cast_lt
  exact ⟨k, hk, hf, hpos.symm.trans hs.1, hneg.symm.trans hs.2⟩

end Cslib
