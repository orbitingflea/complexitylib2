/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.CRTSign

/-!
# Natural arithmetic for dyadic residue approximations

Canonical nonnegative residues permit dyadic CRT approximation using only natural
multiplication, division, summation and remainder. The bridge identifies that numerator
formula with the rational approximation used by the correctness theorem. No represented
integer or product of moduli is an input to the operation.
-/

public section

namespace Cslib

/-- The numerator of a dyadic residue sum, reduced to its precision. -/
@[expose] def dyadicResidueNumerator (s : Finset ℕ) (B : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ p ∈ s, (2 ^ B * c p) / p) % 2 ^ B

/-- Natural quotient arithmetic agrees exactly with the mathematical dyadic CRT formula. -/
theorem dyadicResidueNumerator_eq (s : Finset ℕ) (B : ℕ) (c : ℕ → ℕ) :
    (dyadicResidueNumerator s B c : ℚ) / (2 : ℚ) ^ B =
      crtCircleApprox (fun p : s => (p : ℕ)) B (fun p => (c p : ℤ)) := by
  have hfloor (p : ℕ) :
      ⌊(2 : ℚ) ^ B * ((c p : ℚ) / p)⌋ = (((2 ^ B * c p) / p : ℕ) : ℤ) := by
    calc
      _ = ⌊((2 ^ B * c p : ℕ) : ℚ) / p⌋ := by
        congr 1
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc]
      _ = _ := by rw [Rat.floor_natCast_div_natCast, Int.ofNat_ediv_ofNat]
  have hsum :
      dyadicSumNumerator B (fun p : s => (c p : ℚ) / (p : ℕ)) =
        ((∑ p ∈ s, (2 ^ B * c p) / p : ℕ) : ℤ) := by
    simp only [dyadicSumNumerator, hfloor]
    rw [Finset.sum_coe_sort s (fun p : ℕ => (((2 ^ B * c p) / p : ℕ) : ℤ)),
      Nat.cast_sum]
  simp only [crtCircleApprox, dyadicCircleApprox, Int.cast_natCast, hsum,
    dyadicResidueNumerator]
  rw [show (2 : ℤ) ^ B = ((2 ^ B : ℕ) : ℤ) by norm_cast,
    ← Int.natCast_emod, Int.cast_natCast]

end Cslib
