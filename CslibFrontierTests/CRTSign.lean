/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Foundations.NumberTheory.CRTSign
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# CRT sign recovery through ordinary imports

The coprime moduli `5, 7` give product `35`. Precision eight suffices for both signs of
one with cutoff three, flag margin `1/8`, threshold `1/6`, and error `1/64`.
The examples exercise the residue operation, CRT identity, zero, rounding of negative
fractions, wrapping near zero, and the first-flag theorem with all numerical conditions.
-/

namespace CslibFrontierTests.CRTSign

open Cslib Finset

/-- A concrete coprime modulus family with product 35. -/
@[expose] public def moduli : Fin 2 → ℤ := ![5, 7]

private theorem moduli_pos (i : Fin 2) : 0 < moduli i := by
  fin_cases i <;> norm_num [moduli]

private theorem moduli_coprime : Pairwise fun i j => IsCoprime (moduli i) (moduli j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [moduli, Int.isCoprime_iff_gcd_eq_one] at *

private theorem cofactor_inverse (i : Fin 2) : crtCofactor moduli i * 3 ≡ 1 [ZMOD moduli i] := by
  fin_cases i
  · norm_num [crtCofactor, show (univ : Finset (Fin 2)).erase 0 = {1} by decide,
      moduli, Int.ModEq]
  · norm_num [crtCofactor, show (univ : Finset (Fin 2)).erase 1 = {0} by decide,
      moduli, Int.ModEq]

/-- Weighted residues of the integer after `k` doublings, using the inverse 3. -/
@[expose] public def coefficients (X : ℤ) (k : ℕ) (i : Fin 2) : ℤ :=
  crtCoefficient (moduli i) 3 ((2 : ℤ) ^ k * X)

private theorem coefficients_modEq (X : ℤ) (k : ℕ) (i : Fin 2) :
    coefficients X k i * crtCofactor moduli i ≡ (2 : ℤ) ^ k * X [ZMOD moduli i] :=
  crtCoefficient_modEq _ _ _ _ (cofactor_inverse i)

-- The small residue data for +1 and -1 are different canonical representatives.
example : coefficients 1 0 = ![3, 3] := by
  funext i
  fin_cases i <;> norm_num [coefficients, crtCoefficient, moduli]

example : coefficients (-1) 0 = ![2, 4] := by
  funext i
  fin_cases i <;> norm_num [coefficients, crtCoefficient, moduli]

-- A concrete CRT circle identity, rather than exact reconstruction of a large integer.
example : ∃ z : ℤ, (∑ i : Fin 2, (coefficients (-1) 0 i : ℚ) / moduli i) -
    (-1 : ℚ) / (∏ i : Fin 2, moduli i : ℤ) = z := by
  apply crt_circle_identity moduli (coefficients (-1) 0) (-1) moduli_pos moduli_coprime
  simpa using coefficients_modEq (-1) 0

-- The rounding operation also accepts negative summands directly.
example : dyadicCircleApprox 3 (fun _ : Fin 1 => (-1 / 3 : ℚ)) = 5 / 8 := by
  norm_num [dyadicCircleApprox, dyadicSumNumerator, Fin.sum_univ_succ]

example : CircleClose (1 / 7) (dyadicCircleApprox 3 (fun _ : Fin 1 => (-1 / 3 : ℚ)))
    (-1 / 3) := by
  apply dyadicCircleApprox_close
  · refine ⟨0, ?_⟩
    norm_num [Fin.sum_univ_succ]
  · norm_num

-- Error equal to one grid unit would not follow from a strict precision hypothesis.
example : ¬ ((Fintype.card (Fin 1) : ℚ) / 2 ^ 3 < 1 / 8) := by norm_num

-- A circular approximation can wrap across zero. The flag margin excludes that point.
example : CircleClose (1 / 64) (127 / 128) (1 / 256) := by
  refine ⟨1, ?_⟩
  norm_num

example : ¬ CircleFlag (1 / 8) (127 / 128) := by norm_num [CircleFlag]

example : ∀ k, ¬ CircleFlag (1 / 8) (crtCircleApprox moduli 8 (coefficients 0 k)) := by
  intro k
  apply crtCircleApprox_not_flag_zero moduli _ 8 (ε := 1 / 64)
    moduli_pos moduli_coprime
  · simpa using coefficients_modEq 0 k
  · norm_num
  · norm_num

-- The generic theorem is instantiated with every numerical and modular premise discharged.
/-- The mathematical integer-sign contract holds for both signs of one. -/
public theorem sign_correct (X : ℤ) (hX : X = 1 ∨ X = -1) :
    ∃ k ≤ 3, FirstCircleFlag (1 / 8)
      (fun j => crtCircleApprox moduli 8 (coefficients X j)) k ∧
      (0 < X ↔ crtCircleApprox moduli 8 (coefficients X k) < 1 / 2) ∧
      (X < 0 ↔ 1 / 2 < crtCircleApprox moduli 8 (coefficients X k)) := by
  apply crt_firstCircleFlag_sign moduli (coefficients X) X 8 3
    (a := 1 / 6) (ε := 1 / 64) moduli_pos moduli_coprime
  · intro k _ i
    exact coefficients_modEq X k i
  · rcases hX with rfl | rfl <;> norm_num
  · rcases hX with rfl | rfl <;> norm_num [moduli, Fin.prod_univ_succ]
  · norm_num [moduli, Fin.prod_univ_succ]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

example : ∃ k ≤ 3, FirstCircleFlag (1 / 8)
    (fun j => crtCircleApprox moduli 8 (coefficients 1 j)) k ∧
    crtCircleApprox moduli 8 (coefficients 1 k) < 1 / 2 := by
  obtain ⟨k, hk, hf, hs, _⟩ := sign_correct 1 (Or.inl rfl)
  exact ⟨k, hk, hf, hs.mp (by norm_num)⟩

example : ∃ k ≤ 3, FirstCircleFlag (1 / 8)
    (fun j => crtCircleApprox moduli 8 (coefficients (-1) j)) k ∧
    1 / 2 < crtCircleApprox moduli 8 (coefficients (-1) k) := by
  obtain ⟨k, hk, hf, _, hs⟩ := sign_correct (-1) (Or.inr rfl)
  exact ⟨k, hk, hf, hs.mp (by norm_num)⟩

-- The actual first flag in the positive instance is index three, with dyadic value 57/256.
example : FirstCircleFlag (1 / 8)
    (fun j => crtCircleApprox moduli 8 (coefficients 1 j)) 3 := by
  constructor
  · norm_num [CircleFlag, crtCircleApprox, dyadicCircleApprox, dyadicSumNumerator,
      coefficients, crtCoefficient, moduli, Fin.sum_univ_succ]
  · intro j hj
    interval_cases j <;>
      norm_num [CircleFlag, crtCircleApprox, dyadicCircleApprox, dyadicSumNumerator,
        coefficients, crtCoefficient, moduli, Fin.sum_univ_succ]

example : crtCircleApprox moduli 8 (coefficients 1 3) = 57 / 256 := by
  norm_num [crtCircleApprox, dyadicCircleApprox, dyadicSumNumerator,
    coefficients, crtCoefficient, moduli, Fin.sum_univ_succ]

-- The rounding API also handles an empty family at precision zero.
example : dyadicCircleApprox 0 (fun i : Fin 0 => Fin.elim0 i) = 0 := by
  norm_num [dyadicCircleApprox, dyadicSumNumerator]

end CslibFrontierTests.CRTSign
