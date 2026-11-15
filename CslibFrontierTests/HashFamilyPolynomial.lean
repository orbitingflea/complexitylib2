/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Probability.HashFamily.Polynomial
public import Mathlib.Algebra.Field.ZMod

/-!
# Fixed-length polynomial hash clients

These ordinary-module clients exercise the public coefficient-order bridges, a nonvacuous
restricted seed-space bound, the empty vector, and the full-field specialization.
-/

public section

namespace CslibFrontierTests.HashFamilyPolynomial

open Cslib Cslib.Probability
open scoped ENNReal

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def finThreeToZModFive : Fin 3 ↪ ZMod 5 := Fin.castLEEmb (by decide : 3 ≤ 5)

private def restrictedX : Fin 2 → ZMod 5 := ![1, 0]

private def restrictedY : Fin 2 → ZMod 5 := ![0, 0]

/-- The two distinct messages collide at exactly the embedded point zero. -/
example :
    restrictedX ≠ restrictedY ∧
    (Finset.univ.filter fun s : Fin 3 =>
      coeffPolyHash (finThreeToZModFive s) restrictedX =
        coeffPolyHash (finThreeToZModFive s) restrictedY).card = 1 := by
  decide

/-- Source-order Horner evaluation agrees with both existing polynomial-evaluation APIs. -/
example :
    coeffPolyHash (3 : ZMod 5) restrictedX =
        polynomialHash (restrictedX ∘ Fin.rev) 3 ∧
      polyHash (3 : ZMod 5) (List.ofFn restrictedX) =
        3 ^ 2 + coeffPolyHash 3 restrictedX :=
  ⟨coeffPolyHash_eq_polynomialHash_rev 3 restrictedX, polyHash_ofFn_eq 3 restrictedX⟩

/-- The three-point embedding gives the nontrivial theorem bound `2 / 3 < 1`. -/
example :
    IsUniversalHash (PMF.uniformOfFintype (Fin 3))
        (fun s (x : Fin 2 → ZMod 5) => coeffPolyHash (finThreeToZModFive s) x) (2 / 3) ∧
      (2 / 3 : ℝ≥0∞) < 1 := by
  constructor
  · simpa using isUniversalHash_coeffPolyHash_of_embedding finThreeToZModFive 2
  · rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    norm_num

/-- The empty coefficient vector evaluates to zero. -/
example (k : ZMod 5) (x : Fin 0 → ZMod 5) : coeffPolyHash k x = 0 := by
  simp [coeffPolyHash]

/-- Sampling the point from all of `ZMod 5` gives the full-field specialization. -/
example :
    IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
      (fun k (x : Fin 2 → ZMod 5) => coeffPolyHash k x)
      (2 / Fintype.card (ZMod 5)) :=
  isUniversalHash_coeffPolyHash 2

end CslibFrontierTests.HashFamilyPolynomial
