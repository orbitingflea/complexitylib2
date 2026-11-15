/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Computability.TreeEval.Ary.Packed.InterpolationSpace
public import CslibFrontier.Computability.TreeEval.Ary.Packed.GateInterpolationSpace

/-!
# Executable packed interpolation regressions

Three symbols over `ZMod 7` exercise non-Boolean interpolation. The basis and full two-coordinate
grid are computed through the counter procedures. The basis's native space theorem is checked
on its total binary-parameter domain, including the guarded zero-modulus cases.
-/

@[expose] public section

namespace CslibFrontierTests.TreeEvalInterpolation

open Cslib.TreeEval.Ary.Packed Turing.MultiTapeTM

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : basisWeight 7 3 1 0 = 0 := by decide
example : basisWeight 7 3 1 1 = 1 := by decide
example : basisWeight 7 3 1 2 = 0 := by decide
example : basisWeight 7 3 1 4 = 6 := by decide

/-- `cast_basisWeight` holds for `s > p` as well, both when `a` collides with another symbol modulo
`p` (so both sides vanish, including `a.val ≥ p` and `x ≥ p`) and when `a`'s residue is unique in
`0, …, s - 1`. -/
example :
    (Lagrange.basis Finset.univ (fun j : Fin 9 => (j.val : ZMod 7)) ⟨8, by decide⟩).eval
        ((10 : ℕ) : ZMod 7) = 0 ∧
      (Lagrange.basis Finset.univ (fun j : Fin 8 => (j.val : ZMod 7)) ⟨2, by decide⟩).eval
        ((9 : ℕ) : ZMod 7) = 1 := by
  rw [← cast_basisWeight, ← cast_basisWeight]
  decide

example : basisWeight 0 0 1 4 = 1 := by decide
example : basisWeight 0 3 1 4 = 0 := by decide
example : basisWeight 1 3 1 4 = 0 := by decide

/-- The alphabet counter is charged in binary, without an alphabet-cardinality space term. -/
theorem native_basis_certificate :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ × ℕ => basisWeight q.1 q.2.1 q.2.2.1 q.2.2.2)
      encBasisArgs encNat (fun q => (encBasisArgs q).length) := basisWeight_inSpace

/-- The whole coordinate product also has a total native certificate in the encoded inputs. -/
theorem native_grid_weight_certificate :
    ComputableInSpace (fun q : (ℕ × ℕ × ℕ × ℕ) × List ℕ =>
      gridWeight q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      encGridWeightArgs encNat (fun q => (encGridWeightArgs q).length) := gridWeight_inSpace

/-- A nonbinary two-variable multiplication table, addressed by base-three digits. -/
def table (k : ℕ) : ℕ := k % 3 * (k / 3 % 3)

example : gridDigit 3 5 0 = 2 ∧ gridDigit 3 5 1 = 1 := by decide
example : gridWeight 7 3 2 5 [4, 5] = 1 := by decide
example : interpolateGrid 7 3 2 table [4, 5] = 6 := by decide

/-- The empty coordinate tuple is evaluated once, rather than producing an empty sum. -/
example : interpolateGrid 7 3 0 (fun _ => 5) [] = 5 := by decide

example : interpolateGrid 0 3 2 table [4, 5] = 0 := by decide

/-- Missing coordinates use the documented zero default, with no hidden well-formedness premise. -/
example : gridWeight 7 3 2 0 [] = 1 := by decide

/-- The executable formula agrees with the library's existing extension for every table. -/
theorem executable_extension_agrees (h : Fin 3 ↪ ZMod 7)
    (hh : ∀ a, h a = (a.val : ZMod 7)) (values : ℕ → ℕ) (x : List ℕ) :
    ((interpolateGrid 7 3 2 values x : ℕ) : ZMod 7) =
      Cslib.Code.lowDegreeExtension h
        (fun a : Fin 2 → Fin 3 => (values (finFunctionFinEquiv a) : ZMod 7))
        (fun i => (x.getD i 0 : ZMod 7)) :=
  cast_interpolateGrid (by decide) h hh values x

end CslibFrontierTests.TreeEvalInterpolation
