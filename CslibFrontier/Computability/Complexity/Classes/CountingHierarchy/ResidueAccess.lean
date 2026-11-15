/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv

/-!
# Computational access to implicitly represented integers

An integer family is a specification parameter, not a machine input. Its access interface
supplies a logarithmic magnitude bound, admissible positive moduli, and canonical residues.
Efficiency is stated separately for the bound and the single uniform residue evaluator.
The magnitude exponent is binary and can itself have exponential value. No encoding or
computation of the represented integer is required.

This interface does not fix a prime window, a precision, or a hierarchy increment. Those
belong to sign-recovery theorems using the interface.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Residue access to a bounded integer family. The represented integer occurs only in the
specification fields; the evaluator receives an instance and one binary modulus. -/
structure IntegerResidueAccess {α : Type} (X : α → ℤ) where
  /-- A logarithmic magnitude bound, represented in binary by efficiency certificates. -/
  magnitudeExponent : α → ℕ
  /-- Moduli on which the evaluator is required to return a correct canonical residue. -/
  admissible : α → ℕ → Prop
  /-- Every admissible modulus is positive. -/
  modulus_pos : ∀ w p, admissible w p → 0 < p
  /-- One total residue evaluator, including behavior outside the admissible domain. -/
  residue : α × ℕ → ℕ
  /-- Magnitude control does not require constructing the bound as machine data. -/
  magnitude_le : ∀ w, (X w).natAbs ≤ 2 ^ magnitudeExponent w
  /-- Correct canonical residues are required exactly on the admissible domain. -/
  residue_eq : ∀ w p, admissible w p → residue (w, p) = (X w % (p : ℤ)).toNat

namespace IntegerResidueAccess

variable {α : Type} {X : α → ℤ} (R : IntegerResidueAccess X)

/-- An admissible residue has fewer than its modulus many possible values. -/
theorem residue_lt {w : α} {p : ℕ} (hp : R.admissible w p) : R.residue (w, p) < p := by
  rw [R.residue_eq w p hp]
  have hpos := R.modulus_pos w p hp
  have h := Int.emod_lt_of_pos (X w) (by omega : 0 < (p : ℤ))
  omega

/-- An admissible canonical residue represents the implicit integer modulo its modulus. -/
theorem residue_modEq {w : α} {p : ℕ} (hp : R.admissible w p) :
    (R.residue (w, p) : ℤ) ≡ X w [ZMOD (p : ℤ)] := by
  have hpos := R.modulus_pos w p hp
  rw [R.residue_eq w p hp, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega : (p : ℤ) ≠ 0))]
  exact Int.mod_modEq _ _

/-- Efficiency of the access operations: a polynomial-time binary exponent and one F_a
residue evaluator on all instance/modulus pairs, including malformed or inadmissible ones. -/
@[expose] def InCountingFunction (a : ℕ) (enc : α ↪ List Bool) : Prop :=
  ComputableInPolyTime R.magnitudeExponent enc encNat ∧
    R.residue ∈ CountingFunction a (encPair enc encNat) encNat

/-- The residue certificate supplies polynomial encoded output length even off its valid domain. -/
theorem polyBounded_residue_length {a : ℕ} {enc : α ↪ List Bool}
    (hR : R.InCountingFunction a enc) :
    PolyBounded (fun x => (encPair enc encNat x).length)
      (fun x => (encNat (R.residue x)).length) :=
  CountingFunction.polyBounded_length hR.2

end IntegerResidueAccess

end Cslib.Complexity
