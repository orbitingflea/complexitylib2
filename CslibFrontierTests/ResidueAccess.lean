/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Primality
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.BoundedSearch
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueAccess
public import CslibFrontier.Foundations.NumberTheory.DyadicResidues
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! Checked ordinary-module uses of implicit negative integers, interval quantification,
first-event selection, total primality and natural dyadic arithmetic. -/

public section

namespace CslibFrontierTests.ResidueAccess

open Cslib Cslib.Complexity Turing.MultiTapeTM

example : primeTest 0 = false := by decide
example : primeTest 1 = false := by decide
example : primeTest 2 = true := by decide
example : primeTest 9 = false := by decide
example : primeTest 17 = true := by decide

/-- The interface admits every positive modulus for the fixed negative integer minus one. -/
def minusOneAccess : IntegerResidueAccess (fun _ : List Bool => (-1 : ℤ)) where
  magnitudeExponent := fun _ => 0
  admissible := fun _ p => 0 < p
  modulus_pos := fun _ _ hp => hp
  residue := fun (_, p) => ((-1 : ℤ) % p).toNat
  magnitude_le := fun _ => by decide
  residue_eq := fun _ _ _ => rfl

example : minusOneAccess.InCountingFunction 0 encBits := by
  constructor
  · exact ComputableInPolyTime.const 0
  · apply CountingFunction.of_polyTime
    exact ComputableInPolyTime.intBin_emodNat' (.const (-1)) (.snd _ _)

example : minusOneAccess.residue ([], 5) = 4 := by decide
example : minusOneAccess.residue ([], 1) = 0 := by decide
example : (minusOneAccess.residue ([], 5) : ℤ) ≡ -1 [ZMOD 5] :=
  minusOneAccess.residue_modEq (by change 0 < 5; decide)

example : firstEventTest (fun p : Unit × ℕ => decide (p.2 = 2 ∨ p.2 = 5))
    (fun p => decide (p.2 < 3)) (fun _ => 6) () = true := by
  rw [firstEventTest_eq_true_iff]
  refine ⟨2, by decide, by decide, by decide, ?_⟩
  intro j hj
  simp only [decide_eq_false_iff_not]
  omega

/-- A later matching event cannot replace the first event. -/
example : firstEventTest (fun p : Unit × ℕ => decide (p.2 = 2 ∨ p.2 = 5))
    (fun p => decide (3 < p.2)) (fun _ => 6) () ≠ true := by
  intro h
  obtain ⟨i, hi, hevent, htest, hprev⟩ :=
    (firstEventTest_eq_true_iff _ _ _ _).mp h
  simp only [decide_eq_true_eq] at hevent htest
  have hi5 : i = 5 := by omega
  have htwo := hprev 2 (by omega)
  contradiction

example : firstEventTest (fun _ : Unit × ℕ => true) (fun _ => true)
    (fun _ => 0) () ≠ true := by
  intro h
  obtain ⟨i, hi, _⟩ := (firstEventTest_eq_true_iff _ _ _ _).mp h
  omega

example (a : ℕ) :
    firstEventTest (fun p : List Bool × ℕ => decide (p.2 < BitString.binaryValue p.1))
      (fun _ => true) (fun w => BitString.binaryValue w + 1) ∈
        CountingFunction (a + 2) encBits encBool := by
  apply firstEventTest_mem_CountingFunction Decoder.bits
  · exact CountingFunction.of_polyTime (by fun_prop)
  · exact CountingFunction.of_polyTime (ComputableInPolyTime.const true)
  · exact ComputableInPolyTime.binary_add' (by fun_prop) (.const 1)

example : dyadicResidueNumerator {5, 7} 8 (fun _ => 3) = 6 := by decide

example : crtCircleApprox (fun p : ({5, 7} : Finset ℕ) => (p : ℕ)) 8
    (fun _ => 3) = 3 / 128 := by
  have h := dyadicResidueNumerator_eq ({5, 7} : Finset ℕ) 8 (fun _ => 3)
  norm_num [dyadicResidueNumerator] at h
  exact h.symm

end CslibFrontierTests.ResidueAccess
