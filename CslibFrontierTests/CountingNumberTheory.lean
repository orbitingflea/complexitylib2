/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.DiscreteLog
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Generator

/-! Ordinary-module clients of binary interval sums and total prime-field arithmetic. -/

public section

open Cslib Cslib.Complexity Turing.MultiTapeTM

example : generatorTest (2, 1) = true := by
  rw [generatorTest_eq_true_iff]
  exact ⟨by decide, by decide, by decide, IsPrimitiveRoot.one⟩

example : generatorTest (0, 1) ≠ true :=
  generatorTest_ne_true_of_not_prime (by decide)

example : generatorTest (4, 2) ≠ true :=
  generatorTest_ne_true_of_not_prime (by decide)

example : generatorTest (5, 5) ≠ true := by
  intro h
  have := (generatorTest_eq_true_iff 5 5).mp h
  omega

example : modularLogSum 5 2 3 = 3 := by decide
example : modularLogSum 5 2 0 = 0 := by decide
example : modularLogSum 2 1 1 = 0 := by decide
example : modularLogSum 1 7 9 = 0 := by decide
example : modularLogSum 0 7 9 = 0 := by decide

/-- A variable binary interval has an exponentially large possible endpoint. -/
example (a : ℕ) :
    (fun n => ∑ i ∈ Finset.range n, i) ∈ CountingFunction (a + 1) encNat encNat :=
  CountingFunction.sum_range Decoder.nat
    (CountingFunction.of_polyTime (ComputableInPolyTime.snd _ _)) ComputableInPolyTime.id'

example : (∑ i ∈ Finset.range 5, i) = 10 := by decide
example : (∑ i ∈ Finset.range 0, i) = 0 := by decide

/-- Binary modular exponentiation accepts a binary exponent without constructing the full power. -/
example (a : ℕ) :
    (fun (p, g, e) => powMod p g e) ∈ CountingFunction a encNat3 encNat :=
  CountingFunction.powMod (CountingFunction.of_polyTime (by fun_prop))
    (CountingFunction.of_polyTime (by fun_prop)) (CountingFunction.of_polyTime (by fun_prop))

example : powMod 0 2 1000 = 1 := by decide
example : powMod 5 2 20 = 1 := by decide
