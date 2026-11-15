/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Foundations.NumberTheory.FiniteField.GeneratorProducts
public import CslibFrontier.Foundations.NumberTheory.FiniteField.Enumeration
public import CslibFrontier.Foundations.Data.BitString.WeightedEnumeration

/-! Ordinary-module clients of finite-field products and weighted binary enumeration. -/

public section

namespace CslibFrontierTests.PrimeFieldProducts

open Cslib

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Three nonzero factors whose product modulo five is four. -/
def factors : Fin 3 → ZMod 5 := ![2, 3, 4]

example : ZMod.generatorLogSum 5 (2 : ZMod 5) 3 = 3 := by decide
example : ZMod.generatorLogSum 2 (1 : ZMod 2) 1 = 0 := by decide
example : ZMod.generatorLogSum 5 (2 : ZMod 5) 0 = 0 := by decide
example : (∏ i, factors i) = 4 := by decide

/-- The average evaluates a product without selecting a generator. -/
example :
    (∑ γ ∈ primitiveRoots 4 (ZMod 5),
      if ∃ i : Fin 3, factors i = 0 then 0
      else γ ^ ((∑ i, ZMod.generatorLogSum 5 γ (factors i)) % 4)) /
        ((primitiveRoots 4 (ZMod 5)).card : ZMod 5) = 4 := by
  have h := (ZMod.prod_eq_generator_average Finset.univ factors).symm
  simpa only [Finset.mem_univ, true_and] using h.trans (by decide)

/-- The prime two has a nonzero generator count even though its logarithms are all zero. -/
example : ((primitiveRoots 1 (ZMod 2)).card : ZMod 2) ≠ 0 :=
  ZMod.primitiveRoots_card_ne_zero

/-- Natural representatives enumerate every residue exactly once. -/
example : (∑ i ∈ Finset.range 5, (i : ZMod 5)) = ∑ x : ZMod 5, x :=
  ZMod.sum_range_natCast id

/-- A short interval can be enumerated by wider words without multiplying its weights. -/
example : (∑ w : Fin 3 → Bool,
    if BitString.binaryValue (List.ofFn w) < 5
      then (BitString.binaryValue (List.ofFn w) : ℤ) - 2 else 0) = 0 := by
  rw [BitString.sum_binaryValue_lt (by decide : 5 ≤ 2 ^ 3) (fun i => (i : ℤ) - 2)]
  decide

example : (∑ w : Fin 0 → Bool,
    if BitString.binaryValue (List.ofFn w) < 0 then (7 : ℕ) else 0) = 0 := by decide

end CslibFrontierTests.PrimeFieldProducts
