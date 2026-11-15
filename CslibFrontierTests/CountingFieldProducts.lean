/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Products
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Certified total prime-field products through ordinary imports

The factor evaluator reads its index as a binary natural and adds one. The modulus is
also read in binary, while the number of index bits is one less than the primary word's
length (with saturated subtraction). The same certified function has nonzero and zero outputs.
Concrete examples cover prime and nonprime moduli, zero factors, a width-zero domain,
noncanonical factors, restrictions, and an empty allowed domain.
-/

public section

namespace CslibFrontierTests.CountingFieldProducts

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The factor value is one plus the binary value of the supplied index word. -/
def factor (x : List Bool × List Bool) : ℕ := BitString.binaryValue x.2 + 1

private theorem factor_polyTime :
    ComputableInPolyTime factor (encPair encBits encBits) encNat := by
  unfold factor
  fun_prop

/-- A variable binary modulus and a unary polynomial width supply an F_4 product. -/
noncomputable def exampleProduct (w : List Bool) : ℕ :=
  primeFieldProduct (BitString.binaryValue w) (w.length - 1) (fun i => factor (w, i))

/-- One fixed total function and strict certificate handle every primary word and modulus. -/
theorem exampleProduct_level : exampleProduct ∈ CountingFunction 4 encBits encNat :=
  CountingFunction.prod_primeField_bits Decoder.bits
    (CountingFunction.of_polyTime factor_polyTime) (by fun_prop) (by fun_prop)

/-- Encoded output length is polynomially bounded by the strict function certificate. -/
example : PolyBounded (fun w => (encBits w).length)
    (fun w => (encNat (exampleProduct w)).length) :=
  CountingFunction.polyBounded_length exampleProduct_level

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- These are two values of the same certified function, not separate constant instances.
-- Input five has width two: factors 1,2,3,4 have product 4 modulo 5.
example : exampleProduct [true, false, true] = 4 := by
  change primeFieldProduct 5 2 (fun w => BitString.binaryValue w + 1) = 4
  rw [primeFieldProduct_eq_val]
  decide

-- Input two has width one, so its factor two gives zero in the two-element field.
example : exampleProduct [true, false] = 0 := by
  change primeFieldProduct 2 1 (fun w => BitString.binaryValue w + 1) = 0
  rw [primeFieldProduct_eq_val]
  decide

-- Width zero still has the one empty index word.
example : primeFieldProduct 2 0 (fun _ => 1) = 1 := by
  rw [primeFieldProduct_eq_val]
  decide

example : primeFieldProduct 5 0 (fun _ => 0) = 0 := by
  rw [primeFieldProduct_eq_val]
  decide

-- A factor divisible by p is zero in the field even if its natural value is nonzero.
example : primeFieldProduct 5 0 (fun _ => 5) = 0 := by
  rw [primeFieldProduct_eq_val]
  decide

-- Natural factors need not already be canonical residues: 6*7 = 2 modulo 5.
example : primeFieldProduct 5 1 (fun w => 6 + BitString.binaryValue w) = 2 := by
  rw [primeFieldProduct_eq_val]
  decide

example : primeFieldProduct 0 0 (fun _ => 1) = 0 :=
  primeFieldProduct_eq_zero_of_not_prime (by decide) _ _

example : primeFieldProduct 1 0 (fun _ => 1) = 0 :=
  primeFieldProduct_eq_zero_of_not_prime (by decide) _ _

example : primeFieldProduct 4 2 (fun _ => 1) = 0 :=
  primeFieldProduct_eq_zero_of_not_prime (by decide) _ _

-- Restrict to the three indices whose binary values are below three.
example : primeFieldProduct 5 2 (fun w =>
    if decide (BitString.binaryValue w < 3) then BitString.binaryValue w + 1 else 1) = 1 := by
  rw [primeFieldProduct_eq_val]
  decide

-- No allowed indices gives the empty product, including when the excluded factors are zero.
example : primeFieldProduct 5 2 (fun _ => if false then 0 else 1) = 1 := by
  rw [primeFieldProduct_eq_val]
  decide

/-- An index restriction shares the evaluator's level rather than adding an oracle level. -/
example :
    (fun w : List Bool => primeFieldProduct (BitString.binaryValue w) w.length
      (fun i => if decide (BitString.binaryValue i < BitString.binaryValue w)
        then factor (w, i) else 1)) ∈ CountingFunction 4 encBits encNat := by
  apply CountingFunction.prod_primeField_bits_restrict (a := 0) Decoder.bits
    (p := BitString.binaryValue) (r := List.length)
    (V := fun x : List Bool × List Bool =>
      decide (BitString.binaryValue x.2 < BitString.binaryValue x.1))
    (CountingFunction.of_polyTime factor_polyTime)
  · apply CountingFunction.of_polyTime
    exact ComputableInPolyTime.binary_lt' (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

end CslibFrontierTests.CountingFieldProducts
