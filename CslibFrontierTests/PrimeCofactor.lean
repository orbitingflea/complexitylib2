/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.PrimeCofactor
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueAccess
import CslibFrontier.Foundations.Data.BitString.MultiplicativeEnumeration

/-!
# Prime-window cofactor and weighted-residue clients

The window `3 < q ≤ 7` consists of `5, 7`; the omitted products modulo those primes are
`2, 5`. The canonical residues of minus one are `4, 6`. Their weighted coefficients are
checked at doubling exponents zero and one, including the subtype-cofactor congruence.
Other examples cover the prime two, empty and reversed windows, nonprime defaults, generic
access-interface composition, and multiplicative enumeration through ordinary imports.
-/

public section

namespace CslibFrontierTests.PrimeCofactor

open Cslib Cslib.Complexity Turing.MultiTapeTM Finset

-- The numerator mask and cofactor factors share the same total window predicate.
example : primeWindowTest 7 3 5 = true := by decide
example : primeWindowTest 7 3 7 = true := by decide
example : primeWindowTest 7 3 3 = false := by decide
example : primeWindowTest 7 3 4 = false := by decide
example : primeWindowTest 7 3 11 = false := by decide
example : primeWindowTest 7 3 0 = false := by decide

example : (fun p : ℕ => if primeWindowTest 7 3 p then 4 else 0) ∈
    CountingFunction 1 encNat encNat :=
  CountingFunction.ite
    (CountingFunction.primeWindowTest_mem (.const 7) (.const 3) ComputableInPolyTime.id')
    (CountingFunction.of_polyTime (.const 4)) (CountingFunction.of_polyTime (.const 0))

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem cofactor_five : primeCofactor 7 3 5 = 2 := by
  rw [primeCofactor_eq_val]
  decide

private theorem cofactor_seven : primeCofactor 7 3 7 = 5 := by
  rw [primeCofactor_eq_val]
  decide

-- The cofactor is one when the only prime is omitted, or when the window is empty.
private theorem cofactor_two : primeCofactor 2 1 2 = 1 := by
  rw [primeCofactor_eq_val]
  decide

example : primeCofactor 3 7 5 = 1 := by
  rw [primeCofactor_eq_val]
  decide

example : (primeCofactor 7 3 5 : ZMod 5) ≠ 0 := primeCofactor_ne_zero _ _

example : primeCofactor 7 3 0 = 0 := primeCofactor_eq_zero_of_not_prime (by decide) _ _
example : primeCofactor 7 3 1 = 0 := primeCofactor_eq_zero_of_not_prime (by decide) _ _
example : primeCofactor 7 3 4 = 0 := primeCofactor_eq_zero_of_not_prime (by decide) _ _

example : primeWindowCoefficient 7 3 5 0 4 = 2 := by
  rw [primeWindowCoefficient_eq_val, cofactor_five]
  decide +kernel

example : primeWindowCoefficient 7 3 5 1 4 = 4 := by
  rw [primeWindowCoefficient_eq_val, cofactor_five]
  decide +kernel

example : primeWindowCoefficient 7 3 7 0 6 = 4 := by
  rw [primeWindowCoefficient_eq_val, cofactor_seven]
  decide +kernel

example : primeWindowCoefficient 7 3 7 1 6 = 1 := by
  rw [primeWindowCoefficient_eq_val, cofactor_seven]
  decide +kernel

example : primeWindowCoefficient 2 1 2 0 1 = 1 := by
  rw [primeWindowCoefficient_eq_val, cofactor_two]
  decide +kernel

example : primeWindowCoefficient 2 1 2 1 1 = 0 := by
  rw [primeWindowCoefficient_eq_val, cofactor_two]
  decide +kernel

example : primeWindowCoefficient 7 3 0 10 4 = 0 :=
  primeWindowCoefficient_eq_zero_of_not_prime (by decide) _ _ _ _
example : primeWindowCoefficient 7 3 1 10 4 = 0 :=
  primeWindowCoefficient_eq_zero_of_not_prime (by decide) _ _ _ _
example : primeWindowCoefficient 7 3 4 10 4 = 0 :=
  primeWindowCoefficient_eq_zero_of_not_prime (by decide) _ _ _ _

example : primeWindowCoefficient 7 3 5 100 0 = 0 := primeWindowCoefficient_zero _ _ _ _

-- The hypothesis accepts the exact natural-to-integer congruence of the residue interface.
example : (primeWindowCoefficient 7 3 5 1 4 : ℤ) *
    (∏ q ∈ (Nat.primesLE 7 \ Nat.primesLE 3).erase 5, (q : ℤ)) ≡ -2 [ZMOD 5] := by
  have h := primeWindowCoefficient_modEq (Y := 7) (L := 3) (p := 5) (k := 1) (r := 4)
    (X := -1) (by decide) (by decide)
  norm_num at h ⊢
  exact h

-- The subtype bridge does not need a nonzero distinguished modulus.
example : crtCofactor (fun q : ↥({0, 5} : Finset ℕ) => (q.val : ℤ)) ⟨0, by decide⟩ = 5 := by
  rw [crtCofactor_finset]
  decide

example : (∏ w : Fin 2 → Bool,
    if BitString.binaryValue (List.ofFn w) ∈ ({1, 3} : Finset ℕ)
      then BitString.binaryValue (List.ofFn w) + 1 else 1) = 8 := by
  rw [BitString.prod_binaryValue_mem (k := 4) (by decide) ({1, 3} : Finset ℕ)
    (by decide) (fun i : ℕ => i + 1)]
  decide

example : (∏ w : Fin 0 → Bool,
    if BitString.binaryValue (List.ofFn w) < 0 then (7 : ℕ) else 1) = 1 := by
  rw [BitString.prod_binaryValue_lt (by decide : 0 ≤ 2 ^ 0) (fun _ => (7 : ℕ))]
  decide

/-- A variable binary window endpoint is handled by one uniform F_5 cofactor certificate. -/
example : (fun Y : ℕ => primeCofactor (Y + 7) 3 5) ∈ CountingFunction 5 encNat encNat :=
  CountingFunction.primeCofactor_mem Decoder.nat
    (ComputableInPolyTime.binary_add' ComputableInPolyTime.id' (.const 7)) (.const 3) (.const 5)

/-- A binary exponent of unbounded value is kept inside modular powering. -/
example : (fun k : ℕ => primeWindowCoefficient 7 3 5 k (k % 5)) ∈
    CountingFunction 5 encNat encNat := by
  simpa only [Nat.zero_max, Function.comp_apply] using
    CountingFunction.primeWindowCoefficient_mem (a := 0) Decoder.nat
      (.const 7) (.const 3) (.const 5) ComputableInPolyTime.id'
      (CountingFunction.of_polyTime
        (ComputableInPolyTime.binary_mod.comp (ComputableInPolyTime.id'.prod (.const 5))))

/-- The parent's access interface supplies the congruence directly, with no magnitude or
canonicality premise needed by the coefficient theorem. -/
example {α : Type} {X : α → ℤ} (R : IntegerResidueAccess X) (w : α) (Y L k : ℕ)
    (p : ↥(Nat.primesLE Y \ Nat.primesLE L)) (hp : R.admissible w p.val) :
    (primeWindowCoefficient Y L p.val k (R.residue (w, p.val)) : ℤ) *
        crtCofactor (fun q : ↥(Nat.primesLE Y \ Nat.primesLE L) => (q.val : ℤ)) p ≡
      (2 : ℤ) ^ k * X w [ZMOD (p.val : ℤ)] :=
  primeWindowCoefficient_modEq_subtype Y L k _ p (R.residue_modEq hp)

/-- The one uniform residue certificate composes with the polynomial-time selected modulus.
The represented integer is absent from the resulting machine inputs and outputs. -/
example {α : Type} {enc : α ↪ List Bool} {X : α → ℤ} {a : ℕ}
    (D : Decoder enc) (R : IntegerResidueAccess X) (hR : R.InCountingFunction a enc)
    {Y L p k : α → ℕ} (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat) (hp : ComputableInPolyTime p enc encNat)
    (hk : ComputableInPolyTime k enc encNat) :
    (fun w => primeWindowCoefficient (Y w) (L w) (p w) (k w) (R.residue (w, p w))) ∈
      CountingFunction (max a 5) enc encNat :=
  CountingFunction.primeWindowCoefficient_mem D hY hL hp hk
    (CountingFunction.preprocess hR.2 (ComputableInPolyTime.id'.prod hp))

end CslibFrontierTests.PrimeCofactor
