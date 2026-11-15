/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Products
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Primality
public import CslibFrontier.Foundations.NumberTheory.PrimeWindowBounds
public import CslibFrontier.Foundations.NumberTheory.CRTFiniteSet
import CslibFrontier.Foundations.Data.BitString.MultiplicativeEnumeration
import CslibFrontier.Foundations.FieldTheory.Finite.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Prime-window cofactors and weighted CRT residues

`primeCofactor Y L p` computes the product of primes `L < q ≤ Y`, omitting `p`, modulo `p`.
Its certificate is uniform F_5 for polynomial-time binary cutoffs and modulus. Weighted CRT
coefficients additionally use a supplied residue and a binary exponent; an F_a residue gives
an F_max(a,5) coefficient. Neither operation constructs a full prime product or represented
integer. Nonprime moduli, including zero and one, return zero.

## Main definitions

* `Cslib.Complexity.primeWindowTest`: the shared total primality/range predicate.
* `Cslib.Complexity.primeCofactor`: modular product of the other window primes.
* `Cslib.Complexity.primeWindowCoefficient`: weighted natural CRT coefficient.

## Main results

* `Cslib.Complexity.primeCofactor_cast`, `Cslib.Complexity.primeCofactor_ne_zero`:
  correctness and invertibility of the cofactor residue.
* `Cslib.Complexity.primeWindowCoefficient_modEq`: the local CRT congruence.
* `Cslib.Complexity.CountingFunction.primeCofactor_mem`: the uniform F_5 certificate.
* `Cslib.Complexity.CountingFunction.primeWindowCoefficient_mem`: the coefficient certificate.

## References

* [OpenAI2026CountingHierarchy], Section 2, equation `crt-residues`. The cutoffs and exponent
  are generic parameters; this module does not implement integer reconstruction or sign recovery.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

/-- Total test for membership in the prime window `L < p ≤ Y`, shared by cofactor factors
and weighted-residue summation. All three arguments use their ordinary binary values. -/
@[expose] def primeWindowTest (Y L p : ℕ) : Bool :=
  primeTest p && decide (L < p ∧ p ≤ Y)

/-- The Boolean window test is exactly membership in the finite mathematical prime window. -/
theorem primeWindowTest_eq_true_iff (Y L p : ℕ) :
    primeWindowTest Y L p = true ↔ p ∈ Nat.primesLE Y \ Nat.primesLE L := by
  simp only [primeWindowTest, Bool.and_eq_true, primeTest, decide_eq_true_eq,
    Nat.mem_primesLE_sdiff_primesLE_iff]

private def cofactorFactor (Y L p : ℕ) (w : List Bool) : ℕ :=
  let q := BitString.binaryValue w
  if primeWindowTest Y L q then if q ≠ p then q else 1 else 1

/-- Product modulo `p` of the primes `L < q ≤ Y` other than `p`. Only binary-width indices
are passed to the factor evaluator. Every nonprime modulus has the total default zero. -/
noncomputable def primeCofactor (Y L p : ℕ) : ℕ :=
  primeFieldProduct p Y.size (cofactorFactor Y L p)

/-- Weighted CRT coefficient for the supplied natural residue `r` and doubling exponent `k`.
All powering is modular. Its inputs contain neither an implicit integer nor a full cofactor. -/
noncomputable def primeWindowCoefficient (Y L p k r : ℕ) : ℕ :=
  if primeTest p then
    ((powMod p 2 k * r) % p * powMod p (primeCofactor Y L p) (p - 2)) % p else 0

private theorem cofactorFactor_eq (Y L p : ℕ) (w : List Bool) :
    cofactorFactor Y L p w =
      if BitString.binaryValue w ∈ (Nat.primesLE Y \ Nat.primesLE L).erase p then
        BitString.binaryValue w else 1 := by
  simp only [cofactorFactor, primeWindowTest_eq_true_iff, mem_erase]
  split_ifs <;> tauto


/-- On a prime modulus, the computed residue casts to the mathematical erased-window product.
No order between the cutoffs or membership of the modulus in the window is required. -/
theorem primeCofactor_cast {p : ℕ} [Fact p.Prime] (Y L : ℕ) :
    (primeCofactor Y L p : ZMod p) =
      ∏ q ∈ (Nat.primesLE Y \ Nat.primesLE L).erase p, (q : ZMod p) := by
  classical
  rw [primeCofactor, primeFieldProduct_spec]
  simp only [cofactorFactor_eq, Nat.cast_ite, Nat.cast_one]
  apply BitString.prod_binaryValue_mem (k := Y + 1) (by have := Nat.lt_size_self Y; omega)
  intro q hq
  have hY := (Nat.mem_primesLE_sdiff_primesLE_iff.mp (mem_erase.mp hq).2).2.2
  exact mem_range.mpr (by omega)

/-- Cofactor residues are canonical at every positive modulus. -/
theorem primeCofactor_lt {p : ℕ} (hp : 0 < p) (Y L : ℕ) : primeCofactor Y L p < p :=
  primeFieldProduct_lt hp _ _

/-- Nonprime and malformed moduli have cofactor default zero. -/
theorem primeCofactor_eq_zero_of_not_prime {p : ℕ} (hp : ¬p.Prime) (Y L : ℕ) :
    primeCofactor Y L p = 0 :=
  primeFieldProduct_eq_zero_of_not_prime hp _ _

/-- A cofactor is nonzero in every prime field: all its prime factors differ from the modulus. -/
theorem primeCofactor_ne_zero {p : ℕ} [Fact p.Prime] (Y L : ℕ) :
    (primeCofactor Y L p : ZMod p) ≠ 0 := by
  rw [primeCofactor_cast]
  apply prod_ne_zero_iff.mpr
  intro q hq hzero
  have hqprime := (Nat.mem_primesLE_sdiff_primesLE_iff.mp (mem_erase.mp hq).2).1
  have hdiv := (ZMod.natCast_eq_zero_iff q p).mp hzero
  exact (mem_erase.mp hq).1 ((hqprime.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hdiv)

/-- The natural cofactor output is the canonical representative of the mathematical product. -/
theorem primeCofactor_eq_val {p : ℕ} [Fact p.Prime] (Y L : ℕ) :
    primeCofactor Y L p =
      (∏ q ∈ (Nat.primesLE Y \ Nat.primesLE L).erase p, (q : ZMod p)).val := by
  rw [← primeCofactor_cast, ZMod.val_natCast_of_lt
    (primeCofactor_lt (Fact.out : p.Prime).pos Y L)]

/-- Weighted coefficients have the total default zero at every nonprime modulus. -/
theorem primeWindowCoefficient_eq_zero_of_not_prime {p : ℕ} (hp : ¬p.Prime) (Y L k r : ℕ) :
    primeWindowCoefficient Y L p k r = 0 := by
  simp [primeWindowCoefficient, primeTest, hp]

/-- Weighted coefficients are canonical natural residues at every positive modulus. -/
theorem primeWindowCoefficient_lt {p : ℕ} (hp : 0 < p) (Y L k r : ℕ) :
    primeWindowCoefficient Y L p k r < p := by
  unfold primeWindowCoefficient
  split_ifs
  · exact Nat.mod_lt _ hp
  · exact hp


/-- The weighted coefficient represents the modular power times the supplied residue,
divided by the nonzero cofactor residue. -/
theorem primeWindowCoefficient_cast {p : ℕ} [Fact p.Prime] (Y L k r : ℕ) :
    (primeWindowCoefficient Y L p k r : ZMod p) =
      (2 : ZMod p) ^ k * (r : ZMod p) * (primeCofactor Y L p : ZMod p)⁻¹ := by
  have hp : p.Prime := Fact.out
  rw [primeWindowCoefficient, ite_eq_left (show primeTest p = true by simp [primeTest, hp]),
    ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul,
    powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    ZMod.pow_card_sub_two_eq_inv (primeCofactor_ne_zero Y L), Nat.cast_ofNat]

/-- The natural coefficient is the canonical representative of its field formula. -/
theorem primeWindowCoefficient_eq_val {p : ℕ} [Fact p.Prime] (Y L k r : ℕ) :
    primeWindowCoefficient Y L p k r =
      ((2 : ZMod p) ^ k * (r : ZMod p) * (primeCofactor Y L p : ZMod p)⁻¹).val := by
  rw [← primeWindowCoefficient_cast, ZMod.val_natCast_of_lt
    (primeWindowCoefficient_lt (Fact.out : p.Prime).pos Y L k r)]

/-- A zero supplied residue gives a zero weighted coefficient at every modulus. -/
@[simp] theorem primeWindowCoefficient_zero (Y L p k : ℕ) :
    primeWindowCoefficient Y L p k 0 = 0 := by
  simp [primeWindowCoefficient]

/-- A supplied residue of any integer yields the weighted local CRT congruence.
The integer, the full omitted-prime product and the full power occur only in this statement.
The premise is exactly the shape of `IntegerResidueAccess.residue_modEq`. -/
theorem primeWindowCoefficient_modEq {Y L p k r : ℕ} {X : ℤ} (hp : p.Prime)
    (hr : (r : ℤ) ≡ X [ZMOD (p : ℤ)]) :
    (primeWindowCoefficient Y L p k r : ℤ) *
        (∏ q ∈ (Nat.primesLE Y \ Nat.primesLE L).erase p, (q : ℤ)) ≡
      (2 : ℤ) ^ k * X [ZMOD (p : ℤ)] := by
  let : Fact p.Prime := ⟨hp⟩
  have hC := primeCofactor_ne_zero (p := p) Y L
  have hr' : (r : ZMod p) = (X : ZMod p) := by
    simpa only [Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff _ _ p).mpr hr
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_prod, Int.cast_pow, Int.cast_ofNat]
  rw [primeWindowCoefficient_cast, ← primeCofactor_cast, mul_assoc,
    inv_mul_cancel₀ hC, mul_one, hr']


/-- Subtype-indexed local congruence, ready for `crt_circle_identity` and its sign callers.
Every modulus in the prime window is prime; only the supplied residue's congruence is needed. -/
theorem primeWindowCoefficient_modEq_subtype (Y L k r : ℕ)
    (p : ↥(Nat.primesLE Y \ Nat.primesLE L)) {X : ℤ}
    (hr : (r : ℤ) ≡ X [ZMOD (p.val : ℤ)]) :
    (primeWindowCoefficient Y L p.val k r : ℤ) *
        Cslib.crtCofactor (fun q : ↥(Nat.primesLE Y \ Nat.primesLE L) => (q.val : ℤ)) p ≡
      (2 : ℤ) ^ k * X [ZMOD (p.val : ℤ)] := by
  rw [Cslib.crtCofactor_finset]
  exact primeWindowCoefficient_modEq
    (Nat.mem_primesLE_sdiff_primesLE_iff.mp p.property).1 hr

namespace CountingFunction

variable {α : Type} {enc : α ↪ List Bool}

/-- Uniform prime-window membership is F_1 for polynomial-time binary parameters.
This certificate is shared by cofactor products and the final masked residue sum. -/
theorem primeWindowTest_mem {Y L p : α → ℕ}
    (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat)
    (hp : ComputableInPolyTime p enc encNat) :
    (fun x => primeWindowTest (Y x) (L x) (p x)) ∈ CountingFunction 1 enc encBool := by
  have hprime := preprocess primeTest_mem_CountingFunction hp
  have hguard : ComputableInPolyTime (fun x => decide (L x < p x ∧ p x ≤ Y x)) enc encBool :=
    ComputableInPolyTime.decide_and (ComputableInPolyTime.binary_lt' hL hp)
      (ComputableInPolyTime.binary_le' hp hY)
  exact map (prod hprime (of_polyTime hguard))
    (g := fun pair : Bool × Bool => pair.1 && pair.2) (by fun_prop)

private theorem cofactorFactor_mem {Y L p : α → ℕ}
    (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat)
    (hp : ComputableInPolyTime p enc encNat) :
    (fun x : α × List Bool => cofactorFactor (Y x.1) (L x.1) (p x.1) x.2) ∈
      CountingFunction 1 (encPair enc encBits) encNat := by
  have hY' := hY.comp (ComputableInPolyTime.fst enc encBits)
  have hL' := hL.comp (ComputableInPolyTime.fst enc encBits)
  have hp' := hp.comp (ComputableInPolyTime.fst enc encBits)
  have hq : ComputableInPolyTime (fun x : α × List Bool => BitString.binaryValue x.2)
      (encPair enc encBits) encNat := by fun_prop
  have hwindow := primeWindowTest_mem hY' hL' hq
  have hguard := ComputableInPolyTime.decide_ne hq hp'
  have hselect := ite (of_polyTime (a := 1) hguard) (of_polyTime hq)
    (of_polyTime (ComputableInPolyTime.const 1))
  simpa only [cofactorFactor, decide_eq_true_eq, Function.comp_apply] using
    ite hwindow hselect (of_polyTime (ComputableInPolyTime.const 1))

/-- The uniform cofactor algorithm lies in F_5. The primality factor test is F_1 and the
conservative product rule adds four levels. All three parameters have binary PT certificates. -/
theorem primeCofactor_mem (D : Decoder enc) {Y L p : α → ℕ}
    (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat)
    (hp : ComputableInPolyTime p enc encNat) :
    (fun x => primeCofactor (Y x) (L x) (p x)) ∈ CountingFunction 5 enc encNat :=
  prod_primeField_bits D (cofactorFactor_mem hY hL hp) hp
    (ComputableInPolyTime.binary_size.comp hY)

/-- An F_a supplied residue and PT binary cutoffs, modulus and exponent give a total weighted
coefficient in F_max(a,5). Strict certificates charge intermediate residues, queries and outputs;
no implicit integer or large mathematical product is supplied as machine data. -/
theorem primeWindowCoefficient_mem {a : ℕ} (D : Decoder enc) {Y L p k r : α → ℕ}
    (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat)
    (hp : ComputableInPolyTime p enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hr : r ∈ CountingFunction a enc encNat) :
    (fun x => primeWindowCoefficient (Y x) (L x) (p x) (k x) (r x)) ∈
      CountingFunction (max a 5) enc encNat := by
  have hcofactor := mono (Nat.le_max_right a 5) (primeCofactor_mem D hY hL hp)
  have hinverse := powMod (of_polyTime hp) hcofactor
    (of_polyTime (ComputableInPolyTime.binary_sub' hp (.const 2)))
  have hpower := powMod (of_polyTime (a := max a 5) hp)
    (of_polyTime (ComputableInPolyTime.const 2)) (of_polyTime hk)
  have hscaled := nat_mod (nat_mul hpower (mono (Nat.le_max_left a 5) hr)) (of_polyTime hp)
  have hvalue := nat_mod (nat_mul hscaled hinverse) (of_polyTime hp)
  have hprime := preprocess primeTest_mem_CountingFunction hp
  exact ite (mono (by omega : 1 ≤ max a 5) hprime) hvalue
    (of_polyTime (ComputableInPolyTime.const 0))

end CountingFunction
end Cslib.Complexity
