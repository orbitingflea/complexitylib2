/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.DiscreteLog
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Generator
public import CslibFrontier.Foundations.NumberTheory.FiniteField.Enumeration
import CslibFrontier.Foundations.FieldTheory.Finite.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Short-index products in prime fields

A total evaluator averages the logarithm formula over every multiplicative generator.
Each sum uses a uniform short-index evaluator. No generator is selected, and the unreduced
product and full powers occur only in correctness proofs. Composite moduli, including zero
and one, return zero. The modulus is binary and the index width is polynomial-time unary.

## Main definitions

* `Cslib.Complexity.generatorCount`: the number of accepted canonical generators.
* `Cslib.Complexity.primeFieldProduct`: the total generator-average product evaluator.

## Main results

* `Cslib.Complexity.primeFieldProduct_spec`: agreement with the prime-field product.
* `Cslib.Complexity.CountingFunction.prod_primeField_bits`: the conservative F_(a+4) bound.

## References

* [OpenAI2026CountingHierarchy], Section 2, Products in a finite field. Averaging replaces
  the source's generator selection; the existing algebraic average theorem supplies correctness.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

/-- Count canonical generators by their total Boolean test; nonprime moduli give zero. -/
noncomputable def generatorCount (p : ℕ) : ℕ :=
  ∑ g ∈ range p, if generatorTest (p, g) then 1 else 0

/-- Sum the total logarithm evaluator over all bitstrings of width `b`, for one base. -/
private def primeFieldLogSum (p g b : ℕ) (f : List Bool → ℕ) : ℕ :=
  ∑ i : Fin b → Bool, modularLogSum p g (f (List.ofFn i))

/-- Sum the modular logarithm product formulas, masking every nongenerator by zero. -/
private noncomputable def generatorProductSum (p b : ℕ) (f : List Bool → ℕ) : ℕ :=
  ∑ g ∈ range p, if generatorTest (p, g) then
    powMod p g (primeFieldLogSum p g b f % (p - 1)) else 0

open Classical in
/-- Total product evaluator on residue factors. Its inputs contain no unreduced product.
For a prime modulus it returns the canonical product residue; for every other modulus it
returns zero, even though `powMod` itself has the fixed value one at modulus zero. -/
noncomputable def primeFieldProduct (p b : ℕ) (f : List Bool → ℕ) : ℕ :=
  if ∃ w : List Bool, w.length = b ∧ f w % p = 0 then 0 else
    generatorProductSum p b f * powMod p (generatorCount p) (p - 2) % p

/-- The accepted natural representatives count the algebraic generator set exactly. -/
theorem generatorCount_eq_card {p : ℕ} [Fact p.Prime] :
    generatorCount p = (primitiveRoots (p - 1) (ZMod p)).card := by
  classical
  rw [generatorCount, ← ZMod.count_range_natCast_mem (primitiveRoots (p - 1) (ZMod p))]
  apply sum_congr rfl
  intro g hg
  simp only [generatorTest_eq_true_iff_mem (mem_range.mp hg)]

/-- The generator count vanishes on every nonprime modulus. -/
theorem generatorCount_eq_zero_of_not_prime {p : ℕ} (hp : ¬p.Prime) :
    generatorCount p = 0 := by
  simp [generatorCount, generatorTest_ne_true_of_not_prime hp]

/-- Every nongenerator summand is zero at a nonprime modulus. -/
private theorem generatorProductSum_eq_zero_of_not_prime {p : ℕ} (hp : ¬p.Prime)
    (b : ℕ) (f : List Bool → ℕ) : generatorProductSum p b f = 0 := by
  simp [generatorProductSum, generatorTest_ne_true_of_not_prime hp]

/-- Composite and malformed moduli use the total default zero. -/
theorem primeFieldProduct_eq_zero_of_not_prime {p : ℕ} (hp : ¬p.Prime)
    (b : ℕ) (f : List Bool → ℕ) : primeFieldProduct p b f = 0 := by
  classical
  simp [primeFieldProduct, generatorProductSum_eq_zero_of_not_prime hp]

private theorem generatorProductSum_cast {p : ℕ} [Fact p.Prime]
    (b : ℕ) (f : List Bool → ℕ) :
    (generatorProductSum p b f : ZMod p) =
      ∑ γ ∈ primitiveRoots (p - 1) (ZMod p),
        γ ^ ((∑ i : Fin b → Bool, ZMod.generatorLogSum p γ (f (List.ofFn i))) % (p - 1)) := by
  classical
  rw [generatorProductSum, Nat.cast_sum, ← ZMod.sum_range_natCast_mem]
  apply sum_congr rfl
  intro g hg
  simp only [Nat.cast_ite, Nat.cast_zero,
    generatorTest_eq_true_iff_mem (mem_range.mp hg)]
  congr 1
  rw [powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow]
  congr 2
  unfold primeFieldLogSum
  exact sum_congr rfl fun i _ =>
    modularLogSum_eq_generatorLogSum (Fact.out : p.Prime).ne_zero g _

/-- The evaluator returns a canonical residue whenever the modulus is positive. -/
theorem primeFieldProduct_lt {p : ℕ} (hp : 0 < p) (b : ℕ) (f : List Bool → ℕ) :
    primeFieldProduct p b f < p := by
  classical
  unfold primeFieldProduct
  split_ifs
  · exact hp
  · exact Nat.mod_lt _ hp

/-- The total evaluator agrees with the full mathematical product at a prime modulus.
The product is a specification, never an intermediate value of the evaluator. -/
theorem primeFieldProduct_spec {p : ℕ} [Fact p.Prime] (b : ℕ) (f : List Bool → ℕ) :
    (primeFieldProduct p b f : ZMod p) = ∏ i : Fin b → Bool, (f (List.ofFn i) : ZMod p) := by
  classical
  have hp : p.Prime := Fact.out
  by_cases hz : ∃ w : List Bool, w.length = b ∧ f w % p = 0
  · rw [primeFieldProduct, ite_eq_left hz, Nat.cast_zero]
    obtain ⟨w, hw, hzero⟩ := hz
    subst b
    symm
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨w.get, mem_univ _, ?_⟩
    rw [List.ofFn_get, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero hzero
  · have hnonzero : ¬ ∃ i ∈ (univ : Finset (Fin b → Bool)),
        (f (List.ofFn i) : ZMod p) = 0 := by
      rintro ⟨i, _, hi⟩
      exact hz ⟨List.ofFn i, List.length_ofFn,
        Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hi)⟩
    rw [primeFieldProduct, ite_eq_right hz, ZMod.natCast_mod, Nat.cast_mul,
      powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow,
      generatorCount_eq_card, ZMod.pow_card_sub_two_eq_inv ZMod.primitiveRoots_card_ne_zero,
      generatorProductSum_cast, ← div_eq_mul_inv]
    have h := ZMod.prod_eq_generator_average univ
      (fun i : Fin b → Bool => (f (List.ofFn i) : ZMod p))
    simp only [ite_eq_right hnonzero] at h
    exact h.symm

/-- The natural output is the least representative of the full mathematical product. -/
theorem primeFieldProduct_eq_val {p : ℕ} [Fact p.Prime] (b : ℕ) (f : List Bool → ℕ) :
    primeFieldProduct p b f = (∏ i : Fin b → Bool, (f (List.ofFn i) : ZMod p)).val := by
  rw [← primeFieldProduct_spec,
    ZMod.val_natCast_of_lt (primeFieldProduct_lt (Fact.out : p.Prime).pos b f)]

/-- A restricted product is the product over exactly the selected bitstrings. Excluded
indices contribute one, so selecting no indices gives the empty product. -/
theorem primeFieldProduct_restrict_spec {p : ℕ} [Fact p.Prime] (b : ℕ)
    (f : List Bool → ℕ) (V : List Bool → Bool) :
    (primeFieldProduct p b (fun w => if V w then f w else 1) : ZMod p) =
      ∏ i ∈ (univ : Finset (Fin b → Bool)).filter (fun i => V (List.ofFn i)),
        (f (List.ofFn i) : ZMod p) := by
  classical
  rw [primeFieldProduct_spec, Finset.prod_filter]
  simp only [Nat.cast_ite, Nat.cast_one]

namespace CountingFunction

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- Counting the accepted generator tests costs one level beyond the tests themselves. -/
theorem generatorCount_mem : generatorCount ∈ CountingFunction 2 encNat encNat := by
  have hterm := ite (middle := encNat) generatorTest_mem_CountingFunction
    (of_polyTime (ComputableInPolyTime.const 1))
    (of_polyTime (ComputableInPolyTime.const 0))
  exact sum_range Decoder.nat hterm ComputableInPolyTime.id'

private theorem primeFieldLogSum_mem (D : Decoder enc) {p g r : α → ℕ}
    {f : α × List Bool → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hp : ComputableInPolyTime p enc encNat) (hg : ComputableInPolyTime g enc encNat)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => primeFieldLogSum (p x) (g x) (r x) (fun w => f (x, w))) ∈
      CountingFunction (a + 2) enc encNat := by
  have hp' : ComputableInPolyTime (fun x : α × List Bool => p x.1)
      (encPair enc encBits) encNat := hp.comp (ComputableInPolyTime.fst _ _)
  have hg' : ComputableInPolyTime (fun x : α × List Bool => g x.1)
      (encPair enc encBits) encNat := hg.comp (ComputableInPolyTime.fst _ _)
  have hargs := prod (of_polyTime hp') (prod (of_polyTime hg')
    (mono (show a ≤ a + 1 by omega) hf))
  have hlog := comp (mono (show 1 ≤ a + 1 by omega) modularLogSum_mem_CountingFunction) hargs
  exact sum_bits D hlog hr

private theorem generatorProductSum_mem (D : Decoder enc) {p r : α → ℕ}
    {f : α × List Bool → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hp : ComputableInPolyTime p enc encNat)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => generatorProductSum (p x) (r x) (fun w => f (x, w))) ∈
      CountingFunction (a + 3) enc encNat := by
  have hp' : ComputableInPolyTime (fun x : α × ℕ => p x.1)
      (encPair enc encNat) encNat := hp.comp (ComputableInPolyTime.fst _ _)
  have hr' : ComputableInPolyTime (fun x : α × ℕ => r x.1)
      (encPair enc encNat) encUnary := hr.comp (ComputableInPolyTime.fst _ _)
  have hf' := preprocess (input := encPair (encPair enc encNat) encBits) hf
    (g := fun x : (α × ℕ) × List Bool => (x.1.1, x.2))
    (by fun_prop)
  have hlog := primeFieldLogSum_mem (Decoder.pair D Decoder.nat) hf' hp'
    (ComputableInPolyTime.snd _ _) hr'
  have hexp := nat_mod hlog
    (of_polyTime (ComputableInPolyTime.binary_sub' hp' (.const 1)))
  have hpower := powMod (of_polyTime hp')
    (of_polyTime (ComputableInPolyTime.snd enc encNat)) hexp
  have htest := preprocess generatorTest_mem_CountingFunction
    (g := fun x : α × ℕ => (p x.1, x.2)) (hp'.prod (ComputableInPolyTime.snd _ _))
  have hterm := ite (mono (show 1 ≤ a + 2 by omega) htest) hpower
    (of_polyTime (ComputableInPolyTime.const 0))
  exact sum_range D hterm hp

/-- The generator-average evaluator is in F_(a+3), including on every nonprime input.
The strict certificates of composition and summation bound every query and intermediate output. -/
theorem primeFieldProduct_mem (D : Decoder enc) {p r : α → ℕ} {f : α × List Bool → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hp : ComputableInPolyTime p enc encNat)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => primeFieldProduct (p x) (r x) (fun w => f (x, w))) ∈
      CountingFunction (a + 3) enc encNat := by
  classical
  have hsum := generatorProductSum_mem D hf hp hr
  have hcount := preprocess generatorCount_mem hp
  have hinv := powMod (of_polyTime hp)
    (mono (show 2 ≤ a + 3 by omega) hcount)
    (of_polyTime (ComputableInPolyTime.binary_sub' hp (.const 2)))
  have hvalue := nat_mod (nat_mul hsum hinv) (of_polyTime hp)
  have hp' : ComputableInPolyTime (fun x : α × List Bool => p x.1)
      (encPair enc encBits) encNat := hp.comp (ComputableInPolyTime.fst _ _)
  have hzero := map (nat_mod hf (of_polyTime hp'))
    (g := fun n : ℕ => decide (n = 0)) (by fun_prop)
  have hflag := exists_bits D hzero hr
  simpa only [primeFieldProduct, decide_eq_true_eq] using
    ite (mono (show a + 1 ≤ a + 3 by omega) hflag)
      (of_polyTime (ComputableInPolyTime.const 0)) hvalue

/-- Short-index prime-field products of F_a factors lie in F_(a+4), with total zero default
on every nonprime modulus. The modulus is polynomial-time binary, and width polynomial-time
unary; factor, query, intermediate and output lengths follow from strict certificates.
The stronger F_(a+3) bound comes from averaging rather than selecting a generator. -/
theorem prod_primeField_bits (D : Decoder enc) {p r : α → ℕ} {f : α × List Bool → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hp : ComputableInPolyTime p enc encNat)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => primeFieldProduct (p x) (r x) (fun w => f (x, w))) ∈
      CountingFunction (a + 4) enc encNat :=
  mono (by omega) (primeFieldProduct_mem D hf hp hr)

/-- A same-level predicate restricts the product by replacing excluded factors with one.
This includes an empty allowed domain and does not add a counting level. -/
theorem prod_primeField_bits_restrict (D : Decoder enc) {p r : α → ℕ}
    {f : α × List Bool → ℕ} {V : α × List Bool → Bool}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hV : V ∈ CountingFunction a (encPair enc encBits) encBool)
    (hp : ComputableInPolyTime p enc encNat)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => primeFieldProduct (p x) (r x)
      (fun w => if V (x, w) then f (x, w) else 1)) ∈
      CountingFunction (a + 4) enc encNat :=
  prod_primeField_bits D (ite hV hf (of_polyTime (ComputableInPolyTime.const 1))) hp hr

end CountingFunction
end Cslib.Complexity
