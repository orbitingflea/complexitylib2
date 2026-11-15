/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib, Mathlib/FieldTheory/Finite/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Products in prime fields by averaging generators

The generators of the multiplicative group of `ZMod p`, for prime `p`, form a nonempty set of
cardinality strictly below `p`. Their cardinality is therefore invertible in the prime field.
Every generator represents each nonzero factor by exactly one exponent below `p - 1`.
Summing the matching exponents gives a total finite formula for logarithms, without selecting a
generator or an exponent. Averaging the resulting product formula over all generators then
recovers the original product.

These are algebraic statements, without computational complexity certificates. The denominator
argument uses the fact that the field is prime: the number of generators in a general finite
field can vanish in that field's characteristic.

## Main definitions

* `ZMod.generatorLogSum`: the sum of all exponents whose power equals the supplied element.

## Main results

* `ZMod.primitiveRoots_nonempty`: there is a generator of the prime field.
* `ZMod.primitiveRoots_card_bounds`, `ZMod.primitiveRoots_card_ne_zero`: the generator count is
  positive and invertible in the prime field.
* `ZMod.generatorLogSum_spec`: the sum is the unique bounded logarithm on nonzero elements.
* `ZMod.prod_eq_generator_average`: a product equals the average of its logarithm formulas.
-/

public section

namespace ZMod

variable {p : ℕ}

/-- Sum all matching exponents below `p - 1`. This is a total finite formula, including at
composite and zero moduli and for nongenerators. Its logarithm specification requires a prime
modulus, a primitive root and a nonzero element. -/
@[expose] def generatorLogSum (p : ℕ) (γ x : ZMod p) : ℕ :=
  ∑ e ∈ Finset.range (p - 1), if γ ^ e = x then e else 0

variable [Fact p.Prime]

/-- The multiplicative group of a prime field has a generator, represented as a field element. -/
theorem primitiveRoots_nonempty : (primitiveRoots (p - 1) (ZMod p)).Nonempty := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hu' : orderOf u = p - 1 := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hu
  have hγ : IsPrimitiveRoot (u : ZMod p) (p - 1) :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu')
  exact ⟨u, (mem_primitiveRoots (by omega)).mpr hγ⟩

/-- The number of multiplicative generators is positive and strictly below the prime modulus.
This includes `p = 2`, whose sole generator is one. -/
theorem primitiveRoots_card_bounds :
    0 < (primitiveRoots (p - 1) (ZMod p)).card ∧
      (primitiveRoots (p - 1) (ZMod p)).card < p := by
  obtain ⟨γ, hγ⟩ := primitiveRoots_nonempty (p := p)
  have hroot := isPrimitiveRoot_of_mem_primitiveRoots hγ
  simp only [hroot.card_primitiveRoots]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  exact ⟨Nat.totient_pos.mpr (by omega), (Nat.totient_le (p - 1)).trans_lt (by omega)⟩

/-- The natural generator count is nonzero as an element of the prime field, and hence has a
multiplicative inverse. -/
theorem primitiveRoots_card_ne_zero :
    ((primitiveRoots (p - 1) (ZMod p)).card : ZMod p) ≠ 0 := by
  obtain ⟨hpos, hlt⟩ := primitiveRoots_card_bounds (p := p)
  intro hzero
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hdiv)

/-- At a primitive root, a nonzero element has one matching exponent, so the sum of all matching
exponents is that exponent. No efficient algorithm is asserted here. -/
theorem generatorLogSum_spec {γ x : ZMod p} (hγ : IsPrimitiveRoot γ (p - 1))
    (hx : x ≠ 0) : generatorLogSum p γ x < p - 1 ∧ γ ^ generatorLogSum p γ x = x := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let : NeZero (p - 1) := ⟨by omega⟩
  obtain ⟨e, he, hpow⟩ := hγ.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx)
  have hsum : generatorLogSum p γ x = e := by
    unfold generatorLogSum
    rw [Finset.sum_eq_single e]
    · exact ite_eq_left hpow
    · intro j hj hje
      exact ite_eq_right fun h => hje
        (hγ.pow_inj (Finset.mem_range.mp hj) he (h.trans hpow.symm))
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr he))
  rw [hsum]
  exact ⟨he, hpow⟩

open Classical in
/-- A finite product in a prime field is the average, over every multiplicative generator, of
its discrete-logarithm formula. Zero factors are handled by the explicit zero test. The formula
also covers empty products. It assumes no efficient logarithm or generator selection algorithm. -/
theorem prod_eq_generator_average {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    (∏ i ∈ s, f i) =
      (∑ γ ∈ primitiveRoots (p - 1) (ZMod p),
        if ∃ i ∈ s, f i = 0 then 0
        else γ ^ ((∑ i ∈ s, generatorLogSum p γ (f i)) % (p - 1))) /
          ((primitiveRoots (p - 1) (ZMod p)).card : ZMod p) := by
  have hterm (γ : ZMod p) (hmem : γ ∈ primitiveRoots (p - 1) (ZMod p)) :
      (if ∃ i ∈ s, f i = 0 then 0
        else γ ^ ((∑ i ∈ s, generatorLogSum p γ (f i)) % (p - 1))) = ∏ i ∈ s, f i := by
    by_cases hz : ∃ i ∈ s, f i = 0
    · rw [ite_eq_left hz]
      exact (Finset.prod_eq_zero_iff.mpr hz).symm
    · rw [ite_eq_right hz]
      have hγ := isPrimitiveRoot_of_mem_primitiveRoots hmem
      calc
        γ ^ ((∑ i ∈ s, generatorLogSum p γ (f i)) % (p - 1)) =
            γ ^ (∑ i ∈ s, generatorLogSum p γ (f i)) := by
          rw [hγ.eq_orderOf, pow_mod_orderOf]
        _ = ∏ i ∈ s, γ ^ generatorLogSum p γ (f i) :=
          (Finset.prod_pow_eq_pow_sum s (fun i => generatorLogSum p γ (f i)) γ).symm
        _ = ∏ i ∈ s, f i := Finset.prod_congr rfl fun i hi =>
          (generatorLogSum_spec hγ fun h => hz ⟨i, hi, h⟩).2
  have hsum :
      (∑ γ ∈ primitiveRoots (p - 1) (ZMod p),
        if ∃ i ∈ s, f i = 0 then 0
        else γ ^ ((∑ i ∈ s, generatorLogSum p γ (f i)) % (p - 1))) =
          ((primitiveRoots (p - 1) (ZMod p)).card : ZMod p) * (∏ i ∈ s, f i) := by
    calc
      _ = ∑ _γ ∈ primitiveRoots (p - 1) (ZMod p), (∏ i ∈ s, f i) :=
        Finset.sum_congr rfl hterm
      _ = _ := by simp
  rw [hsum, mul_div_cancel_left₀ _ (primitiveRoots_card_ne_zero (p := p))]

end ZMod
