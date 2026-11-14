/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Dimension
public import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Ring

/-!
# Low-degree agreement with multiplicative bit characters

Smolensky's counting argument [Smolensky1987] extends from `±1` parity characters (`BitString.chi`)
to multiplicative characters `phaseChar ω S x = ∏ i ∈ S, ω ^ (x i).toNat` for any `ω ≠ 0, 1` in a
field `F`: in characteristic `q`, a primitive `p`-th root of unity (`p ≠ q`) satisfies both
`ω ≠ 0` and `ω ≠ 1`.

On the cube, `ω ^ b.toNat = 1 + (ω - 1) · bitVal F b`, so every coordinate factor has degree at
most one (`phaseChar_mem_lowDegree`), every monomial expands into `phaseChar` functions, and every
single-coordinate factor has inverse `ω⁻¹ (1 + ω - ω ^ b.toNat)` of degree at most one. Hence if
a function `Q` of degree at most `D` agrees with `phaseChar ω univ` (`ω ^ weight x`) on a set `G`,
every function on `G` agrees with one of degree at most `|ι| / 2 + D` (`exists_agree_of_phaseChar`),
bounding `#G` by the dimension bound `card_le_of_forall_exists_agree`
(`card_agree_phaseCharOn_univ_le`, `card_agree_phaseChar_le`).

## Main definitions

* `Cslib.BitString.phaseChar`: the multiplicative character `∏ i ∈ S, ω ^ (x i).toNat`.

## Main results

* `Cslib.BitString.card_le_of_forall_exists_agree`: a set on which every function agrees with a
  degree-`H` function has size at most the number of sets of at most `H` coordinates.
* `Cslib.BitString.exists_agree_of_phaseChar`: if `Q` of degree `D` agrees with `phaseChar ω univ`
  on `G` (`ω ≠ 0, 1`), every function on `G` agrees with one of degree at most `|ι| / 2 + D`.
* `Cslib.BitString.card_agree_phaseCharOn_univ_le`, `Cslib.BitString.card_agree_phaseChar_le`:
  a low-degree function agrees with `x ↦ ω ^ weight x` on at most `#{S | #S ≤ n / 2 + D}` inputs.

## References

* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

public section

namespace Cslib.BitString

open Finset

/-! ### Multiplicative characters `phaseChar` -/

section CommRing

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The multiplicative character of a set `S` of coordinates with base `ω : R`: the product of
`ω ^ (x i).toNat` over `i ∈ S`. At `ω = -1` this is `BitString.chi`. -/
@[expose] def phaseChar (ω : R) (S : Finset ι) (x : ι → Bool) : R :=
  ∏ i ∈ S, ω ^ (x i).toNat

/-- Evaluating `phaseChar ω S` at `x`. -/
theorem phaseChar_apply (ω : R) (S : Finset ι) (x : ι → Bool) :
    phaseChar ω S x = ∏ i ∈ S, ω ^ (x i).toNat :=
  rfl

/-- The multiplicative character of the empty set is `1`. -/
@[simp] theorem phaseChar_empty (ω : R) (x : ι → Bool) : phaseChar ω (∅ : Finset ι) x = 1 :=
  prod_empty

/-- Multiplicative characters multiply across disjoint coordinate sets. -/
theorem phaseChar_union [DecidableEq ι] (ω : R) {S T : Finset ι} (hST : Disjoint S T)
    (x : ι → Bool) : phaseChar ω (S ∪ T) x = phaseChar ω S x * phaseChar ω T x :=
  prod_union hST

/-- On all coordinates of a finite cube, `phaseChar ω univ x` equals `ω ^ weight x`. -/
theorem phaseChar_univ_eq_pow_weight [Fintype ι] (ω : R) (x : ι → Bool) :
    phaseChar ω univ x = ω ^ weight x := by
  simp only [phaseChar, prod_pow_eq_pow_sum, weight_eq_sum_toNat]

/-- Each coordinate factor `ω ^ b.toNat` is affine-linear in `bitVal R b`. -/
private theorem pow_toNat_eq_one_add_mul_bitVal (ω : R) (b : Bool) :
    ω ^ b.toNat = 1 + (ω - 1) * bitVal R b := by
  cases b <;> simp [bitVal]

/-- The multiplicative character of `S` has degree at most `#S`. -/
theorem phaseChar_mem_lowDegree (ω : R) (S : Finset ι) :
    phaseChar ω S ∈ lowDegree R ι #S := by
  have hfun : phaseChar ω S =
      ∏ i ∈ S, (1 + (ω - 1) • fun x : ι → Bool => bitVal R (x i)) := by
    funext x
    simp [phaseChar, Finset.prod_apply, pow_toNat_eq_one_add_mul_bitVal]
  rw [hfun]
  simpa using prod_mem_lowDegree S (a := 1) fun i _ =>
    Submodule.add_mem _ (one_mem_lowDegree 1) (Submodule.smul_mem _ _ (bitVal_mem_lowDegree i))

end CommRing

/-! ### Dimension and agreement bounds over a field -/

section Field

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- If every function agrees on `G` with a function of degree at most `H`, then `G` has at most as
many points as there are sets of at most `H` coordinates. -/
theorem card_le_of_forall_exists_agree {H : ℕ} (G : Finset (ι → Bool))
    (hG : ∀ f : (ι → Bool) → F, ∃ p ∈ lowDegree F ι H, ∀ x ∈ G, p x = f x) :
    #G ≤ #{S : Finset ι | #S ≤ H} := by
  classical
  -- restricting to `G` is onto
  let restrict : lowDegree F ι H →ₗ[F] (G → F) :=
    { toFun := fun p x => p.1 x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective restrict := fun g => by
    obtain ⟨p, hp, hpx⟩ := hG fun x => if hx : x ∈ G then g ⟨x, hx⟩ else 0
    refine ⟨⟨p, hp⟩, funext fun x => ?_⟩
    change p x.1 = g x
    simpa using hpx x.1 x.2
  have h := LinearMap.finrank_range_le restrict
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h
  exact h.trans (finrank_lowDegree_le H)

section

variable {F : Type*} [Field F] {ι : Type*}

/-- When `ω ≠ 1`, every monomial expands as a linear combination of `phaseChar ω T` over subsets
`T`. -/
private theorem monomial_mem_span_phaseChar {ω : F} (hω1 : ω ≠ 1) (S : Finset ι) :
    monomial F S ∈ Submodule.span F (Set.range (phaseChar ω (ι := ι))) := by
  classical
  have hne : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
  have hfun : monomial F S = ∑ T ∈ S.powerset,
      ((ω - 1)⁻¹ ^ #S * (-1 : F) ^ #(S \ T)) • phaseChar ω T := by
    funext x
    simp only [monomial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, phaseChar]
    have hsplit : ∏ i ∈ S, bitVal F (x i) =
        ∏ i ∈ S, ((ω - 1)⁻¹ * (ω ^ (x i).toNat + (-1 : F))) :=
      prod_congr rfl fun i _ => by
        cases x i <;> simp [bitVal, ← sub_eq_add_neg, inv_mul_cancel₀ hne]
    rw [hsplit, prod_mul_distrib, prod_const, prod_add, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_const]
    ring
  rw [hfun]
  exact Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

end

/-- If `Q` has degree at most `D` and agrees with `phaseChar ω univ` (`ω ≠ 0, 1`) on `G`, every
function agrees on `G` with a function of degree at most `|ι| / 2 + D`. -/
theorem exists_agree_of_phaseChar {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {D : ℕ}
    {Q : (ι → Bool) → F} (hQ : Q ∈ lowDegree F ι D) (G : Finset (ι → Bool))
    (hG : ∀ x ∈ G, Q x = phaseChar ω univ x) (f : (ι → Bool) → F) :
    ∃ p ∈ lowDegree F ι (Fintype.card ι / 2 + D), ∀ x ∈ G, p x = f x := by
  classical
  -- every function lies in the span of `phaseChar ω`
  have hf : f ∈ Submodule.span F (Set.range (phaseChar ω (ι := ι))) := by
    have hle : lowDegree F ι (Fintype.card ι) ≤
        Submodule.span F (Set.range (phaseChar ω (ι := ι))) := by
      rw [lowDegree, Submodule.span_le]
      rintro _ ⟨S, _, rfl⟩
      exact monomial_mem_span_phaseChar hω1 S
    exact hle (mem_lowDegree_self f)
  -- degree-1 inverse factor for `ω ^ (x i).toNat`
  let invFactor (i : ι) (x : ι → Bool) : F := ω⁻¹ * (1 + ω - ω ^ (x i).toNat)
  have hinv_deg (i : ι) : invFactor i ∈ lowDegree F ι 1 := by
    have hfun : invFactor i =
        1 - (ω⁻¹ * (ω - 1)) • fun x : ι → Bool => bitVal F (x i) := by
      funext x
      simp only [invFactor, Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      cases x i
      · simp only [Bool.toNat_false, pow_zero, add_sub_cancel_left, bitVal_false, mul_zero,
          sub_zero]
        exact inv_mul_cancel₀ hω0
      · simp only [Bool.toNat_true, pow_one, add_sub_cancel_right, mul_one, bitVal_true]
        rw [mul_sub, mul_one, inv_mul_cancel₀ hω0]
        ring
    rw [hfun]
    exact Submodule.sub_mem _ (one_mem_lowDegree 1)
      (Submodule.smul_mem _ _ (bitVal_mem_lowDegree i))
  have hinv_mul (T : Finset ι) (x : ι → Bool) :
      phaseChar ω T x * ∏ i ∈ T, invFactor i x = 1 := by
    rw [phaseChar, ← prod_mul_distrib]
    exact prod_eq_one fun i _ => by
      dsimp only [invFactor]
      cases x i
      · simp [inv_mul_cancel₀ hω0]
      · simp [mul_inv_cancel₀ hω0]
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, rfl⟩ := hg
    by_cases hS : #S ≤ Fintype.card ι / 2
    · exact ⟨phaseChar ω S, lowDegree_mono (by omega) (phaseChar_mem_lowDegree ω S), fun _ _ => rfl⟩
    · refine ⟨Q * ∏ i ∈ Sᶜ, invFactor i, ?_, fun x hx => ?_⟩
      · have hc : #Sᶜ ≤ Fintype.card ι / 2 := by
          rw [card_compl]
          omega
        have hprod : (∏ i ∈ Sᶜ, invFactor i) ∈ lowDegree F ι (Fintype.card ι / 2) :=
          lowDegree_mono (by simpa using hc) (prod_mem_lowDegree Sᶜ fun i _ => hinv_deg i)
        exact lowDegree_mono (by omega) (mul_mem_lowDegree hQ hprod)
      · simp only [Pi.mul_apply, Finset.prod_apply]
        rw [hG x hx, ← union_compl S, phaseChar_union ω (disjoint_compl_right : Disjoint S Sᶜ),
          mul_assoc, hinv_mul Sᶜ x, mul_one]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hpx⟩ := hf
    obtain ⟨q, hq, hqx⟩ := hg
    exact ⟨p + q, Submodule.add_mem _ hp hq, fun x hx => by simp [hpx x hx, hqx x hx]⟩
  | smul c f _ hf =>
    obtain ⟨p, hp, hpx⟩ := hf
    exact ⟨c • p, Submodule.smul_mem _ c hp, fun x hx => by simp [hpx x hx]⟩

/-- A function of degree at most `D` agrees with `phaseChar ω univ` (`ω ≠ 0, 1`) on at most as many
inputs as there are sets of at most `|ι| / 2 + D` coordinates. -/
theorem card_agree_phaseCharOn_univ_le [DecidableEq ι] [DecidableEq F] {ω : F} (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) {D : ℕ} {Q : (ι → Bool) → F} (hQ : Q ∈ lowDegree F ι D) :
    #{x : ι → Bool | Q x = phaseChar ω univ x} ≤ #{S : Finset ι | #S ≤ Fintype.card ι / 2 + D} :=
  card_le_of_forall_exists_agree _ (exists_agree_of_phaseChar hω0 hω1 hQ _ fun _ hx =>
    (mem_filter.1 hx).2)

/-- A function of degree at most `D` agrees with `x ↦ ω ^ weight x` (`ω ≠ 0, 1`) on at most as
many inputs as there are sets of at most `n / 2 + D` coordinates. -/
theorem card_agree_phaseChar_le [DecidableEq F] {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {n D : ℕ} {Q : BitString n → F} (hQ : Q ∈ lowDegree F (Fin n) D) :
    #{x : BitString n | Q x = ω ^ weight x} ≤ #{S : Finset (Fin n) | #S ≤ n / 2 + D} := by
  have h := card_agree_phaseCharOn_univ_le hω0 hω1 hQ
  rw [Fintype.card_fin] at h
  simp only [← phaseChar_univ_eq_pow_weight]
  exact h

end Field

end Cslib.BitString
