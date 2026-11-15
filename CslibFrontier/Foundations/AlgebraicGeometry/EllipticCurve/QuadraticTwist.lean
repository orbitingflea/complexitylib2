/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Quadratic twists of Weierstrass curves and their point counts

For a Weierstrass curve `W` in `IsCharNeTwoNF` form `Y² = X³ + a₂ X² + a₄ X + a₆` over a
commutative ring `R` and a scalar `c : R`, the quadratic twist `W.quadraticTwist c` is the
Weierstrass curve `Y² = X³ + c a₂ X² + c² a₄ X + c³ a₆`, with discriminant `c⁶ W.Δ`. Over a field
`F` with `c ≠ 0`, the coordinate scaling `(x, y) ↦ (c x, c² y)` identifies the solutions of the
twisted equation `c y² = x³ + a₂ x² + a₄ x + a₆` with the affine solutions of
`W.quadraticTwist c` (`WeierstrassCurve.quadraticTwistEquationEquiv`), and when `W` is elliptic it
identifies `(W.quadraticTwist c).toAffine.Point` with the point at infinity together with those
solutions (`WeierstrassCurve.quadraticTwistPointEquiv`).

Over a finite field `F`, twisting the cubic `X³ + α X² + β X + γ` by `c ≠ 0` multiplies its
character sum `cubicCharSum` by `quadraticChar F c`. When `c` is a quadratic non-residue
(`¬ IsSquare c`), the character sums of `W` and `W.quadraticTwist c` cancel, giving
`#E(F) + #Ẽ(F) = 2 #F + 2` (and `#Ẽ(F) = #F + 1 + t` when `#E(F) = #F + 1 - t`), as in
[Boneh and Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 15.3.2
(p. 623).

Note that `WeierstrassCurve.Manin.twistPoly` in `ManinTwist.lean` is the instance
`(ofCubic (C α) (C β) (C γ)).quadraticTwist (cubicPoly α β γ)` over `Polynomial k` (with
`WeierstrassCurve.Manin.twist` its base change to `RatFunc k`), used internally in Manin's proof
of Hasse's bound.

## Main definitions

* `WeierstrassCurve.quadraticTwist W c`: the Weierstrass curve
  `Y² = X³ + c a₂ X² + c² a₄ X + c³ a₆`.
* `WeierstrassCurve.quadraticTwistEquationEquiv`: the coordinate-scaling equivalence
  `(x, y) ↦ (c x, c² y)` from solutions of `c y² = x³ + a₂ x² + a₄ x + a₆` to affine solutions of
  `W.quadraticTwist c`.
* `WeierstrassCurve.quadraticTwistPointEquiv`: for elliptic `W`, the equivalence between
  `(W.quadraticTwist c).toAffine.Point` and `WithZero` of the solutions of
  `c y² = x³ + a₂ x² + a₄ x + a₆`.

## Main results

* `WeierstrassCurve.quadraticTwist_Δ`: `(W.quadraticTwist c).Δ = c ^ 6 * W.Δ`.
* `WeierstrassCurve.isElliptic_quadraticTwist`: `W.quadraticTwist c` is elliptic when `W` is
  elliptic in `IsCharNeTwoNF` form and `c` is a unit.
* `WeierstrassCurve.ringChar_ne_two_of_isCharNeTwoNF`: over a field, an elliptic curve in
  `IsCharNeTwoNF` form forces `ringChar F ≠ 2`.
* `WeierstrassCurve.natCard_point_quadraticTwist_eq_one_add`,
  `WeierstrassCurve.natCard_point_quadraticTwist_eq_one_add_of_isShortNF`: the number of points of
  `W.quadraticTwist c` is one plus the number of solutions of `c y² = x³ + a₂ x² + a₄ x + a₆` (or
  `c y² = x³ + a₄ x + a₆`).
* `WeierstrassCurve.cubicCharSum_mul`: for `c ≠ 0`, twisting scales `cubicCharSum` by
  `quadraticChar F c`.
* `WeierstrassCurve.natCard_point_quadraticTwist`: for `c ≠ 0` and elliptic `W`,
  `#Ẽ(F) = #F + 1 + χ(c) · cubicCharSum W.a₂ W.a₄ W.a₆`.
* `WeierstrassCurve.natCard_point_quadraticTwist_of_isSquare`: twisting by a nonzero square
  preserves `#E(F)`.
* `WeierstrassCurve.natCard_equation_add_quadraticTwist`: for `¬ IsSquare c`, the affine solution
  sets of `W` and `W.quadraticTwist c` have `2 #F` points in total, even without `IsElliptic`.
* `WeierstrassCurve.natCard_point_add_quadraticTwist`,
  `WeierstrassCurve.natCard_point_add_quadraticTwist_zmod`: for `¬ IsSquare c`,
  `#E(F) + #Ẽ(F) = 2 #F + 2` (and `2 p + 2` over `ZMod p`).
* `WeierstrassCurve.natCard_point_quadraticTwist_eq_of_eq_sub`: if `#E(F) = #F + 1 - t` and
  `¬ IsSquare c`, then `#Ẽ(F) = #F + 1 + t`.

## Implementation notes and deviations from the source

* [BonehShoup2023], Section 15.3.2 (p. 623) writes the twist of `y² = x³ + a x + b` over `𝔽_p`
  (`p > 3`) as the non-monic equation `c y² = x³ + a x + b`. Because Mathlib's `WeierstrassCurve`
  is monic in `Y²` and `X³`, `W.quadraticTwist c` is defined as the isomorphic Weierstrass model
  `Y² = X³ + c a₂ X² + c² a₄ X + c³ a₆`, and `quadraticTwistPointEquiv` records the explicit
  bijection with `WithZero` of the solutions of `c y² = x³ + a₂ x² + a₄ x + a₆`.
* The results are stated for any curve satisfying `[W.IsCharNeTwoNF]` (`a₁ = 0` and `a₃ = 0`, which
  includes `ofCubic α β γ` and short Weierstrass curves `[W.IsShortNF]`) over any finite field `F`,
  with `natCard_point_add_quadraticTwist_zmod` specializing to `ZMod p`. Over a field,
  `[W.IsCharNeTwoNF]` together with `[W.IsElliptic]` forces `ringChar F ≠ 2`, so odd characteristic
  is not needed as a separate hypothesis.
* The informal notion of "twist security" and the 256-bit twist-order factorizations of secp256r1
  and secp256k1 in [BonehShoup2023], Section 15.3.2 are not formalized here.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 15.2
  (Equation (15.4), p. 618) and Section 15.3.2 (p. 623).
-/

public section

open Polynomial

namespace WeierstrassCurve

/-! ### The quadratic twist of a Weierstrass curve -/

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Every curve `ofCubic α β γ` (`Y² = X³ + α X² + β X + γ`) is in `IsCharNeTwoNF` form
(`a₁ = 0` and `a₃ = 0`). -/
instance instIsCharNeTwoNFOfCubic (α β γ : R) : (ofCubic α β γ).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- Every curve `ofCubic 0 β γ` (`Y² = X³ + β X + γ`) is in short Weierstrass normal form
(`a₁ = a₂ = a₃ = 0`). -/
instance instIsShortNFOfCubicZero (β γ : R) : (ofCubic 0 β γ).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The quadratic twist of a Weierstrass curve `W` (in `IsCharNeTwoNF` form
`Y² = X³ + a₂ X² + a₄ X + a₆`) by `c : R`, namely the Weierstrass curve
`Y² = X³ + c a₂ X² + c² a₄ X + c³ a₆` ([BonehShoup2023], Section 15.3.2, p. 623).
When `c` is a unit, the change of coordinates `(x, y) ↦ (c x, c² y)` identifies its affine
solutions with those of the twisted equation `c y² = x³ + a₂ x² + a₄ x + a₆`.
Outside `IsCharNeTwoNF`, `a₁` and `a₃` are ignored and `W.quadraticTwist c` is not the quadratic
twist of `W`. -/
@[expose] def quadraticTwist (W : WeierstrassCurve R) (c : R) : WeierstrassCurve R :=
  ofCubic (c * W.a₂) (c ^ 2 * W.a₄) (c ^ 3 * W.a₆)

@[simp] lemma quadraticTwist_a₁ (c : R) : (W.quadraticTwist c).a₁ = 0 := rfl
@[simp] lemma quadraticTwist_a₂ (c : R) : (W.quadraticTwist c).a₂ = c * W.a₂ := rfl
@[simp] lemma quadraticTwist_a₃ (c : R) : (W.quadraticTwist c).a₃ = 0 := rfl
@[simp] lemma quadraticTwist_a₄ (c : R) : (W.quadraticTwist c).a₄ = c ^ 2 * W.a₄ := rfl
@[simp] lemma quadraticTwist_a₆ (c : R) : (W.quadraticTwist c).a₆ = c ^ 3 * W.a₆ := rfl

instance instIsCharNeTwoNFQuadraticTwist (c : R) : (W.quadraticTwist c).IsCharNeTwoNF :=
  instIsCharNeTwoNFOfCubic _ _ _

instance instIsShortNFQuadraticTwist [W.IsShortNF] (c : R) : (W.quadraticTwist c).IsShortNF where
  a₁ := rfl
  a₂ := by simp
  a₃ := rfl

@[simp] theorem quadraticTwist_one [W.IsCharNeTwoNF] : W.quadraticTwist 1 = W := by
  ext <;> simp

theorem quadraticTwist_quadraticTwist (c d : R) :
    (W.quadraticTwist c).quadraticTwist d = W.quadraticTwist (d * c) := by
  ext <;> simp [quadraticTwist] <;> ring

/-- For a curve `W` in `IsCharNeTwoNF` form, the discriminant of `W.quadraticTwist c` is
`c⁶ * W.Δ`. -/
theorem quadraticTwist_Δ [W.IsCharNeTwoNF] (c : R) :
    (W.quadraticTwist c).Δ = c ^ 6 * W.Δ := by
  simp only [Δ_of_isCharNeTwoNF, quadraticTwist_a₂, quadraticTwist_a₄, quadraticTwist_a₆]
  ring

/-- Twisting an elliptic curve in `IsCharNeTwoNF` form by a unit yields an elliptic curve. -/
theorem isElliptic_quadraticTwist [W.IsCharNeTwoNF] [W.IsElliptic] {c : R} (hc : IsUnit c) :
    (W.quadraticTwist c).IsElliptic := by
  rw [isElliptic_iff, quadraticTwist_Δ]
  exact (hc.pow 6).mul W.isUnit_Δ

private lemma eval_cubicPoly_mul (α β γ c x : R) :
    (cubicPoly (c * α) (c ^ 2 * β) (c ^ 3 * γ)).eval (c * x) =
      c ^ 3 * (cubicPoly α β γ).eval x := by
  simp only [eval_cubicPoly]
  ring

end Ring

/-! ### Bijection with solutions of the twisted equation `c y² = x³ + a₂ x² + a₄ x + a₆` -/

section Bijection

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- Over a field, an elliptic curve in `IsCharNeTwoNF` form (`a₁ = a₃ = 0`) exists only in
characteristic different from two: in characteristic two its discriminant vanishes. This supplies
the hypothesis `ringChar F ≠ 2` of `natCard_point_eq` and `hasse_bound` for such a curve. -/
theorem ringChar_ne_two_of_isCharNeTwoNF [W.IsCharNeTwoNF] [W.IsElliptic] : ringChar F ≠ 2 := by
  intro h2
  have : CharP F 2 := h2 ▸ ringChar.charP F
  exact W.isUnit_Δ.ne_zero (by rw [W.Δ_of_char_two]; simp)

/-- Over a field, `(c x, c² y)` lies on `W.quadraticTwist c` iff `(x, y)` satisfies the twisted
equation `c y² = x³ + a₂ x² + a₄ x + a₆`. -/
theorem quadraticTwist_equation_iff {c : F} (hc : c ≠ 0) (x y : F) :
    (W.quadraticTwist c).toAffine.Equation (c * x) (c ^ 2 * y) ↔
      c * y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
  rw [Affine.equation_iff]
  simp only [quadraticTwist_a₁, quadraticTwist_a₂, quadraticTwist_a₃, quadraticTwist_a₄,
    quadraticTwist_a₆, zero_mul, add_zero]
  constructor
  · intro h
    apply mul_left_cancel₀ hc3
    linear_combination h
  · intro h
    linear_combination c ^ 3 * h

/-- Scaling coordinates by `(x, y) ↦ (c x, c² y)` identifies the solutions of the twisted
equation `c y² = x³ + a₂ x² + a₄ x + a₆` with the affine solutions of `W.quadraticTwist c`. -/
noncomputable def quadraticTwistEquationEquiv {c : F} (hc : c ≠ 0) :
    {xy : F × F // c * xy.2 ^ 2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆} ≃
      {XY : F × F // (W.quadraticTwist c).toAffine.Equation XY.1 XY.2} :=
  Equiv.subtypeEquiv
    (Equiv.prodCongr (Equiv.mulLeft₀ c hc) (Equiv.mulLeft₀ (c ^ 2) (pow_ne_zero 2 hc)))
    fun xy ↦ (W.quadraticTwist_equation_iff hc xy.1 xy.2).symm

@[simp] theorem quadraticTwistEquationEquiv_apply {c : F} (hc : c ≠ 0) {x y : F}
    (h : c * y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :
    (W.quadraticTwistEquationEquiv hc ⟨(x, y), h⟩ : F × F) = (c * x, c ^ 2 * y) := by
  rfl

@[simp] theorem quadraticTwistEquationEquiv_symm_apply {c : F} (hc : c ≠ 0) {x y : F}
    (h : (W.quadraticTwist c).toAffine.Equation x y) :
    ((W.quadraticTwistEquationEquiv hc).symm ⟨(x, y), h⟩ : F × F) =
      (c⁻¹ * x, (c ^ 2)⁻¹ * y) := by
  rfl

/-- For an elliptic curve `W` in `IsCharNeTwoNF` form and `c ≠ 0`, the points of
`W.quadraticTwist c` are in bijection with the point at infinity (`0`) together with the
solutions of `c y² = x³ + a₂ x² + a₄ x + a₆`. -/
noncomputable def quadraticTwistPointEquiv [W.IsCharNeTwoNF] [W.IsElliptic] {c : F}
    (hc : c ≠ 0) :
    (W.quadraticTwist c).toAffine.Point ≃
      WithZero {xy : F × F // c * xy.2 ^ 2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆} :=
  have : (W.quadraticTwist c).IsElliptic := W.isElliptic_quadraticTwist hc.isUnit
  have hΔ : (W.quadraticTwist c).Δ ≠ 0 := (W.quadraticTwist c).isUnit_Δ.ne_zero
  (W.quadraticTwist c).toAffine.nonsingularPointEquiv.trans <|
    ((Equiv.subtypeEquivRight fun _ ↦
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).symm).trans
        (W.quadraticTwistEquationEquiv hc).symm).optionCongr

@[simp] theorem quadraticTwistPointEquiv_zero [W.IsCharNeTwoNF] [W.IsElliptic] {c : F}
    (hc : c ≠ 0) :
    W.quadraticTwistPointEquiv hc 0 = 0 := by
  rfl

@[simp] theorem quadraticTwistPointEquiv_symm_zero [W.IsCharNeTwoNF] [W.IsElliptic] {c : F}
    (hc : c ≠ 0) :
    (W.quadraticTwistPointEquiv hc).symm 0 = 0 := by
  rfl

theorem quadraticTwistPointEquiv_some [W.IsCharNeTwoNF] [W.IsElliptic] {c : F} (hc : c ≠ 0)
    {x y : F} (h : (W.quadraticTwist c).toAffine.Nonsingular x y) :
    W.quadraticTwistPointEquiv hc (.some _ _ h) =
      WithZero.coe ((W.quadraticTwistEquationEquiv hc).symm ⟨(x, y), h.left⟩) := by
  rfl

theorem quadraticTwistPointEquiv_symm_coe [W.IsCharNeTwoNF] [W.IsElliptic] {c : F} (hc : c ≠ 0)
    {x y : F} (h : c * y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hns : (W.quadraticTwist c).toAffine.Nonsingular (c * x) (c ^ 2 * y)) :
    (W.quadraticTwistPointEquiv hc).symm (WithZero.coe ⟨(x, y), h⟩) = .some _ _ hns := by
  rfl

/-- For an elliptic curve `W` in `IsCharNeTwoNF` form over a finite field and `c ≠ 0`, the number
of points of `W.quadraticTwist c` is one (the point at infinity) plus the number of solutions of
`c y² = x³ + a₂ x² + a₄ x + a₆`. -/
theorem natCard_point_quadraticTwist_eq_one_add [Finite F] [W.IsCharNeTwoNF] [W.IsElliptic]
    {c : F} (hc : c ≠ 0) :
    Nat.card (W.quadraticTwist c).toAffine.Point =
      1 + Nat.card
        {xy : F × F // c * xy.2 ^ 2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆} := by
  rw [Nat.card_congr (W.quadraticTwistPointEquiv hc), add_comm]
  exact Finite.card_option

/-- For a short Weierstrass elliptic curve `y² = x³ + a₄ x + a₆` over a finite field and `c ≠ 0`,
the number of points of `W.quadraticTwist c` is one (the point at infinity) plus the number of
solutions of `c y² = x³ + a₄ x + a₆` ([BonehShoup2023], Section 15.3.2, p. 623). -/
theorem natCard_point_quadraticTwist_eq_one_add_of_isShortNF [Finite F] [W.IsShortNF]
    [W.IsElliptic] {c : F} (hc : c ≠ 0) :
    Nat.card (W.quadraticTwist c).toAffine.Point =
      1 + Nat.card {xy : F × F // c * xy.2 ^ 2 = xy.1 ^ 3 + W.a₄ * xy.1 + W.a₆} := by
  rw [W.natCard_point_quadraticTwist_eq_one_add hc, W.a₂_of_isShortNF]
  simp only [zero_mul, add_zero]

end Bijection

/-! ### Character sums and point counts over finite fields -/

section PointCount

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
private lemma ne_zero_of_not_isSquare {c : F} (hc : ¬ IsSquare c) : c ≠ 0 := by
  rintro rfl
  exact hc IsSquare.zero

/-- For `c ≠ 0`, twisting the cubic `X³ + α X² + β X + γ` by `c` multiplies its character sum
`cubicCharSum` by `quadraticChar F c`. -/
theorem cubicCharSum_mul [DecidableEq F] (α β γ : F) {c : F} (hc : c ≠ 0) :
    cubicCharSum (c * α) (c ^ 2 * β) (c ^ 3 * γ) =
      quadraticChar F c * cubicCharSum α β γ := by
  unfold cubicCharSum
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ c hc), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Equiv.mulLeft₀_apply, eval_cubicPoly_mul, show c ^ 3 = c ^ 2 * c by ring, mul_assoc,
    map_mul, quadraticChar_sq_one' hc, one_mul, map_mul]

/-- For a quadratic non-residue `c`, twisting the cubic `X³ + α X² + β X + γ` by `c` negates its
character sum `cubicCharSum`. -/
theorem cubicCharSum_mul_of_not_isSquare [DecidableEq F] (α β γ : F) {c : F}
    (hc : ¬ IsSquare c) :
    cubicCharSum (c * α) (c ^ 2 * β) (c ^ 3 * γ) = -cubicCharSum α β γ := by
  rw [cubicCharSum_mul α β γ (ne_zero_of_not_isSquare hc),
    quadraticChar_neg_one_iff_not_isSquare.mpr hc, neg_one_mul]

/-- For a nonzero square `c`, twisting the cubic `X³ + α X² + β X + γ` by `c` preserves its
character sum `cubicCharSum`. -/
theorem cubicCharSum_mul_of_isSquare [DecidableEq F] (α β γ : F) {c : F}
    (hc : IsSquare c) (hc0 : c ≠ 0) :
    cubicCharSum (c * α) (c ^ 2 * β) (c ^ 3 * γ) = cubicCharSum α β γ := by
  rw [cubicCharSum_mul α β γ hc0, (quadraticChar_one_iff_isSquare hc0).mpr hc, one_mul]

private lemma cubicCharSum_b₂_b₄_b₆_of_isCharNeTwoNF [DecidableEq F] (hF : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    cubicCharSum (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) = cubicCharSum W.a₂ W.a₄ W.a₆ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [W.b₂_of_isCharNeTwoNF, W.b₄_of_isCharNeTwoNF, W.b₆_of_isCharNeTwoNF,
    mul_div_cancel_left₀ _ h4, mul_div_cancel_left₀ _ h2, mul_div_cancel_left₀ _ h4]

/-- For an elliptic curve `W` in `IsCharNeTwoNF` form over a finite field,
`#E(F) = #F + 1 + cubicCharSum W.a₂ W.a₄ W.a₆`. -/
theorem natCard_point_eq_of_isCharNeTwoNF [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (Nat.card W.toAffine.Point : ℤ) =
      Fintype.card F + 1 + cubicCharSum W.a₂ W.a₄ W.a₆ := by
  have hF : ringChar F ≠ 2 := W.ringChar_ne_two_of_isCharNeTwoNF
  rw [natCard_point_eq hF W, cubicCharSum_b₂_b₄_b₆_of_isCharNeTwoNF hF W]

/-- For an elliptic curve `W` in `IsCharNeTwoNF` form over a finite field and `c ≠ 0`,
`#Ẽ(F) = #F + 1 + χ(c) · cubicCharSum W.a₂ W.a₄ W.a₆`. -/
theorem natCard_point_quadraticTwist [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] {c : F} (hc : c ≠ 0) :
    (Nat.card (W.quadraticTwist c).toAffine.Point : ℤ) =
      Fintype.card F + 1 + quadraticChar F c * cubicCharSum W.a₂ W.a₄ W.a₆ := by
  have : (W.quadraticTwist c).IsElliptic := W.isElliptic_quadraticTwist hc.isUnit
  rw [natCard_point_eq_of_isCharNeTwoNF (W.quadraticTwist c), quadraticTwist_a₂,
    quadraticTwist_a₄, quadraticTwist_a₆, cubicCharSum_mul _ _ _ hc]

omit [Fintype F] in
/-- Twisting by a nonzero square preserves the number of points. -/
theorem natCard_point_quadraticTwist_of_isSquare [Finite F]
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] {c : F}
    (hc : IsSquare c) (hc0 : c ≠ 0) :
    Nat.card (W.quadraticTwist c).toAffine.Point = Nat.card W.toAffine.Point := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  have : (W.quadraticTwist c).IsElliptic := W.isElliptic_quadraticTwist hc0.isUnit
  have h1 := natCard_point_eq_of_isCharNeTwoNF W
  have h2 := natCard_point_eq_of_isCharNeTwoNF (W.quadraticTwist c)
  rw [quadraticTwist_a₂, quadraticTwist_a₄, quadraticTwist_a₆,
    cubicCharSum_mul_of_isSquare _ _ _ hc hc0, ← h1] at h2
  exact_mod_cast h2

/-- Even without nonsingularity (`IsElliptic`), the affine solution sets of `W` (in
`IsCharNeTwoNF` form) and of its quadratic twist by a non-square `c` have `2 #F` points in
total. -/
theorem natCard_equation_add_quadraticTwist (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {c : F} (hc : ¬ IsSquare c) :
    Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} +
      Nat.card {xy : F × F // (W.quadraticTwist c).toAffine.Equation xy.1 xy.2} =
      2 * Fintype.card F := by
  classical
  have hF : ringChar F ≠ 2 := fun h2 ↦ hc (FiniteField.isSquare_of_char_two h2 c)
  have h1 := natCard_equation hF W
  have h2 := natCard_equation hF (W.quadraticTwist c)
  rw [cubicCharSum_b₂_b₄_b₆_of_isCharNeTwoNF hF W] at h1
  rw [cubicCharSum_b₂_b₄_b₆_of_isCharNeTwoNF hF (W.quadraticTwist c), quadraticTwist_a₂,
    quadraticTwist_a₄, quadraticTwist_a₆, cubicCharSum_mul_of_not_isSquare _ _ _ hc] at h2
  omega

/-- **Point count of the quadratic twist** ([BonehShoup2023], Section 15.3.2, p. 623). For an
elliptic curve `W` in `IsCharNeTwoNF` form over a finite field `F` and a quadratic non-residue
`c : F`, `#E(F) + #Ẽ(F) = 2 #F + 2`. -/
theorem natCard_point_add_quadraticTwist (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {c : F} (hc : ¬ IsSquare c) :
    Nat.card W.toAffine.Point + Nat.card (W.quadraticTwist c).toAffine.Point =
      2 * Fintype.card F + 2 := by
  have : (W.quadraticTwist c).IsElliptic :=
    W.isElliptic_quadraticTwist (ne_zero_of_not_isSquare hc).isUnit
  have h1 := W.toAffine.natCard_point_eq_one_add_equation W.isUnit_Δ.ne_zero
  have h2 := (W.quadraticTwist c).toAffine.natCard_point_eq_one_add_equation
    (W.quadraticTwist c).isUnit_Δ.ne_zero
  have heq := W.natCard_equation_add_quadraticTwist hc
  omega

/-- If `#E(F) = q + 1 - t` and `c` is a quadratic non-residue, then `#Ẽ(F) = q + 1 + t`
([BonehShoup2023], Section 15.3.2, p. 623). -/
theorem natCard_point_quadraticTwist_eq_of_eq_sub (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {c : F} (hc : ¬ IsSquare c) {t : ℤ}
    (ht : (Nat.card W.toAffine.Point : ℤ) = Fintype.card F + 1 - t) :
    (Nat.card (W.quadraticTwist c).toAffine.Point : ℤ) = Fintype.card F + 1 + t := by
  have h := natCard_point_add_quadraticTwist W hc
  omega

/-- Over `ZMod p`, an elliptic curve `W` in `IsCharNeTwoNF` form and its quadratic twist by a
quadratic non-residue `c` satisfy `#E(F_p) + #Ẽ(F_p) = 2p + 2` ([BonehShoup2023], Section 15.3.2,
p. 623). -/
theorem natCard_point_add_quadraticTwist_zmod {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve (ZMod p)) [W.IsCharNeTwoNF] [W.IsElliptic] {c : ZMod p}
    (hc : ¬ IsSquare c) :
    Nat.card W.toAffine.Point + Nat.card (W.quadraticTwist c).toAffine.Point = 2 * p + 2 := by
  rw [natCard_point_add_quadraticTwist W hc, ZMod.card]

end PointCount

end WeierstrassCurve
