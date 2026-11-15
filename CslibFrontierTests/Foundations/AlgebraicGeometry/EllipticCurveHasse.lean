/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Decidable
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Hasse
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.QuadraticTwist
import Mathlib.Tactic.NormNum.Prime

/-! Point counts, Hasse's bound, and quadratic twists for small elliptic curves over `ZMod p`,
including the curve `y² = x³ + 3x + 3` over `ZMod 7` from Example 9.69 of [KatzLindell2020], the
12-point curve `y² = x³ + 1` over `ZMod 11` from Equation (15.4) of [BonehShoup2023] (Section 15.2,
p. 618), and quadratic twists from [BonehShoup2023] (Section 15.3.2, p. 623). -/

public section

namespace CslibFrontierTests.EllipticCurveHasse

open WeierstrassCurve

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The curve `y² = x³ + 3x + 3` over `ZMod 7`. -/
abbrev E7 : WeierstrassCurve (ZMod 7) := ofCubic 0 3 3

theorem Δ_E7 : E7.Δ ≠ 0 := by decide

instance : E7.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E7⟩

/-- The curve `y² + y = x³` over `ZMod 2`. -/
abbrev E2 : WeierstrassCurve (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

theorem Δ_E2 : E2.Δ ≠ 0 := by decide

instance : E2.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E2⟩

theorem ringChar_zmod_seven : ringChar (ZMod 7) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- `E7` has 6 points: the point at infinity, `(1, 0)`, `(3, ±2)` and `(4, ±3)`. -/
theorem natCard_E7 : Nat.card E7.toAffine.Point = 6 := by
  rw [E7.toAffine.natCard_point_eq_one_add_equation Δ_E7, Nat.card_eq_fintype_card]
  decide

/-- `E2` has 3 points: the point at infinity, `(0, 0)` and `(0, 1)`. -/
theorem natCard_E2 : Nat.card E2.toAffine.Point = 3 := by
  rw [E2.toAffine.natCard_point_eq_one_add_equation Δ_E2, Nat.card_eq_fintype_card]
  decide

-- The point count of `E7` forces the character sum of `x³ + 3x + 3` over `ZMod 7` to be `-2`.
example : cubicCharSum (E7.b₂ / 4) (E7.b₄ / 2) (E7.b₆ / 4) = -2 := by
  have h := natCard_point_eq ringChar_zmod_seven E7
  rw [natCard_E7, ZMod.card] at h
  omega

-- Manin's bound on that character sum, with the discriminant hypothesis checked by `decide`.
example : cubicCharSum (0 : ZMod 7) 3 3 ^ 2 ≤ 4 * 7 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    cubicCharSum_sq_le ringChar_zmod_seven (α := (0 : ZMod 7)) (β := 3) (γ := 3) (by decide)

-- Hasse's bound for `E7` in integer form: `(6 - 8)² ≤ 28`.
example : ((Nat.card E7.toAffine.Point : ℤ) - (7 + 1)) ^ 2 ≤ 4 * 7 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using hasse_bound ringChar_zmod_seven E7

-- The real form for `E7`: `|6 - 8| ≤ 2 √7`.
example : |(6 : ℝ) - (7 + 1)| ≤ 2 * Real.sqrt 7 := by
  have h := abs_natCard_point_sub_le ringChar_zmod_seven E7
  rw [natCard_E7, ZMod.card] at h
  exact_mod_cast h

-- `hasse_bound_zmod` for `E7`, and for `E2` in characteristic two.
example : (7 : ℝ) + 1 - 2 * Real.sqrt 7 ≤ Nat.card E7.toAffine.Point ∧
    (Nat.card E7.toAffine.Point : ℝ) ≤ 7 + 1 + 2 * Real.sqrt 7 := by
  exact_mod_cast hasse_bound_zmod E7

example : (2 : ℝ) + 1 - 2 * Real.sqrt 2 ≤ Nat.card E2.toAffine.Point ∧
    (Nat.card E2.toAffine.Point : ℝ) ≤ 2 + 1 + 2 * Real.sqrt 2 := by
  exact_mod_cast hasse_bound_zmod E2

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem ringChar_zmod_five : ringChar (ZMod 5) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- The curve `y² = x³ + 3x` over `ZMod 5`. -/
abbrev E5 : WeierstrassCurve (ZMod 5) := ofCubic 0 3 0

/-- The curve `y² = x³ + 2x` over `ZMod 5`. -/
abbrev E5' : WeierstrassCurve (ZMod 5) := ofCubic 0 2 0

theorem Δ_E5 : E5.Δ ≠ 0 := by decide

theorem Δ_E5' : E5'.Δ ≠ 0 := by decide

instance : E5.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E5⟩

instance : E5'.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E5'⟩

/-- `E5` has 10 points, the most that Hasse's bound allows over `ZMod 5`. -/
theorem natCard_E5 : Nat.card E5.toAffine.Point = 10 := by
  rw [E5.toAffine.natCard_point_eq_one_add_equation Δ_E5, Nat.card_eq_fintype_card]
  decide

/-- `E5'` has 2 points, the fewest that Hasse's bound allows over `ZMod 5`. -/
theorem natCard_E5' : Nat.card E5'.toAffine.Point = 2 := by
  rw [E5'.toAffine.natCard_point_eq_one_add_equation Δ_E5', Nat.card_eq_fintype_card]
  decide

-- Over `ZMod 5`, Hasse's bound gives `2 ≤ #E ≤ 10` for every elliptic curve, and `E5'` and `E5`
-- show that both ends are attained.
example (W : WeierstrassCurve (ZMod 5)) [W.IsElliptic] :
    2 ≤ Nat.card W.toAffine.Point ∧ Nat.card W.toAffine.Point ≤ 10 := by
  have h := hasse_bound ringChar_zmod_five W
  simp only [ZMod.card, Nat.cast_ofNat] at h
  constructor
  · have : (2 : ℤ) ≤ Nat.card W.toAffine.Point := by nlinarith
    exact_mod_cast this
  · have : (Nat.card W.toAffine.Point : ℤ) ≤ 10 := by nlinarith
    exact_mod_cast this

example : (2 : ℤ) = Nat.card E5'.toAffine.Point ∧ (Nat.card E5.toAffine.Point : ℤ) = 10 := by
  rw [natCard_E5', natCard_E5]
  norm_num

/-! ### Boneh–Shoup §15.2, Equation (15.4) (p. 618): `y² = x³ + 1` over `ZMod 11` -/

/-- The curve `y² = x³ + 1` over `ZMod 11` from Equation (15.4) of [BonehShoup2023]. -/
abbrev E11 : WeierstrassCurve (ZMod 11) := ofCubic 0 0 1

theorem Δ_E11 : E11.Δ ≠ 0 := by decide

instance : E11.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E11⟩

/-- The 11 affine points of `y² = x³ + 1` over `ZMod 11` listed in Equation (15.4) of
[BonehShoup2023]: `(-1, 0), (0, ±1), (2, ±3), (5, ±4), (7, ±5), (9, ±2)`. -/
theorem affinePoints_E11 :
    (Finset.univ.filter fun xy : ZMod 11 × ZMod 11 ↦ E11.toAffine.Equation xy.1 xy.2) =
      {(-1, 0), (0, 1), (0, -1), (2, 3), (2, -3), (5, 4), (5, -4), (7, 5), (7, -5),
        (9, 2), (9, -2)} := by
  decide

/-- Equation (15.4) of [BonehShoup2023]: `y² = x³ + 1` over `ZMod 11` has 12 points. -/
theorem natCard_E11 : Nat.card E11.toAffine.Point = 12 := by
  rw [E11.toAffine.natCard_point_eq_one_add_equation Δ_E11, Nat.card_eq_fintype_card]
  decide

-- The point count of `E11` is `11 + 1 - t` with `t = 0`, so the cubic character sum is `0`.
example : cubicCharSum E11.a₂ E11.a₄ E11.a₆ = 0 := by
  have h := natCard_point_eq_of_isCharNeTwoNF E11
  rw [natCard_E11, ZMod.card] at h
  omega

/-! ### Boneh–Shoup §15.3.2 (p. 623): quadratic twists over `ZMod 11`, `ZMod 7`, `ZMod 5`,
`ZMod 3` -/

theorem not_isSquare_two_zmod_eleven : ¬ IsSquare (2 : ZMod 11) := by decide

/-- Over `ZMod 11`, twisting `E11` by the non-residue `2` gives a curve with `2 * 11 + 2 - 12 = 12`
points (`t = 0`, so `p + 1 + t = 12`). -/
theorem natCard_quadraticTwist_E11 :
    Nat.card (E11.quadraticTwist 2).toAffine.Point = 12 := by
  have h := natCard_point_add_quadraticTwist_zmod E11 not_isSquare_two_zmod_eleven
  rw [natCard_E11] at h
  omega

-- Explicit action of `quadraticTwistEquationEquiv` and `quadraticTwistPointEquiv` across the
-- module boundary on `(1, 1)` for `2 y² = x³ + 1` over `ZMod 11` (`(c x, c² y) = (2, 4)`),
-- and the resulting cardinality identities.
example :
    (E11.quadraticTwistEquationEquiv (c := 2) (by decide) ⟨(1, 1), by decide⟩ :
      ZMod 11 × ZMod 11) = (2, 4) := by
  simp only [quadraticTwistEquationEquiv_apply]
  decide

example :
    ((E11.quadraticTwistEquationEquiv (c := 2) (by decide)).symm ⟨(2, 4), by decide⟩ :
      ZMod 11 × ZMod 11) = (1, 1) := by
  simp only [quadraticTwistEquationEquiv_symm_apply]
  ext
  · exact inv_mul_cancel₀ (by decide)
  · rw [show (4 : ZMod 11) = 2 ^ 2 by decide]
    exact inv_mul_cancel₀ (by decide)

example : E11.quadraticTwistPointEquiv (c := 2) (by decide) 0 = 0 ∧
    (E11.quadraticTwistPointEquiv (c := 2) (by decide)).symm 0 = 0 :=
  ⟨E11.quadraticTwistPointEquiv_zero _, E11.quadraticTwistPointEquiv_symm_zero _⟩

example :
    E11.quadraticTwistPointEquiv (c := 2) (by decide) (.some (2 : ZMod 11) 4 (by decide)) =
      WithZero.coe ((E11.quadraticTwistEquationEquiv (by decide)).symm ⟨(2, 4), by decide⟩) :=
  E11.quadraticTwistPointEquiv_some (by decide) _

example :
    (E11.quadraticTwistPointEquiv (c := 2) (by decide)).symm
      (WithZero.coe ⟨((1 : ZMod 11), 1), by decide⟩) =
      .some (2 * 1) (2 ^ 2 * 1) (by decide) :=
  E11.quadraticTwistPointEquiv_symm_coe (by decide) (by decide) (by decide)

example :
    Nat.card (E11.quadraticTwist 2).toAffine.Point =
      1 + Nat.card {xy : ZMod 11 × ZMod 11 // 2 * xy.2 ^ 2 = xy.1 ^ 3 + 0 * xy.1 + 1} :=
  E11.natCard_point_quadraticTwist_eq_one_add_of_isShortNF (by decide)

-- Basic algebraic identities on `quadraticTwist` and its discriminant.
example : E11.quadraticTwist 1 = E11 ∧
    (E11.quadraticTwist 2).quadraticTwist 3 = E11.quadraticTwist 6 ∧
    (E11.quadraticTwist 2).Δ = 2 ^ 6 * E11.Δ :=
  ⟨E11.quadraticTwist_one, E11.quadraticTwist_quadraticTwist 2 3, E11.quadraticTwist_Δ 2⟩

-- Direct count of the book's twisted equation `3 y² = x³ + 3 x + 3` over `ZMod 7` (`9` affine
-- solutions, hence `1 + 9 = 10` points).
example : Fintype.card {xy : ZMod 7 × ZMod 7 // 3 * xy.2 ^ 2 = xy.1 ^ 3 + 3 * xy.1 + 3} = 9 := by
  decide

theorem not_isSquare_three_zmod_seven : ¬ IsSquare (3 : ZMod 7) := by decide

/-- Over `ZMod 7`, `E7` has `6 = 7 + 1 - 2` points (`t = 2`), so its twist by the non-residue `3`
has `7 + 1 + 2 = 10` points. -/
theorem natCard_quadraticTwist_E7 :
    Nat.card (E7.quadraticTwist 3).toAffine.Point = 10 := by
  have h : (Nat.card (E7.quadraticTwist 3).toAffine.Point : ℤ) = Fintype.card (ZMod 7) + 1 + 2 :=
    E7.natCard_point_quadraticTwist_eq_of_eq_sub not_isSquare_three_zmod_seven
      (by rw [natCard_E7, ZMod.card]; rfl)
  rw [ZMod.card, Nat.cast_ofNat] at h
  exact_mod_cast h

/-- Over `ZMod 5`, `E5'` is the quadratic twist of `E5` by the non-residue `2`, and
`10 + 2 = 12`. -/
theorem quadraticTwist_E5_eq_E5' : E5.quadraticTwist 2 = E5' := by
  ext <;> decide

example : Nat.card E5.toAffine.Point + Nat.card E5'.toAffine.Point = 2 * 5 + 2 := by
  rw [← quadraticTwist_E5_eq_E5']
  exact natCard_point_add_quadraticTwist_zmod E5 (by decide)

-- Characteristic 3 with `a₂ ≠ 0` (in `IsCharNeTwoNF`, not in `IsShortNF`): `y² = x³ + x² + 2`
-- over `ZMod 3`, twisted by the non-residue `2`.
abbrev E3 : WeierstrassCurve (ZMod 3) := ofCubic 1 0 2

theorem Δ_E3 : E3.Δ ≠ 0 := by decide

instance : E3.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E3⟩

example : E3.a₂ ≠ 0 := by decide

example :
    Nat.card E3.toAffine.Point + Nat.card (E3.quadraticTwist 2).toAffine.Point = 2 * 3 + 2 :=
  natCard_point_add_quadraticTwist_zmod E3 (by decide)

/-! ### Counterexamples showing each hypothesis is needed -/

-- 1. `hc : ¬ IsSquare c` is needed: for the nonzero square `c = 4` in `ZMod 7`, the character sum
-- is unchanged (`cubicCharSum_mul_of_isSquare`) and the twist of `E7` also has 6 points
-- (`natCard_point_quadraticTwist_of_isSquare`), so the sum is `12 ≠ 16`.
example :
    cubicCharSum ((4 : ZMod 7) * 0) (4 ^ 2 * 3) (4 ^ 3 * 3) = cubicCharSum (0 : ZMod 7) 3 3 :=
  cubicCharSum_mul_of_isSquare 0 3 3 (by decide) (by decide)

example : Nat.card (E7.quadraticTwist 4).toAffine.Point = 6 := by
  rw [E7.natCard_point_quadraticTwist_of_isSquare (by decide) (by decide), natCard_E7]

example :
    Nat.card E7.toAffine.Point + Nat.card (E7.quadraticTwist 4).toAffine.Point ≠ 2 * 7 + 2 := by
  rw [E7.natCard_point_quadraticTwist_of_isSquare (by decide) (by decide), natCard_E7]
  decide

-- 2. `hc : c ≠ 0` is needed for `isElliptic_quadraticTwist` and
-- `natCard_point_quadraticTwist_eq_one_add`: at `c = 0`, `E7.quadraticTwist 0` is the singular
-- curve `y² = x³` (`Δ = 0`) with 7 nonsingular points (including `O`), whereas
-- `1 + #{0 · y² = x³ + 3x + 3}` is `8`.
example : ¬ (E7.quadraticTwist 0).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  decide

example :
    Nat.card (E7.quadraticTwist 0).toAffine.Point ≠
      1 + Nat.card {xy : ZMod 7 × ZMod 7 // 0 * xy.2 ^ 2 = xy.1 ^ 3 + E7.a₄ * xy.1 + E7.a₆} := by
  rw [(E7.quadraticTwist 0).toAffine.natCard_point_eq_one_add_nonsingular,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

-- 3. `[W.IsElliptic]` is needed for `natCard_point_add_quadraticTwist` (though not for
-- `natCard_equation_add_quadraticTwist`): the cuspidal cubic `y² = x³` over `ZMod 7` and its
-- twist by `3` have `7 + 7 = 14` affine solutions, but only `7 + 7 = 14 ≠ 16` nonsingular points.
abbrev W7_sing : WeierstrassCurve (ZMod 7) := ofCubic 0 0 0

example :
    Nat.card {xy : ZMod 7 × ZMod 7 // W7_sing.toAffine.Equation xy.1 xy.2} +
      Nat.card {xy : ZMod 7 × ZMod 7 // (W7_sing.quadraticTwist 3).toAffine.Equation xy.1 xy.2} =
      2 * 7 :=
  W7_sing.natCard_equation_add_quadraticTwist not_isSquare_three_zmod_seven

example :
    Nat.card W7_sing.toAffine.Point + Nat.card (W7_sing.quadraticTwist 3).toAffine.Point ≠
      2 * 7 + 2 := by
  rw [W7_sing.toAffine.natCard_point_eq_one_add_nonsingular,
    (W7_sing.quadraticTwist 3).toAffine.natCard_point_eq_one_add_nonsingular,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

-- 4. `[W.IsCharNeTwoNF]` is needed: the elliptic curve `y² + 2y = x³ + 3x + 2` over `ZMod 7`
-- (`a₃ = 2 ≠ 0`) has 6 points, and `quadraticTwist` (which ignores `a₁` and `a₃`) also gives a
-- 6-point curve, so the sum is `12 ≠ 16`.
abbrev W7_a₃ : WeierstrassCurve (ZMod 7) := ⟨0, 0, 2, 3, 2⟩

theorem Δ_W7_a₃ : W7_a₃.Δ ≠ 0 := by decide

instance : W7_a₃.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_W7_a₃⟩

example :
    Nat.card W7_a₃.toAffine.Point + Nat.card (W7_a₃.quadraticTwist 3).toAffine.Point ≠
      2 * 7 + 2 := by
  rw [W7_a₃.toAffine.natCard_point_eq_one_add_nonsingular,
    (W7_a₃.quadraticTwist 3).toAffine.natCard_point_eq_one_add_nonsingular,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

-- 5. Characteristic 2: over `ZMod 2` every element is a square (`¬ IsSquare c` is false) and
-- no `IsCharNeTwoNF` curve is elliptic, which is why `ringChar F ≠ 2` is not needed as an extra
-- hypothesis on `natCard_point_eq_of_isCharNeTwoNF` or `natCard_point_add_quadraticTwist`.
example (c : ZMod 2) : IsSquare c :=
  FiniteField.isSquare_of_char_two (by rw [ZMod.ringChar_zmod_n]) c

example (W : WeierstrassCurve (ZMod 2)) [W.IsCharNeTwoNF] : ¬ W.IsElliptic :=
  fun _ ↦ W.ringChar_ne_two_of_isCharNeTwoNF (ZMod.ringChar_zmod_n 2)

end CslibFrontierTests.EllipticCurveHasse
