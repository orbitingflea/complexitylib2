/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Decidability of affine Weierstrass equations and nonsingularity

Provides `Decidable` instances for `WeierstrassCurve.Affine.Equation` and
`WeierstrassCurve.Affine.Nonsingular` over any commutative ring with decidable equality.

## Main definitions

* `WeierstrassCurve.Affine.instDecidableEquation`: decidability of `W.Equation x y`.
* `WeierstrassCurve.Affine.instDecidableNonsingular`: decidability of `W.Nonsingular x y`.
-/

public section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- `W.Equation x y` is decidable when equality in `R` is decidable. -/
instance instDecidableEquation [DecidableEq R] (x y : R) : Decidable (W.Equation x y) :=
  decidable_of_iff' _ (W.equation_iff x y)

/-- `W.Nonsingular x y` is decidable when equality in `R` is decidable. -/
instance instDecidableNonsingular [DecidableEq R] (x y : R) : Decidable (W.Nonsingular x y) :=
  decidable_of_iff' _ (W.nonsingular_iff x y)

end WeierstrassCurve.Affine
