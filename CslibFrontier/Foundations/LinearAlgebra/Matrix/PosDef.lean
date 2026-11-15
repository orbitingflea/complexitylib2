/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/PosDef.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive semidefinite `2 × 2` real matrices

A symmetric `2 × 2` real matrix `!![a, b; b, c]` with `a, c ≥ 0` and `b² ≤ ac` is positive
semidefinite (`Matrix.posSemidef_fin_two`).

## Main results

* `Matrix.posSemidef_fin_two`: the diagonal-and-determinant criterion for a symmetric `2 × 2` real
  matrix to be positive semidefinite.
-/

public section

namespace Matrix

/-- A symmetric `2 × 2` real matrix with nonnegative diagonal and nonnegative determinant is
positive semidefinite. -/
theorem posSemidef_fin_two {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : b ^ 2 ≤ a * c) :
    (!![a, b; b, c]).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, star_trivial]
    rcases ha.eq_or_lt with rfl | hapos
    · have hb : b = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (by simpa using h)
        (sq_nonneg b))
      subst hb
      nlinarith [mul_nonneg hc (sq_nonneg (x 1))]
    · refine (mul_nonneg_iff_of_pos_left hapos).1 ?_
      nlinarith [sq_nonneg (a * x 0 + b * x 1), mul_nonneg (sub_nonneg.2 h) (sq_nonneg (x 1))]

end Matrix
