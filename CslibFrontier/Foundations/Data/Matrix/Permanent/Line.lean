/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Permanent.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Permanent of a matrix along an affine line

For `n × n` matrices `A` and `B` over a commutative semiring `R`, the map
`x ↦ (A + x • B).permanent` is the evaluation of a univariate polynomial
`Matrix.permanentLinePoly A B : R[X]` of degree at most `n`. This is the algebraic heart of
Lipton's random self-reduction of the permanent: querying `(A + x • B).permanent` at `n + 1`
distinct points determines `A.permanent = (Matrix.permanentLinePoly A B).eval 0` by Lagrange
interpolation.

## Main definitions

* `Matrix.permanentLinePoly`: the univariate polynomial whose evaluation at `x` is
  `(A + x • B).permanent`.

## Main results

* `Matrix.eval_permanentLinePoly`: `(permanentLinePoly A B).eval x = (A + x • B).permanent`.
* `Matrix.eval_zero_permanentLinePoly`: `(permanentLinePoly A B).eval 0 = A.permanent`.
* `Matrix.natDegree_permanentLinePoly_le`: `(permanentLinePoly A B).natDegree ≤ Fintype.card ι`.
* `Matrix.exists_natDegree_le_eval_eq_permanent_add_smul`: `x ↦ (A + x • B).permanent` agrees with
  a polynomial of degree at most `Fintype.card ι`.
-/

public section

namespace Matrix

open Finset Polynomial

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The univariate polynomial whose evaluation at `x : R` is `(A + x • B).permanent`. -/
noncomputable def permanentLinePoly (A B : Matrix ι ι R) : R[X] :=
  (Matrix.of fun i j => C (A i j) + X * C (B i j)).permanent

/-- Evaluating `permanentLinePoly A B` at `x` gives `(A + x • B).permanent`. -/
@[simp]
theorem eval_permanentLinePoly (A B : Matrix ι ι R) (x : R) :
    (permanentLinePoly A B).eval x = (A + x • B).permanent := by
  simp [permanentLinePoly, Matrix.permanent, eval_finsetSum, eval_prod, mul_comm x]

/-- Evaluating `permanentLinePoly A B` at `0` recovers `A.permanent`. -/
theorem eval_zero_permanentLinePoly (A B : Matrix ι ι R) :
    (permanentLinePoly A B).eval 0 = A.permanent := by
  simp [eval_permanentLinePoly]

/-- The polynomial `x ↦ (A + x • B).permanent` has degree at most `Fintype.card ι`. -/
theorem natDegree_permanentLinePoly_le (A B : Matrix ι ι R) :
    (permanentLinePoly A B).natDegree ≤ Fintype.card ι := by
  unfold permanentLinePoly Matrix.permanent
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i : ι, (C (A (σ i) i) + X * C (B (σ i) i)).natDegree
      ≤ ∑ _i : ι, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact (Polynomial.natDegree_mul_le).trans (by simp [Polynomial.natDegree_X_le])
    _ = Fintype.card ι := by simp

/-- The permanent along the line `x ↦ A + x • B` agrees with a polynomial of degree at most
`Fintype.card ι`. -/
theorem exists_natDegree_le_eval_eq_permanent_add_smul (A B : Matrix ι ι R) :
    ∃ P : R[X], P.natDegree ≤ Fintype.card ι ∧ ∀ x, P.eval x = (A + x • B).permanent :=
  ⟨permanentLinePoly A B, natDegree_permanentLinePoly_le A B, eval_permanentLinePoly A B⟩

end Matrix
