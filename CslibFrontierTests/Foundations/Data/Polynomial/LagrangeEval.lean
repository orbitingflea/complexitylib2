/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
public import Mathlib.Algebra.Field.ZMod

/-!
# The value of a polynomial at any point from its values at the nodes: checked instances

An ordinary `module` client of `CslibFrontier.Foundations.Data.Polynomial.LagrangeEval`
([BonehShoup2023], Lemma 22.1 and Corollary 22.2).

* Over `ℚ`, the weights of the nodes `1, 2, 3` at the point `4` are `1, -3, 3`, and every
  polynomial of degree at most two satisfies `f(4) = f(1) - 3 f(2) + 3 f(3)`.
* Both hypotheses of `Lagrange.eval_eq_sum_eval_basis_mul_eval` are needed: the identity fails for
  `X ^ 3` on three nodes, and for repeated nodes.
* Over `ZMod 7`, the weights of the nodes `1, 2` at `5` are `4` and `4`, and the module form holds
  in `ZMod 7 × ZMod 7`.
-/

public section

namespace CslibFrontierTests.LagrangeEval

open Polynomial Finset

/-- Nodes `1, 2, 3` over `ℚ`. -/
def nodes : Fin 3 → ℚ := fun i => ((i : ℕ) : ℚ) + 1

theorem nodes_injective : Function.Injective nodes := by
  intro i j h
  have : ((i : ℕ) : ℚ) = (j : ℕ) := by simpa [nodes] using h
  exact Fin.ext (by exact_mod_cast this)

theorem erase_zero : (univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
theorem erase_one : (univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
theorem erase_two : (univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide

/-! ### The weights of the nodes `1, 2, 3` at the point `4` are `1, -3, 3` -/

example : (Lagrange.basis univ nodes 0).eval 4 = 1 := by
  rw [Lagrange.eval_basis, erase_zero]; norm_num [nodes]

example : (Lagrange.basis univ nodes 1).eval 4 = -3 := by
  rw [Lagrange.eval_basis, erase_one]; norm_num [nodes]

example : (Lagrange.basis univ nodes 2).eval 4 = 3 := by
  rw [Lagrange.eval_basis, erase_two]; norm_num [nodes]

/-- Lemma 22.1 on a quadratic: `f(4) = f(1) - 3 f(2) + 3 f(3)` for every `f` of degree at most
two. -/
example {f : ℚ[X]} (hf : f.natDegree ≤ 2) :
    f.eval 4 = f.eval 1 - 3 * f.eval 2 + 3 * f.eval 3 := by
  have hdeg : f.degree < #(univ : Finset (Fin 3)) := by
    rw [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hf)
  rw [Lagrange.eval_eq_sum_eval_basis_mul_eval nodes_injective.injOn hdeg 4]
  simp only [Lagrange.eval_basis, Fin.sum_univ_three, erase_zero, erase_one, erase_two]
  norm_num [nodes]
  ring

/-! ### Both hypotheses are needed -/

/-- The degree bound is needed: `X ^ 3` has degree `3 = #s`, and the combination of its values at
`1, 2, 3` with the weights at `0` is `6`, not `0`. -/
example : ¬ ((X ^ 3 : ℚ[X]).eval 0 = ∑ i : Fin 3,
    (Lagrange.basis univ nodes i).eval 0 * (X ^ 3 : ℚ[X]).eval (nodes i)) := by
  simp only [Lagrange.eval_basis, Fin.sum_univ_three, erase_zero, erase_one, erase_two]
  norm_num [nodes]

/-- Injectivity of the nodes is needed: with both nodes equal to `1`, both weights vanish, so the
constant polynomial `1` is not recovered. -/
example : ¬ ((1 : ℚ[X]).eval 5 = ∑ i : Fin 2,
    (Lagrange.basis univ (fun _ : Fin 2 => (1 : ℚ)) i).eval 5 * (1 : ℚ[X]).eval 1) := by
  simp [Lagrange.eval_basis]

/-! ### Over `ZMod 7`, and in a module -/

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Over `ZMod 7`, the weight of the node `1` among the nodes `1, 2` at the point `5` is `4`. -/
example : (Lagrange.basis ({0, 1} : Finset (Fin 2)) (fun i => ((i : ℕ) : ZMod 7) + 1) 0).eval 5
    = 4 := by
  have h : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [Lagrange.eval_basis, h, prod_singleton, div_eq_iff (by decide)]; decide

/-- The weight of the node `2` among the nodes `1, 2` at the point `5` is also `4`. -/
example : (Lagrange.basis ({0, 1} : Finset (Fin 2)) (fun i => ((i : ℕ) : ZMod 7) + 1) 1).eval 5
    = 4 := by
  have h : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  rw [Lagrange.eval_basis, h, prod_singleton, div_eq_iff (by decide)]; decide

/-- The identity behind Corollary 22.2 in the module `ZMod 7 × ZMod 7`, for the polynomial
`3 X + 2`, the nodes `1, 2`, the point `5` and `h = (1, 3)`. -/
example : (C 3 * X + C 2 : (ZMod 7)[X]).eval 5 • ((1, 3) : ZMod 7 × ZMod 7) =
    ∑ i : Fin 2, (Lagrange.basis univ (fun i : Fin 2 => ((i : ℕ) : ZMod 7) + 1) i).eval 5 •
      (C 3 * X + C 2 : (ZMod 7)[X]).eval (((i : ℕ) : ZMod 7) + 1) • ((1, 3) : ZMod 7 × ZMod 7) :=
  Lagrange.eval_smul_eq_sum_eval_basis_smul (v := fun i : Fin 2 => ((i : ℕ) : ZMod 7) + 1)
    (by decide : Function.Injective fun i : Fin 2 => ((i : ℕ) : ZMod 7) + 1).injOn
    (by rw [card_univ, Fintype.card_fin]
        exact degree_linear_le.trans_lt (by exact_mod_cast (by decide : 1 < 2))) 5 _

/-- Both sides of the previous example are `(3, 2)`: `f(5) = 3`, and `f(1) = 5`, `f(2) = 1` with
the weights `4, 4` give `4 • 5 • h + 4 • 1 • h = 3 • h`. -/
example : (C 3 * X + C 2 : (ZMod 7)[X]).eval 5 • ((1, 3) : ZMod 7 × ZMod 7) = (3, 2) := by
  simp only [eval_add, eval_C, eval_mul, eval_X]
  decide

end CslibFrontierTests.LagrangeEval
