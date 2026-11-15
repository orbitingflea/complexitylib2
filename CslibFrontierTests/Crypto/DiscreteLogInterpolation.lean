/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiscreteLog.Interpolation
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
import CslibFrontier.Tactic.PolyTime

/-!
# Lagrange interpolation in polynomial time: checked instances

An ordinary `module` client of `CslibFrontier.Crypto.Computational.DiscreteLog.Interpolation`
([BonehShoup2023], Lemma 22.1 and Corollary 22.2).

* Modulo `7`, the computed coefficients of the nodes `1, 2, 3` are `3, 4, 1` at the point `0` and
  `3, 6, 6` at the point `5`, and Lemma 22.1 with them recovers the value `3` of `2 X + 3` at `0`.
* Both hypotheses of `lagrangeWeightNat_cast_eq_eval_basis` are needed: nodes equal modulo `q`,
  and a node outside the list, each give a computed coefficient different from the value of the
  Lagrange basis polynomial.
* In any group of any prime-order group family, two shares of a polynomial of degree at most one
  at the nodes `1, 2` give its constant term in the exponent, and so do enough shares of any
  polynomial.
* The two certificates apply to inputs computed from an encoded input.
-/

public section

namespace CslibFrontierTests.DiscreteLogInterpolation

open Polynomial Turing.MultiTapeTM
open Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### Concrete coefficients modulo `7` -/

/-- Modulo `7`, the coefficients of the nodes `1, 2, 3` at the point `0` are `3, 4, 1`. -/
example : (lagrangeWeightNat 7 [1, 2, 3] 1 0 : ZMod 7) = 3 ∧
    (lagrangeWeightNat 7 [1, 2, 3] 2 0 : ZMod 7) = 4 ∧
    (lagrangeWeightNat 7 [1, 2, 3] 3 0 : ZMod 7) = 1 := by
  simp only [lagrangeWeightNat_cast]
  decide +kernel

/-- At the point `5` they are `3, 6, 6`. -/
example : (lagrangeWeightNat 7 [1, 2, 3] 1 5 : ZMod 7) = 3 ∧
    (lagrangeWeightNat 7 [1, 2, 3] 2 5 : ZMod 7) = 6 ∧
    (lagrangeWeightNat 7 [1, 2, 3] 3 5 : ZMod 7) = 6 := by
  simp only [lagrangeWeightNat_cast]
  decide +kernel

/-- The polynomial `2 X + 3` modulo `7` has the values `5, 0, 2` at `1, 2, 3`; Lemma 22.1 with the
computed coefficients at `0` gives its value `3` there. -/
example : (C 2 * X + C 3 : (ZMod 7)[X]).eval ((0 : ℕ) : ZMod 7) =
    (([1, 2, 3] : List ℕ).map fun j =>
      (lagrangeWeightNat 7 [1, 2, 3] j 0 : ZMod 7) *
        (C 2 * X + C 3 : (ZMod 7)[X]).eval (j : ZMod 7)).sum :=
  eval_eq_sum_lagrangeWeightNat_mul_eval (by decide +kernel)
    (degree_linear_le.trans_lt (by decide)) 0

example : (([1, 2, 3] : List ℕ).map fun j =>
    (lagrangeWeightNat 7 [1, 2, 3] j 0 : ZMod 7) *
      (C 2 * X + C 3 : (ZMod 7)[X]).eval (j : ZMod 7)).sum = 3 := by
  simp only [lagrangeWeightNat_cast, eval_add, eval_mul, eval_C, eval_X]
  decide +kernel

/-- A single node has the coefficient `1` at every point. -/
example (q j x : ℕ) [Fact q.Prime] : (lagrangeWeightNat q [j] j x : ZMod q) = 1 := by
  simp [lagrangeWeightNat_cast]

/-! ### The hypotheses of `lagrangeWeightNat_cast_eq_eval_basis` are needed -/

/-- Nodes must be distinct modulo `q`: for the nodes `1, 6` modulo `5`, the computed coefficient
of `1` is `1`, and the Lagrange basis polynomial of `1` is `0`. -/
example : (lagrangeWeightNat 5 [1, 6] 1 0 : ZMod 5) ≠
    (Lagrange.basis ([1, 6] : List ℕ).toFinset (Nat.cast : ℕ → ZMod 5) 1).eval
      ((0 : ℕ) : ZMod 5) := by
  have h6 : (6 : ZMod 5) = 1 := by decide
  have herase : ([1, 6] : List ℕ).toFinset.erase 1 = {6} := by decide
  rw [lagrangeWeightNat_cast, Lagrange.eval_basis, herase]
  simp [h6]

/-- The node must be in the list: for the single node `1` modulo `5`, the computed coefficient of
`6` is `1`, and the Lagrange basis polynomial of `6` is `0`. -/
example : (lagrangeWeightNat 5 [1] 6 0 : ZMod 5) ≠
    (Lagrange.basis ([1] : List ℕ).toFinset (Nat.cast : ℕ → ZMod 5) 6).eval
      ((0 : ℕ) : ZMod 5) := by
  have h6 : (6 : ZMod 5) = 1 := by decide
  have herase : ([1] : List ℕ).toFinset.erase 6 = {1} := by decide
  rw [lagrangeWeightNat_cast, Lagrange.eval_basis, herase]
  simp [h6]

/-! ### Interpolation in the exponent, in any group of any family -/

/-- The nodes `1, 2` are distinct modulo every prime. -/
theorem nodup_one_two (p : ℕ) [Fact p.Prime] :
    (([1, 2] : List ℕ).map (Nat.cast : ℕ → ZMod p)).Nodup := by
  simp only [List.map_cons, List.map_nil, Nat.cast_one, Nat.cast_ofNat, List.nodup_cons,
    List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true, and_self]
  intro h
  have h1 : ((2 : ZMod p) - 1) = 0 := sub_eq_zero.mpr h.symm
  norm_num at h1

/-- Two shares `(a + b) • h` and `(a + 2 b) • h` of the polynomial `b X + a` at the nodes `1, 2`
combine to `a • h` at the point `0`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) (a b : ZMod (F.order d)) (h : F.Carrier d) :
    F.lagrangeCombine d 0 [(1, (b * 1 + a) • h), (2, (b * 2 + a) • h)] = a • h := by
  have key := lagrangeCombine_eval_smul d (nodup_one_two (F.order d)) (f := C b * X + C a)
    (degree_linear_le.trans_lt (by decide)) 0 h
  simpa using key

/-- Reconstruction in the exponent: from `f(j) • h` at nodes distinct modulo the order, as many
as the degree of `f` plus one, the combination at the point `0` is `f.coeff 0 • h`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) {nodes : List ℕ}
    (hnodes : (nodes.map (Nat.cast : ℕ → ZMod (F.order d))).Nodup) {f : (ZMod (F.order d))[X]}
    (hf : f.degree < nodes.length) (h : F.Carrier d) :
    F.lagrangeCombine d 0 (nodes.map fun j : ℕ => (j, f.eval (j : ZMod (F.order d)) • h)) =
      f.coeff 0 • h := by
  rw [lagrangeCombine_eval_smul d hnodes hf 0 h, Nat.cast_zero, coeff_zero_eq_eval_zero]

/-! ### Efficiency certificates in use -/

/-- The coefficient is computable from the group description, the nodes, the node and the
point. -/
example (F : PrimeOrderGroupFamily) :
    ComputableInPolyTime
      (fun p : F.Desc × List ℕ × ℕ × ℕ => lagrangeWeightNat (F.order p.1) p.2.1 p.2.2.1 p.2.2.2)
      (encPair F.encDesc (encPair (encList encNat) (encPair encNat encNat))) encNat := by
  fun_prop

/-- The combination of the elements `j • g` at a list of nodes read from the input is computable
from the group description, the point and the nodes. -/
example (F : PrimeOrderGroupFamily) :
    ComputableInPolyTime
      (fun a : F.Desc × ℕ × List ℕ => F.encode a.1 (F.lagrangeCombine a.1 a.2.1
        (a.2.2.map fun j : ℕ => (j, (j : ZMod (F.order a.1)) • F.generator a.1))))
      (encPair F.encDesc (encPair encNat (encList encNat))) encBits := by
  refine computableInPolyTime_encode_lagrangeCombine (by fun_prop) (by fun_prop) ?_
  simp only [List.map_map, Function.comp_def]
  fun_prop

end CslibFrontierTests.DiscreteLogInterpolation
