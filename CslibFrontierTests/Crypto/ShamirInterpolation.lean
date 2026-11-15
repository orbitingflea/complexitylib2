/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Interpolation
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval

/-!
# Shamir shares as fixed linear combinations: checked instances

An ordinary `module` client of `CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Interpolation`
([BonehShoup2023], Section 22.5.2), on two-out-of-three sharing over `ZMod 5` at the points
`1, 2, 3` (`threshold = 1`), with the sharing polynomial `3 + 2 X` and the shares `0, 2, 4`.

* Linearity of the shares with `L = {0}`: both weights for party `2` are `3`, and its share is
  `3 • 3 + 3 • 0 = 4`. With `L = ∅` the combination is the secret `3`, so the size bound on `L` is
  needed.
* The same identity, and linearity of the secret for the authorized set `{0, 1}`, act on the
  module `ZMod 5 × ZMod 5`.
* The weights at `0` of `Shamir/Linear.lean` for the nodes `1, 2` are `2` and `4`, by the bridge
  to `Lagrange.eval_basis`.
-/

public section

namespace CslibFrontierTests.ShamirInterpolation

open Finset
open Cslib.Crypto.Protocols.SecretSharing Cslib.Crypto.Protocols.SecretSharing.Shamir

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Two-out-of-three sharing over `ZMod 5` at the points `1, 2, 3` (`threshold = 1`: the book's
`t = 2`). -/
def params3 : Params (ZMod 5) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

/-- The sharing polynomial of the secret `3` is `3 + 2 X`. -/
def r3 : Randomness params3 := ![2]

theorem share_r3 (i : Fin 3) : share params3 r3 3 i = 3 + params3.point i * 2 := by
  have hdeg : (Polynomial.tailPolynomial params3.threshold r3).degree ≤ 0 :=
    Nat.WithBot.lt_one_iff_le_zero.1 (Polynomial.tailPolynomial_degree_lt 1 r3)
  have hc : (Polynomial.tailPolynomial params3.threshold r3).coeff 0 = 2 :=
    Polynomial.tailPolynomial_coeff 1 r3 0
  rw [share, Polynomial.sharingPolynomial_eval, _root_.Polynomial.eq_C_of_degree_le_zero hdeg, hc,
    _root_.Polynomial.eval_C]

/-- The shares of `3` are `0, 2, 4`. -/
example : (fun i => share params3 r3 3 i) = ![0, 2, 4] := by
  funext i; rw [share_r3]; fin_cases i <;> decide

/-! ### Linearity of the shares with `L = {0}` -/

/-- The weight of the secret for party `2` is `3`. -/
example :
    (Lagrange.basis (insertNone {0}) params3.pointOrZero none).eval (params3.point 2) = 3 := by
  have h : (insertNone ({0} : Finset (Fin 3))).erase none = {some 0} := by decide
  rw [Lagrange.eval_basis, h, prod_singleton, Params.pointOrZero_none, Params.pointOrZero_some,
    div_eq_iff (by decide)]
  decide

/-- The weight of the share of party `0` for party `2` is `3`. -/
example : (Lagrange.basis (insertNone {0}) params3.pointOrZero (some 0)).eval (params3.point 2)
    = 3 := by
  have h : (insertNone ({0} : Finset (Fin 3))).erase (some 0) = {none} := by decide
  rw [Lagrange.eval_basis, h, prod_singleton, Params.pointOrZero_none, Params.pointOrZero_some,
    div_eq_iff (by decide)]
  decide

/-- The identity for party `2` and `L = {0}`; with the weights `3, 3` it reads `4 = 3 • 3 + 3 • 0`.
-/
example : share params3 r3 3 2 =
    (Lagrange.basis (insertNone {0}) params3.pointOrZero none).eval (params3.point 2) * 3 +
      ∑ l ∈ ({0} : Finset (Fin 3)),
        (Lagrange.basis (insertNone {0}) params3.pointOrZero (some l)).eval (params3.point 2) *
          share params3 r3 3 l :=
  share_eq_eval_basis_mul_add_sum params3 r3 3 (by decide) 2

/-- The size bound on `L` is needed: with `L = ∅` the right-hand side is the secret `3`, and the
share of party `2` is `4`. -/
example : ¬ (share params3 r3 3 2 =
    (Lagrange.basis (insertNone ∅) params3.pointOrZero none).eval (params3.point 2) * 3 +
      ∑ l ∈ (∅ : Finset (Fin 3)),
        (Lagrange.basis (insertNone ∅) params3.pointOrZero (some l)).eval (params3.point 2) *
          share params3 r3 3 l) := by
  have h : (insertNone (∅ : Finset (Fin 3))).erase none = ∅ := by decide
  rw [share_r3, Lagrange.eval_basis, h]
  decide

/-! ### The same identities in the module `ZMod 5 × ZMod 5` -/

example (h : ZMod 5 × ZMod 5) : share params3 r3 3 2 • h =
    (Lagrange.basis (insertNone {0}) params3.pointOrZero none).eval (params3.point 2) •
        (3 : ZMod 5) • h +
      ∑ l ∈ ({0} : Finset (Fin 3)),
        (Lagrange.basis (insertNone {0}) params3.pointOrZero (some l)).eval (params3.point 2) •
          share params3 r3 3 l • h :=
  share_smul_eq_eval_basis_smul_add_sum params3 r3 3 (by decide) 2 h

/-- Linearity of the secret for the authorized set `{0, 1}`: the weighted shares acting on `h`
give `3 • h`. -/
example (h : ZMod 5 × ZMod 5) :
    ∑ i : ({0, 1} : Finset (Fin 3)),
      Polynomial.lagrangeWeightAtZero (fun i : ({0, 1} : Finset (Fin 3)) => params3.point i) i •
        share params3 r3 3 i • h = (3 : ZMod 5) • h :=
  sum_lagrangeWeightAtZero_smul_share_smul params3 r3 3 (by unfold authorized; decide) h

/-! ### The bridge to the existing weights at `0`: for nodes `1, 2` over `ZMod 5` they are `2`
and `4` -/

example : Polynomial.lagrangeWeightAtZero (fun i : Fin 2 => ((i : ℕ) : ZMod 5) + 1) 0 = 2 := by
  have h : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [Polynomial.lagrangeWeightAtZero_eq_eval_basis, Lagrange.eval_basis, h, prod_singleton,
    div_eq_iff (by decide)]
  decide

example : Polynomial.lagrangeWeightAtZero (fun i : Fin 2 => ((i : ℕ) : ZMod 5) + 1) 1 = 4 := by
  have h : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
  rw [Polynomial.lagrangeWeightAtZero_eq_eval_basis, Lagrange.eval_basis, h, prod_singleton,
    div_eq_iff (by decide)]
  decide

end CslibFrontierTests.ShamirInterpolation
