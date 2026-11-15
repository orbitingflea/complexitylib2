/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Lagrange.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The value of a polynomial at any point from its values at the nodes

Over a field, a polynomial `f` of degree less than `#s` is the Lagrange interpolant of its values
at nodes `v` injective on `s` (`Lagrange.eq_interpolate`). Evaluating at a point `x` gives
`f.eval x = ∑ i ∈ s, (Lagrange.basis s v i).eval x * f.eval (v i)`: the value at `x` is a fixed
linear combination of the values at the nodes, with weights that depend on `s`, `v` and `x` but
not on `f`. This is the identity of Lemma 22.1 ("linearity of interpolation") of
[BonehShoup2023], with the weights `λ_i = ∏ j ∈ s.erase i, (x - v j) / (v i - v j)` of its proof.
Acting on a module over the field, the same identity is the one behind Corollary 22.2
("interpolation in the exponent").

Mathlib evaluates a Lagrange basis polynomial only at a node (`Lagrange.eval_basis_self`,
`Lagrange.eval_basis_of_ne`).

The book states both results over `Z_q` for a prime `q`, for a set `J ⊆ Z_q` of `t` nodes and
polynomials of degree at most `t - 1`, and writes the corollary in a group of order `q`,
multiplicatively. Here the field is arbitrary, the nodes are a function `v` injective on an index
set `s` and the degree bound is `f.degree < #s`, and the group is any module over the field,
written additively (`f.eval x • h` for the book's `h^{ω(j*)}`). The book also says that the
weights, and the combination in the exponent, are efficiently computable; over an arbitrary field
there is nothing to encode, so those clauses are proved separately, over `ZMod q` for the order
`q` of a group of a prime-order group family, in
`CslibFrontier.Crypto.Computational.DiscreteLog.Interpolation`.

## Main results

* `Lagrange.eval_basis`: the value of a Lagrange basis polynomial at any point, as a product of
  quotients.
* `Lagrange.eval_eq_sum_eval_basis_mul_eval`: the identity of Lemma 22.1 of [BonehShoup2023].
* `Lagrange.eval_smul_eq_sum_eval_basis_smul`: the identity behind Corollary 22.2 of
  [BonehShoup2023], in a module.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 22.1.1, Lemma 22.1 (p. 928) and Corollary 22.2 (p. 929).
-/

public section

namespace Lagrange

open Polynomial Finset

variable {F ι : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F}

/-- The value at any point `x` of the Lagrange basis polynomial of the node `i`: the product of the
quotients `(x - v j) / (v i - v j)` over the other indices `j ∈ s`. This is the coefficient `λ_i`
of Lemma 22.1 of [BonehShoup2023]. No hypothesis is needed: if `v j = v i` for some `j ≠ i`, both
sides are `0`. -/
theorem eval_basis (s : Finset ι) (v : ι → F) (i : ι) (x : F) :
    (Lagrange.basis s v i).eval x = ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
  simp [Lagrange.basis, basisDivisor, eval_prod, div_eq_inv_mul]

/-- **The identity of Lemma 22.1** of [BonehShoup2023] ("linearity of interpolation"): for nodes
`v` injective on `s` and a polynomial `f` of degree less than `#s`, the value of `f` at any point
`x` is the combination of its values at the nodes with the weights `(Lagrange.basis s v i).eval x`,
which do not depend on `f`.

The book works over `Z_q` with `J ⊆ Z_q` of size `t` and degree at most `t - 1`; here the field is
arbitrary. The book's claim that the weights are efficiently computable is
`Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_lagrangeWeightNat`. -/
theorem eval_eq_sum_eval_basis_mul_eval (hv : Set.InjOn v s) {f : F[X]} (hf : f.degree < #s)
    (x : F) : f.eval x = ∑ i ∈ s, (Lagrange.basis s v i).eval x * f.eval (v i) := by
  conv_lhs => rw [eq_interpolate hv hf]
  simp [interpolate_apply, eval_finsetSum, mul_comm]

/-- **The identity behind Corollary 22.2** of [BonehShoup2023] ("interpolation in the exponent"),
in a module `M` over the field and written additively: from the elements `f.eval (v i) • h` at
nodes injective on `s`, the element `f.eval x • h` is their combination with the weights of
`Lagrange.eval_eq_sum_eval_basis_mul_eval`.

The book writes this in a group of prime order `q`, multiplicatively, as
`h^{ω(j*)} = ∏ (h^{ω(j)})^{λ_j}`. Its claim that the combination is efficiently computable is
`Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encode_lagrangeCombine`. -/
theorem eval_smul_eq_sum_eval_basis_smul {M : Type*} [AddCommMonoid M] [Module F M]
    (hv : Set.InjOn v s) {f : F[X]} (hf : f.degree < #s) (x : F) (h : M) :
    f.eval x • h = ∑ i ∈ s, (Lagrange.basis s v i).eval x • f.eval (v i) • h := by
  rw [eval_eq_sum_eval_basis_mul_eval hv hf x, sum_smul]
  simp [mul_smul]

end Lagrange
