/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval

/-!
# Shamir shares as fixed linear combinations of other shares

Two of the three properties of Shamir sharing that the book's threshold schemes use
([BonehShoup2023], Section 22.5.2, p. 977). The book derives both on p. 978 from Lemma 22.1
(p. 928); the third, independence of the shares, is not in this file:

* **Linearity of the shares.** For a set `L` of `threshold` parties (the book's `t - 1`) and any
  party `i`, the share of `i` is a fixed linear combination of the secret and the shares of the
  parties in `L`, with weights that depend only on `L` and `i`. The nodes are those of `L` together
  with `0`, where the sharing polynomial takes the secret (`Params.pointOrZero`), and the weights
  are the values at the point of `i` of their Lagrange basis polynomials.
* **Linearity of the secret.** For an authorized set `s`, the secret is a fixed linear combination
  of the shares of `s`. Over the field this is `reconstruct_share_eq_secret` with
  `Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero`; this file gives its action on a module,
  which is how threshold schemes combine signature or decryption shares.

The forms acting on a module over the field are the identity behind Corollary 22.2 of the book
("interpolation in the exponent"), written additively. The weights at `0` already used by
`CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear` (`Polynomial.lagrangeWeightAtZero`)
are the values at `0` of Lagrange basis polynomials
(`Polynomial.lagrangeWeightAtZero_eq_eval_basis`), so `Lagrange.eval_basis` gives their product
formula.

The book's threshold `t` (any `t` shares reconstruct) is `params.threshold + 1` here, so "`J` of
size `t`" is `authorized params J`, and "`L` of size `t - 1`" is `params.threshold ≤ #L`; larger
sets `L` are allowed. These identities define no algorithm and carry no cost statement; the
polynomial-time forms of Lemma 22.1 and Corollary 22.2, over the order of a group of a
prime-order group family, are in `CslibFrontier.Crypto.Computational.DiscreteLog.Interpolation`.

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Params.pointOrZero`: the evaluation points with
  `0` added, indexed by `Option Party`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.lagrangeWeightAtZero_eq_eval_basis`:
  the weights at `0`, `Polynomial.lagrangeWeightAtZero`, are values of Lagrange basis polynomials.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_eq_eval_basis_mul_add_sum`: linearity of
  the shares.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_smul_eq_eval_basis_smul_add_sum`: linearity
  of the shares, acting on a module.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.sum_lagrangeWeightAtZero_smul_share_smul`:
  linearity of the secret, acting on a module.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 22.5.2 (pp. 977–978), Lemma 22.1 and Corollary 22.2
  (pp. 928–929).
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir

open Finset

/-- The weights at `0`, `Polynomial.lagrangeWeightAtZero`, are the values at `0` of the Lagrange
basis polynomials over all nodes, so `Lagrange.eval_basis` gives their product formula. -/
theorem Polynomial.lagrangeWeightAtZero_eq_eval_basis {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq ι] (x : ι → F) (i : ι) :
    Polynomial.lagrangeWeightAtZero x i = (Lagrange.basis univ x i).eval 0 := by
  -- `lagrangeWeightAtZero` is not exposed: read it off the reconstruction of a unit share vector.
  have h := Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero x (Pi.single i 1)
  rw [Fintype.sum_eq_single i (fun j hj => by simp [hj]), Pi.single_eq_same, one_mul] at h
  rw [← h, Polynomial.reconstruct, _root_.Polynomial.constantCoeff_apply,
    _root_.Polynomial.coeff_zero_eq_eval_zero]
  have : Lagrange.interpolate univ x (Pi.single i (1 : F)) = Lagrange.basis univ x i := by
    rw [Lagrange.interpolate_apply, sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [← this]
  congr!

variable {F Party : Type*} [Field F] [Fintype Party]

/-- The evaluation points with `0` added: `none ↦ 0`, where the sharing polynomial takes the
secret, and `some i ↦ params.point i`. These are the nodes `L ∪ {0}` implicit in the book's
derivation of linearity of the shares from Lemma 22.1 with `j* = i` ([BonehShoup2023], p. 978),
indexed so that the secret has its own index. -/
def Params.pointOrZero (params : Params F Party) : Option Party → F :=
  fun o => o.elim 0 params.point

@[simp] theorem Params.pointOrZero_none (params : Params F Party) :
    params.pointOrZero none = 0 := by
  simp [Params.pointOrZero]

@[simp] theorem Params.pointOrZero_some (params : Params F Party) (i : Party) :
    params.pointOrZero (some i) = params.point i := by
  simp [Params.pointOrZero]

theorem Params.pointOrZero_injective (params : Params F Party) :
    Function.Injective params.pointOrZero := by
  rintro (_ | a) (_ | b) h
  · rfl
  · exact absurd h.symm (params.point_nonzero b)
  · exact absurd h (params.point_nonzero a)
  · exact congrArg some (params.point_injective h)

variable [DecidableEq Party]

/-- **Linearity of the shares** ([BonehShoup2023], Section 22.5.2, p. 977): for a set `L` of at
least `threshold` parties and any party `i`, the share of `i` is the combination of the secret `a`
and the shares of the parties in `L` with the values at `params.point i` of the Lagrange basis
polynomials of the nodes `L ∪ {0}`. The weights depend only on `params`, `L` and `i`. As on p. 978
of the book, this is Lemma 22.1 (p. 928) at `j* = point i`.

The book takes `#L = t - 1`, which is `params.threshold` here; the hypothesis is needed, since
with fewer parties the combination is the wrong value. -/
theorem share_eq_eval_basis_mul_add_sum (params : Params F Party) (r : Randomness params) (a : F)
    {L : Finset Party} (hL : params.threshold ≤ #L) (i : Party) :
    share params r a i =
      (Lagrange.basis (insertNone L) params.pointOrZero none).eval (params.point i) * a +
        ∑ l ∈ L, (Lagrange.basis (insertNone L) params.pointOrZero (some l)).eval
          (params.point i) * share params r a l := by
  have hdeg : (Polynomial.sharingPolynomial a
      (Polynomial.tailPolynomial params.threshold r)).degree < #(insertNone L) := by
    refine (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a params.threshold
      r).trans_le ?_
    rw [card_insertNone]
    exact_mod_cast Nat.succ_le_succ hL
  have h := Lagrange.eval_eq_sum_eval_basis_mul_eval
    (params.pointOrZero_injective.injOn (s := ↑(insertNone L))) hdeg (params.point i)
  rw [sum_insertNone] at h
  simpa [share] using h

/-- **Linearity of the shares, acting on a module**: `share_eq_eval_basis_mul_add_sum` applied to
an element `h` of a module over the field. This is the identity behind Corollary 22.2 of
[BonehShoup2023] with the nodes `L ∪ {0}`, written additively: from `a • h` and the elements
`share params r a l • h` for `l ∈ L`, every `share params r a i • h` is a fixed combination. -/
theorem share_smul_eq_eval_basis_smul_add_sum {M : Type*} [AddCommMonoid M] [Module F M]
    (params : Params F Party) (r : Randomness params) (a : F)
    {L : Finset Party} (hL : params.threshold ≤ #L) (i : Party) (h : M) :
    share params r a i • h =
      (Lagrange.basis (insertNone L) params.pointOrZero none).eval (params.point i) • a • h +
        ∑ l ∈ L, (Lagrange.basis (insertNone L) params.pointOrZero (some l)).eval
          (params.point i) • share params r a l • h := by
  conv_lhs => rw [share_eq_eval_basis_mul_add_sum params r a hL i]
  simp [add_smul, sum_smul, mul_smul]

omit [DecidableEq Party] in
/-- **Linearity of the secret, acting on a module** ([BonehShoup2023], Section 22.5.2,
pp. 977–978): for an authorized set `s` and an element `h` of a module over the field, combining
the elements `share params r a i • h` of the parties in `s` with the weights at `0` gives `a • h`.
This is how a threshold scheme combines signature or decryption shares (`σ = ∏ σ_j^{λ_j}` in the
book, written additively). Over the field itself it is `reconstruct_share_eq_secret`. -/
theorem sum_lagrangeWeightAtZero_smul_share_smul {M : Type*} [AddCommMonoid M] [Module F M]
    (params : Params F Party) (r : Randomness params) (a : F) {s : Finset Party}
    (hs : authorized params s) (h : M) :
    ∑ i : s, Polynomial.lagrangeWeightAtZero (fun i : s => params.point i) i •
      share params r a i • h = a • h := by
  have := reconstruct_share_eq_secret params r a hs
  rw [reconstruct, Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero] at this
  conv_rhs => rw [← this]
  rw [sum_smul]
  exact sum_congr rfl fun i _ => by rw [mul_smul, smul_comm]

end Cslib.Crypto.Protocols.SecretSharing.Shamir
