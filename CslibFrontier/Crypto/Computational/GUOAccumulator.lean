/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSACommonRoot
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The accumulator from a group of unknown order: correctness and aggregation

The accumulator of [BonehShoup2023], §10.9 (pp. 421–423), which the book calls the GUO
accumulator, in the group `(ℤ/Nℤ)ˣ` with a base `g`; the modulus, the base and every group element
are natural numbers. Alice commits to a finite set `S` of elements of a type `X`, through a hash
`H : X → ℕ`, by `c = g ^ E` with `E = ∏ x ∈ S, H x` (construction (10.5), p. 421). Adding an
element `x ∉ S` raises the commitment to the power `H x` (p. 421). A membership proof for `x` is
`b = g ^ (E / H x)`, which Bob checks by `b ^ H x = c`. A non-membership proof is a pair `(b, γ)`
with `β * H x + γ * E = 1` and `b = g ^ β`, which Bob checks by `b ^ H x * c ^ γ = g`
(pp. 421–422). One group element `π_T = g ^ (E / ∏ x ∈ T, H x)` proves `T ⊆ S` (p. 423); two
membership proofs for elements with coprime hashes combine into one by Shamir's trick, and the
aggregate splits back into the two proofs (p. 422).

The source's claims map to Lean as follows.

* (10.5) and the update `c' = c ^ H(x)` (p. 421): `guoCommit` and `guoCommit_insert`.
* Membership proofs and Bob's check (p. 421), the aggregate `π_xy` (p. 422) and `π_T` (p. 423):
  `guoSubsetWitness` and `guoVerifySubset`; the proofs verify by
  `guoVerifySubset_subsetWitness`, `guoVerifySubset_singleton` and `guoVerifySubset_pair`.
* Recovering `π_x` from `π_xy` (p. 422): `guoVerifySubset_split`. Carol's aggregation of two
  membership proofs by Theorem 10.6 (pp. 422–423): `guoVerifySubset_commonRoot`.
* Non-membership proofs (pp. 421–422): `guoNonMemCoeff` and `guoNonMemWitness` compute Alice's
  `(b, γ)` and `guoVerifyNonMem` is Bob's check. `guoVerifyNonMem_witness` shows that Alice's proof
  verifies whenever `gcd(H(x), E) = 1`, and `guoNonMemCoeff_lt` is the book's bound on `|γ|`.
* Correctness (p. 422): for a prime `H x` distinct from the hashes of the elements of `S`, the
  exponents are coprime (`coprime_guoExponent`) and Alice's non-membership proof verifies
  (`guoVerifyNonMem_guoCommit`); if they are not coprime and `x ∉ S`, some `y ∈ S` collides with
  `x` (`exists_collision_of_not_coprime_guoExponent`).
* The two equations in the book's security argument (p. 422), `a ^ H(x) = c` and
  `b ^ H(x) * c ^ γ = g`, give `(b * a ^ γ) ^ H(x) = g`: `guoForgeryRoot` and
  `powMod_guoForgeryRoot`. The security theorem itself is not stated here.

## Main definitions

* `Cslib.Crypto.guoExponent`: the exponent `E = ∏ x ∈ S, H x` of (10.5).
* `Cslib.Crypto.guoCommit`: the commitment `g ^ E mod N`.
* `Cslib.Crypto.guoSubsetWitness`: Alice's proof `π_T` that `T ⊆ S`, `g ^ (∏ x ∈ S \ T, H x)`.
* `Cslib.Crypto.guoVerifySubset`: Bob's check `b ^ e = c` for one hash `e` or a product of
  hashes.
* `Cslib.Crypto.guoNonMemCoeff`, `Cslib.Crypto.guoNonMemWitness`: Alice's non-membership proof,
  the negated coefficient `-γ` and the group element `b = g ^ β`.
* `Cslib.Crypto.guoVerifyNonMem`: Bob's non-membership check, including the check that `c` is a
  unit.
* `Cslib.Crypto.guoForgeryRoot`: the root `b * a ^ γ` computed from a membership proof `a` and a
  non-membership proof `(b, γ)` for one element.

## Main results

* `Cslib.Crypto.guoCommit_insert`: the commitment to `insert x S` is `c ^ H x` for `x ∉ S`.
* `Cslib.Crypto.guoVerifySubset_subsetWitness`, `Cslib.Crypto.guoVerifySubset_singleton`,
  `Cslib.Crypto.guoVerifySubset_pair`: Alice's proofs for a subset, an element and a pair verify.
* `Cslib.Crypto.guoVerifySubset_split`, `Cslib.Crypto.guoVerifySubset_commonRoot`: an aggregate
  splits into proofs, and two proofs for coprime exponents against a unit commitment aggregate.
* `Cslib.Crypto.guoNonMemCoeff_lt`, `Cslib.Crypto.guoVerifyNonMem_witness`,
  `Cslib.Crypto.guoVerifyNonMem_guoCommit`: Alice's non-membership proofs verify.
* `Cslib.Crypto.coprime_guoExponent`, `Cslib.Crypto.exists_collision_of_not_coprime_guoExponent`:
  `gcd(H(x), E) = 1` unless the hash collides.
* `Cslib.Crypto.powMod_guoForgeryRoot`: a membership and a non-membership proof for one element
  give an `H x`-th root of `g`.
* `Cslib.Crypto.computableInPolyTime_guoVerifySubset`,
  `Cslib.Crypto.computableInPolyTime_guoVerifyNonMem`,
  `Cslib.Crypto.computableInPolyTime_guoNonMemCoeff`,
  `Cslib.Crypto.computableInPolyTime_neg_guoNonMemCoeff`,
  `Cslib.Crypto.computableInPolyTime_guoNonMemWitness`,
  `Cslib.Crypto.computableInPolyTime_guoForgeryRoot`: both checks, Alice's non-membership proof
  and the root are computable in polynomial time from polynomial-time inputs, the integer `γ` on
  `encIntBin` and every natural number on `encNat`, with no condition on the values.

## Implementation notes

The statements differ from the book's as follows.

* The group is `(ℤ/Nℤ)ˣ`, the one group of unknown order whose generation the book specifies
  (p. 421), represented by natural numbers. Group operations are `powMod`, which returns `1` at
  the modulus `0`. The base is a unit (`Nat.Coprime g N`) where a proof needs it.
* `H` is any function `X → ℕ`. The book's hash takes values in the first `L` primes (p. 421);
  primality is assumed only where it is used, in `coprime_guoExponent` and its consequences.
* `π_T` is `g ^ (∏ x ∈ S \ T, H x)` rather than `g ^ (E / ∏ x ∈ T, H x)`. The two are equal
  when `T ⊆ S` and no hash is `0`, and this form needs no division and no hypothesis on the hashes.
* `γ` is an integer as in the book, but no one inverts a group element: for `γ < 0` Bob compares
  `b ^ H x` with `g * c ^ |γ|`. Alice's `γ` is `-guoNonMemCoeff (H x) E`, so `γ ≤ 0`,
  `|γ| < H x` where the book has `|γ| ≤ H(x)`, and `β = (|γ| * E + 1) / H x` is a natural number.
* Bob checks that `c` is a unit, the book's `c ∈ G`. Without this check `(c, a, b, γ) =
  (0, 0, 0, -1)` would pass both checks for every modulus `N ≥ 1`, base and hash `H x ≥ 1`.
* "Correctness relies on the collision resistance of `H`" (p. 422) is stated by the explicit
  collision of `exists_collision_of_not_coprime_guoExponent`, not as a game against a hash family.

Alice's computing `E` from a list of elements is not certified: `guoCommit` and `guoSubsetWitness`
take a `Finset`, and the certificates for her non-membership proof take `E` as an input.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §10.9, pp. 421–423.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- For a positive modulus, `powMod` is the power in `ZMod N`. -/
private theorem natCast_powMod {N : ℕ} (hN : N ≠ 0) (x e : ℕ) :
    ((powMod N x e : ℕ) : ZMod N) = (x : ZMod N) ^ e := by
  rw [powMod_of_ne_zero hN, ZMod.natCast_mod, Nat.cast_pow]

/-- For `0 < N` and `0 < e`, if `b ^ e mod N` is a unit modulo `N`, then so is `b`. -/
private theorem coprime_of_coprime_powMod {N b e : ℕ} (hN : 0 < N) (he : 0 < e)
    (h : Nat.Coprime (powMod N b e) N) : Nat.Coprime b N := by
  refine (Nat.coprime_pow_left_iff he b N).mp ?_
  rw [Nat.Coprime, ← (Nat.mod_modEq (b ^ e) N).gcd_eq, ← powMod_of_ne_zero hN.ne']
  exact h

section Accumulator

variable {X : Type*}

/-- The exponent `E = H(x₁) ⋯ H(xₙ)` of construction (10.5) in [BonehShoup2023], §10.9, p. 421,
for the set `S = {x₁, …, xₙ}` and the hash `H`. -/
@[expose] def guoExponent (H : X → ℕ) (S : Finset X) : ℕ := ∏ x ∈ S, H x

/-- The commitment `c = g ^ E` to the set `S` in `(ℤ/Nℤ)ˣ`, construction (10.5) in
[BonehShoup2023], §10.9, p. 421. -/
@[expose] def guoCommit (N g : ℕ) (H : X → ℕ) (S : Finset X) : ℕ :=
  powMod N g (guoExponent H S)

/-- Bob's check `b ^ e = c` modulo `N` of a proof `b` against the commitment `c`
([BonehShoup2023], §10.9, pp. 421–423). For a membership proof of `x`, `e = H x`; for an
aggregate proof of a set `T`, `e` is the product of the hashes of its elements. -/
@[expose] def guoVerifySubset (N c e b : ℕ) : Bool := powMod N b e == c

/-- Alice's proof `π_T` that `T ⊆ S`: `g` to the product of the hashes of the elements of `S \ T`.
For `T ⊆ S` and nonzero hashes this is the book's `g ^ (E / ∏ x ∈ T, H x)` ([BonehShoup2023],
§10.9, p. 423); `T = {x}` is the membership proof `π_x` (p. 421), and `T = {x, y}` is the
aggregate `π_xy` (p. 422). -/
@[expose] def guoSubsetWitness [DecidableEq X] (N g : ℕ) (H : X → ℕ) (S T : Finset X) : ℕ :=
  powMod N g (guoExponent H (S \ T))

/-- The accumulator is dynamic ([BonehShoup2023], §10.9, p. 421): for `x ∉ S`, the commitment to
`insert x S` is the commitment `c` to `S` raised to the power `H x`. -/
theorem guoCommit_insert [DecidableEq X] (N g : ℕ) (H : X → ℕ) {S : Finset X} {x : X}
    (hx : x ∉ S) : guoCommit N g H (insert x S) = powMod N (guoCommit N g H S) (H x) := by
  rw [guoCommit, guoCommit, powMod_powMod, guoExponent, guoExponent, Finset.prod_insert hx,
    mul_comm]

/-- Alice's proof that `T ⊆ S` verifies against the commitment to `S`, with the product of the
hashes of the elements of `T` as exponent ([BonehShoup2023], §10.9, p. 423). -/
theorem guoVerifySubset_subsetWitness [DecidableEq X] (N g : ℕ) (H : X → ℕ) {S T : Finset X}
    (hT : T ⊆ S) :
    guoVerifySubset N (guoCommit N g H S) (guoExponent H T) (guoSubsetWitness N g H S T) =
      true := by
  rw [guoVerifySubset, guoSubsetWitness, powMod_powMod, guoCommit, guoExponent, guoExponent,
    guoExponent, Finset.prod_sdiff hT]
  exact beq_self_eq_true _

/-- Correctness of membership proofs ([BonehShoup2023], §10.9, pp. 421–422): for `x ∈ S`, Alice's
proof `π_x` verifies against the commitment to `S`. -/
theorem guoVerifySubset_singleton [DecidableEq X] (N g : ℕ) (H : X → ℕ) {S : Finset X} {x : X}
    (hx : x ∈ S) :
    guoVerifySubset N (guoCommit N g H S) (H x) (guoSubsetWitness N g H S {x}) = true := by
  simpa only [guoExponent, Finset.prod_singleton] using
    guoVerifySubset_subsetWitness N g H (Finset.singleton_subset_iff.mpr hx)

/-- Alice's aggregate proof `π_xy` for distinct `x, y ∈ S` verifies against the commitment to `S`
with the exponent `H x * H y` ([BonehShoup2023], §10.9, p. 422). -/
theorem guoVerifySubset_pair [DecidableEq X] (N g : ℕ) (H : X → ℕ) {S : Finset X} {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    guoVerifySubset N (guoCommit N g H S) (H x * H y) (guoSubsetWitness N g H S {x, y}) =
      true := by
  simpa only [guoExponent, Finset.prod_pair hxy] using guoVerifySubset_subsetWitness N g H
    (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))

/-- An aggregate proof splits ([BonehShoup2023], §10.9, p. 422): if `b` passes Bob's check with
the exponent `e * f`, then `b ^ f mod N` passes it with the exponent `e`. -/
theorem guoVerifySubset_split {N c e f b : ℕ} (h : guoVerifySubset N c (e * f) b = true) :
    guoVerifySubset N c e (powMod N b f) = true := by
  rw [guoVerifySubset, powMod_powMod, mul_comm]
  exact h

/-- Anyone can aggregate two membership proofs ([BonehShoup2023], §10.9, pp. 422–423): if `b₁`
and `b₂` pass Bob's check against a unit `c` with coprime exponents `e` and `f`, then Shamir's
trick `commonRoot` (Theorem 10.6) yields a proof that passes it with the exponent `e * f`. -/
theorem guoVerifySubset_commonRoot {N c e f b₁ b₂ : ℕ} (hef : Nat.Coprime e f)
    (hc : Nat.Coprime c N) (h₁ : guoVerifySubset N c e b₁ = true)
    (h₂ : guoVerifySubset N c f b₂ = true) :
    guoVerifySubset N c (e * f) (commonRoot N e f b₁ b₂) = true := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa [guoVerifySubset, powMod] using h₁
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain rfl : f = 1 := (Nat.coprime_zero_left f).mp hef
    simpa [guoVerifySubset, powMod_of_ne_zero hN.ne'] using h₁
  simp only [guoVerifySubset, beq_iff_eq] at h₁ h₂ ⊢
  have hb : Nat.Coprime b₁ N := coprime_of_coprime_powMod hN he (h₁ ▸ hc)
  rw [powMod_of_ne_zero hN.ne'] at h₁ h₂ ⊢
  rw [pow_mul, ← h₂]
  exact (commonRoot_pow_modEq_right hN hef hb (h₁.trans h₂.symm)).pow f

/-- Bob's check of a non-membership proof `(b, γ)` for an element with hash `h` against the
commitment `c` ([BonehShoup2023], §10.9, pp. 421–422): `c` is a unit modulo `N`, the book's
`c ∈ G`, and `b ^ h * c ^ γ = g`. For `γ < 0` the check compares `b ^ h` with `g * c ^ |γ|`, so
no inverse is computed. -/
@[expose] def guoVerifyNonMem (N g c h b : ℕ) (γ : ℤ) : Bool :=
  decide (Nat.Coprime c N) &&
    if γ < 0 then powMod N b h == g * powMod N c γ.natAbs % N
    else powMod N b h * powMod N c γ.natAbs % N == g % N

/-- The coefficient `k = -γ` of Alice's non-membership proof for an element with hash `h`
against the exponent `E` ([BonehShoup2023], §10.9, p. 421): the inverse of `-E` modulo `h`,
computed by the extended Euclidean algorithm `BinaryGcd.modInv`. When `0 < h` and
`Nat.Coprime h E`, `h` divides `k * E + 1`, so `β * h + γ * E = 1` for `γ = -k` and
`β = (k * E + 1) / h`. -/
@[expose] def guoNonMemCoeff (h E : ℕ) : ℕ := BinaryGcd.modInv (h - E % h) h

/-- The group element `b = g ^ β` of Alice's non-membership proof for an element with hash `h`
against the exponent `E` ([BonehShoup2023], §10.9, p. 421), with
`β = (guoNonMemCoeff h E * E + 1) / h`. -/
@[expose] def guoNonMemWitness (N g h E : ℕ) : ℕ :=
  powMod N g ((guoNonMemCoeff h E * E + 1) / h)

/-- Alice's coefficient satisfies `|γ| < h`, a slightly sharper form of the book's
`|γ| ≤ H(x)` ([BonehShoup2023], §10.9, p. 421). -/
theorem guoNonMemCoeff_lt {h : ℕ} (hh : 0 < h) (E : ℕ) : guoNonMemCoeff h E < h :=
  BinaryGcd.modInv_lt hh

/-- For `0 < h` and `Nat.Coprime h E`, `h` divides `guoNonMemCoeff h E * E + 1`. -/
private theorem dvd_guoNonMemCoeff_mul_add_one {h E : ℕ} (hh : 0 < h) (hcop : Nat.Coprime h E) :
    h ∣ guoNonMemCoeff h E * E + 1 := by
  have hr : E % h < h := Nat.mod_lt _ hh
  have hc : Nat.Coprime (h - E % h) h := by
    refine (Nat.coprime_self_sub_left hr.le).mpr ?_
    rw [Nat.Coprime, (Nat.mod_modEq E h).gcd_eq]
    exact hcop.symm
  have h1 : (h - E % h) * guoNonMemCoeff h E ≡ 1 [MOD h] := BinaryGcd.mul_modInv_modEq_one hh hc
  have h2 : guoNonMemCoeff h E * E + 1 ≡
      guoNonMemCoeff h E * (E % h) + (h - E % h) * guoNonMemCoeff h E [MOD h] :=
    ((Nat.mod_modEq E h).symm.mul_left _).add h1.symm
  rw [mul_comm (guoNonMemCoeff h E) (E % h), ← add_mul, Nat.add_sub_cancel' hr.le] at h2
  exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.mul_mod_right h _))

/-- Correctness of non-membership proofs ([BonehShoup2023], §10.9, pp. 421–422): if `g` is a unit
modulo `N`, `0 < h` and `gcd(h, E) = 1`, then Alice's proof
`(guoNonMemWitness N g h E, -guoNonMemCoeff h E)` passes Bob's check against `c = g ^ E`. -/
theorem guoVerifyNonMem_witness {N g h E : ℕ} (hg : Nat.Coprime g N) (hh : 0 < h)
    (hcop : Nat.Coprime h E) :
    guoVerifyNonMem N g (powMod N g E) h (guoNonMemWitness N g h E)
      (-(guoNonMemCoeff h E : ℤ)) = true := by
  obtain ⟨β, hβ⟩ := dvd_guoNonMemCoeff_mul_add_one hh hcop
  have hwit : guoNonMemWitness N g h E = powMod N g β := by
    rw [guoNonMemWitness, hβ, Nat.mul_div_cancel_left _ hh]
  rw [guoVerifyNonMem, hwit]
  simp only [powMod_powMod, Int.natAbs_neg, Int.natAbs_natCast, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨coprime_powMod hg E, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : g = 1 := Nat.coprime_zero_right g |>.mp hg
    split_ifs <;> simp [powMod]
  · generalize guoNonMemCoeff h E = k at hβ ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hβ1 : β * h = 1 := by rw [mul_comm]; omega
      simp [hβ1, powMod_of_ne_zero hN.ne']
    · have hneg : -(k : ℤ) < 0 := by omega
      rw [ite_eq_left hneg, beq_iff_eq, powMod_of_ne_zero hN.ne', powMod_of_ne_zero hN.ne',
        Nat.mul_mod_mod, ← pow_succ', mul_comm β h, ← hβ, mul_comm E k]

/-- For a prime `H x` distinct from the hashes of the elements of `S`, which are prime too, `H x`
is coprime to the exponent `E` of `S` ([BonehShoup2023], §10.9, p. 422). -/
theorem coprime_guoExponent {H : X → ℕ} {S : Finset X} {x : X} (hx : (H x).Prime)
    (hS : ∀ y ∈ S, (H y).Prime) (hne : ∀ y ∈ S, H y ≠ H x) :
    Nat.Coprime (H x) (guoExponent H S) :=
  Nat.Coprime.prod_right fun y hy => (Nat.coprime_primes hx (hS y hy)).mpr (hne y hy).symm

/-- The book's argument that correctness relies on the collision resistance of `H`
([BonehShoup2023], §10.9, p. 422), stated as an explicit collision: if `x ∉ S`, the hashes are
prime and `gcd(H(x), E) ≠ 1`, then some `y ∈ S` with `y ≠ x` has `H y = H x`. -/
theorem exists_collision_of_not_coprime_guoExponent {H : X → ℕ} {S : Finset X} {x : X}
    (hx : (H x).Prime) (hS : ∀ y ∈ S, (H y).Prime) (hxS : x ∉ S)
    (h : ¬ Nat.Coprime (H x) (guoExponent H S)) : ∃ y ∈ S, y ≠ x ∧ H y = H x := by
  by_contra hno
  push Not at hno
  exact h (coprime_guoExponent hx hS fun y hy => hno y hy (ne_of_mem_of_not_mem hy hxS))

/-- Correctness of non-membership proofs for a committed set ([BonehShoup2023], §10.9,
pp. 421–422): if `g` is a unit modulo `N`, `H x` is prime and distinct from the hashes of the
elements of `S`, which are prime too, then Alice's non-membership proof for `x` passes Bob's check
against the commitment to `S`. -/
theorem guoVerifyNonMem_guoCommit (N g : ℕ) {H : X → ℕ} {S : Finset X} {x : X}
    (hg : Nat.Coprime g N) (hx : (H x).Prime) (hS : ∀ y ∈ S, (H y).Prime)
    (hne : ∀ y ∈ S, H y ≠ H x) :
    guoVerifyNonMem N g (guoCommit N g H S) (H x)
      (guoNonMemWitness N g (H x) (guoExponent H S))
      (-(guoNonMemCoeff (H x) (guoExponent H S) : ℤ)) = true :=
  guoVerifyNonMem_witness hg hx.pos (coprime_guoExponent hx hS hne)

end Accumulator

/-- The root `b * a ^ γ mod N` computed from a membership proof `a` and a non-membership proof
`(b, γ)` for one element ([BonehShoup2023], §10.9, p. 422). For `γ < 0`, `a ^ γ` is
`(a⁻¹) ^ |γ|` with `a⁻¹ = BinaryGcd.modInv a N`. -/
@[expose] def guoForgeryRoot (N a b : ℕ) (γ : ℤ) : ℕ :=
  b * powMod N (if γ < 0 then BinaryGcd.modInv a N else a) γ.natAbs % N

/-- The algebra of the book's security argument ([BonehShoup2023], §10.9, p. 422): if `a` passes
Bob's membership check and `(b, γ)` his non-membership check for the same hash `h` and commitment
`c`, then `guoForgeryRoot N a b γ` is an `h`-th root of `g` modulo `N`. There is no hypothesis on
`N`, `g` or `h`. -/
theorem powMod_guoForgeryRoot {N g c h a b : ℕ} {γ : ℤ}
    (hmem : guoVerifySubset N c h a = true) (hnon : guoVerifyNonMem N g c h b γ = true) :
    powMod N (guoForgeryRoot N a b γ) h = g % N := by
  simp only [guoVerifySubset, beq_iff_eq] at hmem
  simp only [guoVerifyNonMem, Bool.and_eq_true, decide_eq_true_eq] at hnon
  obtain ⟨hcN, hbranch⟩ := hnon
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : c = 1 := Nat.coprime_zero_right c |>.mp hcN
    split_ifs at hbranch <;> simp_all [powMod]
  have hN' := hN.ne'
  have hc : (c : ZMod N) = (a : ZMod N) ^ h := by rw [← hmem, natCast_powMod hN']
  have hcast {x y : ℕ} (hxy : x = y) : (x : ZMod N) = y := congrArg _ hxy
  rw [powMod_of_ne_zero hN', ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, guoForgeryRoot,
    ZMod.natCast_mod, Nat.cast_mul, natCast_powMod hN', mul_pow, ← pow_mul, mul_comm _ h]
  by_cases hγ : γ < 0
  · rw [ite_eq_left hγ, beq_iff_eq] at hbranch
    rw [ite_eq_left hγ]
    have hb : (b : ZMod N) ^ h = g * (c : ZMod N) ^ γ.natAbs := by
      simpa [natCast_powMod hN', ZMod.natCast_mod] using hcast hbranch
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simpa [hc] using hb
    have ha : Nat.Coprime a N := coprime_of_coprime_powMod hN hh (hmem ▸ hcN)
    have hinv : (a : ZMod N) * (BinaryGcd.modInv a N : ZMod N) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (BinaryGcd.mul_modInv_modEq_one hN ha)
    rw [hb, hc, ← pow_mul, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
  · rw [ite_eq_right hγ, beq_iff_eq] at hbranch
    rw [ite_eq_right hγ]
    have hb : (b : ZMod N) ^ h * (c : ZMod N) ^ γ.natAbs = g := by
      simpa [natCast_powMod hN', ZMod.natCast_mod] using hcast hbranch
    rw [← hb, hc, ← pow_mul]

/-! ### Polynomial-time certificates -/

variable {α : Type} {enc : α ↪ List Bool}

/-- Bob's membership and subset check is computable in polynomial time whenever `N`, `c`, `e` and
`b` are, as natural numbers on `encNat`. -/
theorem computableInPolyTime_guoVerifySubset {N c e b : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hc : ComputableInPolyTime c enc encNat)
    (he : ComputableInPolyTime e enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun a => guoVerifySubset (N a) (c a) (e a) (b a)) enc encBool :=
  ComputableInPolyTime.beq (computableInPolyTime_powMod hN hb he) hc

/-- Bob's non-membership check is computable in polynomial time whenever `N`, `g`, `c`, `h` and
`b` are, as natural numbers on `encNat`, and `γ` is, as an integer on `encIntBin`. -/
theorem computableInPolyTime_guoVerifyNonMem {N g c h b : α → ℕ} {γ : α → ℤ}
    (hN : ComputableInPolyTime N enc encNat) (hg : ComputableInPolyTime g enc encNat)
    (hc : ComputableInPolyTime c enc encNat) (hh : ComputableInPolyTime h enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hγ : ComputableInPolyTime γ enc encIntBin) :
    ComputableInPolyTime (fun a => guoVerifyNonMem (N a) (g a) (c a) (h a) (b a) (γ a))
      enc encBool := by
  have habs : ComputableInPolyTime (fun a => (γ a).natAbs) enc encNat :=
    ComputableInPolyTime.intBin_natAbs.comp hγ
  have hbh := computableInPolyTime_powMod hN hb hh
  have hcγ := computableInPolyTime_powMod hN hc habs
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.binary_gcd' hc hN)
      (ComputableInPolyTime.const 1))
    (ComputableInPolyTime.ite_decide (ComputableInPolyTime.intBin_isNeg.comp hγ)
      (ComputableInPolyTime.beq hbh
        (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_mul' hg hcγ) hN))
      (ComputableInPolyTime.beq
        (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_mul' hbh hcγ) hN)
        (ComputableInPolyTime.binary_mod' hg hN)))

/-- Alice's non-membership coefficient `guoNonMemCoeff h E`, the natural number `-γ` on `encNat`,
is computable in polynomial time whenever `h` and `E` are, as natural numbers on `encNat`. -/
theorem computableInPolyTime_guoNonMemCoeff {h E : α → ℕ}
    (hh : ComputableInPolyTime h enc encNat) (hE : ComputableInPolyTime E enc encNat) :
    ComputableInPolyTime (fun a => guoNonMemCoeff (h a) (E a)) enc encNat :=
  ComputableInPolyTime.binary_modInv'
    (ComputableInPolyTime.binary_sub' hh (ComputableInPolyTime.binary_mod' hE hh)) hh

/-- Alice's coefficient `γ = -guoNonMemCoeff h E`, as an integer on `encIntBin`, is computable in
polynomial time whenever `h` and `E` are, as natural numbers on `encNat`. This is the form of `γ`
in `guoVerifyNonMem_witness` and `computableInPolyTime_guoVerifyNonMem`. -/
theorem computableInPolyTime_neg_guoNonMemCoeff {h E : α → ℕ}
    (hh : ComputableInPolyTime h enc encNat) (hE : ComputableInPolyTime E enc encNat) :
    ComputableInPolyTime (fun a => -(guoNonMemCoeff (h a) (E a) : ℤ)) enc encIntBin :=
  ComputableInPolyTime.intBin_neg.comp
    (ComputableInPolyTime.intBin_natCast.comp (computableInPolyTime_guoNonMemCoeff hh hE))

/-- Alice's non-membership group element is computable in polynomial time whenever `N`, `g`, `h`
and `E` are, as natural numbers on `encNat`. -/
theorem computableInPolyTime_guoNonMemWitness {N g h E : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hg : ComputableInPolyTime g enc encNat)
    (hh : ComputableInPolyTime h enc encNat) (hE : ComputableInPolyTime E enc encNat) :
    ComputableInPolyTime (fun a => guoNonMemWitness (N a) (g a) (h a) (E a)) enc encNat :=
  computableInPolyTime_powMod hN hg
    (ComputableInPolyTime.binary_div'
      (ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_mul' (computableInPolyTime_guoNonMemCoeff hh hE) hE)
        (ComputableInPolyTime.const 1)) hh)

/-- The root `guoForgeryRoot` is computable in polynomial time whenever `N`, `a` and `b` are, as
natural numbers on `encNat`, and `γ` is, as an integer on `encIntBin`. -/
theorem computableInPolyTime_guoForgeryRoot {N a b : α → ℕ} {γ : α → ℤ}
    (hN : ComputableInPolyTime N enc encNat) (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hγ : ComputableInPolyTime γ enc encIntBin) :
    ComputableInPolyTime (fun x => guoForgeryRoot (N x) (a x) (b x) (γ x)) enc encNat :=
  ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_mul' hb
      (computableInPolyTime_powMod hN
        (ComputableInPolyTime.ite_decide (ComputableInPolyTime.intBin_isNeg.comp hγ)
          (ComputableInPolyTime.binary_modInv' ha hN) ha)
        (ComputableInPolyTime.intBin_natAbs.comp hγ))) hN

end Cslib.Crypto
