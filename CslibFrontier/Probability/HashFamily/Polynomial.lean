/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Pi
import CslibFrontier.Foundations.Data.List.FoldlIdx
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic

/-!
# Carter–Wegman polynomial evaluation

Over a finite field `F`, a message `m = (a₁, …, a_v)` of length at most `ℓ` is hashed with a key
`k ∈ F` by evaluating a polynomial at `k` [WegmanCarter1981]:

* `polynomialHash c k = ∑ i, c i * k ^ i` exposes the standard ascending fixed-length
  coefficient vector. It is the shared evaluator used by the polynomial `k`-wise independent
  family ([Vadhan2012], Section 3.5.5).
* `coeffPolyHash k x = x₀ k ^ (n - 1) + ⋯ + x_(n - 1)` evaluates a fixed-length
  coefficient vector by `n` Horner multiply-add rounds from zero. If `k` is sampled uniformly
  from a finite set injected into `F`, this family is `n / |S|`-universal
  ([BaumEtAl2026FAEST], Section 4.2.1, printed pp. 22–23).
* `polyHash k m = k ^ v + a₁ k ^ (v - 1) + ⋯ + a_v`, Boneh and Shoup's `Hpoly`
  ([BonehShoup2023], Equation 7.3). It is `ℓ / |F|`-universal ([BonehShoup2023], Lemma 7.2).
* `xpolyHash k m = k * polyHash k m`, their `Hxpoly` ([BonehShoup2023], Equation 7.23). It is
  `(ℓ + 1) / |F|`-Δ-universal ([BonehShoup2023], Lemma 7.8), which is what the Carter–Wegman MAC
  needs.

The leading `k ^ v` lets messages of different lengths be compared: the message polynomials are
monic of degree `v`, so distinct messages give distinct polynomials, and the difference of two of
them has at most `ℓ` roots. Both functions are computed by Horner's rule. The existing
`polynomialHash` instead exposes the standard ascending coefficient vector and a finite sum;
`coeffPolyHash` retains FAEST Figure 4.4 order and an executable one-pass fold. Reversing the
coefficient indices identifies the two APIs.

## Main definitions

* `Cslib.Probability.polynomialHash`: ascending fixed-length coefficient evaluation.
* `Cslib.Probability.coeffPolyHash`: fixed-length coefficient evaluation by Horner's rule.
* `Cslib.Probability.coeffPolyHashLinear`: coefficient evaluation as a linear map.
* `Cslib.Probability.polyHash`, `Cslib.Probability.xpolyHash`: variable-length polynomial
  evaluation hashes.

## Main results

* `Cslib.Probability.polynomialHash_add`, `Cslib.Probability.polynomialHash_eq_eval`: additive
  coefficient evaluation and its agreement with bounded-degree polynomial evaluation.
* `Cslib.Probability.isUniversalHash_coeffPolyHash_of_embedding`: the evaluation point may be
  uniform in any finite set injected into the field.
* `Cslib.Probability.isUniversalHash_coeffPolyHash`: the full-field specialization.
* `Cslib.Probability.coeffPolyHash_eq_polynomialHash_rev`,
  `Cslib.Probability.polyHash_ofFn_eq`: bridges to the existing fixed- and variable-length APIs.
* `Cslib.Probability.isUniversalHash_polyHash`: `polyHash` is `ℓ / |F|`-universal.
* `Cslib.Probability.isDeltaUniversalHash_xpolyHash`: `xpolyHash` is `(ℓ + 1) / |F|`-Δ-universal.

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.2.1 and 7.4.
* [C. Baum et al., *FAEST v3: Algorithm Specifications*][BaumEtAl2026FAEST], Section 4.2.
* [S. P. Vadhan, *Pseudorandomness*][Vadhan2012], Section 3.5.5.
-/

@[expose] public section

namespace Cslib.Probability

open scoped ENNReal

section PolynomialHash

open Finset Polynomial

variable {R : Type*} [Semiring R]

/-- The polynomial hash with coefficient vector `c : Fin k → R`: the value at `x` of the
polynomial `∑ j < k, c j X ^ j`, of degree less than `k`. -/
def polynomialHash {k : ℕ} (c : Fin k → R) (x : R) : R :=
  ∑ j, c j * x ^ (j : ℕ)

/-- The polynomial hash is additive in its coefficient vector. -/
theorem polynomialHash_add {k : ℕ} (c d : Fin k → R) :
    polynomialHash (c + d) = polynomialHash c + polynomialHash d := by
  funext x
  simp only [polynomialHash, Pi.add_apply, add_mul, sum_add_distrib]

/-- The polynomial hash with coefficients `c` evaluates any polynomial of degree less than `k`
whose coefficients are `c`. -/
theorem polynomialHash_eq_eval {k : ℕ} (P : R[X]) (hP : P.natDegree < k) (x : R) :
    polynomialHash (fun j : Fin k => P.coeff j) x = P.eval x := by
  rw [eval_eq_sum_range' hP, polynomialHash]
  exact Fin.sum_univ_eq_sum_range (fun j => P.coeff j * x ^ j) k

end PolynomialHash

variable {F : Type*} [Field F]

/-- Evaluate the fixed-length coefficient vector `x` at `k` by Horner's rule, from the
highest-degree coefficient to the constant coefficient.

The evaluator reads each of the `n` coefficients once and performs exactly `n` field
multiplications and `n` field additions. Besides the input and output, it keeps one field
accumulator and loop/index state. For a field encoding of size `b`, its input has `n * b` bits,
the evaluation point and output each have `b` bits, its running time is
`O(n * (T_mul + T_add))`, and its generic auxiliary state has `b + O(log n)` bits for the field
accumulator and loop index, before field-operation scratch space. Thus the number of retained
field elements is constant, but the total workspace is not independent of `n`. The generic fold
has a control description independent of `n`, apart from the supplied field-operation
descriptions. An unrolled specialization uses `O(n)` field-operation nodes and can omit the
runtime index. These operational counts alone do not establish polynomial time without encoded
field operations and a family-level sampler certificate. -/
def coeffPolyHash (k : F) {n : ℕ} (x : Fin n → F) : F :=
  Fin.foldl n (fun acc i => acc * k + x i) 0

private theorem foldl_mul_add_add (k : F) {n : ℕ} (x y : Fin n → F) (a b : F) :
    Fin.foldl n (fun acc i => acc * k + (x + y) i) (a + b) =
      Fin.foldl n (fun acc i => acc * k + x i) a +
        Fin.foldl n (fun acc i => acc * k + y i) b := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ, Fin.foldl_succ, Fin.foldl_succ]
    simpa only [Pi.add_apply, add_mul, add_assoc, add_left_comm, add_comm] using
      ih (fun i => x i.succ) (fun i => y i.succ) (a * k + x 0) (b * k + y 0)

private theorem foldl_mul_add_smul (k c : F) {n : ℕ} (x : Fin n → F) (a : F) :
    Fin.foldl n (fun acc i => acc * k + (c • x) i) (c * a) =
      c * Fin.foldl n (fun acc i => acc * k + x i) a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ, Fin.foldl_succ]
    simpa only [Pi.smul_apply, smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using
      ih (fun i => x i.succ) (a * k + x 0)

private theorem foldl_mul_add_accumulate (k : F) {n : ℕ} (x : Fin n → F) (a : F) :
    Fin.foldl n (fun acc i => acc * k + x i) a =
      a * k ^ n + Fin.foldl n (fun acc i => acc * k + x i) 0 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ, Fin.foldl_succ]
    conv_lhs => rw [ih]
    conv_rhs => rw [ih]
    ring

@[simp]
theorem coeffPolyHash_zero (k : F) (n : ℕ) : coeffPolyHash k (0 : Fin n → F) = 0 := by
  simpa only [coeffPolyHash, zero_add, zero_mul, zero_smul] using
    foldl_mul_add_smul k 0 (0 : Fin n → F) 0

theorem coeffPolyHash_add (k : F) {n : ℕ} (x y : Fin n → F) :
    coeffPolyHash k (x + y) = coeffPolyHash k x + coeffPolyHash k y := by
  simpa only [coeffPolyHash, zero_add] using foldl_mul_add_add k x y 0 0

theorem coeffPolyHash_smul (k c : F) {n : ℕ} (x : Fin n → F) :
    coeffPolyHash k (c • x) = c • coeffPolyHash k x := by
  simpa only [coeffPolyHash, mul_zero, smul_eq_mul] using foldl_mul_add_smul k c x 0

/-- For a fixed evaluation point, coefficient-vector evaluation is `F`-linear. -/
def coeffPolyHashLinear (k : F) (n : ℕ) : (Fin n → F) →ₗ[F] F where
  toFun := coeffPolyHash k
  map_add' := coeffPolyHash_add k
  map_smul' c x := by
    simpa only [RingHom.id_apply] using coeffPolyHash_smul (n := n) k c x

@[simp]
theorem coeffPolyHashLinear_apply (k : F) {n : ℕ} (x : Fin n → F) :
    coeffPolyHashLinear k n x = coeffPolyHash k x := rfl

/-- Source-order Horner evaluation is the existing ascending-coefficient `polynomialHash` after
reversing the coefficient indices. The Horner form remains separate because it follows FAEST
Figure 4.4 order and evaluates in one pass without first reversing the input. -/
theorem coeffPolyHash_eq_polynomialHash_rev (k : F) {n : ℕ} (x : Fin n → F) :
    coeffPolyHash k x = polynomialHash (x ∘ Fin.rev) k := by
  induction n with
  | zero => simp [coeffPolyHash, polynomialHash]
  | succ n ih =>
    rw [coeffPolyHash, Fin.foldl_succ, foldl_mul_add_accumulate]
    simp only [zero_mul, zero_add]
    change x 0 * k ^ n + coeffPolyHash k (fun i => x i.succ) =
      polynomialHash (x ∘ Fin.rev) k
    rw [ih (fun i => x i.succ)]
    unfold polynomialHash
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_last, Fin.val_castSucc,
      Fin.val_last]
    ac_rfl

/-- Boneh and Shoup's `Hpoly` ([BonehShoup2023], Equation 7.3): hash the message
`(a₁, …, a_v)` with the key `k` to `k ^ v + a₁ k ^ (v - 1) + ⋯ + a_v`, by Horner's rule. -/
def polyHash (k : F) (m : List F) : F :=
  m.foldl (fun acc a => acc * k + a) 1

/-- Boneh and Shoup's `Hxpoly` ([BonehShoup2023], Equation 7.23): `k * polyHash k m`. -/
def xpolyHash (k : F) (m : List F) : F :=
  k * polyHash k m

open Polynomial

/-- The message polynomial `X ^ v + a₁ X ^ (v - 1) + ⋯ + a_v`. -/
private noncomputable def toPoly (m : List F) : F[X] :=
  m.foldl (fun p a => p * X + C a) 1

private theorem eval_foldl (k : F) (p : F[X]) (m : List F) :
    (m.foldl (fun p a => p * X + C a) p).eval k =
      m.foldl (fun acc a => acc * k + a) (p.eval k) := by
  induction m generalizing p with
  | nil => rfl
  | cons a m ih => simp only [List.foldl_cons, ih, eval_add, eval_mul, eval_X, eval_C]

private theorem eval_toPoly (k : F) (m : List F) : (toPoly m).eval k = polyHash k m := by
  rw [toPoly, eval_foldl, eval_one, polyHash]

/-- The variable-length monic evaluator on a fixed-length vector is the coefficient evaluator
plus the common leading term `k ^ n`. -/
theorem polyHash_ofFn_eq (k : F) {n : ℕ} (x : Fin n → F) :
    polyHash k (List.ofFn x) = k ^ n + coeffPolyHash k x := by
  rw [polyHash, List.foldl_ofFn, foldl_mul_add_accumulate]
  simp [coeffPolyHash]

/-- The coefficient polynomial is the existing monic message polynomial with its common leading
term removed. This lets the fixed-length family reuse the existing polynomial encoding,
injectivity, and root-count proof. -/
private noncomputable def coeffToPoly {n : ℕ} (x : Fin n → F) : F[X] :=
  toPoly (List.ofFn x) - X ^ n

private theorem eval_coeffToPoly (k : F) {n : ℕ} (x : Fin n → F) :
    (coeffToPoly x).eval k = coeffPolyHash k x := by
  rw [coeffToPoly, eval_sub, eval_toPoly, eval_pow, eval_X, polyHash_ofFn_eq]
  abel

private theorem toPoly_append_singleton (m : List F) (a : F) :
    toPoly (m ++ [a]) = toPoly m * X + C a := by
  rw [toPoly, List.foldl_append, List.foldl_cons, List.foldl_nil, toPoly]

/-- Message polynomials are monic, of degree the length of the message. -/
private theorem monic_toPoly (m : List F) :
    (toPoly m).Monic ∧ (toPoly m).natDegree = m.length := by
  induction m using List.reverseRecOn with
  | nil => exact ⟨monic_one, natDegree_one⟩
  | append_singleton m a ih =>
    obtain ⟨hmon, hdeg⟩ := ih
    have hmX : (toPoly m * X).Monic := hmon.mul monic_X
    have hdegX : (toPoly m * X).natDegree = m.length + 1 := by
      rw [natDegree_mul_X hmon.ne_zero, hdeg]
    have hlt : (C a).degree < (toPoly m * X).degree := by
      refine degree_C_le.trans_lt ?_
      rw [degree_eq_natDegree hmX.ne_zero, hdegX]
      exact_mod_cast Nat.succ_pos _
    rw [toPoly_append_singleton, List.length_append, List.length_singleton]
    exact ⟨hmX.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hdegX]⟩

/-- Distinct messages have distinct polynomials. -/
private theorem toPoly_injective : Function.Injective (toPoly : List F → F[X]) := by
  intro m
  induction m using List.reverseRecOn with
  | nil =>
    intro m' h
    have hlen := (monic_toPoly m').2
    rw [← h, (monic_toPoly ([] : List F)).2] at hlen
    exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton m a ih =>
    intro m' h
    have hlen := (monic_toPoly m').2
    rw [← h, (monic_toPoly (m ++ [a])).2] at hlen
    obtain rfl | ⟨m'', a', rfl⟩ := List.eq_nil_or_concat m'
    · simp at hlen
    rw [List.concat_eq_append] at h ⊢
    rw [toPoly_append_singleton, toPoly_append_singleton] at h
    have ha : a = a' := by
      simpa using congrArg (coeff · 0) h
    subst ha
    rw [ih (mul_right_cancel₀ X_ne_zero (add_right_cancel h))]

private theorem coeffToPoly_injective (n : ℕ) :
    Function.Injective (coeffToPoly (F := F) (n := n)) := by
  intro x y h
  apply List.ofFn_injective
  apply toPoly_injective
  exact sub_left_injective (by simpa only [coeffToPoly] using h)

private theorem natDegree_coeffToPoly_le {n : ℕ} (x : Fin n → F) :
    (coeffToPoly x).natDegree ≤ n := by
  exact (natDegree_sub_le _ _).trans <| by
    rw [(monic_toPoly (List.ofFn x)).2, List.length_ofFn, natDegree_X_pow, max_self]

/-- Polynomial evaluation at a point uniform in a finite subset of the field is universal with
the conservative degree bound `n / |S|` ([BaumEtAl2026FAEST], Section 4.2.1, printed pp. 22–23).
The injection makes the sampled evaluation points distinct; no field-uniformity is required. -/
theorem isUniversalHash_coeffPolyHash_of_embedding {S : Type*} [Fintype S] [Nonempty S]
    (point : S ↪ F) (n : ℕ) :
    IsUniversalHash (PMF.uniformOfFintype S)
      (fun s (x : Fin n → F) => coeffPolyHash (point s) x) (n / Fintype.card S) := by
  classical
  exact IsUniversalHash.of_card_le fun x y hxy => by
    have hD : coeffToPoly x - coeffToPoly y ≠ 0 :=
      sub_ne_zero.mpr ((coeffToPoly_injective n).ne hxy)
    calc
      (Finset.univ.filter fun s =>
          coeffPolyHash (point s) x = coeffPolyHash (point s) y).card =
          ((Finset.univ.filter fun s =>
            coeffPolyHash (point s) x = coeffPolyHash (point s) y).image point).card :=
        (Finset.card_image_of_injective _ point.injective).symm
      _ ≤ (coeffToPoly x - coeffToPoly y).roots.toFinset.card := by
        refine Finset.card_le_card fun k hk => ?_
        rw [Finset.mem_image] at hk
        obtain ⟨s, hs, rfl⟩ := hk
        rw [Multiset.mem_toFinset, mem_roots hD, IsRoot.def, eval_sub, eval_coeffToPoly,
          eval_coeffToPoly, sub_eq_zero]
        exact (Finset.mem_filter.mp hs).2
      _ ≤ (coeffToPoly x - coeffToPoly y).roots.card := Multiset.toFinset_card_le _
      _ ≤ (coeffToPoly x - coeffToPoly y).natDegree := card_roots' _
      _ ≤ n := (natDegree_sub_le _ _).trans <|
        max_le (natDegree_coeffToPoly_le x) (natDegree_coeffToPoly_le y)

/-- Full-field coefficient evaluation is `n / |F|`-universal. -/
theorem isUniversalHash_coeffPolyHash [Fintype F] (n : ℕ) :
    IsUniversalHash (PMF.uniformOfFintype F)
      (fun k (x : Fin n → F) => coeffPolyHash k x) (n / Fintype.card F) := by
  simpa using isUniversalHash_coeffPolyHash_of_embedding (F := F)
    (Function.Embedding.refl F) n

/-- **`Hpoly` is `ℓ / |F|`-universal** ([BonehShoup2023], Lemma 7.2): two distinct messages of
length at most `ℓ` collide only at the roots of the nonzero difference of their polynomials. -/
theorem isUniversalHash_polyHash [Fintype F] (ℓ : ℕ) :
    IsUniversalHash (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => polyHash k m) (ℓ / Fintype.card F) := by
  classical
  exact IsUniversalHash.of_card_le fun m m' hm => by
    have hD : toPoly m.1 - toPoly m'.1 ≠ 0 :=
      sub_ne_zero.mpr (toPoly_injective.ne (Subtype.coe_injective.ne hm))
    calc (Finset.univ.filter fun k => polyHash k m.1 = polyHash k m'.1).card
        ≤ (toPoly m.1 - toPoly m'.1).roots.toFinset.card := by
          refine Finset.card_le_card fun k hk => ?_
          rw [Multiset.mem_toFinset, mem_roots hD, IsRoot.def, eval_sub, eval_toPoly,
            eval_toPoly, sub_eq_zero]
          exact (Finset.mem_filter.mp hk).2
      _ ≤ (toPoly m.1 - toPoly m'.1).roots.card := Multiset.toFinset_card_le _
      _ ≤ (toPoly m.1 - toPoly m'.1).natDegree := card_roots' _
      _ ≤ ℓ := (natDegree_sub_le _ _).trans <| max_le
          ((monic_toPoly m.1).2.trans_le m.2) ((monic_toPoly m'.1).2.trans_le m'.2)

/-- **`Hxpoly` is `(ℓ + 1) / |F|`-Δ-universal** ([BonehShoup2023], Lemma 7.8): a difference `d`
of the hashes of two distinct messages occurs only at the roots of the nonzero polynomial
`X (f - g) - d` of degree at most `ℓ + 1`. -/
theorem isDeltaUniversalHash_xpolyHash [Fintype F] (ℓ : ℕ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m)
      ((ℓ + 1) / Fintype.card F) := by
  classical
  have h : IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m)
      ((ℓ + 1 : ℕ) / Fintype.card F) := IsDeltaUniversalHash.of_card_le fun m m' hm d => by
    have hD : toPoly m.1 - toPoly m'.1 ≠ 0 :=
      sub_ne_zero.mpr (toPoly_injective.ne (Subtype.coe_injective.ne hm))
    have hdeg : (toPoly m.1 - toPoly m'.1).natDegree ≤ ℓ := (natDegree_sub_le _ _).trans <|
      max_le ((monic_toPoly m.1).2.trans_le m.2) ((monic_toPoly m'.1).2.trans_le m'.2)
    have hE : X * (toPoly m.1 - toPoly m'.1) - C d ≠ 0 := fun h0 => by
      have h1 := congrArg natDegree (sub_eq_zero.mp h0)
      rw [natDegree_X_mul hD, natDegree_C] at h1
      exact Nat.succ_ne_zero _ h1
    calc (Finset.univ.filter fun k => xpolyHash k m.1 - xpolyHash k m'.1 = d).card
        ≤ (X * (toPoly m.1 - toPoly m'.1) - C d).roots.toFinset.card := by
          refine Finset.card_le_card fun k hk => ?_
          rw [Multiset.mem_toFinset, mem_roots hE, IsRoot.def, eval_sub, eval_mul, eval_X,
            eval_C, eval_sub, eval_toPoly, eval_toPoly, sub_eq_zero, mul_sub]
          exact (Finset.mem_filter.mp hk).2
      _ ≤ (X * (toPoly m.1 - toPoly m'.1) - C d).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X * (toPoly m.1 - toPoly m'.1) - C d).natDegree := card_roots' _
      _ ≤ ℓ + 1 := (natDegree_sub_le _ _).trans <| max_le
          (by rw [natDegree_X_mul hD]; exact Nat.succ_le_succ hdeg)
          (by rw [natDegree_C]; exact Nat.zero_le _)
  push_cast at h
  exact h

end Cslib.Probability
