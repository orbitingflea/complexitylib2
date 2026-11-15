/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable
public import CslibFrontier.Probability.Product
public import Mathlib.Data.ZMod.ValMinAbs
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Encryption-based reusable fuzzy extractor from LWE: construction and reduction step

This file formalizes the encryption-based strongly reusable fuzzy extractor from
Learning With Errors of Apon, Cho, Eldefrawy, and Katz ([AponChoEldefrawyKatz2017],
Section 5), which the paper proves strongly reusable in the standard model without random
oracles. We formalize the construction, its correctness, and the reduction step of the Section 5
security argument as a concrete advantage inequality; the security theorem itself is future work
(see below).

## Construction (Section 5)

Given a public matrix `A : Matrix (Fin m) (Fin n) (ZMod q)`, an encryption error sampler
`E : ProbComp (Fin l → ZMod q)`, and a syndrome decoder
`decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
  ProbComp (Option (Fin n → ZMod q))`:
* **Symmetric-key encryption (`symEncrypt`)**: given secret `s : Fin n → ZMod q` and key
  `r : Fin l → Bool`, sample uniform `B : Matrix (Fin l) (Fin n) (ZMod q)` and error
  `e ← E`, and output `(B, B s + e + ⌊q / 2⌋ r)`.
* **Symmetric-key decryption (`symDecrypt`)**: given `s`, `B`, and `h`, compute `h - B s`
  and apply the `[3q / 8, 5q / 8]` threshold decoder coordinatewise.
* **Generation (`lweEncryptFuzzyExtractor.gen`)**: on reading `w : Fin m → ZMod q`, sample
  uniform `s : Fin n → ZMod q` and uniform key `r : Fin l → Bool`, encrypt
  `(B, h) ← symEncrypt E s r`, and output `(r, ⟨A s + w, B, h⟩)`.
* **Reproduction (`lweEncryptFuzzyExtractor.rep`)**: on close reading `w'` and helper
  `⟨c, B, h⟩`, decode `c - w'` with `decode A`; on `some s`, output `symDecrypt s B h`.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor.encodeHalfBit`,
  `Cslib.Crypto.FuzzyExtractor.encodeHalfBits`,
  `Cslib.Crypto.FuzzyExtractor.decodeThresholdBit`,
  `Cslib.Crypto.FuzzyExtractor.decodeThresholdBits`: half-modulus bit encoding and
  `[3q / 8, 5q / 8]` threshold decoding over `ZMod q`.
* `Cslib.Crypto.FuzzyExtractor.symEncrypt`, `Cslib.Crypto.FuzzyExtractor.symDecrypt`: the
  LWE-based symmetric-key encryption scheme `(Enc, Dec)` of Section 5.
* `Cslib.Crypto.FuzzyExtractor.EncryptHelper`,
  `Cslib.Crypto.FuzzyExtractor.lweEncryptFuzzyExtractor`: helper structure `(c, B, h)` and
  the Section 5 encryption-based reusable fuzzy extractor.
* `Cslib.Crypto.FuzzyExtractor.encryptLWEErrorLaw`,
  `Cslib.Crypto.FuzzyExtractor.encryptSimQueryLoop`,
  `Cslib.Crypto.FuzzyExtractor.encryptRealReduction`,
  `Cslib.Crypto.FuzzyExtractor.encryptIdealReduction`: the combined `(m + (Q + 1) * l)`-row
  LWE error distribution and the real/ideal LWE reductions simulating `Q` shift queries.

## Main results

* `Cslib.Crypto.FuzzyExtractor.decodeThresholdBit_add_encodeHalfBit`,
  `Cslib.Crypto.FuzzyExtractor.decodeThresholdBits_add_encodeHalfBits`,
  `Cslib.Crypto.FuzzyExtractor.symDecrypt_symEncrypt_eq`: deterministic decryption
  correctness whenever every coordinate `e i` of the encryption error satisfies
  `8 * (e i).valMinAbs.natAbs + 4 ≤ q`.
* `Cslib.Crypto.FuzzyExtractor.DecoderCorrectWithError.setupCorrect_lweEncryptFuzzyExtractor`:
  if `decode` fails with probability at most `δ` over a uniform matrix
  (`DecoderCorrectWithError decode t δ`) and every error vector in `(ProbComp.eval E).support`
  has centered coordinates bounded by `8 * (e i).valMinAbs.natAbs + 4 ≤ q`, then
  `lweEncryptFuzzyExtractor` reproduces with error at most `δ`, averaged over a uniform `A`.
* `Cslib.Crypto.FuzzyExtractor.realGame_encryptRealReduction`,
  `Cslib.Crypto.FuzzyExtractor.realGame_encryptIdealReduction`,
  `Cslib.Crypto.FuzzyExtractor.randomGame_encryptRealReduction_eq_ideal`: exact game
  identities linking the real and random LWE games of `encryptRealReduction` and
  `encryptIdealReduction` to `strongReuseRealGame` and `strongReuseIdealGame`.
* `Cslib.Crypto.FuzzyExtractor.strongReuseAdvantage_lweEncryptFuzzyExtractor_le`: the reduction
  step of the Section 5 argument. For every biometric source `W`, encryption error sampler `E`,
  error bound `t`, query count `Q`, and strong-reusability adversary `adv`,
  `strongReuseAdvantage ≤ LWE.advantage uniform errs (encryptRealReduction t Q adv) +
    LWE.advantage uniform errs (encryptIdealReduction t Q adv)`,
  where the combined LWE instance has `m + (Q + 1) * l` rows and error law
  `errs = encryptLWEErrorLaw W (ProbComp.eval E) Q`. When `W = χ^m`, `E = χ^l`, and `l = m`,
  this is the paper's `LWE_{n, (t + 2) m, q, χ}` ([AponChoEldefrawyKatz2017], Section 5).
  Here `Q` is the letter `t` of Section 5, the number of oracle calls the adversary makes. It is
  not the Hamming bound `t` of Definitions 1–3, which is the argument `t` of these lemmas.

## What is not proved

* The strong-reusability security theorem. The adversary in
  `strongReuseAdvantage_lweEncryptFuzzyExtractor_le` is unrestricted. Concluding strong
  reusability from `DecisionLWEWithErrors` needs an adversary class in the reuse experiments and
  efficiency certificates for `encryptRealReduction` and `encryptIdealReduction`; this is future
  work, recorded under "Reusable fuzzy extractors from LWE" in `roadmap/cryptography.md`. For
  i.i.d. errors, `decisionLWE_iff_decisionLWEWithErrors` connects that conclusion to
  `DecisionLWE`.

## References

* [D. Apon, C. Cho, K. Eldefrawy, and J. Katz, *Efficient, Reusable Fuzzy Extractors from
  LWE*][AponChoEldefrawyKatz2017], Section 5.
-/

public section

namespace Cslib.Crypto.FuzzyExtractor

open Probability
open scoped _root_.Matrix ENNReal NNReal

variable {m n l q : ℕ} [NeZero q]

/-! ### Half-Modulus Encoding and `[3q / 8, 5q / 8]` Threshold Decoding -/

/-- Half-modulus bit encoding in `ZMod q` ([AponChoEldefrawyKatz2017], Section 5):
`false ↦ 0` and `true ↦ ⌊q / 2⌋`. -/
@[expose] def encodeHalfBit (q : ℕ) (b : Bool) : ZMod q :=
  if b then ((q / 2 : ℕ) : ZMod q) else 0

/-- Coordinatewise half-modulus encoding of an `l`-bit key `r : Fin l → Bool` in
`Fin l → ZMod q`. -/
@[expose] def encodeHalfBits (q : ℕ) {l : ℕ} (r : Fin l → Bool) : Fin l → ZMod q :=
  fun i => encodeHalfBit q (r i)

/-- Per-coordinate threshold decoder in `ZMod q` ([AponChoEldefrawyKatz2017], Section 5):
outputs `true` iff the canonical residue `x.val` lies in `[3q / 8, 5q / 8]`, i.e.,
`3 * q ≤ 8 * x.val ∧ 8 * x.val ≤ 5 * q`. -/
@[expose] def decodeThresholdBit (q : ℕ) (x : ZMod q) : Bool :=
  decide (3 * q ≤ 8 * x.val ∧ 8 * x.val ≤ 5 * q)

/-- Coordinatewise threshold decoding of a vector `v : Fin l → ZMod q` to `Fin l → Bool`. -/
@[expose] def decodeThresholdBits (q : ℕ) {l : ℕ} (v : Fin l → ZMod q) : Fin l → Bool :=
  fun i => decodeThresholdBit q (v i)

/-- If an integer error `z : ℤ` satisfies `8 * z.natAbs + 4 ≤ q`, then adding `(z : ZMod q)`
to `encodeHalfBit q b` decodes back to `b` under the `[3q / 8, 5q / 8]` threshold decoder. -/
theorem decodeThresholdBit_intCast_add_encodeHalfBit (b : Bool) (z : ℤ)
    (hz : 8 * z.natAbs + 4 ≤ q) :
    decodeThresholdBit q ((z : ZMod q) + encodeHalfBit q b) = b := by
  have hupper : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
  have hlower : -(z.natAbs : ℤ) ≤ z := by
    have := Int.le_natAbs (a := -z)
    simpa only [Int.natAbs_neg, neg_neg] using neg_le_neg this
  have hmod : ∀ x : ℤ, 0 ≤ x → x < (q : ℤ) →
      (((x : ZMod q).val : ℕ) : ℤ) = x := by
    intro x hx hx'
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hx hx']
  cases b
  · simp only [encodeHalfBit, Bool.false_eq_true, ↓reduceIte, add_zero, decodeThresholdBit,
      decide_eq_false_iff_not, not_and_or, not_le]
    by_cases hnonneg : 0 ≤ z
    · left
      have hval := hmod z hnonneg (by omega)
      omega
    · right
      have hcast : ((z + (q : ℤ) : ℤ) : ZMod q) = (z : ZMod q) := by
        rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
      have hval : (((z : ZMod q).val : ℕ) : ℤ) = z + (q : ℤ) := by
        rw [← hcast]
        exact hmod (z + (q : ℤ)) (by omega) (by omega)
      omega
  · simp only [encodeHalfBit, ↓reduceIte, decodeThresholdBit, decide_eq_true_eq]
    have hcast : (z : ZMod q) + ((q / 2 : ℕ) : ZMod q) =
        ((z + ((q / 2 : ℕ) : ℤ) : ℤ) : ZMod q) := by
      rw [Int.cast_add, Int.cast_natCast]
    rw [hcast]
    have hval := hmod (z + ((q / 2 : ℕ) : ℤ)) (by omega) (by omega)
    omega

/-- If a residue `e : ZMod q` has centered representative `e.valMinAbs` satisfying
`8 * e.valMinAbs.natAbs + 4 ≤ q`, then `decodeThresholdBit q (e + encodeHalfBit q b) = b`. -/
theorem decodeThresholdBit_add_encodeHalfBit (b : Bool) (e : ZMod q)
    (he : 8 * e.valMinAbs.natAbs + 4 ≤ q) :
    decodeThresholdBit q (e + encodeHalfBit q b) = b := by
  simpa only [ZMod.coe_valMinAbs] using
    decodeThresholdBit_intCast_add_encodeHalfBit (q := q) b e.valMinAbs he

/-- Coordinatewise threshold decoding recovers `r : Fin l → Bool` from
`e + encodeHalfBits q r` whenever every coordinate `e i` satisfies
`8 * (e i).valMinAbs.natAbs + 4 ≤ q`. -/
theorem decodeThresholdBits_add_encodeHalfBits (r : Fin l → Bool) (e : Fin l → ZMod q)
    (he : ∀ i : Fin l, 8 * (e i).valMinAbs.natAbs + 4 ≤ q) :
    decodeThresholdBits q (e + encodeHalfBits q r) = r := by
  ext i
  exact decodeThresholdBit_add_encodeHalfBit (r i) (e i) (he i)

/-! ### Section 5 Symmetric Encryption and Fuzzy Extractor Construction -/

/-- Symmetric-key encryption `Enc_s(r)` of [AponChoEldefrawyKatz2017], Section 5:
sample uniform `B : Matrix (Fin l) (Fin n) (ZMod q)` and error `e ← E`, and output
`(B, B s + e + ⌊q / 2⌋ r)`. -/
@[expose] noncomputable def symEncrypt (E : ProbComp (Fin l → ZMod q))
    (s : Fin n → ZMod q) (r : Fin l → Bool) :
    ProbComp (Matrix (Fin l) (Fin n) (ZMod q) × (Fin l → ZMod q)) := do
  let B ← ProbComp.uniform (Matrix (Fin l) (Fin n) (ZMod q))
  let e ← E
  return (B, B.mulVec s + e + encodeHalfBits q r)

/-- Symmetric-key decryption `Dec_s(B, h)` of [AponChoEldefrawyKatz2017], Section 5:
compute `h - B s` and apply the `[3q / 8, 5q / 8]` threshold decoder coordinatewise. -/
@[expose] def symDecrypt (s : Fin n → ZMod q)
    (B : Matrix (Fin l) (Fin n) (ZMod q)) (h : Fin l → ZMod q) : Fin l → Bool :=
  decodeThresholdBits q (h - B.mulVec s)

/-- Deterministic decryption identity: `symDecrypt s B (B s + e + encodeHalfBits q r) = r`
whenever every coordinate of `e` satisfies `8 * (e i).valMinAbs.natAbs + 4 ≤ q`. -/
theorem symDecrypt_symEncrypt_eq (s : Fin n → ZMod q)
    (B : Matrix (Fin l) (Fin n) (ZMod q)) (e : Fin l → ZMod q) (r : Fin l → Bool)
    (he : ∀ i : Fin l, 8 * (e i).valMinAbs.natAbs + 4 ≤ q) :
    symDecrypt s B (B.mulVec s + e + encodeHalfBits q r) = r := by
  have hsub : B.mulVec s + e + encodeHalfBits q r - B.mulVec s = e + encodeHalfBits q r := by
    abel
  rw [symDecrypt, hsub, decodeThresholdBits_add_encodeHalfBits r e he]

/-- Helper data `P = (c, B, h)` for the Section 5 encryption-based reusable fuzzy extractor
([AponChoEldefrawyKatz2017], Section 5), consisting of:
* `codeOffset`: the code-offset vector `c = A s + w : Fin m → ZMod q`,
* `encMatrix`: the fresh encryption matrix `B : Matrix (Fin l) (Fin n) (ZMod q)`,
* `ciphertext`: the LWE ciphertext vector `h = B s + e + ⌊q / 2⌋ r : Fin l → ZMod q`. -/
structure EncryptHelper (m n l q : ℕ) where
  /-- Code-offset vector `c = A s + w`. -/
  codeOffset : Fin m → ZMod q
  /-- Fresh LWE matrix `B` for symmetric-key encryption. -/
  encMatrix : Matrix (Fin l) (Fin n) (ZMod q)
  /-- LWE ciphertext vector `h = B s + e + ⌊q / 2⌋ r`. -/
  ciphertext : Fin l → ZMod q
  deriving DecidableEq

instance : Inhabited (EncryptHelper m n l q) :=
  ⟨⟨0, 0, 0⟩⟩

/-- The Section 5 encryption-based reusable fuzzy extractor from LWE
([AponChoEldefrawyKatz2017], Section 5), parameterized by the public matrix
`A : Matrix (Fin m) (Fin n) (ZMod q)`, encryption error sampler `E : ProbComp (Fin l → ZMod q)`,
and syndrome decoder `decode`:
* `gen w`: sample uniform secret `s : Fin n → ZMod q` and uniform key `r : Fin l → Bool`,
  encrypt `(B, h) ← symEncrypt E s r`, and output `(r, ⟨A s + w, B, h⟩)`.
* `rep w' ⟨c, B, h⟩`: decode `c - w'` using `decode A`; on `some s`, output
  `symDecrypt s B h` (defaulting to `fun _ => false` on `none`). -/
@[expose] noncomputable def lweEncryptFuzzyExtractor (m n l q : ℕ) [NeZero q]
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (A : Matrix (Fin m) (Fin n) (ZMod q)) :
    FuzzyExtractor (Fin m → ZMod q) (Fin l → Bool) (EncryptHelper m n l q) where
  gen w := do
    let s ← ProbComp.uniform (Fin n → ZMod q)
    let r ← ProbComp.uniform (Fin l → Bool)
    let (B, h) ← symEncrypt E s r
    return (r, ⟨A.mulVec s + w, B, h⟩)
  rep w' helper := do
    let sOpt ← decode A (helper.codeOffset - w')
    match sOpt with
    | some s => return symDecrypt s helper.encMatrix helper.ciphertext
    | none => return fun _ => false

/-! ### Section 5 Correctness -/

/-- If `decode` fails with probability at most `δ` over a uniform matrix
(`DecoderCorrectWithError decode t δ`) and every error vector `e` in the support of `E` satisfies
`8 * (e i).valMinAbs.natAbs + 4 ≤ q` for all `i : Fin l`, then
`lweEncryptFuzzyExtractor m n l q E decode` reproduces with error at most `δ` for readings at
Hamming distance at most `t`, averaged over a uniform public matrix `A`
([AponChoEldefrawyKatz2017], Section 5). Decryption is exact once decoding succeeds, so the only
failure is a decoding failure. -/
theorem DecoderCorrectWithError.setupCorrect_lweEncryptFuzzyExtractor
    {E : ProbComp (Fin l → ZMod q)}
    {decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))}
    {t : ℕ} {δ : ℝ≥0} (hdec : DecoderCorrectWithError decode t δ)
    (herr : ∀ e ∈ (ProbComp.eval E).support, ∀ i : Fin l, 8 * (e i).valMinAbs.natAbs + 4 ≤ q) :
    SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
      (lweEncryptFuzzyExtractor m n l q E decode) t δ := by
  intro w w' hdis
  rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub] at hdis
  rw [← ENNReal.coe_le_coe]
  simp only [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simp only [setupReproduceGame, FuzzyExtractor.reproduceGame, FuzzyExtractor.reproduceCheck,
    lweEncryptFuzzyExtractor, symEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))
    (PMF.uniformOfFintype (Fin n → ZMod q))]
  refine PMF.bind_apply_le_on_support _ fun s _ => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))
    (PMF.uniformOfFintype (Fin l → Bool))]
  refine PMF.bind_apply_le_on_support _ fun r _ => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))
    (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))]
  refine PMF.bind_apply_le_on_support _ fun B _ => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))) (ProbComp.eval E)]
  refine PMF.bind_apply_le_on_support _ fun e he => ?_
  simp only [add_sub_assoc]
  exact uniform_bind_decode_bind_apply_false_le_of_failProbability_le decode s (w - w') _
    (fun A => by simp [symDecrypt_symEncrypt_eq s B e r (herr e he)]) (hdec s (w - w') hdis)

/-! ### Row-Block Splitting for `(m + (Q + 1) * l)`-Row LWE Instances -/

/-- Index equivalence partitioning `Fin (m + (Q + 1) * l)` into:
* `Sum.inl i` (`i : Fin m`) for the `m` rows of the public matrix `A`,
* `Sum.inr (Sum.inl i)` (`i : Fin l`) for the `l` rows of the challenge encryption matrix `B`,
* `Sum.inr (Sum.inr (k, i))` (`k : Fin Q`, `i : Fin l`) for row `i` of the `k`-th shift-query
  encryption matrix `B_k`. -/
private def rowIndexEquiv (m l Q : ℕ) :
    Fin m ⊕ (Fin l ⊕ (Fin Q × Fin l)) ≃ Fin (m + (Q + 1) * l) :=
  (Equiv.sumCongr (Equiv.refl (Fin m))
    ((Equiv.sumCongr (Equiv.refl (Fin l)) finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by ring))))).trans finSumFinEquiv

/-- Stack an `m`-row block, an `l`-row block, and `Q` blocks of `l` rows into a single
`(m + (Q + 1) * l)`-row family. -/
private def joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    Fin (m + (Q + 1) * l) → α :=
  fun idx =>
    match (rowIndexEquiv m l Q).symm idx with
    | Sum.inl i => xA i
    | Sum.inr (Sum.inl i) => xB i
    | Sum.inr (Sum.inr (k, i)) => xQ k i

/-- Extract the top `m`-row block from a `(m + (Q + 1) * l)`-row family. -/
private def headRows {m l Q : ℕ} {α : Type} (f : Fin (m + (Q + 1) * l) → α) : Fin m → α :=
  fun i => f (rowIndexEquiv m l Q (Sum.inl i))

/-- Extract the challenge `l`-row block from a `(m + (Q + 1) * l)`-row family. -/
private def challengeRows {m l Q : ℕ} {α : Type} (f : Fin (m + (Q + 1) * l) → α) : Fin l → α :=
  fun i => f (rowIndexEquiv m l Q (Sum.inr (Sum.inl i)))

/-- Extract the `Q` query blocks of `l` rows each from a `(m + (Q + 1) * l)`-row family. -/
private def queryRows {m l Q : ℕ} {α : Type} (f : Fin (m + (Q + 1) * l) → α) : Fin Q → Fin l → α :=
  fun k i => f (rowIndexEquiv m l Q (Sum.inr (Sum.inr (k, i))))

/-- Extract the top `m × n` matrix block from an `(m + (Q + 1) * l) × n` matrix. -/
private def headMatrixRows {m n l Q : ℕ} {α : Type}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  headRows M

/-- Extract the challenge `l × n` matrix block from an `(m + (Q + 1) * l) × n` matrix. -/
private def challengeMatrixRows {m n l Q : ℕ} {α : Type}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α) : Matrix (Fin l) (Fin n) α :=
  challengeRows M

/-- Extract the `Q` query matrix blocks of size `l × n` from an `(m + (Q + 1) * l) × n` matrix. -/
private def queryMatrixRows {m n l Q : ℕ} {α : Type}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α) : Fin Q → Matrix (Fin l) (Fin n) α :=
  queryRows M

private def joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    Matrix (Fin (m + (Q + 1) * l)) (Fin n) α :=
  joinRows A B B_vec

@[simp]
private theorem headRows_joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    headRows (joinRows xA xB xQ) = xA := by
  ext i
  simp [headRows, joinRows]

@[simp]
private theorem challengeRows_joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    challengeRows (joinRows xA xB xQ) = xB := by
  ext i
  simp [challengeRows, joinRows]

@[simp]
private theorem queryRows_joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    queryRows (joinRows xA xB xQ) = xQ := by
  ext k i
  simp [queryRows, joinRows]

@[simp]
private theorem headMatrixRows_joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    headMatrixRows (joinMatrixRows A B B_vec) = A :=
  headRows_joinRows A B B_vec

@[simp]
private theorem challengeMatrixRows_joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    challengeMatrixRows (joinMatrixRows A B B_vec) = B :=
  challengeRows_joinRows A B B_vec

@[simp]
private theorem queryMatrixRows_joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    queryMatrixRows (joinMatrixRows A B B_vec) = B_vec :=
  queryRows_joinRows A B B_vec

@[simp]
private theorem joinRows_headRows_challengeRows_queryRows {m l Q : ℕ} {α : Type}
    (f : Fin (m + (Q + 1) * l) → α) :
    joinRows (headRows f) (challengeRows f) (queryRows f) = f := by
  ext idx
  simp only [joinRows, headRows, challengeRows, queryRows]
  rcases h : (rowIndexEquiv m l Q).symm idx with i | (i | ⟨k, i⟩) <;>
    simp [← h]

private def splitRowsEquiv (m l Q : ℕ) (α : Type) :
    (Fin m → α) × ((Fin l → α) × (Fin Q → Fin l → α)) ≃ (Fin (m + (Q + 1) * l) → α) where
  toFun p :=
    let (xA, rest) := p
    let (xB, xQ) := rest
    joinRows xA xB xQ
  invFun f := (headRows f, (challengeRows f, queryRows f))
  left_inv p := by
    obtain ⟨xA, xB, xQ⟩ := p
    simp
  right_inv f := by simp

private def splitMatrixRowsEquiv (m n l Q : ℕ) (α : Type) :
    Matrix (Fin m) (Fin n) α × (Matrix (Fin l) (Fin n) α × (Fin Q → Matrix (Fin l) (Fin n) α)) ≃
      Matrix (Fin (m + (Q + 1) * l)) (Fin n) α :=
  splitRowsEquiv m l Q (Fin n → α)

@[simp]
private theorem headRows_mulVec_add {m n l Q q : ℕ}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (err : Fin (m + (Q + 1) * l) → ZMod q) :
    headRows (M *ᵥ s + err) = (headMatrixRows M).mulVec s + headRows err := rfl

@[simp]
private theorem challengeRows_mulVec_add {m n l Q q : ℕ}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (err : Fin (m + (Q + 1) * l) → ZMod q) :
    challengeRows (M *ᵥ s + err) = (challengeMatrixRows M).mulVec s + challengeRows err := rfl

@[simp]
private theorem queryRows_mulVec_add {m n l Q q : ℕ}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (err : Fin (m + (Q + 1) * l) → ZMod q) :
    queryRows (M *ᵥ s + err) = fun k => (queryMatrixRows M k).mulVec s + queryRows err k := rfl

private theorem uniform_bind_splitRows {m l Q : ℕ} {α β : Type} [Fintype α] [Nonempty α]
    (k : (Fin (m + (Q + 1) * l) → α) → PMF β) :
    (PMF.uniformOfFintype (Fin (m + (Q + 1) * l) → α)).bind k =
      (PMF.uniformOfFintype (Fin m → α)).bind fun xA =>
        (PMF.uniformOfFintype (Fin l → α)).bind fun xB =>
          (PMF.uniformOfFintype (Fin Q → Fin l → α)).bind fun xQ =>
            k (joinRows xA xB xQ) := by
  rw [← Probability.PMF.uniformOfFintype_bind_bind_equiv (splitRowsEquiv m l Q α) k]
  congr 1 with xA : 1
  rw [← Probability.PMF.uniformOfFintype_bind_bind_equiv (Equiv.refl _)
    (fun b => k ((splitRowsEquiv m l Q α) (xA, b)))]
  rfl

private theorem uniform_bind_splitMatrixRows {m n l Q : ℕ} {α β : Type}
    [Fintype α] [Inhabited α]
    (k : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α → PMF β) :
    (PMF.uniformOfFintype (Matrix (Fin (m + (Q + 1) * l)) (Fin n) α)).bind k =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) α)).bind fun A =>
        (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) α)).bind fun B =>
          (PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) α)).bind fun B_vec =>
            k (joinMatrixRows A B B_vec) := by
  rw [← Probability.PMF.uniformOfFintype_bind_bind_equiv (splitMatrixRowsEquiv m n l Q α) k]
  congr 1 with A : 1
  rw [← Probability.PMF.uniformOfFintype_bind_bind_equiv (Equiv.refl _)
    (fun b => k ((splitMatrixRowsEquiv m n l Q α) (A, b)))]
  rfl

/-! ### Section 5 Strong Reusability Reduction to Decisional LWE -/

/-- The product error distribution on `Fin (m + (Q + 1) * l) → ZMod q` for the Section 5
strong-reusability LWE reduction ([AponChoEldefrawyKatz2017], Section 5):
* the first `m` coordinates are drawn from the biometric source `W`;
* the next `l` coordinates (challenge encryption error) are drawn from `E`;
* the remaining `Q` blocks of `l` coordinates (shift-query encryption errors) are drawn
  independently from `E`.
When `W = χ^m`, `E = χ^l`, and `l = m`, this is `χ^{(Q + 2) m}`, matching `LWE_{n, (t + 2) m, q, χ}`
in [AponChoEldefrawyKatz2017], Section 5, where `t` is the number of oracle calls (our `Q`), not the
Hamming bound. -/
noncomputable def encryptLWEErrorLaw {m l q : ℕ} [NeZero q]
    (W : PMF (Fin m → ZMod q)) (E : PMF (Fin l → ZMod q)) (Q : ℕ) :
    PMF (Fin (m + (Q + 1) * l) → ZMod q) :=
  W.bind fun w =>
    E.bind fun e₀ =>
      (Probability.PMF.pi (fun _ : Fin Q => E)).bind fun eQ =>
        PMF.pure (joinRows w e₀ eQ)

/-- With a uniform source and uniform encryption errors, the combined error law of
`encryptLWEErrorLaw` is uniform on all `m + (Q + 1) * l` rows. Together with
`LWE.advantage_uniform_error_eq_zero`, this shows that the right-hand side of
`strongReuseAdvantage_lweEncryptFuzzyExtractor_le` can be `0`. -/
theorem encryptLWEErrorLaw_uniform (Q : ℕ) :
    encryptLWEErrorLaw (PMF.uniformOfFintype (Fin m → ZMod q))
        (PMF.uniformOfFintype (Fin l → ZMod q)) Q =
      PMF.uniformOfFintype (Fin (m + (Q + 1) * l) → ZMod q) := by
  rw [encryptLWEErrorLaw, Probability.PMF.pi_uniformOfFintype,
    ← uniform_bind_splitRows PMF.pure, PMF.bind_pure]

/-- Simulate `qRem` shift queries of a strong-reusability adversary `adv` using pre-allocated
`l`-row LWE blocks `(B_k, b_k)` ([AponChoEldefrawyKatz2017], Section 5, step 2 of the
simulation on p. 12): on shift `δ`, clamp `δ` to weight `≤ t`, sample fresh uniform
`s' : Fin n → ZMod q` and key `r_i : Fin l → Bool`, form `c_i = c* + A s' + clampShift t δ` and
`h_i = b_k + B_k s' + encodeHalfBits q r_i`, and pass `(⟨c_i, B_k, h_i⟩, r_i)` to
`adv.observe`. The simulator never sees `s`, `w*`, or the LWE errors. -/
noncomputable def encryptSimQueryLoop {m n l q : ℕ} [NeZero q] {St : Type}
    (t : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q)) (cStar : Fin m → ZMod q)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St) :
    (qRem : ℕ) →
    (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q)) →
    (Fin qRem → Fin l → ZMod q) →
    St → ProbComp St
  | 0, _, _, st => return st
  | qRem + 1, B_vec, b_vec, st => do
    let (st', δ) ← adv.shift st
    let δ' := clampShift t δ
    let s' ← ProbComp.uniform (Fin n → ZMod q)
    let r_i ← ProbComp.uniform (Fin l → Bool)
    let B₀ := B_vec 0
    let b₀ := b_vec 0
    let c_i := cStar + A.mulVec s' + δ'
    let h_i := b₀ + B₀.mulVec s' + encodeHalfBits q r_i
    let st'' ← adv.observe st' (⟨c_i, B₀, h_i⟩, r_i)
    encryptSimQueryLoop t A cStar adv qRem (Fin.tail B_vec) (Fin.tail b_vec) st''

/-- The real-key LWE reduction of [AponChoEldefrawyKatz2017], Section 5 (simulation on p. 12):
given an `(m + (Q + 1) * l)`-row LWE instance `(M, b)`, extract:
* `(A, c*) = (headMatrixRows M, headRows b)` for the public matrix and challenge code-offset vector,
* `(B, b₁) = (challengeMatrixRows M, challengeRows b)` for the challenge encryption,
* `(B_vec, b_vec) = (queryMatrixRows M, queryRows b)` for the `Q` shift queries;
sample a uniform challenge key `r* : Fin l → Bool`, set `h* = b₁ + encodeHalfBits q r*`,
run `adv` with `encryptSimQueryLoop`, and pass `r*` to `adv.guess`.
The reduction never sees the secret `s`, reading `w*`, or encryption errors. -/
noncomputable def encryptRealReduction {m n l q : ℕ} [NeZero q] {St : Type}
    (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (b : Fin (m + (Q + 1) * l) → ZMod q) : Experiment := do
  let A := headMatrixRows M
  let cStar := headRows b
  let B := challengeMatrixRows M
  let b₁ := challengeRows b
  let rStar ← ProbComp.uniform (Fin l → Bool)
  let hStar := b₁ + encodeHalfBits q rStar
  let st₀ ← adv.start A ⟨cStar, B, hStar⟩
  let st ← encryptSimQueryLoop t A cStar adv Q (queryMatrixRows M) (queryRows b) st₀
  adv.guess st rStar

/-- The ideal-key LWE reduction of [AponChoEldefrawyKatz2017], Section 5 (simulation on p. 12):
as `encryptRealReduction`, except `adv.guess` receives an independent uniform key
`u ← ProbComp.uniform (Fin l → Bool)` in place of `r*`. -/
noncomputable def encryptIdealReduction {m n l q : ℕ} [NeZero q] {St : Type}
    (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (b : Fin (m + (Q + 1) * l) → ZMod q) : Experiment := do
  let A := headMatrixRows M
  let cStar := headRows b
  let B := challengeMatrixRows M
  let b₁ := challengeRows b
  let rStar ← ProbComp.uniform (Fin l → Bool)
  let hStar := b₁ + encodeHalfBits q rStar
  let st₀ ← adv.start A ⟨cStar, B, hStar⟩
  let st ← encryptSimQueryLoop t A cStar adv Q (queryMatrixRows M) (queryRows b) st₀
  let u ← ProbComp.uniform (Fin l → Bool)
  adv.guess st u

/-! ### Reduction Equivalence Lemmas -/

private theorem eval_encryptSimQueryLoop_eq {m n l q : ℕ} [NeZero q] {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (t : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (w : Fin m → ZMod q)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (Q : ℕ) (st : St) :
    ((PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) (ZMod q))).bind fun B_vec =>
      (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E)).bind fun e_vec =>
        ProbComp.eval (encryptSimQueryLoop t A (A.mulVec s + w) adv Q B_vec
          (fun k => (B_vec k).mulVec s + e_vec k) st)) =
      ProbComp.eval (reuseQueryLoop t (fun δ => do
        let (r, p) ← (lweEncryptFuzzyExtractor m n l q E decode A).gen (w + δ)
        return (p, r)) adv Q st) := by
  induction Q generalizing st with
  | zero =>
    simp [encryptSimQueryLoop, reuseQueryLoop, ProbComp.eval_pure, PMF.bind_const]
  | succ qRem ih =>
    rw [← Probability.PMF.pi_uniformOfFintype, Probability.PMF.pi_fin_succ qRem,
      Probability.PMF.pi_fin_succ qRem (ProbComp.eval E)]
    simp only [encryptSimQueryLoop, reuseQueryLoop, lweEncryptFuzzyExtractor, symEncrypt,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
      PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def,
      Fin.cons_zero, Fin.tail_cons]
    have htail : ∀ (B₀ : Matrix (Fin l) (Fin n) (ZMod q))
        (B_rest : Fin qRem → Matrix (Fin l) (Fin n) (ZMod q))
        (e₀ : Fin l → ZMod q) (e_rest : Fin qRem → Fin l → ZMod q),
        Fin.tail (fun k : Fin (qRem + 1) =>
          Matrix.mulVec (@Fin.cons qRem (fun _ => Matrix (Fin l) (Fin n) (ZMod q)) B₀ B_rest k) s +
            @Fin.cons qRem (fun _ => Fin l → ZMod q) e₀ e_rest k) =
          fun k : Fin qRem => (B_rest k).mulVec s + e_rest k := by
      intro B₀ B_rest e₀ e_rest
      ext k
      simp [Fin.tail]
    simp_rw [htail, Probability.PMF.pi_uniformOfFintype]
    simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin qRem => ProbComp.eval E))
      (ProbComp.eval (adv.shift st))]
    simp_rw [PMF.bind_comm (ProbComp.eval E) (ProbComp.eval (adv.shift st))]
    simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q)))
      (ProbComp.eval (adv.shift st))]
    rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))
      (ProbComp.eval (adv.shift st))]
    congr 1 with p : 1
    obtain ⟨st', δ⟩ := p
    simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin qRem => ProbComp.eval E))
      (PMF.uniformOfFintype (Fin n → ZMod q))]
    simp_rw [PMF.bind_comm (ProbComp.eval E) (PMF.uniformOfFintype (Fin n → ZMod q))]
    simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q)))
      (PMF.uniformOfFintype (Fin n → ZMod q))]
    rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))
      (PMF.uniformOfFintype (Fin n → ZMod q))]
    have hsec : ∀ (s' : Fin n → ZMod q) (B₀ : Matrix (Fin l) (Fin n) (ZMod q))
        (e₀ : Fin l → ZMod q) (r_i : Fin l → Bool),
        (⟨A.mulVec s + w + A.mulVec s' + clampShift t δ, B₀,
          B₀.mulVec s + e₀ + B₀.mulVec s' + encodeHalfBits q r_i⟩ :
          EncryptHelper m n l q) =
        ⟨A.mulVec (s + s') + (w + clampShift t δ), B₀,
          B₀.mulVec (s + s') + e₀ + encodeHalfBits q r_i⟩ := by
      intro s' B₀ e₀ r_i
      congr 1
      · rw [Matrix.mulVec_add]
        abel
      · rw [Matrix.mulVec_add]
        abel
    simp_rw [hsec]
    refine (Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addLeft s) (fun s₁ =>
      (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q))).bind fun B₀ =>
        (PMF.uniformOfFintype (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q))).bind fun B_rest =>
          (ProbComp.eval E).bind fun e₀ =>
            (Probability.PMF.pi fun _ : Fin qRem => ProbComp.eval E).bind fun e_rest =>
              (PMF.uniformOfFintype (Fin l → Bool)).bind fun r_i =>
                (ProbComp.eval (adv.observe st'
                        ({ codeOffset := A.mulVec s₁ + (w + clampShift t δ), encMatrix := B₀,
                           ciphertext := B₀.mulVec s₁ + e₀ + encodeHalfBits q r_i },
                          r_i))).bind
                  fun st'' => ProbComp.eval (encryptSimQueryLoop t A (A.mulVec s + w) adv qRem
                    B_rest (fun k => (B_rest k).mulVec s + e_rest k) st''))).trans ?_
    congr 1 with s₁ : 1
    simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin qRem => ProbComp.eval E))
      (PMF.uniformOfFintype (Fin l → Bool))]
    simp_rw [PMF.bind_comm (ProbComp.eval E) (PMF.uniformOfFintype (Fin l → Bool))]
    simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q)))
      (PMF.uniformOfFintype (Fin l → Bool))]
    rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))
      (PMF.uniformOfFintype (Fin l → Bool))]
    congr 1 with r_i : 1
    congr 1 with B₀ : 1
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q)))
      (ProbComp.eval E)]
    congr 1 with e₀ : 1
    simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin qRem => ProbComp.eval E))
      (ProbComp.eval (adv.observe st' (⟨A.mulVec s₁ + (w + clampShift t δ), B₀,
        B₀.mulVec s₁ + e₀ + encodeHalfBits q r_i⟩, r_i)))]
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin qRem → Matrix (Fin l) (Fin n) (ZMod q)))
      (ProbComp.eval (adv.observe st' (⟨A.mulVec s₁ + (w + clampShift t δ), B₀,
        B₀.mulVec s₁ + e₀ + encodeHalfBits q r_i⟩, r_i)))]
    congr 1 with st'' : 1
    exact ih st''

private theorem realGame_encrypt_embed {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (K : St → (Fin l → Bool) → PMF Bool) :
    ((PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s =>
      W.bind fun w =>
        (ProbComp.eval E).bind fun e₀ =>
          (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E)).bind fun eQ =>
            (PMF.uniformOfFintype (Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))).bind fun M =>
              (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
                (ProbComp.eval (adv.start (headMatrixRows M)
                  ⟨headRows (M *ᵥ s + joinRows w e₀ eQ), challengeMatrixRows M,
                    challengeRows (M *ᵥ s + joinRows w e₀ eQ) + encodeHalfBits q rStar⟩)).bind
                  fun st₀ =>
                    (ProbComp.eval (encryptSimQueryLoop t (headMatrixRows M)
                      (headRows (M *ᵥ s + joinRows w e₀ eQ)) adv Q
                      (queryMatrixRows M) (queryRows (M *ᵥ s + joinRows w e₀ eQ)) st₀)).bind
                      fun st => K st rStar) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        W.bind fun w =>
          (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s =>
            (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
              (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q))).bind fun B =>
                (ProbComp.eval E).bind fun e₀ =>
                  (ProbComp.eval (adv.start A
                    ⟨A.mulVec s + w, B, B.mulVec s + e₀ + encodeHalfBits q rStar⟩)).bind
                    fun st₀ =>
                      (ProbComp.eval (reuseQueryLoop t (fun δ => do
                        let (r, p) ← (lweEncryptFuzzyExtractor m n l q E decode A).gen (w + δ)
                        return (p, r)) adv Q st₀)).bind fun st => K st rStar := by
  simp_rw [uniform_bind_splitMatrixRows]
  simp only [headRows_mulVec_add, challengeRows_mulVec_add, queryRows_mulVec_add,
    headRows_joinRows, challengeRows_joinRows, queryRows_joinRows,
    headMatrixRows_joinMatrixRows, challengeMatrixRows_joinMatrixRows,
    queryMatrixRows_joinMatrixRows]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin n → ZMod q)) W]
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))) W]
  congr 1 with w : 1
  conv_rhs =>
    rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))
      (PMF.uniformOfFintype (Fin n → ZMod q))]
  congr 1 with s : 1
  simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E))
    (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))]
  rw [PMF.bind_comm (ProbComp.eval E)
    (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))]
  congr 1 with A : 1
  simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E))
    (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))]
  rw [PMF.bind_comm (ProbComp.eval E)
    (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))]
  conv_rhs =>
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → Bool))
      (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))]
  congr 1 with B : 1
  conv_rhs =>
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → Bool)) (ProbComp.eval E)]
  congr 1 with e₀ : 1
  rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E))
    (PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) (ZMod q)))]
  simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E))
    (PMF.uniformOfFintype (Fin l → Bool))]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) (ZMod q)))
    (PMF.uniformOfFintype (Fin l → Bool))]
  congr 1 with rStar : 1
  simp_rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E))
    (ProbComp.eval (adv.start A ⟨A.mulVec s + w, B, B.mulVec s + e₀ + encodeHalfBits q rStar⟩))]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) (ZMod q)))
    (ProbComp.eval (adv.start A ⟨A.mulVec s + w, B, B.mulVec s + e₀ + encodeHalfBits q rStar⟩))]
  congr 1 with st₀ : 1
  have hloop := congrArg (fun p : PMF St => p.bind fun st => K st rStar)
    (eval_encryptSimQueryLoop_eq E decode t A s w adv Q st₀)
  simpa only [PMF.bind_bind] using hloop

/-- The real LWE game against `encryptRealReduction t Q adv` is identically distributed to
the strong-reusability real game `strongReuseRealGame` of `lweEncryptFuzzyExtractor`. -/
theorem realGame_encryptRealReduction {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St) :
    LWE.realGame (PMF.uniformOfFintype (Fin n → ZMod q))
      (encryptLWEErrorLaw W (ProbComp.eval E) Q)
      (encryptRealReduction t Q adv) =
      strongReuseRealGame
        (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
        (lweEncryptFuzzyExtractor m n l q E decode) W t Q adv := by
  have h := realGame_encrypt_embed E decode W t Q adv fun st rStar =>
    ProbComp.eval (adv.guess st rStar)
  simp only [LWE.realGame, LWE.eval_realExperiment, encryptLWEErrorLaw, encryptRealReduction,
    ProbComp.eval_bind, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.pure_bind]
  refine h.trans ?_
  simp only [strongReuseRealGame, Game.withSetup, strongReuseRealExperiment,
    lweEncryptFuzzyExtractor, symEncrypt,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind]

/-- The real LWE game against `encryptIdealReduction t Q adv` is identically distributed to
the strong-reusability ideal game `strongReuseIdealGame` of `lweEncryptFuzzyExtractor`. -/
theorem realGame_encryptIdealReduction {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St) :
    LWE.realGame (PMF.uniformOfFintype (Fin n → ZMod q))
      (encryptLWEErrorLaw W (ProbComp.eval E) Q)
      (encryptIdealReduction t Q adv) =
      strongReuseIdealGame
        (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
        (lweEncryptFuzzyExtractor m n l q E decode) W t Q adv := by
  have h := realGame_encrypt_embed E decode W t Q adv fun st _ =>
    (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => ProbComp.eval (adv.guess st u)
  simp only [LWE.realGame, LWE.eval_realExperiment, encryptLWEErrorLaw, encryptIdealReduction,
    ProbComp.eval_bind, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.pure_bind]
  refine h.trans ?_
  simp only [strongReuseIdealGame, Game.withSetup, strongReuseIdealExperiment,
    lweEncryptFuzzyExtractor, symEncrypt,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind]

private theorem uniform_mask_encodeHalfBits_eq {l q : ℕ} [NeZero q] {St α : Type}
    (G : (Fin l → ZMod q) → PMF St) (H : St → (Fin l → Bool) → PMF α) :
    ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
      (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
        (G (b₁ + encodeHalfBits q rStar)).bind fun st => H st rStar) =
    ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
      (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
        (G (b₁ + encodeHalfBits q rStar)).bind fun st =>
          (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => H st u) := by
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))]
  symm
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))]
  have hshift : ∀ rStar : Fin l → Bool,
      ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
        (G (b₁ + encodeHalfBits q rStar)).bind fun st => H st rStar) =
      (PMF.uniformOfFintype (Fin l → ZMod q)).bind fun hStar =>
        (G hStar).bind fun st => H st rStar :=
    fun rStar => Probability.PMF.uniformOfFintype_bind_equiv
      (Equiv.addRight (encodeHalfBits q rStar))
      (fun hStar => (G hStar).bind fun st => H st rStar)
  have hshift_u : ∀ rStar : Fin l → Bool,
      ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
        (G (b₁ + encodeHalfBits q rStar)).bind fun st =>
          (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => H st u) =
      (PMF.uniformOfFintype (Fin l → ZMod q)).bind fun hStar =>
        (G hStar).bind fun st =>
          (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => H st u :=
    fun rStar => Probability.PMF.uniformOfFintype_bind_equiv
      (Equiv.addRight (encodeHalfBits q rStar))
      (fun hStar => (G hStar).bind fun st =>
        (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => H st u)
  simp_rw [hshift, hshift_u, PMF.bind_const]
  symm
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → Bool))]
  congr 1 with hStar : 1
  exact PMF.bind_comm _ _ _

/-- In the uniform-oracle LWE world (`LWE.randomGame`), `b₁` is uniform on `Fin l → ZMod q`
and independent of the rest of the challenge, so `h* = b₁ + encodeHalfBits q r*` information-
theoretically hides `r*`. Consequently, `encryptRealReduction` and `encryptIdealReduction`
induce the exact same random-world distribution ([AponChoEldefrawyKatz2017], Section 5,
p. 12). -/
theorem randomGame_encryptRealReduction_eq_ideal {St : Type}
    (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St) :
    LWE.randomGame (encryptRealReduction t Q adv) =
      LWE.randomGame (encryptIdealReduction t Q adv) := by
  simp only [LWE.randomGame, LWE.eval_randomExperiment, encryptRealReduction,
    encryptIdealReduction, ProbComp.eval_bind, ProbComp.eval_uniform]
  congr 1 with M : 1
  rw [uniform_bind_splitRows, uniform_bind_splitRows]
  congr 1 with cStar : 1
  simp only [headRows_joinRows, challengeRows_joinRows, queryRows_joinRows]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))
    (PMF.uniformOfFintype (Fin Q → Fin l → ZMod q))]
  symm
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))
    (PMF.uniformOfFintype (Fin Q → Fin l → ZMod q))]
  symm
  congr 1 with b_vec : 1
  simpa only [PMF.bind_bind] using uniform_mask_encodeHalfBits_eq
    (fun hStar =>
      (ProbComp.eval (adv.start (headMatrixRows M)
        ⟨cStar, challengeMatrixRows M, hStar⟩)).bind fun st₀ =>
        ProbComp.eval (encryptSimQueryLoop t (headMatrixRows M) cStar adv Q
          (queryMatrixRows M) b_vec st₀))
    (fun st key => ProbComp.eval (adv.guess st key))

/-- **Strong reusability of the Section 5 encryption-based fuzzy extractor from LWE**
([AponChoEldefrawyKatz2017], Section 5): for every biometric source `W`, encryption error
sampler `E`, error bound `t`, query count `Q`, and strong-reusability adversary `adv`,
the strong-reusability advantage against `lweEncryptFuzzyExtractor` is bounded by the sum
of the decisional LWE advantages of `encryptRealReduction t Q adv` and
`encryptIdealReduction t Q adv` against `(m + (Q + 1) * l)`-sample LWE with uniform secret
on `Fin n → ZMod q` and error distribution `encryptLWEErrorLaw W (ProbComp.eval E) Q`.
When `W = χ^m`, `E = χ^l`, and `l = m`, this corresponds to the paper's `LWE_{n, (t + 2) m, q, χ}`,
whose `t` is the number of oracle calls (our `Q`), not the Hamming bound `t` here. -/
theorem strongReuseAdvantage_lweEncryptFuzzyExtractor_le {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St) :
    strongReuseAdvantage
      (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
      (lweEncryptFuzzyExtractor m n l q E decode) W t Q adv ≤
      LWE.advantage (PMF.uniformOfFintype (Fin n → ZMod q))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptRealReduction t Q adv) +
      LWE.advantage (PMF.uniformOfFintype (Fin n → ZMod q))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptIdealReduction t Q adv) := by
  simp only [strongReuseAdvantage, LWE.advantage,
    ← realGame_encryptRealReduction E decode W t Q adv,
    ← realGame_encryptIdealReduction E decode W t Q adv,
    ← randomGame_encryptRealReduction_eq_ideal t Q adv]
  rw [Game.advantage_comm
    (LWE.realGame (PMF.uniformOfFintype (Fin n → ZMod q))
      (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptIdealReduction t Q adv))]
  exact Game.advantage_triangle _ _ _

end Cslib.Crypto.FuzzyExtractor
