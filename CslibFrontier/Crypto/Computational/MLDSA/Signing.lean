/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
import Batteries.Data.Fin.Lemmas
import Mathlib.Tactic.Ring

/-!
# Bounded ML-DSA signing

FIPS 204 Algorithm 7 signs by rejection sampling. After the response and low-bits checks on
line 23, line 28 performs a second rejection check: `‖c t₀‖∞ < γ₂`, and the hint has at most
`ω` set coefficients. This module adds that complete two-stage acceptance predicate to the
existing semantic ML-DSA surface and gives executable bounded-loop semantics.

The source-shaped loop takes an explicit mask schedule. Attempt `i` uses the counter
`κ + i ℓ`, matching Algorithm 7 line 31. Exhausting the supplied attempt limit returns `none`.
This pure result represents the standard's single error result, but does not model destruction
of intermediate state or side-channel behavior. The model does not identify its explicit mask
schedule with FIPS 204's seeded `ExpandMask`; that requires its distribution and counter behavior.

Appendix C, Table 3 of the published FIPS 204 gives `814` as the minimum permitted bounded
signing limit under its stated hash/XOF distribution assumptions. This module does not derive
the standard's failure estimate from the semantic mask model.

## Main definitions

* `Cslib.Crypto.MLDSA.hintWeight`: number of set hint coefficients.
* `Cslib.Crypto.MLDSA.compressedSignAttempt`: one semantic Algorithm 7 attempt, including
  both rejection stages.
* `Cslib.Crypto.MLDSA.compressedSignBoundedFrom`,
  `Cslib.Crypto.MLDSA.compressedSignBounded`: first successful attempt in a bounded mask
  schedule, with an explicit starting counter or counter zero.

## Main results

* `Cslib.Crypto.MLDSA.signAttempt_eq_some_of_compressedSignAttempt_eq_some`: every compressed
  attempt output is also the corresponding uncompressed attempt output.
* `Cslib.Crypto.MLDSA.compressedVerify_compressedSignAttempt`,
  `Cslib.Crypto.MLDSA.compressedVerify_compressedSignBounded`: accepted attempts and bounded
  signing outputs pass compressed verification.

## References

* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*, Section 6.2, Algorithm 7 and Appendix C][NISTFIPS204]
-/

public section

namespace Cslib.Crypto.MLDSA

variable (P : Params)

/-- Number of set coefficients in an ML-DSA hint vector. This is the quantity compared with
`ω` on line 28 of FIPS 204 Algorithm 7. -/
@[expose] def hintWeight (h : Fin P.k → Fin P.n → Bool) : ℕ :=
  ∑ i, Fin.countP (h i)

/-- The line-28 norm check `‖c t₀‖∞ < γ₂`, stated for the already-computed product. -/
@[expose] def LowProductShort (ct₀ : Fin P.k → Fin P.n → ZMod P.q) : Prop :=
  ∀ i j, |(ct₀ i j).valMinAbs| < P.γ₂

instance (ct₀ : Fin P.k → Fin P.n → ZMod P.q) :
    Decidable (LowProductShort P ct₀) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- One semantic execution of FIPS 204 Algorithm 7 lines 11--30.

The hash and mask are still the abstract values used by `Basic.lean`; seed expansion, the message
representative, byte encodings and malformed-input behavior are not modeled here. Unlike
`signAttempt`, this compressed attempt constructs the FIPS hint and includes both line-28 checks. -/
@[expose] def compressedSignAttempt (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (y : Fin P.ℓ → Fin P.n → ZMod P.q) : Option (CompressedSignature P) :=
  let w := moduleSISMap sk.A y
  let c := H (highBitsVec P w, msg)
  let z := y + fun j => negacyclicMul c (sk.s₁ j)
  let r₀ := w - fun i => negacyclicMul c (sk.s₂ i)
  if ResponseShort P z ∧ LowBitsShort P r₀ then
    let ct₀ := fun i => negacyclicMul c (publicKeyLowPart P d sk.publicKey i)
    let h := fun i => makeHintVec P.q P.γ₂ (-ct₀ i) (r₀ i + ct₀ i)
    if LowProductShort P ct₀ ∧ hintWeight P h ≤ ω then
      some ⟨z, h, c⟩
    else none
  else none

/-- Every compressed attempt output is also the corresponding output of the uncompressed
`signAttempt`; the compressed attempt only adds the second-stage checks and the hint. -/
theorem signAttempt_eq_some_of_compressedSignAttempt_eq_some (d ω : ℕ) (H : Hash P)
    (sk : SecretKey P) (msg : List Bool) (y : Fin P.ℓ → Fin P.n → ZMod P.q)
    {σ : CompressedSignature P} (hout : compressedSignAttempt P d ω H sk msg y = some σ) :
    signAttempt P H sk msg y = some (⟨σ.z, σ.c⟩ : Signature P) := by
  simp only [compressedSignAttempt] at hout
  split_ifs at hout with hshort hfinal
  cases hout
  unfold signAttempt
  rw [ite_eq_left hshort]

/-- **Correctness of one compressed attempt.** Under the secret-key and hash-to-ball bounds,
every signature returned by `compressedSignAttempt` passes `compressedVerify` under the matching
public key. The proof uses the derived compressed/uncompressed commitment bridge and the
`MakeHint`/`UseHint` recovery theorem. -/
theorem compressedVerify_compressedSignAttempt (hP : P.Valid) (hγq : 4 * P.γ₂ < P.q)
    {d ω : ℕ} {H : Hash P} (hH : ∀ x, InBall P.τ (H x)) {sk : SecretKey P}
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η) {msg : List Bool}
    {y : Fin P.ℓ → Fin P.n → ZMod P.q} {σ : CompressedSignature P}
    (hout : compressedSignAttempt P d ω H sk msg y = some σ) :
    compressedVerify P d H sk.publicKey msg σ = true := by
  have : NeZero P.q := ⟨by have := hP.one_lt_q; omega⟩
  have hsign := signAttempt_eq_some_of_compressedSignAttempt_eq_some P d ω H sk msg y hout
  simp only [compressedSignAttempt] at hout
  split_ifs at hout with hshort hfinal
  cases hout
  obtain ⟨hct₀, _⟩ := hfinal
  set w := moduleSISMap sk.A y
  set c := H (highBitsVec P w, msg)
  set r₀ := w - fun i => negacyclicMul c (sk.s₂ i)
  set ct₀ := fun i => negacyclicMul c (publicKeyLowPart P d sk.publicKey i)
  have hverify := verify_signAttempt hP hH hs₂ hsign
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at hverify
  obtain ⟨⟨hz', hc⟩, hhash⟩ := hverify
  simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hz', hc⟩, ?_⟩
  conv_rhs => rw [← hhash]
  congr 1
  apply Prod.ext
  · funext i
    rw [compressedVerifierCommitment_eq_verifierCommitment_add_lowPart,
      verifierCommitment_publicKey]
    simp only [Pi.add_apply]
    rw [useHintVec_makeHintVec hP.γ₂_pos hP.two_mul_γ₂_dvd hγq (z := -ct₀ i)
      (r := r₀ i + ct₀ i) (fun j => by
        simpa only [Pi.neg_apply, Int.abs_eq_natAbs, ZMod.natAbs_valMinAbs_neg] using
          (hct₀ i j).le)]
    funext j
    simp only [highBitsVec, Pi.add_apply, Pi.neg_apply]
    congr 1
    ring
  · rfl

/-- Counter supplied to the `i`-th scheduled attempt. Algorithm 7 starts at `κ` and advances it
by `ℓ` after every rejection. -/
@[expose] def signingAttemptCounter {K : ℕ} (κ : ℕ) (i : Fin K) : ℕ :=
  κ + (i : ℕ) * P.ℓ

/-- The `K` scheduled Algorithm 7 attempts starting from counter `κ`, with line 31's
counter progression built into each mask lookup. -/
@[expose] def compressedSignAttempts (d ω : ℕ) (H : Hash P) (sk : SecretKey P) (msg : List Bool)
    (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (κ K : ℕ) :
    Fin K → Option (CompressedSignature P) :=
  fun i => compressedSignAttempt P d ω H sk msg (maskAt (signingAttemptCounter P κ i))

/-- Bounded Algorithm 7 signing from counter `κ`: return the first accepted signature among
`K` scheduled attempts, or `none` if every attempt rejects. This is the pure semantics of the
finite-maximum option in Section 6.2, footnote 10, and of Algorithm 7 lines 10--32. -/
@[expose] def compressedSignBoundedFrom (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (κ K : ℕ) :
    Option (CompressedSignature P) :=
  Fin.findSome? (compressedSignAttempts P d ω H sk msg maskAt κ K)

/-- Bounded Algorithm 7 signing with the initial counter `κ = 0` from Algorithm 7 line 8. -/
@[expose] def compressedSignBounded (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (K : ℕ) :
    Option (CompressedSignature P) :=
  compressedSignBoundedFrom P d ω H sk msg maskAt 0 K

/-- Every signature returned by bounded signing from an arbitrary starting counter passes
compressed verification under the matching public key. -/
theorem compressedVerify_compressedSignBoundedFrom (hP : P.Valid)
    (hγq : 4 * P.γ₂ < P.q) {d ω : ℕ} {H : Hash P} (hH : ∀ x, InBall P.τ (H x))
    {sk : SecretKey P} (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η) {msg : List Bool}
    {maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q} {κ K : ℕ} {σ : CompressedSignature P}
    (hout : compressedSignBoundedFrom P d ω H sk msg maskAt κ K = some σ) :
    compressedVerify P d H sk.publicKey msg σ = true := by
  obtain ⟨i, hi, _⟩ :=
    (Fin.findSome?_eq_some_iff
      (f := compressedSignAttempts P d ω H sk msg maskAt κ K) (a := σ)).mp
      (by simpa only [compressedSignBoundedFrom] using hout)
  apply compressedVerify_compressedSignAttempt P hP hγq hH hs₂
  simpa only [compressedSignAttempts] using hi

/-- Every signature returned by bounded signing from Algorithm 7's initial counter passes
compressed verification under the matching public key. -/
theorem compressedVerify_compressedSignBounded (hP : P.Valid) (hγq : 4 * P.γ₂ < P.q)
    {d ω : ℕ} {H : Hash P} (hH : ∀ x, InBall P.τ (H x)) {sk : SecretKey P}
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η) {msg : List Bool}
    {maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q} {K : ℕ} {σ : CompressedSignature P}
    (hout : compressedSignBounded P d ω H sk msg maskAt K = some σ) :
    compressedVerify P d H sk.publicKey msg σ = true := by
  apply compressedVerify_compressedSignBoundedFrom P hP hγq hH hs₂
  simpa only [compressedSignBounded] using hout

end Cslib.Crypto.MLDSA
