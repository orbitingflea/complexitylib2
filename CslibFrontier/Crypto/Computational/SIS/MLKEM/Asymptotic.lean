/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Family
public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Security
public import CslibFrontier.Crypto.Computational.LWE.Module.Native
import CslibFrontier.Probability.PMF
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# IND-CPA of K-PKE with ideal coin expansion, from Module-LWE

`indCPA_kpkeIdealCoins_of_decisionModuleLWEWith` is IND-CPA of K-PKE with ideal coin expansion and
the matrix in the public key. Key generation and encryption draw their centered-binomial noise from
fair coins, where Kyber v3.02 and FIPS 203 expand a seed with `PRF`. The public key carries the
sampled matrix in place of the seed `ρ` from which Kyber's encryption re-derives it with `XOF`, and
the adversary has no `XOF` or `G` oracle. It is a step towards Kyber v3.02 ([AvanziEtAl2021],
§4.3.1, Theorem 1, p. 20), not that theorem, which assumes that `XOF` and `G` are random oracles
and whose bound has an `Adv^prf` term. The `PRF` hop is `indCPA_kpkePRF_of_decisionModuleLWEWith`
(`CslibFrontier.Crypto.Computational.SIS.MLKEM.PRFSecurity`), whose last step is this one and which
keeps the matrix in the public key; the random-oracle lift is open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6893099765).

For a K-PKE parameter family `P` computable in polynomial time from the unary security parameter,
the theorem shows that the word-level family `kpke P` is IND-CPA secure (`WordPKE.INDCPA`: every
uniform strict PPT chosen-message adversary has negligible advantage) whenever decision Module-LWE
(`DecisionModuleLWEWith`) holds for the two shapes of Kyber's proof, with the centered-binomial laws
`cbdLaw` (Kyber's `β_η`), from which K-PKE samples (`eval_sampleVecCBD`):

* the public-key shape `k × k` with secret and error `CBD_{η₁}`, the term `Adv^mlwe_{k,k,η₁}`, and
* the ciphertext shape `(k + 1) × k` with secret `CBD_{η₁}` and error `CBD_{η₂}`, the term
  `Adv^mlwer_{k+1,k,η₁,η₂,d_u}` without compression, which is decision Module-LWE with these laws
  ([AvanziEtAl2021], footnote 3, pp. 21–22).

These are the two terms of §4.4, eq. (6), p. 22, which replaces Theorem 1's
`2 · Adv^mlwe_{k+1,k,η}`; the `Adv^prf` term has no counterpart here.

## The proof

A word adversary `A` plays the two-stage experiment of `toExplicitCoinPKE (P κ)` as
`wordAdversary P A κ`, which encodes the public key and ciphertext and decodes the messages. The
word game and this experiment differ only in the matrix of key generation, which the word family
draws within `k * k * n / 2 ^ κ` of uniform (`closeTo_keyGenWord`). The concrete
bound `cpaAdvantage_le` bounds the experiment by four Module-LWE advantages of the explicit
reductions, here as the families `keyReduction P A b` and `ciphertextReduction P A b`
(`advantage_gameOn_le`). Both families are uniform strict PPT whenever `A` is
(`isPPT_keyReduction`, `isPPT_ciphertextReduction`): their runs equal word programs that read the
public key, the challenge ciphertext and the encryption from the Module-LWE sample word with the
natives of `CslibFrontier.Crypto.Computational.SIS.MLKEM.Native` and
`CslibFrontier.Crypto.Computational.LWE.Module.Native`, and run `A`'s stages. The theorem applies
the two assumptions to these reductions through their certificates.

## Differences from Kyber v3.02 Theorem 1

Two differences make this a step and not Theorem 1:

* Key generation and encryption decode fair bits with `SamplePolyCBD`, where Kyber expands a
  32-byte seed with `PRF` (`σ` in key generation, the coins `r` in encryption). This idealizes the
  scheme's own coin expansion, so the bound has no `Adv^prf` term. The `PRF` hops, under
  `PseudorandomFunctionOver`, are in `indCPA_kpkePRF_of_decisionModuleLWEWith`.
* The public key carries the matrix `A`, which key generation draws coefficientwise by the bounded
  modular sampler within `k * k * n / 2 ^ κ` of uniform. In Kyber the public key is
  `Encode(t̂) ‖ ρ` with `(ρ, σ) := G(d)`, and encryption re-derives `A` as `XOF(ρ)` (Algorithms 4
  and 5, pp. 8–9). Theorem 1 assumes that `XOF` and `G` are random oracles, which the adversary may
  query, so a reduction in its model must answer the adversary's `XOF` queries at `ρ` with its
  Module-LWE matrix. Here neither the scheme nor the adversary has an `XOF` or `G` oracle
  (`WordPKE.INDCPA` quantifies over adversaries without oracles), so that step is not formalized.
  The proved distance compares matrix distributions only and does not relate the random-oracle
  game to this one. The random-oracle lift (the scheme with `ρ` in the public key and `XOF` and `G`
  oracles, with a lazily sampled, programmable simulator and its efficiency witness) is open under
  [#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6893099765).

The remaining differences restate Theorem 1 in this library's setting rather than weaken it:

* The ciphertext hop is decision Module-LWE on the uncompressed sample with secret `CBD_{η₁}` and
  error `CBD_{η₂}`, the Module-LWER problem of eq. (6) without compression; the reduction adds the
  message and compresses the ciphertext itself. This assumption implies eq. (6)'s
  `Adv^mlwer_{k+1,k,η₁,η₂,d_u}` term, since compressing a sample maps the Module-LWE games to the
  Module-LWER ones, and at `η₁ = η₂` it is Theorem 1's `Adv^mlwe_{k+1,k,η}` term.
* The statement is asymptotic over a parameter family, against uniform classical strict PPT
  adversaries; the source states concrete bounds at fixed parameter sets with adversaries of
  roughly the same running time. The assumptions are meaningful only when the parameters grow
  with `κ`: at a fixed FIPS 203 parameter set `DecisionModuleLWEWith` fails.
* Polynomials are in coefficient form, keys and ciphertexts are words of residue lists, and
  messages are words of exactly `n` bits.

This is IND-CPA of K-PKE (Kyber.CPAPKE) with ideal coin expansion and the matrix in the public
key; it is not a statement about ML-KEM ([NISTFIPS203]) or its Fujisaki–Okamoto transform.

## Main definitions

* `Cslib.Crypto.MLKEM.cbdLaw`: the centered-binomial law `β_η^k` of the assumptions.
* `Cslib.Crypto.MLKEM.wordAdversary`: the two-stage adversary played by a word adversary.
* `Cslib.Crypto.MLKEM.keyReduction`, `Cslib.Crypto.MLKEM.ciphertextReduction`: the two hops as
  families of decision Module-LWE distinguishers.

## Main results

* `Cslib.Crypto.MLKEM.eval_sampleVecCBD`: K-PKE's vector sampler draws from `cbdLaw`.
* `Cslib.Crypto.MLKEM.isPPT_keyReduction`, `Cslib.Crypto.MLKEM.isPPT_ciphertextReduction`: the
  reductions are uniform strict PPT, from the adversary's certificate.
* `Cslib.Crypto.MLKEM.advantage_gameOn_le`: the concrete bound at each `κ`.
* `Cslib.Crypto.MLKEM.indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`: IND-CPA of K-PKE with
  ideal coin expansion and the matrix in the public key from decision Module-LWE, a step towards
  Kyber v3.02 Theorem 1.

## References

* [R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation
  (version 3.02)*][AvanziEtAl2021], 4 August 2021, §4.3 (p. 19), §4.3.1 (Theorem 1, p. 20) and
  §4.4 (eq. (6) and footnote 3, pp. 21–22)
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203]
-/

public section

namespace Cslib.Crypto.MLKEM

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open scoped NNReal ENNReal

/-! ### Public keys and ciphertexts from Module-LWE sample words -/

section Samples

variable (P : Params)

/-- The public-key word read from the word of a `k × k` Module-LWE sample `(A, t)`: the public key
`(A, t)`. -/
private def keySamplePublicKey (sample : List Bool) : List Bool :=
  let s := ModuleLWE.sampleDecoder.decode sample
  encPublicKeyResidues
    (ModuleLWE.entryResidues P.k P.k P.n ((Decoder.list (Decoder.list Decoder.nat)).decode s.1),
      ModuleLWE.chunkResidues P.k P.n s.2)

/-- The public-key word read from the word of a `(k + 1) × k` Module-LWE sample `(M, w)`: the
public key `unextendPublicKeyMatrix M`, whose matrix is the transpose of rows `1, …, k` of `M` and
whose vector is row `0`. -/
private def extendedSamplePublicKey (sample : List Bool) : List Bool :=
  let s := ModuleLWE.sampleDecoder.decode sample
  let M := ModuleLWE.entryResidues (P.k + 1) P.k P.n
    ((Decoder.list (Decoder.list Decoder.nat)).decode s.1)
  encPublicKeyResidues ((List.range P.k).map fun i => (List.range P.k).map fun j =>
    (M.getD (j + 1) []).getD i [], M.getD 0 [])

/-- The ciphertext word that the ciphertext hop builds from the word of a `(k + 1) × k`
Module-LWE sample `(M, w)` and a message word `m`: the compression of
`unextendCiphertext w + (0, Decompress_1(m))`. -/
private def extendedSampleCiphertext (sample m : List Bool) : List Bool :=
  let w := ModuleLWE.chunkResidues (P.k + 1) P.n (ModuleLWE.sampleDecoder.decode sample).2
  encCiphertextResidues
    (((List.range P.k).map fun i => w.getD (i + 1) []).map (compressResidues P.q P.du),
      compressResidues P.q P.dv (addResidues P.q (w.getD 0 []) (messageResidues P.n P.q m)))

variable [NeZero P.q]

omit [NeZero P.q] in
private theorem keySamplePublicKey_encodeSample (pk : PublicKey P) :
    keySamplePublicKey P (ModuleLWE.encodeSample pk) = encodePublicKey pk := by
  simp only [keySamplePublicKey, ModuleLWE.encodeSample, ModuleLWE.sampleDecoder.decode_enc,
    ModuleLWE.entryResidues_encodeMatrix, ModuleLWE.chunkResidues_flattenPolyVec, encodePublicKey,
    matrixResidues]

omit [NeZero P.q] in
private theorem extendedSamplePublicKey_encodeSample
    (M : Matrix (Fin (P.k + 1)) (Fin P.k) (Fin P.n → ZMod P.q))
    (w : Fin (P.k + 1) → Fin P.n → ZMod P.q) :
    extendedSamplePublicKey P (ModuleLWE.encodeSample (M, w)) =
      encodePublicKey (unextendPublicKeyMatrix M) := by
  simp only [extendedSamplePublicKey, ModuleLWE.encodeSample, ModuleLWE.sampleDecoder.decode_enc,
    ModuleLWE.entryResidues_encodeMatrix, encodePublicKey, matrixResidues, unextendPublicKeyMatrix]
  congr 2
  · apply List.ext_getElem (by simp)
    intro i h₁ h₂
    have hi : i < P.k := by simpa using h₁
    apply List.ext_getElem (by simp [polyVecResidues])
    intro j h₃ h₄
    have hj : j < P.k := by simpa using h₃
    simp [polyVecResidues, hi, hj]
  · simp [polyVecResidues]

private theorem extendedSampleCiphertext_encodeSample
    (M : Matrix (Fin (P.k + 1)) (Fin P.k) (Fin P.n → ZMod P.q))
    (w : Fin (P.k + 1) → Fin P.n → ZMod P.q) (m : List Bool) :
    extendedSampleCiphertext P (ModuleLWE.encodeSample (M, w)) m =
      encodeCiphertext (compressCiphertext P
        (unextendCiphertext w + (0, messagePoly P fun i => m.getD i false))) := by
  simp only [extendedSampleCiphertext, ModuleLWE.encodeSample, ModuleLWE.sampleDecoder.decode_enc,
    ModuleLWE.chunkResidues_flattenPolyVec, encodeCiphertext, compressCiphertext,
    unextendCiphertext]
  congr 2
  · apply List.ext_getElem (by simp [polyVecResidues])
    intro i h₁ h₂
    have hi : i < P.k := by simpa using h₁
    simp [polyVecResidues, hi, compressResidues_polyResidues]
  · have h0 : (polyVecResidues w).getD 0 [] = polyResidues (w 0) := by simp [polyVecResidues]
    rw [h0, messageResidues_eq, addResidues_polyResidues, compressResidues_polyResidues]
    simp

end Samples

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

private theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.keySamplePublicKey {P : α → Params}
    {sample : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hsample : ComputableInPolyTime sample input encBits) :
    ComputableInPolyTime (fun x => keySamplePublicKey (P x) (sample x)) input encBits := by
  unfold Cslib.Crypto.MLKEM.keySamplePublicKey
  dsimp only
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hk : ComputableInPolyTime (fun x => (P x).k) input encUnary := by fun_prop
  have hs := ModuleLWE.sampleDecoder.computableInPolyTime.comp hsample
  have hrows := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime.comp hs.fst'
  exact ((ComputableInPolyTime.entryResidues hk hk hn hrows).prod
    (ComputableInPolyTime.chunkResidues hk hn hs.snd')).encoding_comp
      (output := encPublicKeyResidues)

private theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.extendedSamplePublicKey
    {P : α → Params} {sample : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hsample : ComputableInPolyTime sample input encBits) :
    ComputableInPolyTime (fun x => extendedSamplePublicKey (P x) (sample x)) input encBits := by
  unfold Cslib.Crypto.MLKEM.extendedSamplePublicKey
  dsimp only
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hk : ComputableInPolyTime (fun x => (P x).k) input encUnary := by fun_prop
  have hk1 : ComputableInPolyTime (fun x => (P x).k + 1) input encUnary := by fun_prop
  have hs := ModuleLWE.sampleDecoder.computableInPolyTime.comp hsample
  have hrows := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime.comp hs.fst'
  have hM := ComputableInPolyTime.entryResidues hk1 hk hn hrows
  let I := encPair (encPair input encUnary) encUnary
  have hentry : ComputableInPolyTime (fun p : (α × ℕ) × ℕ =>
      ((ModuleLWE.entryResidues ((P p.1.1).k + 1) (P p.1.1).k (P p.1.1).n
        ((Decoder.list (Decoder.list Decoder.nat)).decode
          (ModuleLWE.sampleDecoder.decode (sample p.1.1)).1)).getD (p.2 + 1) []).getD p.1.2 [])
      I (encList encNat) :=
    ComputableInPolyTime.listGetDWithInput
      (ComputableInPolyTime.listGetDWithInput (hM.comp (by fun_prop)) (by fun_prop) [])
      (by fun_prop) []
  have hrow : ComputableInPolyTime (fun p : α × ℕ => (List.range (P p.1).k).map fun j =>
      ((ModuleLWE.entryResidues ((P p.1).k + 1) (P p.1).k (P p.1).n
        ((Decoder.list (Decoder.list Decoder.nat)).decode
          (ModuleLWE.sampleDecoder.decode (sample p.1)).1)).getD (j + 1) []).getD p.2 [])
      (encPair input encUnary) encPolyVecResidues :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp (hk.comp (by fun_prop)))
      hentry
  have hA : ComputableInPolyTime (fun x => (List.range (P x).k).map fun i =>
      (List.range (P x).k).map fun j =>
        ((ModuleLWE.entryResidues ((P x).k + 1) (P x).k (P x).n
          ((Decoder.list (Decoder.list Decoder.nat)).decode
            (ModuleLWE.sampleDecoder.decode (sample x)).1)).getD (j + 1) []).getD i [])
      input encMatrixResidues :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hk) hrow
  have hb := ComputableInPolyTime.listGetDWithInput hM (ComputableInPolyTime.const 0) []
  exact (hA.prod hb).encoding_comp (output := encPublicKeyResidues)

private theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.extendedSampleCiphertext
    {P : α → Params} {sample m : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hsample : ComputableInPolyTime sample input encBits)
    (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun x => extendedSampleCiphertext (P x) (sample x) (m x)) input
      encBits := by
  unfold Cslib.Crypto.MLKEM.extendedSampleCiphertext
  dsimp only
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun x => (P x).q) input encNat := by fun_prop
  have hk : ComputableInPolyTime (fun x => (P x).k) input encUnary := by fun_prop
  have hk1 : ComputableInPolyTime (fun x => (P x).k + 1) input encUnary := by fun_prop
  have hdu : ComputableInPolyTime (fun x => (P x).du) input encUnary := by fun_prop
  have hdv : ComputableInPolyTime (fun x => (P x).dv) input encUnary := by fun_prop
  have hs := ModuleLWE.sampleDecoder.computableInPolyTime.comp hsample
  have hw := ComputableInPolyTime.chunkResidues hk1 hn hs.snd'
  have hui : ComputableInPolyTime (fun p : α × ℕ =>
      (ModuleLWE.chunkResidues ((P p.1).k + 1) (P p.1).n
        (ModuleLWE.sampleDecoder.decode (sample p.1)).2).getD (p.2 + 1) [])
      (encPair input encUnary) (encList encNat) :=
    ComputableInPolyTime.listGetDWithInput (hw.comp (by fun_prop)) (by fun_prop) []
  have hu : ComputableInPolyTime (fun x => (List.range (P x).k).map fun i =>
      (ModuleLWE.chunkResidues ((P x).k + 1) (P x).n
        (ModuleLWE.sampleDecoder.decode (sample x)).2).getD (i + 1) [])
      input encPolyVecResidues :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hk) hui
  have hcu : ComputableInPolyTime (fun x => ((List.range (P x).k).map fun i =>
      (ModuleLWE.chunkResidues ((P x).k + 1) (P x).n
        (ModuleLWE.sampleDecoder.decode (sample x)).2).getD (i + 1) []).map
          (compressResidues (P x).q (P x).du)) input encPolyVecResidues :=
    ComputableInPolyTime.mapWithInput hu
      (ComputableInPolyTime.compressResidues
        (hq.comp (ComputableInPolyTime.fst input (encList encNat)))
        (hdu.comp (ComputableInPolyTime.fst input (encList encNat)))
        (ComputableInPolyTime.snd input (encList encNat)))
  have hv := ComputableInPolyTime.compressResidues hq hdv
    (ComputableInPolyTime.addResidues hq
      (ComputableInPolyTime.listGetDWithInput hw (ComputableInPolyTime.const 0) [])
      (ComputableInPolyTime.messageResidues hn hq hm))
  exact (hcu.prod hv).encoding_comp (output := encCiphertextResidues)

end PolyTime

/-! ### The reductions -/

section Reductions

variable (P : ℕ → Params)

/-- The two-stage K-PKE adversary that a word-level IND-CPA adversary `A` plays at security
parameter `κ`. Its first stage runs `A.choose` on the word of the public key, reads the first `n`
bits of each chosen message (`false` beyond the end), and saves whether the pair is admissible for
`kpke P` beside `A`'s state. Its second stage runs `A.guess` on the word of the ciphertext if the
pair was admissible, and returns `false` otherwise, as `Encryption.gameOn` does. -/
noncomputable def wordAdversary (A : Encryption.WordAdversary) (κ : ℕ) :
    CpaAdversary (P κ) (Bool × List Bool) where
  choose pk := (fun choice : Encryption.ChoiceOut (List Bool) =>
      (⟨fun i => (Encryption.ChoiceOut.msg₀ choice).getD i false,
          fun i => (Encryption.ChoiceOut.msg₁ choice).getD i false⟩,
        ((kpke P).IsMessagePair κ (encodePublicKey pk) (Encryption.ChoiceOut.msg₀ choice)
          (Encryption.ChoiceOut.msg₁ choice), Encryption.ChoiceOut.state choice))) <$>
    A.choose κ (encodePublicKey pk)
  guess state ct := if state.1 then A.guess κ state.2 (encodeCiphertext ct) else pure false

/-- **The public-key hop for the family**: at each `κ`, `mlweKeyReduction` at `P κ` for the
adversary `wordAdversary P A κ` and the challenge bit `b`. It is a `k × k` decision Module-LWE
distinguisher, uniform in `κ`. -/
noncomputable def keyReduction (A : Encryption.WordAdversary) (b : Bool) :
    ModuleLWE.Distinguisher (fun κ => (P κ).k) (fun κ => (P κ).k) (fun κ => (P κ).n)
      (fun κ => (P κ).q) :=
  fun κ => mlweKeyReduction (P κ) (wordAdversary P A κ) b

/-- **The ciphertext hop for the family**: at each `κ`, `mlweReduction` at `P κ` for the adversary
`wordAdversary P A κ` and the challenge bit `b`. It is a `(k + 1) × k` decision Module-LWE
distinguisher, uniform in `κ`. -/
noncomputable def ciphertextReduction (A : Encryption.WordAdversary) (b : Bool) :
    ModuleLWE.Distinguisher (fun κ => (P κ).k + 1) (fun κ => (P κ).k) (fun κ => (P κ).n)
      (fun κ => (P κ).q) :=
  fun κ => mlweReduction (P κ) (wordAdversary P A κ) b

/-- The word program of the public-key hop on `(κ, sample)`. -/
private noncomputable def keyReductionWord (A : Encryption.WordAdversary) (b : Bool)
    (x : ℕ × List Bool) : ProbComp Bool := do
  let choice ← A.choose x.1 (keySamplePublicKey (P x.1) x.2)
  let coins ← BitString.sampleList (coinLength (P x.1))
  if (kpke P).IsMessagePair x.1 (keySamplePublicKey (P x.1) x.2) choice.1.1 choice.1.2 then
    A.guess x.1 choice.2 (encDetWord (P x.1) (keySamplePublicKey (P x.1) x.2)
      (if b then choice.1.2 else choice.1.1) coins)
  else
    pure false

/-- The word program of the ciphertext hop on `(κ, sample)`. -/
private noncomputable def ciphertextReductionWord (A : Encryption.WordAdversary) (b : Bool)
    (x : ℕ × List Bool) : ProbComp Bool := do
  let choice ← A.choose x.1 (extendedSamplePublicKey (P x.1) x.2)
  if (kpke P).IsMessagePair x.1 (extendedSamplePublicKey (P x.1) x.2) choice.1.1 choice.1.2 then
    A.guess x.1 choice.2
      (extendedSampleCiphertext (P x.1) x.2 (if b then choice.1.2 else choice.1.1))
  else
    pure false

private theorem select_getD (m₀ m₁ : List Bool) (b : Bool) {n : ℕ} :
    (⟨fun i : Fin n => m₀.getD i false, fun i => m₁.getD i false⟩ : MessagePair _).select b =
      fun i : Fin n => (if b then m₁ else m₀).getD i false := by
  cases b <;> rfl

private theorem eval_keyReduction [∀ κ, NeZero (P κ).q] (A : Encryption.WordAdversary)
    (b : Bool) (κ : ℕ) (M : Matrix (Fin (P κ).k) (Fin (P κ).k) (Fin (P κ).n → ZMod (P κ).q))
    (t : Fin (P κ).k → Fin (P κ).n → ZMod (P κ).q) :
    ProbComp.eval (keyReduction P A b κ M t) =
      ProbComp.eval (keyReductionWord P A b (κ, ModuleLWE.encodeSample (M, t))) := by
  simp only [keyReduction, mlweKeyReduction, keyReductionWord, keySamplePublicKey_encodeSample,
    wordAdversary, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun choice => ?_)
  simp only [Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁, Encryption.ChoiceOut.msgs,
    Encryption.ChoiceOut.state, select_getD]
  by_cases hv : (kpke P).IsMessagePair κ (encodePublicKey (M, t)) choice.1.1 choice.1.2 = true
  · simp only [hv, ite_true]
    have h := congrArg (fun μ => μ.bind fun ct => ProbComp.eval (A.guess κ choice.2 ct))
      (eval_encDetWord_sampleList (P κ) (M, t) (if b then choice.1.2 else choice.1.1))
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
      Function.comp_def] at h
    exact h.symm
  · simp only [hv, Bool.false_eq_true, ite_false, PMF.bind_const]

private theorem eval_ciphertextReduction [∀ κ, NeZero (P κ).q] (A : Encryption.WordAdversary)
    (b : Bool) (κ : ℕ)
    (M : Matrix (Fin ((P κ).k + 1)) (Fin (P κ).k) (Fin (P κ).n → ZMod (P κ).q))
    (w : Fin ((P κ).k + 1) → Fin (P κ).n → ZMod (P κ).q) :
    ProbComp.eval (ciphertextReduction P A b κ M w) =
      ProbComp.eval (ciphertextReductionWord P A b (κ, ModuleLWE.encodeSample (M, w))) := by
  simp only [ciphertextReduction, mlweReduction, ciphertextReductionWord,
    extendedSamplePublicKey_encodeSample, extendedSampleCiphertext_encodeSample, wordAdversary,
    ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun choice => ?_)
  simp only [Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁, Encryption.ChoiceOut.msgs,
    Encryption.ChoiceOut.state, select_getD]

variable {P}

/-- **The public-key hop is uniform strict PPT** when the parameters are computable in polynomial
time and `A` is uniform strict PPT. -/
theorem isPPT_keyReduction [∀ κ, NeZero (P κ).q] (hP : ComputableInPolyTime P encUnary encParams)
    {A : Encryption.WordAdversary} (hA : A.IsPPT) (b : Bool) :
    (keyReduction P A b).IsPPT := by
  have hW : IsPPTOn (encPair encUnary encBits) encBool (keyReductionWord P A b) := by
    unfold keyReductionWord
    let E := encPair encUnary encBits
    have hκ : ComputableInPolyTime (fun x : ℕ × List Bool => x.1) E encUnary := by fun_prop
    have hPκ : ComputableInPolyTime (fun x : ℕ × List Bool => P x.1) E encParams := hP.comp hκ
    have hpk := ComputableInPolyTime.keySamplePublicKey hPκ
      (by fun_prop : ComputableInPolyTime (fun x : ℕ × List Bool => x.2) E encBits)
    have hchoose := hA.choose.on.preprocess (hκ.prod hpk)
    refine hchoose.bind_with ?_
    let F := encPair E (Encryption.encChoiceOut encBits)
    have hκF : ComputableInPolyTime (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
        y.1.1) F encUnary := by fun_prop
    have hPF : ComputableInPolyTime (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
        P y.1.1) F encParams := hP.comp hκF
    have hL : ComputableInPolyTime (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
        coinLength (P y.1.1)) F encUnary := by
      unfold coinLength
      fun_prop
    refine (isPPTOn_sampleList.preprocess hL).bind_with ?_
    let G := encPair F encBits
    have hκG : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool => z.1.1.1) G
        encUnary := by fun_prop
    have hPG : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool => P z.1.1.1) G
        encParams := hP.comp hκG
    have hpkG : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool =>
          keySamplePublicKey (P z.1.1.1) z.1.1.2) G encBits :=
      ComputableInPolyTime.keySamplePublicKey hPG (by fun_prop)
    have hvalid : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool =>
          (kpke P).IsMessagePair z.1.1.1 (keySamplePublicKey (P z.1.1.1) z.1.1.2) z.1.2.1.1
            z.1.2.1.2) G encBool := by
      simp only [WordPKE.IsMessagePair, kpke]
      fun_prop
    have hm : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool =>
          if b then z.1.2.1.2 else z.1.2.1.1) G encBits := by
      cases b <;> fun_prop
    have hct := ComputableInPolyTime.encDetWord hPG hpkG hm
      (by fun_prop : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool => z.2) G encBits)
    have hguess := hA.guess.preprocess (hκG.prod ((by fun_prop : ComputableInPolyTime
        (fun z : ((ℕ × List Bool) × Encryption.ChoiceOut (List Bool)) × List Bool => z.1.2.2) G
        encBits).prod hct))
    exact IsPPTOn.cond' hvalid hguess (ComputableInPolyTime.const false).isPPTOn
  have h := hW.preprocess (ComputableInPolyTime.of_eq fun _ => rfl :
    ComputableInPolyTime ModuleLWE.Input.words
      (ModuleLWE.encInput (fun κ => (P κ).k) (fun κ => (P κ).k) (fun κ => (P κ).n)
        (fun κ => (P κ).q)) (encPair encUnary encBits))
  exact h.congr fun x => (eval_keyReduction P A b x.secParam x.matrix x.target).symm

/-- **The ciphertext hop is uniform strict PPT** when the parameters are computable in polynomial
time and `A` is uniform strict PPT. -/
theorem isPPT_ciphertextReduction [∀ κ, NeZero (P κ).q]
    (hP : ComputableInPolyTime P encUnary encParams) {A : Encryption.WordAdversary}
    (hA : A.IsPPT) (b : Bool) : (ciphertextReduction P A b).IsPPT := by
  have hW : IsPPTOn (encPair encUnary encBits) encBool (ciphertextReductionWord P A b) := by
    unfold ciphertextReductionWord
    let E := encPair encUnary encBits
    have hκ : ComputableInPolyTime (fun x : ℕ × List Bool => x.1) E encUnary := by fun_prop
    have hPκ : ComputableInPolyTime (fun x : ℕ × List Bool => P x.1) E encParams := hP.comp hκ
    have hpk := ComputableInPolyTime.extendedSamplePublicKey hPκ
      (by fun_prop : ComputableInPolyTime (fun x : ℕ × List Bool => x.2) E encBits)
    have hchoose := hA.choose.on.preprocess (hκ.prod hpk)
    refine hchoose.bind_with ?_
    let F := encPair E (Encryption.encChoiceOut encBits)
    have hκF : ComputableInPolyTime (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
        y.1.1) F encUnary := by fun_prop
    have hPF : ComputableInPolyTime (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
        P y.1.1) F encParams := hP.comp hκF
    have hvalid : ComputableInPolyTime
        (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
          (kpke P).IsMessagePair y.1.1 (extendedSamplePublicKey (P y.1.1) y.1.2) y.2.1.1 y.2.1.2)
        F encBool := by
      simp only [WordPKE.IsMessagePair, kpke]
      fun_prop
    have hm : ComputableInPolyTime
        (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) =>
          if b then y.2.1.2 else y.2.1.1) F encBits := by
      cases b <;> fun_prop
    have hct := ComputableInPolyTime.extendedSampleCiphertext hPF
      (by fun_prop : ComputableInPolyTime
        (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) => y.1.2) F encBits) hm
    have hguess := hA.guess.preprocess (hκF.prod ((by fun_prop : ComputableInPolyTime
        (fun y : (ℕ × List Bool) × Encryption.ChoiceOut (List Bool) => y.2.2) F encBits).prod hct))
    exact IsPPTOn.cond' hvalid hguess (ComputableInPolyTime.const false).isPPTOn
  have h := hW.preprocess (ComputableInPolyTime.of_eq fun _ => rfl :
    ComputableInPolyTime ModuleLWE.Input.words
      (ModuleLWE.encInput (fun κ => (P κ).k + 1) (fun κ => (P κ).k) (fun κ => (P κ).n)
        (fun κ => (P κ).q)) (encPair encUnary encBits))
  exact h.congr fun x => (eval_ciphertextReduction P A b x.secParam x.matrix x.target).symm

end Reductions

/-! ### From the word game to the two-stage experiment -/

section Bridge

variable (P : ℕ → Params) [∀ κ, NeZero (P κ).q]

/-- The common continuation of the word-level IND-CPA game of `kpke P` and of the two-stage
experiment of `toExplicitCoinPKE (P κ)`, after the public-key word. -/
private noncomputable def afterKey (A : Encryption.WordAdversary) (b : Bool) (κ : ℕ)
    (pk : List Bool) : Game :=
  (ProbComp.eval (A.choose κ pk)).bind fun choice =>
    if (kpke P).IsMessagePair κ pk (Encryption.ChoiceOut.msg₀ choice)
        (Encryption.ChoiceOut.msg₁ choice) then
      (ProbComp.eval ((kpke P).encrypt κ pk
        (if b then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice))).bind
        fun ct => ProbComp.eval (A.guess κ (Encryption.ChoiceOut.state choice) ct)
    else
      PMF.pure false

omit [∀ κ, NeZero (P κ).q] in
private theorem eval_gameOn_eq (A : Encryption.WordAdversary) (b : Bool) (κ : ℕ) :
    ProbComp.eval
      (Encryption.gameOn (kpke P).IsMessagePair (kpke P).keyGen (kpke P).encrypt A b κ) =
      ((ProbComp.eval ((kpke P).keyGen κ)).map Prod.fst).bind (afterKey P A b κ) := by
  rw [Encryption.eval_gameOn]
  rfl

private theorem eval_cpaExperiment_eq (A : Encryption.WordAdversary) (b : Bool) (κ : ℕ) :
    ProbComp.eval ((toExplicitCoinPKE (P κ)).toPKE.cpaExperiment (fun _ _ _ => true)
      (wordAdversary P A κ) b) =
      ((ProbComp.eval (keyGen (P κ))).map fun keys => encodePublicKey (P := P κ) keys.1).bind
        (afterKey P A b κ) := by
  rw [PKE.eval_cpaExperiment, Game.withSetup, PMF.bind_map, PMF.bind_map]
  refine congrArg _ (funext fun keys => ?_)
  simp only [Function.comp_apply, eval_lrExperiment, ite_true, afterKey, wordAdversary,
    ProbComp.eval_map, PMF.bind_map]
  refine congrArg _ (funext fun choice => ?_)
  simp only [Function.comp_apply, Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁,
    Encryption.ChoiceOut.msgs, Encryption.ChoiceOut.state, select_getD]
  by_cases hv : (kpke P).IsMessagePair κ (encodePublicKey keys.1) choice.1.1 choice.1.2 = true
  · simp only [hv, ite_true]
    have h := eval_encDetWord_sampleList (P κ) keys.1 (if b then choice.1.2 else choice.1.1)
    rw [show (kpke P).encrypt κ (encodePublicKey keys.1) (if b then choice.1.2 else choice.1.1) =
      (do
        let coins ← BitString.sampleList (coinLength (P κ))
        return encDetWord (P κ) (encodePublicKey keys.1) (if b then choice.1.2 else choice.1.1)
          coins) from rfl, h]
    simp only [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt, toExplicitCoinPKE,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
      Function.comp_def]
  · simp only [hv, Bool.false_eq_true, ite_false, PMF.bind_const, ProbComp.eval_pure]

/-- **The word game is the two-stage experiment up to the matrix sampler.** At each `κ` and
challenge bit, the word-level IND-CPA game of `kpke P` against `A` and the two-stage experiment of
`toExplicitCoinPKE (P κ)` against `wordAdversary P A κ`, whose matrix is exactly uniform, differ
by at most `k * k * n / 2 ^ κ`. -/
private theorem advantage_gameOn_cpaExperiment_le (A : Encryption.WordAdversary) (b : Bool)
    (κ : ℕ) :
    Game.advantage
        (ProbComp.eval (Encryption.gameOn (kpke P).IsMessagePair (kpke P).keyGen (kpke P).encrypt
          A b κ))
        (ProbComp.eval ((toExplicitCoinPKE (P κ)).toPKE.cpaExperiment (fun _ _ _ => true)
          (wordAdversary P A κ) b)) ≤
      ((P κ).k * (P κ).k * (P κ).n : ℝ≥0) / 2 ^ κ := by
  rw [eval_gameOn_eq, eval_cpaExperiment_eq, Game.advantage_comm]
  have h := Game.coe_advantage_bind_le_of_closeTo (closeTo_keyGenWord (P κ) κ) (afterKey P A b κ)
  rw [← ENNReal.coe_le_coe]
  refine h.trans_eq ?_
  rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero)]
  push_cast
  rfl

/-- **Concrete IND-CPA bound for the word family**, a step of
`indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`: at each `κ`, the
advantage of `A` in the word-level IND-CPA game of `kpke P` is at most the four Module-LWE
advantages of the explicit reductions `keyReduction P A b` and `ciphertextReduction P A b`, plus
twice the matrix-sampler distance `k * k * n / 2 ^ κ`. -/
theorem advantage_gameOn_le (A : Encryption.WordAdversary) (κ : ℕ) :
    Encryption.advantage
        (Encryption.gameOn (kpke P).IsMessagePair (kpke P).keyGen (kpke P).encrypt A) κ ≤
      ((P κ).k * (P κ).k * (P κ).n : ℝ≥0) / 2 ^ κ +
        ((ModuleLWE.advantage (ProbComp.eval (sampleVecCBD (P κ).k (P κ).n (P κ).q (P κ).η₁))
            (ProbComp.eval (sampleVecCBD (P κ).k (P κ).n (P κ).q (P κ).η₁))
            (keyReduction P A false κ) +
          ModuleLWE.advantage (ProbComp.eval (sampleVecCBD (P κ).k (P κ).n (P κ).q (P κ).η₁))
            (ProbComp.eval (sampleVecCBD ((P κ).k + 1) (P κ).n (P κ).q (P κ).η₂))
            (ciphertextReduction P A false κ)) +
        (ModuleLWE.advantage (ProbComp.eval (sampleVecCBD (P κ).k (P κ).n (P κ).q (P κ).η₁))
            (ProbComp.eval (sampleVecCBD (P κ).k (P κ).n (P κ).q (P κ).η₁))
            (keyReduction P A true κ) +
          ModuleLWE.advantage (ProbComp.eval (sampleVecCBD (P κ).k (P κ).n (P κ).q (P κ).η₁))
            (ProbComp.eval (sampleVecCBD ((P κ).k + 1) (P κ).n (P κ).q (P κ).η₂))
            (ciphertextReduction P A true κ))) +
        ((P κ).k * (P κ).k * (P κ).n : ℝ≥0) / 2 ^ κ := by
  have h₀ := advantage_gameOn_cpaExperiment_le P A false κ
  have h₁ := advantage_gameOn_cpaExperiment_le P A true κ
  have hcpa := cpaAdvantage_le (P κ) (wordAdversary P A κ)
  rw [Game.advantage_comm] at h₁
  refine (Game.advantage_triangle _ _ _).trans (add_le_add
    ((Game.advantage_triangle _ _ _).trans (add_le_add h₀ hcpa)) h₁)

end Bridge

/-! ### IND-CPA with ideal coin expansion -/

/-- The centered-binomial law `β_η^k` on vectors of `k` polynomials of `ℤ_q[X] / (X^n + 1)`: every
coefficient is an independent centered-binomial sample of width `η` ([NIST, Section 4.2.2,
Algorithm 8][NISTFIPS203]) reduced modulo `q`. Kyber v3.02 draws Module-LWE secrets and errors
from it ([AvanziEtAl2021], §4.3, p. 19). -/
noncomputable def cbdLaw (k n q η : ℕ) [NeZero q] : PMF (Fin k → Fin n → ZMod q) :=
  PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
    (ProbComp.eval (ProbComp.sampleCenteredBinomial η)).map (Int.cast : ℤ → ZMod q)

/-- K-PKE's vector sampler `sampleVecCBD` draws from `cbdLaw`. -/
theorem eval_sampleVecCBD (k n q η : ℕ) [NeZero q] :
    ProbComp.eval (sampleVecCBD k n q η) = cbdLaw k n q η := by
  have hpoly : ProbComp.eval (samplePolyCBD n q η) =
      ProbComp.eval (OracleComp.replicateFin n
        ((Int.cast : ℤ → ZMod q) <$> ProbComp.sampleCenteredBinomial η)) := by
    rw [ProbComp.eval_replicateFin_map_coords, samplePolyCBD]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map]
    rfl
  rw [sampleVecCBD, ProbComp.eval_replicateFin, cbdLaw]
  congr 1 with j : 1
  rw [hpoly, ProbComp.eval_replicateFin, ProbComp.eval_map]

/-- **IND-CPA of K-PKE with ideal coin expansion and the matrix in the public key** (fair coins in
place of `PRF`; no `XOF` or `G` oracles), a step towards Kyber v3.02 Theorem 1 ([AvanziEtAl2021],
§4.3.1, p. 20) and not that theorem, which assumes that `XOF` and `G` are random oracles and whose
bound has an `Adv^prf` term. The `PRF` hop is `indCPA_kpkePRF_of_decisionModuleLWEWith`, which
applies this one to its last game and keeps the matrix in the public key; the random-oracle lift is
open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6893099765).

Let `P` be a K-PKE parameter family computable in polynomial time from the unary security
parameter. If decision Module-LWE is hard for the `k × k` key shape with secrets and errors from
`cbdLaw` of width `η₁` (`hkey`) and for the `(k + 1) × k` ciphertext shape with secrets of width
`η₁` and errors of width `η₂` (`hct`), then the word-level family `kpke P`, whose key generation
and encryption draw their noise from fair coins, is IND-CPA secure (`WordPKE.INDCPA`): every
uniform strict PPT adversary has negligible advantage.

The two assumptions are the terms of §4.4, eq. (6), p. 22. Besides the coins, the public key
carries the matrix, which the word family samples within a proved negligible distance
`k * k * n / 2 ^ κ` of uniform, in place of the seed `ρ` from which Kyber re-derives it with `XOF`.
The adversary has no `XOF` or `G` oracle, so the step of Theorem 1's random-oracle model that
answers its `XOF` queries at `ρ` with the Module-LWE matrix is not formalized. The ciphertext hop
is uncompressed. The module documentation lists all the differences. -/
theorem indCPA_kpkeIdealCoins_of_decisionModuleLWEWith {P : ℕ → Params} [∀ κ, NeZero (P κ).q]
    (hP : ComputableInPolyTime P encUnary encParams)
    (hkey : DecisionModuleLWEWith (fun κ => (P κ).k) (fun κ => (P κ).k) (fun κ => (P κ).n)
      (fun κ => (P κ).q) (fun κ => cbdLaw (P κ).k (P κ).n (P κ).q (P κ).η₁)
      (fun κ => cbdLaw (P κ).k (P κ).n (P κ).q (P κ).η₁))
    (hct : DecisionModuleLWEWith (fun κ => (P κ).k + 1) (fun κ => (P κ).k) (fun κ => (P κ).n)
      (fun κ => (P κ).q) (fun κ => cbdLaw (P κ).k (P κ).n (P κ).q (P κ).η₁)
      (fun κ => cbdLaw ((P κ).k + 1) (P κ).n (P κ).q (P κ).η₂)) :
    (kpke P).INDCPA := by
  intro A hA
  simp only [← eval_sampleVecCBD] at hkey hct
  have hk₀ := hkey _ (isPPT_keyReduction hP hA false)
  have hk₁ := hkey _ (isPPT_keyReduction hP hA true)
  have hc₀ := hct _ (isPPT_ciphertextReduction hP hA false)
  have hc₁ := hct _ (isPPT_ciphertextReduction hP hA true)
  have hk : ComputableInPolyTime (fun κ => (P κ).k) encUnary encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun κ => (P κ).n) encUnary encUnary := by fun_prop
  have hε := PolynomiallyBounded.negligible_div_two_pow
    ((hk.polynomiallyBounded.mul hk.polynomiallyBounded).mul hn.polynomiallyBounded)
  push_cast at hε
  exact negligible_of_le ((hε.add ((hk₀.add hc₀).add (hk₁.add hc₁))).add hε)
    fun κ => advantage_gameOn_le P A κ

end Cslib.Crypto.MLKEM
