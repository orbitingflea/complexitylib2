/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Native
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.SIS.Module.ApproximateSampling
import CslibFrontier.Probability.PMF
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# The word-level K-PKE family

For a K-PKE parameter family `P : ℕ → Params`, `kpke P` is K-PKE as a word-level public-key
encryption family (`FujisakiOkamoto.WordPKE`), with native algorithms built from the residue-list
natives of `CslibFrontier.Crypto.Computational.SIS.MLKEM.Native`. At security parameter `κ`:

* public keys, secret keys and ciphertexts are the words of their residue lists
  (`encodePublicKey`, `encodeSecretKey`, `encodeCiphertext`); messages are words of `n` bits;
* key generation `keyGenWord (P κ) κ` draws every coefficient of the matrix `A` with the bounded
  modular sampler at `q.size + κ` fair bits, draws `s, e ← CBD_{η₁}^k` from fair bits by
  `SamplePolyCBD`, and returns the words of `(A, A s + e)` and `s`;
* deterministic encryption `encDetWord` decodes `coinLength (P κ)` fair coins into
  `r ← CBD_{η₁}^k`, `e₁ ← CBD_{η₂}^k`, `e₂ ← CBD_{η₂}` and encrypts; decryption `decWord` never
  fails.

The word algorithms realize the typed scheme `toExplicitCoinPKE (P κ)` of
`CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE`: encryption with fair coins has exactly the
law of the word of `encrypt` with coins from `sampleCoins` (`eval_encDetWord_sampleList`),
decryption computes `decrypt` (`decWord_encode`), and key generation is K-PKE key generation with
an approximately uniform matrix (`eval_keyGenWord`), within `k * k * n / 2 ^ κ` of the exactly
uniform matrix of `keyGen` (`closeTo_keyGenWord`). With parameters computable in polynomial time
from the unary security parameter, the family is efficient (`kpke_isEfficient`), and its
ciphertexts fit the ciphertext space `ctLength` (`kpke_ciphertextFits`).

This is the family of the certified asymptotic IND-CPA theorem for K-PKE
([#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6888265804)).
It makes no security claim.

## Model differences from FIPS 203

* The matrix is drawn coefficientwise, approximately uniformly, rather than expanded from a seed
  by `SampleNTT`; coins are fair bits rather than `PRF` outputs.
* Polynomials are in coefficient form rather than the NTT domain, and keys and ciphertexts are
  words of residue lists rather than `ByteEncode` outputs.

## Main definitions

* `Cslib.Crypto.MLKEM.encPublicKeyResidues`, `Cslib.Crypto.MLKEM.encodePublicKey`,
  `Cslib.Crypto.MLKEM.encodeSecretKey`, `Cslib.Crypto.MLKEM.encodeCiphertext`: the words of keys
  and ciphertexts.
* `Cslib.Crypto.MLKEM.coinLength`, `Cslib.Crypto.MLKEM.ctLength`: the coin length and the
  ciphertext length bound.
* `Cslib.Crypto.MLKEM.encDetWord`, `Cslib.Crypto.MLKEM.decWord`, `Cslib.Crypto.MLKEM.keyGenWord`:
  the word algorithms.
* `Cslib.Crypto.MLKEM.kpke`: the word-level K-PKE family.

## Main results

* `Cslib.Crypto.MLKEM.eval_encDetWord_sampleList`, `Cslib.Crypto.MLKEM.decWord_encode`,
  `Cslib.Crypto.MLKEM.eval_keyGenWord`, `Cslib.Crypto.MLKEM.closeTo_keyGenWord`: the word
  algorithms realize K-PKE.
* `Cslib.Crypto.MLKEM.kpke_isEfficient`: `kpke P` is efficient for a polynomial-time family.
* `Cslib.Crypto.MLKEM.kpke_ciphertextFits`: ciphertexts fit their ciphertext space.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.FujisakiOkamoto
open scoped ENNReal

/-! ### Words of keys and ciphertexts -/

/-- The layout of public-key words: the residue rows of `A`, framed, then the residue lists of
`b`. -/
abbrev encPublicKeyResidues : List (List (List ℕ)) × List (List ℕ) ↪ List Bool :=
  encPair encMatrixResidues encPolyVecResidues

/-- The word of a public key `(A, b)`: the residue rows of `A`, framed, then the residue lists of
`b` (`encPublicKeyResidues`). -/
def encodePublicKey {P : Params} (pk : PublicKey P) : List Bool :=
  encPublicKeyResidues (matrixResidues pk.1, polyVecResidues pk.2)

/-- The word of a secret key `s`: the residue lists of `s`. -/
def encodeSecretKey {P : Params} (s : SecretKey P) : List Bool :=
  encPolyVecResidues (polyVecResidues s)

/-- The word of a ciphertext `(c₁, c₂)`: the `d_u`-bit residue lists of `c₁`, framed, then the
`d_v`-bit residues of `c₂` (`encCiphertextResidues`). -/
def encodeCiphertext {P : Params} (ct : Ciphertext P) : List Bool :=
  encCiphertextResidues (polyVecResidues ct.1, polyResidues ct.2)

/-- The number of fair coins of one encryption: `2 η₁` bits for each coefficient of `r`, then
`2 η₂` bits for each coefficient of `e₁` and of `e₂`. -/
def coinLength (P : Params) : ℕ :=
  P.k * (P.n * (2 * P.η₁)) + P.k * (P.n * (2 * P.η₂)) + P.n * (2 * P.η₂)

/-! ### Word algorithms -/

/-- The decoder of public-key words (`encPublicKeyResidues`). -/
def publicKeyDecoder : Decoder encPublicKeyResidues :=
  Decoder.pair (Decoder.list (Decoder.list (Decoder.list Decoder.nat)))
    (Decoder.list (Decoder.list Decoder.nat))

/-- The decoder of ciphertext words (`encCiphertextResidues`). -/
def ciphertextDecoder : Decoder encCiphertextResidues :=
  Decoder.pair (Decoder.list (Decoder.list Decoder.nat)) (Decoder.list Decoder.nat)

/-- Deterministic K-PKE encryption on words: decode the public key, decode the coins into
`r ← CBD_{η₁}^k`, `e₁ ← CBD_{η₂}^k`, `e₂ ← CBD_{η₂}` by `SamplePolyCBD`, and encrypt. -/
def encDetWord (P : Params) (pk m coins : List Bool) : List Bool :=
  let key := publicKeyDecoder.decode pk
  let L₁ := P.k * (P.n * (2 * P.η₁))
  let L₂ := P.k * (P.n * (2 * P.η₂))
  encCiphertextResidues
    (encryptResidues P key.1 key.2 m (cbdVecResidues P.k P.n P.q P.η₁ (coins.take L₁))
      (cbdVecResidues P.k P.n P.q P.η₂ ((coins.drop L₁).take L₂))
      (cbdResidues P.n P.q P.η₂ (coins.drop (L₁ + L₂))))

/-- K-PKE decryption on words. It never fails. -/
def decWord (P : Params) (sk ct : List Bool) : Option (List Bool) :=
  let c := ciphertextDecoder.decode ct
  some (decryptResidues P ((Decoder.list (Decoder.list Decoder.nat)).decode sk) c.1 c.2)

/-- K-PKE key generation on words with a uniform matrix drawn coefficientwise by the bounded
modular sampler at `q.size + precision` fair bits, and `s, e ← CBD_{η₁}^k` by `SamplePolyCBD` from
fair bits. It returns the public-key and secret-key words. -/
noncomputable def keyGenWord (P : Params) (precision : ℕ) : ProbComp (List Bool × List Bool) := do
  let A ← OracleComp.replicate P.k (OracleComp.replicate P.k
    (OracleComp.replicate P.n (ProbComp.sampleModNat (P.q.size + precision) P.q)))
  let sBits ← BitString.sampleList (P.k * (P.n * (2 * P.η₁)))
  let eBits ← BitString.sampleList (P.k * (P.n * (2 * P.η₁)))
  return (encPublicKeyResidues (A, publicKeyResidues P A (cbdVecResidues P.k P.n P.q P.η₁ sBits)
      (cbdVecResidues P.k P.n P.q P.η₁ eBits)),
    encPolyVecResidues (cbdVecResidues P.k P.n P.q P.η₁ sBits))

/-! ### Polynomial-time certificates -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Deterministic encryption on words, with computed parameters and inputs. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.encDetWord {P : α → Params}
    {pk m coins : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hpk : ComputableInPolyTime pk input encBits) (hm : ComputableInPolyTime m input encBits)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime (fun x => encDetWord (P x) (pk x) (m x) (coins x)) input encBits := by
  unfold Cslib.Crypto.MLKEM.encDetWord
  dsimp only
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun x => (P x).q) input encNat := by fun_prop
  have hk : ComputableInPolyTime (fun x => (P x).k) input encUnary := by fun_prop
  have hη₁ : ComputableInPolyTime (fun x => (P x).η₁) input encUnary := by fun_prop
  have hη₂ : ComputableInPolyTime (fun x => (P x).η₂) input encUnary := by fun_prop
  have hL₁ : ComputableInPolyTime (fun x => (P x).k * ((P x).n * (2 * (P x).η₁))) input
      encUnary := by fun_prop
  have hL₂ : ComputableInPolyTime (fun x => (P x).k * ((P x).n * (2 * (P x).η₂))) input
      encUnary := by fun_prop
  have hkey := publicKeyDecoder.computableInPolyTime.comp hpk
  have hr := ComputableInPolyTime.cbdVecResidues hk hn hq hη₁
    (ComputableInPolyTime.bitsTakeWithInput hcoins hL₁)
  have he₁ := ComputableInPolyTime.cbdVecResidues hk hn hq hη₂
    (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.bitsDropWithInput hcoins hL₁)
      hL₂)
  have he₂ := ComputableInPolyTime.cbdResidues hn hq hη₂
    (ComputableInPolyTime.bitsDropWithInput hcoins (ComputableInPolyTime.unary_add' hL₁ hL₂))
  exact (ComputableInPolyTime.encryptResidues hP hkey.fst' hkey.snd' hm hr he₁ he₂).encoding_comp

/-- Decryption on words, with computed parameters and inputs. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.decWord {P : α → Params}
    {sk ct : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hsk : ComputableInPolyTime sk input encBits) (hct : ComputableInPolyTime ct input encBits) :
    ComputableInPolyTime (fun x => decWord (P x) (sk x) (ct x)) input (encOption encBits) := by
  unfold Cslib.Crypto.MLKEM.decWord
  dsimp only
  have hc := ciphertextDecoder.computableInPolyTime.comp hct
  have hs := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime.comp hsk
  exact (ComputableInPolyTime.optionSome encBits).comp
    (ComputableInPolyTime.decryptResidues hP hs hc.fst' hc.snd')

/-- Word key generation is uniform strict PPT in the parameters and the unary precision. -/
theorem isPPTOn_keyGenWord :
    IsPPTOn (encPair encParams encUnary) (encPair encBits encBits)
      (fun x => keyGenWord x.1 x.2) := by
  unfold keyGenWord
  let E := encPair encParams encUnary
  have hn : ComputableInPolyTime (fun x : Params × ℕ => x.1.n) E encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun x : Params × ℕ => x.1.q) E encNat := by fun_prop
  have hk : ComputableInPolyTime (fun x : Params × ℕ => x.1.k) E encUnary := by fun_prop
  have hη₁ : ComputableInPolyTime (fun x : Params × ℕ => x.1.η₁) E encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun x : Params × ℕ => x.1.q.size + x.2) E encUnary := by
    fun_prop
  have hL : ComputableInPolyTime (fun x : Params × ℕ => x.1.k * (x.1.n * (2 * x.1.η₁))) E
      encUnary := by fun_prop
  have hA := ((isPPTOn_sampleModNat hw hq).replicate hn |>.replicate hk).replicate hk
  have hs := isPPTOn_sampleList.preprocess
    (hL.comp (ComputableInPolyTime.fst E encMatrixResidues))
  have he := isPPTOn_sampleList.preprocess
    ((hL.comp (ComputableInPolyTime.fst E encMatrixResidues)).comp
      (ComputableInPolyTime.fst (encPair E encMatrixResidues) encBits))
  refine hA.bind_with (hs.bind_with (he.bind_with ?_))
  let F := encPair (encPair (encPair E encMatrixResidues) encBits) encBits
  have hP : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.1.1.1) F
      encParams := by fun_prop
  have hA' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.1.2) F
      encMatrixResidues := by fun_prop
  have hs' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.2) F
      encBits := by fun_prop
  have he' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.2) F
      encBits := by fun_prop
  have hn' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.1.1.1.n) F
      encUnary := by fun_prop
  have hq' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.1.1.1.q) F
      encNat := by fun_prop
  have hk' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.1.1.1.k) F
      encUnary := by fun_prop
  have hη' : ComputableInPolyTime
      (fun y : (((Params × ℕ) × List (List (List ℕ))) × List Bool) × List Bool => y.1.1.1.1.η₁) F
      encUnary := by fun_prop
  have hsv := ComputableInPolyTime.cbdVecResidues hk' hn' hq' hη' hs'
  have hev := ComputableInPolyTime.cbdVecResidues hk' hn' hq' hη' he'
  exact (((hA'.prod (ComputableInPolyTime.publicKeyResidues hP hA' hsv hev)).encoding_comp
    (output := encPublicKeyResidues)).prod
      (hsv.encoding_comp (output := encPolyVecResidues))).isPPTOn

end PolyTime

/-! ### Laws of the word algorithms -/

section Laws

variable (P : Params) [NeZero P.q]

/-- **Coins from fair bits.** Decoding `coinLength P` uniform bits as `encDetWord` does gives the
residues of K-PKE's coin law `sampleCoins P`: `r ← CBD_{η₁}^k`, `e₁ ← CBD_{η₂}^k`,
`e₂ ← CBD_{η₂}`. -/
theorem uniformList_map_coinResidues :
    (BitString.uniformList (coinLength P)).map (fun coins =>
      (cbdVecResidues P.k P.n P.q P.η₁ (coins.take (P.k * (P.n * (2 * P.η₁)))),
        cbdVecResidues P.k P.n P.q P.η₂
          ((coins.drop (P.k * (P.n * (2 * P.η₁)))).take (P.k * (P.n * (2 * P.η₂)))),
        cbdResidues P.n P.q P.η₂
          (coins.drop (P.k * (P.n * (2 * P.η₁)) + P.k * (P.n * (2 * P.η₂)))))) =
      (ProbComp.eval (sampleCoins P)).map fun (r, e₁, e₂) =>
        (polyVecResidues r, polyVecResidues e₁, polyResidues e₂) := by
  set L₁ := P.k * (P.n * (2 * P.η₁))
  set L₂ := P.k * (P.n * (2 * P.η₂))
  set L₃ := P.n * (2 * P.η₂)
  have hlen : coinLength P = L₁ + (L₂ + L₃) := by simp only [coinLength, L₁, L₂, L₃]; omega
  have h₁ := uniformList_map_cbdVecResidues P.k P.n P.q P.η₁
  have h₂ := uniformList_map_cbdVecResidues P.k P.n P.q P.η₂
  have h₃ := uniformList_map_cbdResidues P.n P.q P.η₂
  calc _ = (BitString.uniformList L₁).bind fun a => (BitString.uniformList L₂).bind fun b =>
        (BitString.uniformList L₃).bind fun c =>
          PMF.pure (cbdVecResidues P.k P.n P.q P.η₁ a, cbdVecResidues P.k P.n P.q P.η₂ b,
            cbdResidues P.n P.q P.η₂ c) := by
        have hB := BitString.uniformList_bind_split L₁ (L₂ + L₃) fun front rest =>
          PMF.pure (cbdVecResidues P.k P.n P.q P.η₁ front,
            cbdVecResidues P.k P.n P.q P.η₂ (rest.take L₂), cbdResidues P.n P.q P.η₂ (rest.drop L₂))
        rw [hlen, PMF.map]
        simp only [Function.comp_def, List.drop_drop] at hB ⊢
        rw [hB]
        congr 1 with front : 1
        exact BitString.uniformList_bind_split L₂ L₃ fun b c =>
          PMF.pure (cbdVecResidues P.k P.n P.q P.η₁ front, cbdVecResidues P.k P.n P.q P.η₂ b,
            cbdResidues P.n P.q P.η₂ c)
    _ = ((BitString.uniformList L₁).map (cbdVecResidues P.k P.n P.q P.η₁)).bind fun r =>
        ((BitString.uniformList L₂).map (cbdVecResidues P.k P.n P.q P.η₂)).bind fun e₁ =>
          ((BitString.uniformList L₃).map (cbdResidues P.n P.q P.η₂)).bind fun e₂ =>
            PMF.pure (r, e₁, e₂) := by
        simp only [PMF.bind_map, Function.comp_def]
    _ = _ := by
        rw [h₁, h₂, h₃]
        simp only [sampleCoins, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_map,
          PMF.map_bind, PMF.pure_map, Function.comp_def]

/-- **Encryption realizes K-PKE.** Encrypting `m` under the word of a public key `pk`, with
`coinLength P` fair coins, has the law of the word of K-PKE's encryption `encrypt P pk` of the
first `n` bits of `m` with coins drawn by `sampleCoins P`. -/
theorem eval_encDetWord_sampleList (pk : PublicKey P) (m : List Bool) :
    ProbComp.eval (do
      let coins ← BitString.sampleList (coinLength P)
      return encDetWord P (encodePublicKey pk) m coins) =
      (ProbComp.eval (sampleCoins P)).map fun coins =>
        encodeCiphertext (encrypt P pk (fun i => m.getD i false) coins) := by
  have hkey : publicKeyDecoder.decode (encodePublicKey pk) =
      (matrixResidues pk.1, polyVecResidues pk.2) :=
    publicKeyDecoder.decode_enc _
  have hlaw := congrArg (PMF.map fun (r, e₁, e₂) =>
      encCiphertextResidues
        (encryptResidues P (matrixResidues pk.1) (polyVecResidues pk.2) m r e₁ e₂))
    (uniformList_map_coinResidues P)
  simp only [PMF.map_comp, Function.comp_def, encryptResidues_eq] at hlaw
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, encDetWord, hkey]
  exact (PMF.bind_pure_comp _ _).trans (hlaw.trans rfl)

/-- **Key generation realizes K-PKE with an approximately uniform matrix.** The word key
generator draws `A` with independent coefficients from the bounded modular sampler at
`q.size + precision` fair bits and `s, e ← CBD_{η₁}^k`, and returns the words of the K-PKE keys
`(A, A s + e)` and `s`. -/
theorem eval_keyGenWord (precision : ℕ) :
    ProbComp.eval (keyGenWord P precision) = (do
      let A ← PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.n =>
        (ProbComp.eval (ProbComp.sampleModNat (P.q.size + precision) P.q)).map
          (Nat.cast : ℕ → ZMod P.q)
      let s ← ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)
      let e ← ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)
      return (encodePublicKey (P := P) (moduleLWEKeyGen A s e), encodeSecretKey (P := P) s)) := by
  have hA := eval_sampleModNat_coefficients P.k P.k P.n (P.q.size + precision) P.q
  have hs := uniformList_map_cbdVecResidues P.k P.n P.q P.η₁
  calc _ = (ProbComp.eval (OracleComp.replicate P.k (OracleComp.replicate P.k
        (OracleComp.replicate P.n (ProbComp.sampleModNat (P.q.size + precision) P.q))))).bind
          fun A => ((BitString.uniformList (P.k * (P.n * (2 * P.η₁)))).map
            (cbdVecResidues P.k P.n P.q P.η₁)).bind fun s =>
              ((BitString.uniformList (P.k * (P.n * (2 * P.η₁)))).map
                (cbdVecResidues P.k P.n P.q P.η₁)).bind fun e =>
                  PMF.pure (encPublicKeyResidues (A, publicKeyResidues P A s e),
                    encPolyVecResidues s) := by
        simp only [keyGenWord, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
          PMF.bind_map, Function.comp_def]
    _ = _ := by
        rw [hA, hs]
        simp only [PMF.bind_map, Function.comp_def, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
        congr 1 with A : 1
        congr 1 with s : 1
        congr 1 with e : 1
        have hpk := publicKeyResidues_eq P A s e
        simp only [encodePublicKey, encodeSecretKey, moduleLWEKeyGen, ← hpk]
        rfl

/-- The public key of the word key generator is within `k * k * n / 2 ^ precision` of the word of
the public key of K-PKE's key generation `keyGen P`, whose matrix is exactly uniform. -/
theorem closeTo_keyGenWord (precision : ℕ) :
    CloseTo ((ProbComp.eval (keyGen P)).map fun keys => encodePublicKey (P := P) keys.1)
      ((ProbComp.eval (keyGenWord P precision)).map Prod.fst)
      ((P.k : ℝ≥0∞) * P.k * P.n / 2 ^ precision) := by
  have h := (closeTo_uniform_pi_sampleModNat_precision P.k P.k P.n precision P.q).bind_left
    fun A => (do
      let s ← ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)
      let e ← ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)
      return encodePublicKey (P := P) (moduleLWEKeyGen A s e))
  rw [eval_keyGenWord]
  convert h using 1
  · simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind,
      PMF.pure_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  · simp only [PMF.map_bind, PMF.pure_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    rfl

end Laws

/-- The bound on the length of ciphertext words: `k` framed residue lists and one residue list, each
of at most `n` residues of `d_u` and `d_v` bits. -/
def ctLength (P : Params) : ℕ :=
  2 * (P.k * (2 * (P.n * (2 * P.du + 1)) + 1)) + 1 + P.n * (2 * P.dv + 1)

/-- **K-PKE as a word-level public-key encryption family.** At security parameter `κ`, the scheme
uses the parameters `P κ`: messages are words of `n` bits, coins are `coinLength (P κ)` fair bits,
ciphertexts are words of length at most `ctLength (P κ)`, and key generation draws the matrix at
precision `κ`. -/
noncomputable def kpke (P : ℕ → Params) : WordPKE where
  msgLen κ := (P κ).n
  coinLen κ := coinLength (P κ)
  ctLen κ := ctLength (P κ)
  keyGen κ := keyGenWord (P κ) κ
  encDet κ := encDetWord (P κ)
  dec κ := decWord (P κ)

/-- **K-PKE is an efficient word-level family** whenever its parameters are computable in
polynomial time from the unary security parameter. -/
theorem kpke_isEfficient {P : ℕ → Params} (hP : ComputableInPolyTime P encUnary encParams) :
    (kpke P).IsEfficient where
  msgLen := by
    change ComputableInPolyTime (fun κ => (P κ).n) encUnary encUnary
    fun_prop
  coinLen := by
    change ComputableInPolyTime (fun κ => coinLength (P κ)) encUnary encUnary
    unfold coinLength
    fun_prop
  ctLen := by
    change ComputableInPolyTime (fun κ => ctLength (P κ)) encUnary encUnary
    unfold ctLength
    fun_prop
  keyGen := by
    change IsPPTOn encUnary (encPair encBits encBits) fun κ => keyGenWord (P κ) κ
    have h : ComputableInPolyTime (fun κ => (P κ, κ)) encUnary (encPair encParams encUnary) :=
      hP.prod ComputableInPolyTime.id'
    simpa only using isPPTOn_keyGenWord.preprocess h
  encDet := by
    change ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool =>
      encDetWord (P x.1) x.2.1 x.2.2.1 x.2.2.2) encEncDetInput encBits
    exact ComputableInPolyTime.encDetWord (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  dec := by
    change ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => decWord (P x.1) x.2.1 x.2.2)
      (encKeyedInput encBits) (encOption encBits)
    exact ComputableInPolyTime.decWord (by fun_prop) (by fun_prop) (by fun_prop)

private theorem length_encList_encNat_le {n d : ℕ} {xs : List ℕ} (hlen : xs.length ≤ n)
    (hx : ∀ x ∈ xs, x < 2 ^ d) : (encList encNat xs).length ≤ n * (2 * d + 1) := by
  rw [length_encList]
  calc (xs.map fun x => 2 * (encNat x).length + 1).sum ≤ xs.length • (2 * d + 1) := by
        refine (List.sum_le_length_nsmul _ (2 * d + 1) ?_).trans_eq (by simp)
        simp only [List.mem_map]
        rintro _ ⟨x, hxs, rfl⟩
        have := length_encNat_le_of_lt_two_pow (hx x hxs)
        omega
    _ ≤ n * (2 * d + 1) := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hlen

private theorem lt_of_mem_compressResidues {q d x : ℕ} {a : List ℕ}
    (hx : x ∈ compressResidues q d a) : x < 2 ^ d := by
  simp only [compressResidues, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  have hp : (0 : ℤ) < ((2 ^ d : ℕ) : ℤ) := by positivity
  rw [ZMod.modulusSwitchResidue]
  have h₁ := Int.emod_nonneg ((2 * ((2 ^ d : ℕ) : ℤ) * y + q) / (2 * (q : ℤ))) hp.ne'
  have h₂ := Int.emod_lt_of_pos ((2 * ((2 ^ d : ℕ) : ℤ) * y + q) / (2 * (q : ℤ))) hp
  omega

private theorem length_addResidues_le (q : ℕ) (a b : List ℕ) :
    (addResidues q a b).length ≤ a.length := by
  simp [addResidues]

/-- Ciphertext words are at most `ctLength P` bits long, for every public-key word, message and
coin word. -/
theorem length_encDetWord_le (P : Params) (pk m coins : List Bool) :
    (encDetWord P pk m coins).length ≤ ctLength P := by
  simp only [encDetWord, encCiphertextResidues, encPair_apply, List.length_append, length_frame,
    encryptResidues, ctLength]
  have hu : (encPolyVecResidues (((List.range P.k).map fun i =>
      addResidues P.q (negacyclicInnerResidues P.n P.q
        ((publicKeyDecoder.decode pk).1.map fun row => row.getD i [])
        (cbdVecResidues P.k P.n P.q P.η₁ (coins.take (P.k * (P.n * (2 * P.η₁))))))
        ((cbdVecResidues P.k P.n P.q P.η₂ ((coins.drop (P.k * (P.n * (2 * P.η₁)))).take
          (P.k * (P.n * (2 * P.η₂))))).getD i [])).map (compressResidues P.q P.du))).length ≤
      P.k * (2 * (P.n * (2 * P.du + 1)) + 1) := by
    rw [encPolyVecResidues, length_encList]
    refine (List.sum_le_length_nsmul _ (2 * (P.n * (2 * P.du + 1)) + 1) ?_).trans_eq (by simp)
    intro y hy
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hy
    obtain ⟨i, -, rfl⟩ := hy
    have := length_encList_encNat_le (n := P.n) (d := P.du)
      (xs := compressResidues P.q P.du (addResidues P.q (negacyclicInnerResidues P.n P.q
        ((publicKeyDecoder.decode pk).1.map fun row => row.getD i [])
        (cbdVecResidues P.k P.n P.q P.η₁ (coins.take (P.k * (P.n * (2 * P.η₁))))))
        ((cbdVecResidues P.k P.n P.q P.η₂ ((coins.drop (P.k * (P.n * (2 * P.η₁)))).take
          (P.k * (P.n * (2 * P.η₂))))).getD i [])))
      (by
        simp only [compressResidues, List.length_map]
        refine (length_addResidues_le _ _ _).trans ?_
        simp [negacyclicInnerResidues])
      fun x hx => lt_of_mem_compressResidues hx
    omega
  have hv := length_encList_encNat_le (n := P.n) (d := P.dv)
    (xs := compressResidues P.q P.dv (addResidues P.q (addResidues P.q
      (negacyclicInnerResidues P.n P.q (publicKeyDecoder.decode pk).2
        (cbdVecResidues P.k P.n P.q P.η₁ (coins.take (P.k * (P.n * (2 * P.η₁))))))
      (cbdResidues P.n P.q P.η₂ (coins.drop (P.k * (P.n * (2 * P.η₁)) +
        P.k * (P.n * (2 * P.η₂))))))
      (messageResidues P.n P.q m)))
    (by
      simp only [compressResidues, List.length_map]
      refine (length_addResidues_le _ _ _).trans ((length_addResidues_le _ _ _).trans ?_)
      simp [negacyclicInnerResidues])
    fun x hx => lt_of_mem_compressResidues hx
  omega

/-- **K-PKE ciphertexts fit their ciphertext space.** -/
theorem kpke_ciphertextFits (P : ℕ → Params) : (kpke P).CiphertextFits :=
  fun κ pk _ _ m r _ _ => length_encDetWord_le (P κ) pk m r

/-- Decrypting the word of a ciphertext under the word of a secret key computes `decrypt`. -/
theorem decWord_encode (P : Params) [NeZero P.q] (s : SecretKey P) (ct : Ciphertext P) :
    decWord P (encodeSecretKey s) (encodeCiphertext ct) = some (List.ofFn (decrypt P s ct)) := by
  simp only [decWord, encodeSecretKey, encodeCiphertext, ciphertextDecoder.decode_enc,
    Decoder.decode_enc, decryptResidues_eq]

end Cslib.Crypto.MLKEM
