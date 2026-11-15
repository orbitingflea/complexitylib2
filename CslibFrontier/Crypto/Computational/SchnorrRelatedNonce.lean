/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.RelatedNonce
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Computational.DiscreteLog.Extract

/-!
# Polynomial-time Schnorr related-nonce extraction

Computes the related-nonce Schnorr key recovery of [BonehShoup2023], Exercise 19.1, on bit words
over a `PrimeOrderGroupFamily`: `schnorrRelatedNonceExtractWord` computes
`extractNat (F.order d) (a * c₀) (a * z₀ + b) c₁ z₁` on the binary encodings of `a, b, c₀, z₀,
c₁, z₁`, runs in polynomial time (`computableInPolyTime_schnorrRelatedNonceExtractWord`), and
recovers `relatedNonceExtract` modulo `F.order d` whenever `a * c₀ ≠ c₁` modulo `F.order d`
(`ofBits_schnorrRelatedNonceExtractWord`).

**Scope.** This module covers only the polynomial-time deterministic word extraction step; there is
no word-level attack game or PPT reduction over `PrimeOrderGroupFamily`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRelatedNonceExtractWord`: binary-word key recovery from
  a group description `d` and six words `(a, b, c₀, z₀, c₁, z₁)`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrRelatedNonceExtractWord`:
  `schnorrRelatedNonceExtractWord` is computable in polynomial time.
* `Cslib.Crypto.PrimeOrderGroupFamily.ofBits_schnorrRelatedNonceExtractWord`: decoded `ZMod`
  agreement with `relatedNonceExtract` when `a * c₀ ≠ c₁` modulo `F.order d`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.2 and Exercise 19.1.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Turing.MultiTapeTM Protocols SigmaProtocol

variable {F : PrimeOrderGroupFamily}

variable (F) in
/-- The key recovery of [BonehShoup2023], Exercise 19.1, on words: from the description and the
binary numbers `a`, `b`, `c₀`, `z₀`, `c₁`, `z₁`, the binary value of
`extractNat q (a * c₀) (a * z₀ + b) c₁ z₁`. -/
def schnorrRelatedNonceExtractWord :
    F.Desc × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool
  | (d, a, b, c₀, z₀, c₁, z₁) =>
    (extractNat (F.order d) (ofBits a * ofBits c₀) (ofBits a * ofBits z₀ + ofBits b) (ofBits c₁)
      (ofBits z₁)).bits

/-- `schnorrRelatedNonceExtractWord` is computable in polynomial time. -/
theorem computableInPolyTime_schnorrRelatedNonceExtractWord :
    ComputableInPolyTime F.schnorrRelatedNonceExtractWord
      (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))) encBits := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits
    (encPair encBits (encPair encBits encBits)))))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool =>
        p.1) encIn F.encDesc := by fun_prop
  have hword {k : F.Desc × List Bool × List Bool × List Bool × List Bool × List Bool ×
      List Bool → List Bool} (hk : ComputableInPolyTime k encIn encBits) :
      ComputableInPolyTime (fun p => ofBits (k p)) encIn encNat :=
    ComputableInPolyTime.bitsToNat.comp hk
  have ha := hword (k := fun p => p.2.1) (by fun_prop)
  have hb := hword (k := fun p => p.2.2.1) (by fun_prop)
  have hc₀ := hword (k := fun p => p.2.2.2.1) (by fun_prop)
  have hz₀ := hword (k := fun p => p.2.2.2.2.1) (by fun_prop)
  have hc₁ := hword (k := fun p => p.2.2.2.2.2.1) (by fun_prop)
  have hz₁ := hword (k := fun p => p.2.2.2.2.2.2) (by fun_prop)
  have hext := computableInPolyTime_extractNat hd (.binary_mul' ha hc₀)
    (.binary_add' (.binary_mul' ha hz₀) hb) hc₁ hz₁
  exact hext.encoding_comp

/-- `schnorrRelatedNonceExtractWord` computes `relatedNonceExtract` on binary numbers, whenever
`a * c₀ ≠ c₁` modulo the group order. -/
theorem ofBits_schnorrRelatedNonceExtractWord (d : F.Desc) (a b c₀ z₀ c₁ z₁ : List Bool)
    (hc : (ofBits a : ZMod (F.order d)) * (ofBits c₀ : ZMod (F.order d)) ≠
      (ofBits c₁ : ZMod (F.order d))) :
    ((ofBits (F.schnorrRelatedNonceExtractWord (d, a, b, c₀, z₀, c₁, z₁)) : ℕ) :
        ZMod (F.order d)) =
      relatedNonceExtract (ofBits a : ZMod (F.order d)) (ofBits b : ZMod (F.order d))
        (ofBits c₀ : ZMod (F.order d)) (ofBits z₀ : ZMod (F.order d))
        (ofBits c₁ : ZMod (F.order d)) (ofBits z₁ : ZMod (F.order d)) := by
  rw [schnorrRelatedNonceExtractWord, ofBits_bits,
    extractNat_cast (by rw [Nat.cast_mul]; exact hc)]
  simp [relatedNonceExtract]

end Cslib.Crypto.PrimeOrderGroupFamily
