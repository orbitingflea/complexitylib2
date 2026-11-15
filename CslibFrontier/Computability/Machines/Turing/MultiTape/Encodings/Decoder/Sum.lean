/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Sum

/-!
# Total decoding of tagged sums

The first bit chooses the summand and the remainder is decoded by its supplied decoder. This topic
module keeps tagged-sum construction out of the lower-fan-out basic decoder module.

## Main definitions

* `Turing.MultiTapeTM.Decoder.sum`: total decoding of `encSum`.

## Main results

The decoder's `Decoder.decode_enc` field proves that it retracts `encSum`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Decoder

/-- Tagged sums are decoded according to their first bit. Empty and malformed words select the
left summand, consistently with `Decoder.bool`. -/
def sum {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} (D₁ : Decoder enc₁)
    (D₂ : Decoder enc₂) : Decoder (encSum enc₁ enc₂) where
  decode w := if w.headD false then .inr (D₂.decode w.tail) else .inl (D₁.decode w.tail)
  decode_enc s := by cases s <;> simp [D₁.decode_enc, D₂.decode_enc]
  computable := by
    obtain ⟨d₁, e₁, h₁⟩ := D₁.computable
    obtain ⟨d₂, e₂, h₂⟩ := D₂.computable
    have hleft := (ComputableInDegree.inl enc₁ enc₂).comp
      (h₁.comp Internal.DecoderWords.tail_degree)
    have hright := (ComputableInDegree.inr enc₁ enc₂).comp
      (h₂.comp Internal.DecoderWords.tail_degree)
    have hdecode := Internal.DecoderWords.bool_degree.ite
      (hright.restrict _) (hleft.restrict _)
    exact ⟨_, _, by simpa only [Function.comp_apply] using hdecode⟩

end Turing.MultiTapeTM.Decoder
