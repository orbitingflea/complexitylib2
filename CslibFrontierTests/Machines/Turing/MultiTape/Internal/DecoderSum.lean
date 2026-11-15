/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Sum

/-! Checked malformed-input and round-trip clients for tagged-sum decoders. -/

open Turing.MultiTapeTM

example {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (D₁ : Decoder a) (D₂ : Decoder b) (s : α ⊕ β) :
    (Decoder.sum D₁ D₂).decode [] = .inl (D₁.decode []) ∧
    (Decoder.sum D₁ D₂).decode (encSum a b s) = s ∧
    ComputableInPolyTime (Decoder.sum D₁ D₂).decode encBits (encSum a b) :=
  ⟨rfl, (Decoder.sum D₁ D₂).decode_enc s, (Decoder.sum D₁ D₂).computableInPolyTime⟩
