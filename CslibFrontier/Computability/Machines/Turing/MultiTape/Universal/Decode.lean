/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Decoding descriptions of machines

Every word decodes to a description of a machine (`Turing.MultiTapeTM.Universal.descDecoder`):
the decoder inverts the encoding `Turing.MultiTapeTM.Universal.eDesc` of descriptions, returns a
description of polynomial encoded length on every other word, and is computable within
bounds of fixed degrees. It is assembled from the generic decoders of
`CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder` along the fields of a
description, its transitions, their keys and their actions. The same constructive chain decodes
the signed unary head position and zipper fields of a work tape.

A description framed at the start of a word is recovered whatever follows it
(`Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append`), so a description can be padded
to any length.

## Main definitions

* `Turing.MultiTapeTM.Universal.decodeDesc`: the description decoded from a word.
* `Turing.MultiTapeTM.Universal.intUnaryDecoder`, `.tapeDecoder`: total decoders of signed unary
  integers and encoded work tapes.

## Main results

* `Turing.MultiTapeTM.Universal.decodeDesc_eDesc`: decoding inverts the encoding.
* `Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append`: padded descriptions.
* `Turing.MultiTapeTM.Universal.exists_computableInDegree_decodeDesc`: decoding is
  computable within bounds of fixed degrees.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Universal

/-- The sign read from a word: zero if it is empty (`q.1`), and otherwise positive or negative as
its head (`q.2`) is `true` or `false`. -/
def signOf (q : Bool × Bool) : SignType := if q.1 then 0 else if q.2 then 1 else -1

/-- Moves are decoded from the head of the word. -/
def signDecoder : Decoder encSign where
  decode w := signOf (w.isEmpty, w.headD false)
  decode_enc m := by cases m <;> rfl
  computable := ⟨_, _, (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encSign) signOf).comp
      (Internal.DecoderWords.empty_degree.prod Internal.DecoderWords.bool_degree)⟩

/-- Symbols and blanks. -/
def symDecoder : Decoder eSym := .option .unary

/-- Unary signed integers, through their nonnegative/negative tagged-sum representation. -/
def intUnaryDecoder : Decoder encIntUnary :=
  (Decoder.sum .unary .unary).map
    (Sum.elim Int.ofNat Int.negSucc)
    (fun z => match z with | .ofNat n => .inl n | .negSucc n => .inr n)
    (fun z => by cases z <;> rfl) fun s => by cases s <;> rfl

/-- Work-tape zippers, from their signed head position and two symbol lists. -/
def tapeDecoder : Decoder eTape :=
  (Decoder.pair intUnaryDecoder (.pair (.list symDecoder) (.list symDecoder))).map
    (fun (head, left, right) => ⟨head, left, right⟩)
    (fun t => (t.head, t.left, t.right)) (fun _ => rfl) fun _ => rfl

/-- Keys of transitions, from their fields. -/
def keyDecoder : Decoder eKey :=
  (Decoder.pair .unary (.pair symDecoder (.list symDecoder))).map
    (fun (state, input, work) => ⟨state, input, work⟩)
    (fun k => (k.state, k.input, k.work)) (fun _ => rfl)
    fun _ => rfl

/-- Actions on a work tape. -/
def tapeActDecoder : Decoder eTA := .pair (.option symDecoder) signDecoder

/-- Actions, from their fields. -/
def actDecoder : Decoder eAct :=
  (Decoder.pair signDecoder (.pair (.list tapeActDecoder) (.pair symDecoder symDecoder))).map
    (fun (inputTape, workTapes, output, state) => ⟨inputTape, workTapes, output, state⟩)
    (fun a => (a.inputTape, a.workTapes, a.output, a.state)) (fun _ => rfl) fun _ => rfl

/-- **The decoder of descriptions.** -/
def descDecoder : Decoder eDesc :=
  (Decoder.pair .unary (.pair .unary (.list (.pair keyDecoder actDecoder)))).map
    (fun (tapes, q₀, table) => ⟨tapes, q₀, table⟩)
    (fun d => (d.tapes, d.q₀, d.table)) (fun _ => rfl)
    fun _ => rfl

/-- The description decoded from a word. -/
def decodeDesc (w : List Bool) : Desc := descDecoder.decode w

/-- Decoding inverts the encoding of descriptions. -/
theorem decodeDesc_eDesc (d : Desc) : decodeDesc (eDesc d) = d :=
  descDecoder.decode_enc d

/-- **Padded descriptions.** A description framed at the start of a word is decoded from the
framed word, whatever follows it. -/
theorem decodeDesc_unframe_frame_append (d : Desc) (pad : List Bool) :
    decodeDesc (unframe (frame (eDesc d) ++ pad)) = d := by
  rw [unframe_frame_append, decodeDesc_eDesc]

/-- **Decoding is efficient.** It is computable, and the decoded descriptions have
encoded length polynomial in the length of the word, within bounds of fixed degrees. -/
theorem exists_computableInDegree_decodeDesc :
    ∃ d e, ComputableInDegree decodeDesc encBits eDesc d e :=
  descDecoder.computable

end Universal

end Turing.MultiTapeTM
