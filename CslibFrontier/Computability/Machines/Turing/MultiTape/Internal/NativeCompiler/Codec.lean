/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.CodecWordMachines
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelIte
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelTakeDropUnary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler

/-!
# Named native streaming codecs

This module retains the actual finite-state transducers used by the first layer of an encoded
universal interpreter. `NativeCompiler.ofTransducer` packages the transducer followed by the
existing input rewind, with its constructive state encoding, exact description, linear clock and
zero workspace. It does not select a machine from an existential computability certificate.

The named codecs are total on malformed words. In particular, the Boolean decoder uses `false` on
empty input, frame decoders follow the existing incomplete-frame convention, and `framesDecoder`
closes a final incomplete frame. Pair projections reuse those same machines directly rather than
treating encoded tuple access as a semantic callback.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.ofTransducer`: retain a finite transducer as a named
  tidy compiler.
* `Turing.MultiTapeTM.Internal.NativeCompiler.prefixBit`: retain a raw-word prefix operation.
* `Turing.MultiTapeTM.Internal.NativeCompiler.optionSome`, `.sumInl`, `.sumInr`: retain the direct
  one-bit prefix transducers for standard option and sum encodings.
* `Turing.MultiTapeTM.Internal.NativeCompiler.optionIsSomeBool`, `.optionIsSomeTest`: retain the
  standard option-constructor test in Boolean and branch-test encodings.
* `Turing.MultiTapeTM.Internal.NativeCompiler.sumTag`, `.sumPayload`: retain the constructor tag
  and untagged payload word.
* `Turing.MultiTapeTM.Internal.NativeCompiler.framedValue`: retain standard framing while keeping
  the semantic value type.
* `Turing.MultiTapeTM.Internal.NativeCompiler.first`,
  `Turing.MultiTapeTM.Internal.NativeCompiler.second`: direct standard-pair projections.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryDecoder`,
  `Turing.MultiTapeTM.Internal.NativeCompiler.boolDecoder`: total unary and Boolean decoders.
* `Turing.MultiTapeTM.Internal.NativeCompiler.isEmpty`, `.boolToTest`, `.unaryIsZero`,
  `.unaryIsZeroTest`, `.unaryPred`: retained empty-word testing, the explicit Boolean-to-branch
  tag conversion, unary zero testing and saturating unary predecessor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unframeDecoder`,
  `Turing.MultiTapeTM.Internal.NativeCompiler.unframeValue`,
  `Turing.MultiTapeTM.Internal.NativeCompiler.dropFrameDecoder`,
  `Turing.MultiTapeTM.Internal.NativeCompiler.framesDecoder`: named total frame parsers.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryListDecoder`: split a raw word into frames and
  replace every frame by its unary length in one streaming pass.
* `Turing.MultiTapeTM.Internal.NativeCompiler.takeUnary`, `.dropUnary`: retain the direct linear
  encoded-list prefix and suffix machines through the existing tidy normal form.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.machine_ofTransducer`: the retained machine is
  definitionally the supplied transducer followed by input rewind.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Encodings Internal.DecoderWords Internal.FrameMachines

universe u v

/-- Retain a finite transducer followed by input rewind as a named tidy compiler. Every input bit
is read by the transducer and by the rewind; emitted bits are included in the transducer clock. -/
@[expose] noncomputable def ofTransducer {Alpha Beta : Type*} {State : Type} [Fintype State]
    {f : Alpha → Beta} {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (transducer : Transducer Bool State) (stateEncoding : State ↪ ℕ)
    (run_eq : ∀ input, transducer.run transducer.q₀ (encIn input) = encOut (f input)) :
    NativeCompiler f encIn encOut :=
  {
    tapeCount := 0
    State := (State × Option Bool × Bool) ⊕ RewindState
    machine := transducer.toTM.seq (rewindInput Bool)
    stateEncoding := sumStateEncoding (transducerMachineStateEncoding stateEncoding)
      rewindStateEncoding
    time := fun input => 4 * (encIn input).length + 8
    workspace := fun _ => 0
    computes := fun input => by
      simpa only [run_eq input] using transducer.computesTidily (encIn input)
  }

/-- The transducer constructor retains its exact transducer-plus-rewind machine. -/
theorem machine_ofTransducer {Alpha Beta : Type*} {State : Type} [Fintype State]
    {f : Alpha → Beta} {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (transducer : Transducer Bool State) (stateEncoding : State ↪ ℕ)
    (run_eq : ∀ input, transducer.run transducer.q₀ (encIn input) = encOut (f input)) :
    (ofTransducer transducer stateEncoding run_eq).machine =
      transducer.toTM.seq (rewindInput Bool) :=
  rfl

/-- Prefix a fixed tag bit, streaming the input unchanged after the first transition. -/
def prefixBitT (tag : Bool) : Transducer Bool Bool where
  q₀ := false
  step
    | false, bit => (true, [tag, bit])
    | true, bit => (true, [bit])
  final
    | false => [tag]
    | true => []
  length_step_le state bit := by cases state <;> cases bit <;> simp
  length_final_le state := by cases state <;> simp

private lemma prefixBitT_step_false (tag bit : Bool) :
    (prefixBitT tag).step false bit = (true, [tag, bit]) := rfl

private lemma prefixBitT_step_true (tag bit : Bool) :
    (prefixBitT tag).step true bit = (true, [bit]) := rfl

/-- The prefix transducer emits exactly the fixed tag followed by the input. -/
theorem prefixBitT_run (tag : Bool) (input : List Bool) :
    (prefixBitT tag).run (prefixBitT tag).q₀ input = tag :: input := by
  have copy : ∀ word : List Bool, (prefixBitT tag).run true word = word := by
    intro word
    induction word with
    | nil => rfl
    | cons bit word ih =>
        rw [Transducer.run_cons, prefixBitT_step_true, ih]
        rfl
  cases input with
  | nil => rfl
  | cons bit input =>
      change (prefixBitT tag).run false (bit :: input) = _
      rw [Transducer.run_cons, prefixBitT_step_false, copy]
      rfl

/-- Retained raw-word prefix operation. -/
@[expose] noncomputable def prefixBit (tag : Bool) :
    NativeCompiler (fun word => tag :: word) encBits encBits :=
  ofTransducer (prefixBitT tag) Universal.eBit (prefixBitT_run tag)

/-- Retained constructor for the standard `some` tag. -/
@[expose] noncomputable def optionSome {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler some enc (encOption enc) :=
  ofTransducer (prefixBitT true) Universal.eBit fun input => by
    simp only [encOption_some, prefixBitT_run]

/-- Retained constructor for the standard left-sum tag. -/
@[expose] noncomputable def sumInl {Alpha Beta : Type*} (encLeft : Alpha ↪ List Bool)
    (encRight : Beta ↪ List Bool) : NativeCompiler Sum.inl encLeft (encSum encLeft encRight) :=
  ofTransducer (prefixBitT false) Universal.eBit fun input => by
    simp only [encSum_inl, prefixBitT_run]

/-- Retained constructor for the standard right-sum tag. -/
@[expose] noncomputable def sumInr {Alpha Beta : Type*} (encLeft : Alpha ↪ List Bool)
    (encRight : Beta ↪ List Bool) : NativeCompiler Sum.inr encRight (encSum encLeft encRight) :=
  ofTransducer (prefixBitT true) Universal.eBit fun input => by
    simp only [encSum_inr, prefixBitT_run]

/-- Retained standard framing with the semantic value type unchanged. -/
@[expose] noncomputable def framedValue {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler id enc (encFramed enc) :=
  (encodeFrame enc).ofOutputEq (g := id) fun _ => rfl

/-- Drop the first bit of a raw word. -/
@[expose] noncomputable def tailDecoder : NativeCompiler List.tail encBits encBits :=
  ofTransducer (headT (some false)) Universal.eBit headT_some_false_run

/-- Total Boolean decoder, returning `false` on empty input and the first symbol otherwise. -/
@[expose] noncomputable def boolDecoder :
    NativeCompiler (fun input : List Bool => input.headD false) encBits encBool :=
  ofTransducer (headDefaultT false) Universal.eBit fun input =>
    headDefaultT_run false input

/-- Read the constructor tag of a standard sum encoding. -/
@[expose] noncomputable def sumTag {Alpha Beta : Type*} (encLeft : Alpha ↪ List Bool)
    (encRight : Beta ↪ List Bool) :
    NativeCompiler Sum.isRight (encSum encLeft encRight) encBool :=
  (boolDecoder.ofInputEq (fun value => encSum encLeft encRight value) fun _ => rfl).ofOutputEq
    fun value => by cases value <;> rfl

/-- Emit the untagged payload word of a standard sum encoding. -/
@[expose] noncomputable def sumPayload {Alpha Beta : Type*} (encLeft : Alpha ↪ List Bool)
    (encRight : Beta ↪ List Bool) :
    NativeCompiler (fun value => (encSum encLeft encRight value).tail)
      (encSum encLeft encRight) encBits :=
  tailDecoder.ofInputEq (fun value => encSum encLeft encRight value) fun _ => rfl


/-- Explicit encoding of the three frame-parser states. -/
@[expose] def frameStateEncoding : FrameState ↪ ℕ :=
  ⟨fun state => match state with | .marker => 0 | .bit => 1 | .done => 2,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Explicit encoding of the three list-frame-parser states. -/
@[expose] def framesStateEncoding : FramesState ↪ ℕ :=
  ⟨fun state => match state with | .between => 0 | .marker => 1 | .symbol => 2,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Explicit encoding of the direct unary take/drop kernel's eight control states. -/
@[expose] def takeDropUnaryStateEncoding : TakeDropUnary.State ↪ ℕ :=
  ⟨fun state => match state with
    | .skip => 0
    | .skipBit => 1
    | .copy => 2
    | .rewind => 3
    | .marker false => 4
    | .marker true => 5
    | .symbol false => 6
    | .symbol true => 7,
    by intro a b h; grind⟩

/-- Explicit encoding of the four control states used to clear a work tape and its shadow. -/
@[expose] def clearShadowedStateEncoding : ClearShadowedState ↪ ℕ :=
  ⟨fun state => match state with | .start => 0 | .left => 1 | .sweep => 2 | .home => 3,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Constructive encoding of the recursively nested control used to clear a list of work tapes. -/
@[expose] def clearListStateEncoding : (count : ℕ) → ClearListState count ↪ ℕ
  | 0 => unitStateEncoding
  | count + 1 =>
      sumStateEncoding clearShadowedStateEncoding (clearListStateEncoding count)

/-- Decode a framed list of words to their unary lengths in one streaming pass. This uses the
same total convention as `frames`: a final incomplete frame is closed. -/
def unaryListT : Transducer Bool FramesState where
  q₀ := .between
  step
    | .between, true => (.marker, [])
    | .between, false => (.between, [false])
    | .marker, _ => (.symbol, [true, true])
    | .symbol, true => (.marker, [])
    | .symbol, false => (.between, [false])
  final
    | .between => []
    | _ => [false]
  length_step_le state bit := by cases state <;> cases bit <;> simp
  length_final_le state := by cases state <;> simp

private lemma unaryListT_step_between_false :
    unaryListT.step .between false = (.between, [false]) := rfl

private lemma unaryListT_step_between_true :
    unaryListT.step .between true = (.marker, []) := rfl

private lemma unaryListT_step_marker (bit : Bool) :
    unaryListT.step .marker bit = (.symbol, [true, true]) := by
  cases bit <;> rfl

private lemma unaryListT_step_symbol_false :
    unaryListT.step .symbol false = (.between, [false]) := rfl

private lemma unaryListT_step_symbol_true :
    unaryListT.step .symbol true = (.marker, []) := rfl

/-- While inside a frame, `unaryListT` emits the unary length of that frame and continues with
the remaining framed word. -/
theorem unaryListT_run_symbol : ∀ word : List Bool,
    unaryListT.run .symbol word =
      frame (encUnary (unframe word).length) ++ unaryListT.run .between (dropFrame word)
  | [] => rfl
  | [true] => rfl
  | false :: word => by
      rw [Transducer.run_cons, unaryListT_step_symbol_false]
      simp [unframe, dropFrame, frame]
  | true :: bit :: word => by
    rw [Transducer.run_cons, unaryListT_step_symbol_true, Transducer.run_cons,
      unaryListT_step_marker, unaryListT_run_symbol word]
    simp only [List.nil_append, unframe, dropFrame, List.length_cons, encUnary_apply,
      List.replicate_succ, frame_cons, List.cons_append]

/-- The streaming decoder emits the standard encoded list of all decoded unary lengths. -/
theorem unaryListT_run (word : List Bool) :
    unaryListT.run .between word =
      encList encUnary ((frames word).map List.length) := by
  induction word using frames.induct with
  | case1 => rw [frames_nil]; rfl
  | case2 word hword ih =>
    rw [frames_of_ne_nil hword, List.map_cons, encList_cons, ← ih]
    rcases word with _ | ⟨_ | _, rest⟩
    · exact absurd rfl hword
    · rw [Transducer.run_cons, unaryListT_step_between_false]
      simp [unframe, dropFrame, frame, encUnary_apply]
    · rcases rest with _ | ⟨bit, rest⟩
      · rfl
      · rw [Transducer.run_cons, unaryListT_step_between_true, Transducer.run_cons,
          unaryListT_step_marker, unaryListT_run_symbol rest]
        simp only [List.nil_append, unframe, dropFrame, List.length_cons, encUnary_apply,
          List.replicate_succ, frame_cons, List.cons_append]

/-- The first projection of the standard framed pair encoding, using the frame parser directly. -/
@[expose] noncomputable def first {Alpha : Type u} {Beta : Type v}
    (encFirst : Alpha ↪ List Bool)
    (encSecond : Beta ↪ List Bool) :
    NativeCompiler Prod.fst (encPair encFirst encSecond) encFirst := by
  letI : Fintype FrameState := Fintype.ofFinite FrameState
  exact ofTransducer (readFrameT true) frameStateEncoding fun input => by
    change (readFrameT true).run .marker (encPair encFirst encSecond input) = encFirst input.1
    rw [readFrameT_run_true]
    exact unframe_encPair encFirst encSecond input.1 input.2

/-- The second projection of the standard framed pair encoding, using the frame parser directly. -/
@[expose] noncomputable def second {Alpha : Type u} {Beta : Type v}
    (encFirst : Alpha ↪ List Bool)
    (encSecond : Beta ↪ List Bool) :
    NativeCompiler Prod.snd (encPair encFirst encSecond) encSecond := by
  letI : Fintype FrameState := Fintype.ofFinite FrameState
  exact ofTransducer (readFrameT false) frameStateEncoding fun input => by
    change (readFrameT false).run .marker (encPair encFirst encSecond input) = encSecond input.2
    rw [readFrameT_run_false]
    exact dropFrame_encPair encFirst encSecond input.1 input.2

/-- Total unary decoder: every input symbol contributes one unary output symbol. -/
@[expose] noncomputable def unaryDecoder :
    NativeCompiler List.length encBits encUnary :=
  ofTransducer unaryLengthT unitStateEncoding fun input => by
    change unaryLengthT.run () input = List.replicate input.length true
    exact unaryLengthT_run input

/-- Read the standard option constructor tag with one-bit Boolean output. -/
@[expose] noncomputable def optionIsSomeBool {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler Option.isSome (encOption enc) encBool :=
  (boolDecoder.ofInputEq (fun value => encOption enc value) fun _ => rfl).ofOutputEq
    fun value => by cases value <;> rfl

/-- Test whether a raw word is empty. The machine scans the whole input, emits the standard
Boolean encoding and rewinds; malformedness is irrelevant because every raw word is accepted. -/
@[expose] noncomputable def isEmpty :
    NativeCompiler (fun input : List Bool => input.isEmpty) encBits encBool :=
  ofTransducer isEmptyT Universal.eBit isEmptyT_run

/-- Convert the one-bit Boolean encoding to the branch-test encoding: false becomes the empty
word and true becomes `[true]`. Branching consumers must charge this retained conversion rather
than interpreting `encBool` as `encTest`. -/
def boolToTestT : Transducer Bool Unit where
  q₀ := ()
  step _ bit := ((), if bit then [true] else [])
  final _ := []
  length_step_le _ bit := by cases bit <;> simp
  length_final_le _ := by simp

/-- The true-filter transducer realizes the empty/nonempty test encoding on one-bit Booleans. -/
theorem boolToTestT_run (input : Bool) :
    boolToTestT.run boolToTestT.q₀ (encBool input) = encTest input := by
  cases input <;> rfl

/-- Retained conversion from one-bit Booleans to empty/nonempty branch tests. -/
@[expose] noncomputable def boolToTest : NativeCompiler id encBool encTest :=
  ofTransducer boolToTestT unitStateEncoding boolToTestT_run

/-- Read the standard option constructor tag in the empty/nonempty branch encoding. -/
@[expose] noncomputable def optionIsSomeTest {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler Option.isSome (encOption enc) encTest :=
  boolToTest.comp (optionIsSomeBool enc)

/-- Test whether a unary natural is zero using the same retained empty-word transducer. -/
@[expose] noncomputable def unaryIsZero :
    NativeCompiler (fun input : ℕ => decide (input = 0)) encUnary encBool :=
  ofTransducer isEmptyT Universal.eBit fun input => by
    rw [isEmptyT_run]
    cases input <;> rfl

/-- Unary zero test in the empty/nonempty branch encoding, including the retained tag conversion. -/
@[expose] noncomputable def unaryIsZeroTest :
    NativeCompiler (fun input : ℕ => decide (input = 0)) encUnary encTest :=
  boolToTest.comp unaryIsZero

/-- Saturating predecessor on unary naturals. This is the public `headT` drop-first-symbol
machine, not the private proof-local predecessor transducer from the degree calculus. -/
@[expose] noncomputable def unaryPred :
    NativeCompiler (fun input : ℕ => input - 1) encUnary encUnary :=
  ofTransducer (headT (some false)) Universal.eBit fun input => by
    rw [headT_some_false_run]
    cases input <;> simp [encUnary_apply, List.replicate_succ]

/-- Total first-frame decoder, including the existing incomplete-frame behavior. -/
@[expose] noncomputable def unframeDecoder : NativeCompiler unframe encBits encBits := by
  letI : Fintype FrameState := Fintype.ofFinite FrameState
  exact ofTransducer (readFrameT true) frameStateEncoding readFrameT_run_true

/-- Remove the frame around a typed encoded value. This retains the same parser as
`unframeDecoder`, with no semantic decoding step. -/
@[expose] noncomputable def unframeValue {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler id (encFramed enc) enc := by
  letI : Fintype FrameState := Fintype.ofFinite FrameState
  exact ofTransducer (readFrameT true) frameStateEncoding fun input => by
    change (readFrameT true).run .marker (encFramed enc input) = enc input
    rw [readFrameT_run_true]
    exact unframe_frame (enc input)

/-- Total decoder for the word following the first frame. -/
@[expose] noncomputable def dropFrameDecoder : NativeCompiler dropFrame encBits encBits := by
  letI : Fintype FrameState := Fintype.ofFinite FrameState
  exact ofTransducer (readFrameT false) frameStateEncoding readFrameT_run_false

/-- Split a raw word into framed words, closing a final incomplete frame. -/
@[expose] noncomputable def framesDecoder :
    NativeCompiler frames encBits (encList encBits) := by
  letI : Fintype FramesState := Fintype.ofFinite FramesState
  exact ofTransducer framesT framesStateEncoding framesT_run

/-- Decode every framed word to its unary length. A final incomplete frame is closed exactly as
by `frames`; no semantic list-map callback is hidden behind this compiler. -/
@[expose] noncomputable def unaryListDecoder :
    NativeCompiler (fun word => (frames word).map List.length) encBits (encList encUnary) := by
  letI : Fintype FramesState := Fintype.ofFinite FramesState
  exact ofTransducer unaryListT framesStateEncoding fun input => by
    change unaryListT.run .between input = encList encUnary ((frames input).map List.length)
    exact unaryListT_run input

/-- Retain the direct encoded-list take/drop kernel through its existing tidy normal form. The
clock and workspace expose both the kernel bound and the exact normal-form overhead. -/
@[expose] noncomputable def takeDropUnary {Alpha : Type*} (keep : Bool)
    (enc : Alpha ↪ List Bool) :
    NativeCompiler
      (fun input : List Alpha × ℕ => if keep then input.1.take input.2 else input.1.drop input.2)
      (encPair (encList enc) encUnary) (encList enc) := by
  let clearCount := (List.finRange 1).length
  let CompilerState :=
    ((Option TakeDropUnary.State ⊕ ClearListState clearCount) ⊕ RewindState)
  letI : Fintype TakeDropUnary.State := Fintype.ofFinite TakeDropUnary.State
  letI : Fintype (ClearListState clearCount) := Fintype.ofFinite (ClearListState clearCount)
  letI : Fintype CompilerState := inferInstance
  exact {
    tapeCount := 1 + 1
    State := CompilerState
    machine := tidy false true (TakeDropUnary.toTM keep)
    stateEncoding := sumStateEncoding
      (sumStateEncoding (optionStateEncoding takeDropUnaryStateEncoding)
        (clearListStateEncoding clearCount))
      rewindStateEncoding
    time := fun input =>
      2 * (3 * (encPair (encList enc) encUnary input).length + 2) +
        3 * (input.2 + 2) + 2 * 1 + 4
    workspace := fun input =>
      2 * (input.2 + 2) + 2 * 1 * (3 * (input.2 + 2) + 2 * 1 + 3)
    computes := fun input => by
      have h := TakeDropUnary.computesInTimeAndSpace_toTM keep
        (encList enc input.1) input.2
      have htidy := h.computesTidily_tidy (m₀ := false) (m₁ := true) (by decide)
      simpa only [encPair_apply, encUnary_apply, TakeDropUnary.stream_encList] using htidy
  }

/-- Retained linear-time prefix of an encoded list at a unary count. -/
@[expose] noncomputable def takeUnary {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun input : List Alpha × ℕ => input.1.take input.2)
      (encPair (encList enc) encUnary) (encList enc) :=
  takeDropUnary true enc

/-- Retained linear-time suffix of an encoded list at a unary count. -/
@[expose] noncomputable def dropUnary {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun input : List Alpha × ℕ => input.1.drop input.2)
      (encPair (encList enc) encUnary) (encList enc) :=
  takeDropUnary false enc

/-- Unary take/drop retains the direct kernel inside the direct tidy normal form. -/
theorem machine_takeDropUnary {Alpha : Type*} (keep : Bool) (enc : Alpha ↪ List Bool) :
    (takeDropUnary keep enc).machine = tidy false true (TakeDropUnary.toTM keep) :=
  rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
