/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-! Checked clients for the named native streaming codecs. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerCodec

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.DecoderWords
  Turing.MultiTapeTM.Internal.NativeCompiler Turing.MultiTapeTM.Universal

/-- Encoding-equality retyping is a zero-runtime view of the same machine. -/
example {Alpha : Type*} (enc : Alpha ↪ List Bool)
    (compiler : NativeCompiler id enc enc) :
    (compiler.ofInputEq id (fun _ => rfl)).machine = compiler.machine ∧
      (compiler.ofOutputEq (g := id) (fun _ => rfl)).machine = compiler.machine :=
  ⟨rfl, rfl⟩

/-- Pair projections retain the direct frame parsers and expose their exact linear clocks. -/
example :
    (first encUnary encBool).time (3, true) =
      4 * (encPair encUnary encBool (3, true)).length + 8 ∧
    (second encUnary encBool).time (3, true) =
      4 * (encPair encUnary encBool (3, true)).length + 8 :=
  ⟨rfl, rfl⟩

/-- Standard option and sum constructors are direct one-bit prefix transducers. -/
example :
    (optionSome encUnary).outputBits 3 = 4 ∧
      (sumInl encUnary encBool).outputBits 3 = 4 ∧
      (sumInr encUnary encBool).outputBits true = 2 ∧
      (framedValue encUnary).outputBits 3 = 7 := by
  decide

/-- Typed unframing removes only the concrete frame around the encoded value. -/
example : (unframeValue encUnary).outputBits 3 = 3 := by
  decide

/-- Total decoder behavior is explicit on malformed and empty raw words. -/
example :
    List.length [false, true] = 2 ∧
      ([].headD false : Bool) = false ∧
      unframe [true] = [] ∧ dropFrame [true] = [] := by
  decide

/-- The emitted result of every named codec is charged by its exact output coordinate and time. -/
example (input : List Bool) :
    unaryDecoder.outputBits input = input.length ∧
      unaryDecoder.outputBits input ≤ unaryDecoder.time input := by
  constructor
  · simp [NativeCompiler.outputBits, encUnary_apply]
  · exact (unaryDecoder.computes input).length_output_le

/-- Empty-word and unary boundary primitives retain the public finite transducers. -/
example :
    isEmpty.outputBits [] = 1 ∧ isEmpty.outputBits [true] = 1 ∧
      unaryIsZero.outputBits 0 = 1 ∧ unaryPred.outputBits 0 = 0 ∧
      unaryPred.outputBits 3 = 2 := by
  decide

/-- Branch tests use the empty/nonempty encoding, not the one-bit Boolean encoding. -/
example :
    boolToTest.outputBits false = 0 ∧ boolToTest.outputBits true = 1 ∧
      (optionIsSomeBool encUnary).outputBits none = 1 ∧
      (optionIsSomeBool encUnary).outputBits (some 3) = 1 ∧
      (optionIsSomeTest encUnary).outputBits none = 0 ∧
      (optionIsSomeTest encUnary).outputBits (some 3) = 1 ∧
      unaryIsZeroTest.outputBits 0 = 1 ∧ unaryIsZeroTest.outputBits 1 = 0 := by
  decide

/-- The state range is computed from the actual retained encoding. -/
example (state : unaryDecoder.State) :
    unaryDecoder.stateEncoding state < unaryDecoder.stateBound :=
  unaryDecoder.stateEncoding_lt_stateBound state

/-- The retained state is the full transducer-machine state followed by the rewind state. -/
example : unaryDecoder.State = ((Unit × Option Bool × Bool) ⊕ RewindState) :=
  rfl

/-- The exact state encoding covers the full transducer-machine state rather than only its source
state. -/
example : unaryDecoder.stateEncoding =
    sumStateEncoding (transducerMachineStateEncoding unitStateEncoding) rewindStateEncoding :=
  rfl

/-- Correcting the state encoding leaves the direct transducer-plus-rewind action schedule
unchanged. -/
example : unaryDecoder.machine = unaryLengthT.toTM.seq (rewindInput Bool) :=
  rfl

/-- The descriptor and its static charge are derived from the corrected machine state encoding. -/
example : unaryDecoder.description =
    @desc unaryDecoder.tapeCount Bool unaryDecoder.State unaryDecoder.stateFintype inferInstance
      unaryDecoder.stateEncoding eBit unaryDecoder.machine :=
  unaryDecoder.description_eq_desc

example : unaryDecoder.staticBits =
    descLen (@desc unaryDecoder.tapeCount Bool unaryDecoder.State unaryDecoder.stateFintype
      inferInstance unaryDecoder.stateEncoding eBit unaryDecoder.machine) := by
  rw [unaryDecoder.staticBits_eq_descLen, unaryDecoder.description_eq_desc]

/-- Correcting the retained control state does not weaken the exact time or workspace formulas. -/
example (input : List Bool) :
    unaryDecoder.time input = 4 * input.length + 8 ∧ unaryDecoder.workspace input = 0 :=
  ⟨rfl, rfl⟩

/-- The retained unary-list decoder preserves the total incomplete-frame convention: a dangling
final marker is discarded rather than becoming an additional empty frame. -/
example :
    (frames [true, false, true]).map List.length = [1] ∧
      unaryListDecoder.outputBits [true, false, true] = 3 := by
  have hframes : frames [true, false, true] = [[false]] := by
    rw [frames_of_ne_nil (by decide)]
    simp only [unframe, dropFrame, frames_nil]
  constructor
  · rw [hframes]
    rfl
  · simp only [NativeCompiler.outputBits, hframes, List.map_cons, List.map_nil, encList_cons,
      encList_nil, encUnary_apply, length_frame, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]

/-- Bounded reply decoding can use the retained direct list-prefix kernel. -/
example :
    (takeUnary encUnary).time ([2, 1, 3], 2) =
      2 * (3 * (encPair (encList encUnary) encUnary ([2, 1, 3], 2)).length + 2) +
        3 * (2 + 2) + 2 * 1 + 4 ∧
      (takeUnary encUnary).workspace ([2, 1, 3], 2) =
        2 * (2 + 2) + 2 * 1 * (3 * (2 + 2) + 2 * 1 + 3) :=
  ⟨rfl, rfl⟩

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerCodec
