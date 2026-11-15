/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Sum

/-!
# Named native binary-indexed list access

This module retains a single-pass scan of a standard framed list with a binary countdown. The
scan keeps the remaining binary index and an optional selected value, processes every encoded
occurrence, and returns an explicit default when the index is out of range.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.listGetDNatCompiler`: total binary-indexed lookup.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listGet?NatCompiler`: optional binary-indexed lookup.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listMapCompiler`: retained standard-list mapping.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listReplaceUnaryCompiler`: retained unary-indexed
  replacement with out-of-range lists unchanged.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listConsCompiler`, `.listTailCompiler`: retained
  standard-list constructor and tail.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listAppendCompiler`, `.optionToListCompiler`:
  retained standard-list concatenation and optional singleton conversion.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listZipWithLeftCompiler`: retained left-length zip
  with an explicit default for a short right list.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listGetNatStreamCompiler`: the retained scan before
  input marshalling.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.time_listGetDNatCompiler`: separates marshalling,
  scan, intermediate-copy and composition costs.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listBits_le_time_listGetDNatCompiler`: every framed
  list occurrence is charged by the complete lookup clock.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

universe u v w

variable {Value : Type u}

/-- Retained standard-list tail, dropping exactly the first framed occurrence when present. -/
@[expose] noncomputable def listTailCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler List.tail (encList encValue) (encList encValue) :=
  (dropFrameDecoder.ofInputEq (fun list => encList encValue list) fun _ => rfl).ofOutputEq
    fun list => by cases list <;> simp [dropFrame, encList_cons, dropFrame_frame_append]

/-- Retained standard-list constructor, framing the new head and appending the encoded tail. -/
@[expose] noncomputable def listConsCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : Value × List Value => input.1 :: input.2)
      (encPair encValue (encList encValue)) (encList encValue) := by
  let head := first encValue (encList encValue)
  let tail := second encValue (encList encValue)
  let framedHead := (encodeFrame encValue).comp head
  let rawTail : NativeCompiler (fun input : Value × List Value => encList encValue input.2)
      (encPair encValue (encList encValue)) encBits :=
    tail.ofOutputEq (g := fun input => encList encValue input.2) fun _ => by
      simp only [encBits_apply]
  exact (append framedHead rawTail).ofOutputEq fun input => by
    simp only [encList_cons, encBits_apply]

/-- Retained standard-list append. Both encoded lists are emitted once, without another framing
layer around either list. -/
@[expose] noncomputable def listAppendCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : List Value × List Value => input.1 ++ input.2)
      (encPair (encList encValue) (encList encValue)) (encList encValue) := by
  let left : NativeCompiler (fun input : List Value × List Value => encList encValue input.1)
      (encPair (encList encValue) (encList encValue)) encBits :=
    (first (encList encValue) (encList encValue)).ofOutputEq
      (g := fun input => encList encValue input.1) fun _ => by simp only [encBits_apply]
  let right : NativeCompiler (fun input : List Value × List Value => encList encValue input.2)
      (encPair (encList encValue) (encList encValue)) encBits :=
    (second (encList encValue) (encList encValue)).ofOutputEq
      (g := fun input => encList encValue input.2) fun _ => by simp only [encBits_apply]
  exact (append left right).ofOutputEq fun input => by
    simp only [encList_append, encBits_apply]

/-- Retained conversion of an option to its zero-or-one-element standard list. -/
@[expose] noncomputable def optionToListCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler Option.toList (encOption encValue) (encList encValue) := by
  let present := optionIsSomeTest encValue
  let singleton := (encodeFrame encBits).comp (optionPayload encValue)
  let empty := const (encOption encValue) encBits []
  exact (ite present singleton empty).ofOutputEq fun value => by
    cases value <;> simp [encList_cons, encBits_apply]

/-- State for binary-indexed access: the remaining index and an optional prior selection. -/
abbrev ListGetNatState (Value : Type u) := ℕ × Option Value

/-- Advance the binary countdown, retaining the first value selected at remaining index zero. -/
@[expose] def listGetNatNext : ListGetNatState Value × Value → ListGetNatState Value
  | ((remaining, selected), value) =>
      if selected.isSome then (remaining, selected)
      else if remaining = 0 then (0, some value) else (remaining - 1, none)

/-- Return a selected value, or the explicit default if the index was out of range. -/
@[expose] def listGetNatFinish (default : Value) (state : ListGetNatState Value) : Value :=
  state.2.getD default

private theorem foldl_listGetNatNext_found (remaining : ℕ) (value : Value)
    (list : List Value) :
    list.foldl (fun state element => listGetNatNext (state, element))
      (remaining, some value) = (remaining, some value) := by
  induction list with
  | nil => rfl
  | cons element list ih =>
      rw [List.foldl_cons]
      rw [show listGetNatNext ((remaining, some value), element) =
        (remaining, some value) by simp [listGetNatNext]]
      exact ih

private theorem listGetNatFinish_foldl (default : Value) (index : ℕ) : ∀ list : List Value,
    listGetNatFinish default
      (list.foldl (fun state element => listGetNatNext (state, element)) (index, none)) =
      list.getD index default
  | [] => by simp [listGetNatFinish]
  | element :: list => by
      cases index with
      | zero =>
          rw [List.foldl_cons]
          rw [show listGetNatNext ((0, none), element) = (0, some element) by
            simp [listGetNatNext]]
          rw [foldl_listGetNatNext_found]
          rfl
      | succ index =>
          simpa [listGetNatNext, listGetNatFinish] using
            listGetNatFinish_foldl default index list

/-- The completed countdown scan implements total list access. -/
theorem listGetNatFinish_streamState (default : Value) (list : List Value) (index : ℕ) :
    listGetNatFinish default
        (streamState (index, none) listGetNatNext list list.length) =
      list.getD index default := by
  simpa [streamState] using listGetNatFinish_foldl default index list

private theorem listGetNatOption_foldl (index : ℕ) : ∀ list : List Value,
    (list.foldl (fun state element => listGetNatNext (state, element)) (index, none)).2 =
      list[index]?
  | [] => rfl
  | element :: list => by
      cases index with
      | zero =>
          rw [List.foldl_cons]
          rw [show listGetNatNext ((0, none), element) = (0, some element) by
            simp [listGetNatNext]]
          rw [foldl_listGetNatNext_found]
          rfl
      | succ index => simpa [listGetNatNext] using listGetNatOption_foldl index list

/-- The completed countdown scan also implements optional list access without a sentinel. -/
theorem listGetNatOption_streamState (list : List Value) (index : ℕ) :
    (streamState (index, none) listGetNatNext list list.length).2 = list[index]? := by
  simpa [streamState] using listGetNatOption_foldl index list

/-- Retained per-occurrence state callback for binary-indexed list access. -/
@[expose] noncomputable def listGetNatNextCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler listGetNatNext
      (encPair (encPair encNat (encOption encValue)) encValue)
      (encPair encNat (encOption encValue)) := by
  let encState := encPair encNat (encOption encValue)
  let encInput := encPair encState encValue
  let state := first encState encValue
  let element := second encState encValue
  let remaining := (first encNat (encOption encValue)).comp state
  let selected := (second encNat (encOption encValue)).comp state
  let alreadySelected := (optionIsSomeTest encValue).comp selected
  let atIndex := natIsZeroTest.comp remaining
  let select := (const encInput encNat 0).pair ((optionSome encValue).comp element)
  let decrement := (natPred.comp remaining).pair
    (const encInput (encOption encValue) none)
  refine (ite alreadySelected state (ite atIndex select decrement)).ofOutputEq ?_
  rintro ⟨⟨remaining, selected⟩, element⟩
  cases selected <;> cases remaining <;> simp [listGetNatNext, encState]

/-- A list scan emits no per-occurrence output; selection remains in the stream state. -/
@[expose] noncomputable def listGetNatEmitCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (Function.const (ListGetNatState Value × Value) ())
      (encPair (encPair encNat (encOption encValue)) encValue) encUnit :=
  const (encPair (encPair encNat (encOption encValue)) encValue) encUnit ()

/-- Retained final selection/default callback. -/
@[expose] noncomputable def listGetNatFinishCompiler (default : Value)
    (encValue : Value ↪ List Bool) :
    NativeCompiler (listGetNatFinish default) (encPair encNat (encOption encValue)) encValue :=
  (optionGetD default encValue).comp (second encNat (encOption encValue))

/-- Retained final optional selection callback, with `none` marking an out-of-range index. -/
@[expose] noncomputable def listGetNatOptionFinishCompiler
    (encValue : Value ↪ List Bool) :
    NativeCompiler Prod.snd (encPair encNat (encOption encValue)) (encOption encValue) :=
  second encNat (encOption encValue)

/-- Explicit peak lifted-callback workspace over the actual list scan. -/
@[expose] noncomputable def listGetNatSMax (default : Value)
    (encValue : Value ↪ List Bool) (input : ListGetNatState Value × List Value) : ℕ :=
  let nextCompiler := listGetNatNextCompiler encValue
  let emitCompiler := listGetNatEmitCompiler encValue
  let finishCompiler := listGetNatFinishCompiler default encValue
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 listGetNatNext input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak lifted-callback workspace for optional binary-indexed access. -/
@[expose] noncomputable def listGetNatOptionSMax
    (encValue : Value ↪ List Bool) (input : ListGetNatState Value × List Value) : ℕ :=
  let nextCompiler := listGetNatNextCompiler encValue
  let emitCompiler := listGetNatEmitCompiler encValue
  let finishCompiler := listGetNatOptionFinishCompiler encValue
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 listGetNatNext input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak encoded state/element length over the actual list scan. -/
@[expose] def listGetNatLMax (encValue : Value ↪ List Bool)
    (input : ListGetNatState Value × List Value) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        ((encPair encNat (encOption encValue))
          (streamState input.1 listGetNatNext input.2 j)).length
      else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encValue input.2[j]).length else 0)

/-- Retained binary-countdown scan before list/index input marshalling. -/
@[expose] noncomputable def listGetNatStreamCompiler (default : Value)
    (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun input : ListGetNatState Value × List Value =>
        listGetNatFinish default
          (streamState input.1 listGetNatNext input.2 input.2.length))
      (encPair (encPair encNat (encOption encValue)) (encList encValue)) encValue := by
  let nextCompiler := listGetNatNextCompiler encValue
  let emitCompiler := listGetNatEmitCompiler encValue
  let finishCompiler := listGetNatFinishCompiler default encValue
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := listGetNatSMax default encValue) (lMax := listGetNatLMax encValue)
  · intro input
    simp only [encUnit_apply, streamEmit_const_nil, List.nil_append]
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair := (streamState input.1 listGetNatNext input.2 j, input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [listGetNatSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        ((encPair encNat (encOption encValue))
          (streamState input.1 listGetNatNext input.2 j)).length else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    simpa only [hj, dite_true] using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encValue input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    simpa only [hj, dite_true] using hsup

/-- Retained binary-countdown scan returning `none` exactly for an out-of-range index. -/
@[expose] noncomputable def listGetNatOptionStreamCompiler
    (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun input : ListGetNatState Value × List Value =>
        (streamState input.1 listGetNatNext input.2 input.2.length).2)
      (encPair (encPair encNat (encOption encValue)) (encList encValue))
      (encOption encValue) := by
  let nextCompiler := listGetNatNextCompiler encValue
  let emitCompiler := listGetNatEmitCompiler encValue
  let finishCompiler := listGetNatOptionFinishCompiler encValue
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := listGetNatOptionSMax encValue) (lMax := listGetNatLMax encValue)
  · intro input
    simp only [encUnit_apply, streamEmit_const_nil, List.nil_append]
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair := (streamState input.1 listGetNatNext input.2 j, input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [listGetNatOptionSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        ((encPair encNat (encOption encValue))
          (streamState input.1 listGetNatNext input.2 j)).length else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    simpa only [hj, dite_true] using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encValue input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    simpa only [hj, dite_true] using hsup

/-- Retained marshalling from `(list, binary index)` to countdown stream state. -/
@[expose] noncomputable def listGetNatMarshalCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : List Value × ℕ => ((input.2, none), input.1))
      (encPair (encList encValue) encNat)
      (encPair (encPair encNat (encOption encValue)) (encList encValue)) := by
  let encInput := encPair (encList encValue) encNat
  let list := first (encList encValue) encNat
  let index := second (encList encValue) encNat
  exact (index.pair (const encInput (encOption encValue) none)).pair list

/-- Optional binary-indexed standard-list access, including marshalling and every scanned entry. -/
@[expose] noncomputable def listGet?NatCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : List Value × ℕ => input.1[input.2]?)
      (encPair (encList encValue) encNat) (encOption encValue) :=
  ((listGetNatOptionStreamCompiler encValue).comp
    (listGetNatMarshalCompiler encValue)).ofOutputEq fun input =>
      congrArg (encOption encValue) (listGetNatOption_streamState input.1 input.2).symm

/-- Total binary-indexed standard-list access, including marshalling and every scanned entry. -/
@[expose] noncomputable def listGetDNatCompiler (default : Value)
    (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : List Value × ℕ => input.1.getD input.2 default)
      (encPair (encList encValue) encNat) encValue :=
  ((listGetNatStreamCompiler default encValue).comp
    (listGetNatMarshalCompiler encValue)).ofOutputEq fun input =>
      congrArg encValue (listGetNatFinish_streamState default input.1 input.2).symm

/-- The complete lookup clock separates marshalling, scan, intermediate-copy and composition
costs. -/
theorem time_listGetDNatCompiler (default : Value) (encValue : Value ↪ List Bool)
    (input : List Value × ℕ) :
    (listGetDNatCompiler default encValue).time input =
      (listGetNatMarshalCompiler encValue).time input +
        (listGetNatStreamCompiler default encValue).time ((input.2, none), input.1) +
        4 * ((encPair (encPair encNat (encOption encValue)) (encList encValue))
          ((input.2, none), input.1)).length + 9 :=
  rfl

/-- Every encoded list occurrence is charged by the binary-indexed scan. -/
theorem listBits_le_time_listGetNatStreamCompiler (default : Value)
    (encValue : Value ↪ List Bool) (input : ListGetNatState Value × List Value) :
    (encList encValue input.2).length ≤
      (listGetNatStreamCompiler default encValue).time input := by
  change (encList encValue input.2).length ≤
    streamFoldPairTime (listGetNatNextCompiler encValue) (listGetNatEmitCompiler encValue)
      (listGetNatFinishCompiler default encValue) input
  simp only [streamFoldPairTime]
  omega

/-- Every encoded list occurrence is also charged by the complete marshalled lookup. -/
theorem listBits_le_time_listGetDNatCompiler (default : Value)
    (encValue : Value ↪ List Bool) (input : List Value × ℕ) :
    (encList encValue input.1).length ≤ (listGetDNatCompiler default encValue).time input := by
  rw [time_listGetDNatCompiler]
  have h : (encList encValue input.1).length ≤
      (listGetNatStreamCompiler default encValue).time ((input.2, none), input.1) := by
    simpa only using listBits_le_time_listGetNatStreamCompiler default encValue
      ((input.2, none), input.1)
  omega

/-! ### Standard-list map -/

variable {Input : Type u} {Output : Type v} {mapValue : Input → Output}

/-- Map keeps no semantic state between framed list elements. -/
@[expose] noncomputable def listMapNextCompiler (encInput : Input ↪ List Bool) :
    NativeCompiler Prod.fst (encPair encUnit encInput) encUnit :=
  first encUnit encInput

/-- Apply and frame the named element compiler for one list-map occurrence. -/
@[expose] noncomputable def listMapEmitCompiler (encInput : Input ↪ List Bool)
    (encOutput : Output ↪ List Bool)
    (compiler : NativeCompiler mapValue encInput encOutput) :
    NativeCompiler (fun input : Unit × Input => mapValue input.2)
      (encPair encUnit encInput) (encFramed encOutput) :=
  (framedValue encOutput).comp (compiler.comp (second encUnit encInput))

/-- List-map finalization emits no additional bits. -/
@[expose] noncomputable def listMapFinishCompiler :
    NativeCompiler (Function.const Unit ([] : List Bool)) encUnit encBits :=
  const encUnit encBits []

/-- Explicit peak lifted-callback workspace over the actual list-map rounds. -/
@[expose] noncomputable def listMapSMax (encInput : Input ↪ List Bool)
    (encOutput : Output ↪ List Bool)
    (compiler : NativeCompiler mapValue encInput encOutput)
    (input : Unit × List Input) : ℕ :=
  let nextCompiler := listMapNextCompiler encInput
  let emitCompiler := listMapEmitCompiler encInput encOutput compiler
  let finishCompiler := listMapFinishCompiler
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 Prod.fst input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak encoded state/element length over the actual list-map rounds. -/
@[expose] def listMapLMax (encInput : Input ↪ List Bool) (input : Unit × List Input) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if _hj : j ≤ input.2.length then (encUnit ()).length else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encInput input.2[j]).length else 0)

/-- Retained list-map scan before input marshalling. -/
@[expose] noncomputable def listMapStreamCompiler (encInput : Input ↪ List Bool)
    (encOutput : Output ↪ List Bool)
    (compiler : NativeCompiler mapValue encInput encOutput) :
    NativeCompiler (fun input : Unit × List Input => input.2.map mapValue)
      (encPair encUnit (encList encInput)) (encList encOutput) := by
  let nextCompiler := listMapNextCompiler encInput
  let emitCompiler := listMapEmitCompiler encInput encOutput compiler
  let finishCompiler := listMapFinishCompiler
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := listMapSMax encInput encOutput compiler) (lMax := listMapLMax encInput)
  · intro input
    induction input.2 with
    | nil => rfl
    | cons element list ih =>
        simpa [streamEmit, encFramed_apply, encList_cons] using ih
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair := (streamState input.1 Prod.fst input.2 j, input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [listMapSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if _hj : j ≤ input.2.length then (encUnit ()).length else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    simpa only [hj, dite_true] using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encInput input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    simpa only [hj, dite_true] using hsup

/-- Retained marshalling from a standard list to the unit-state stream layout. -/
@[expose] noncomputable def listMapMarshalCompiler (encInput : Input ↪ List Bool) :
    NativeCompiler (fun input : List Input => ((), input)) (encList encInput)
      (encPair encUnit (encList encInput)) :=
  (const (encList encInput) encUnit ()).pair (identity (encList encInput))

/-- Retained standard-list map, including marshalling and every element callback. -/
@[expose] noncomputable def listMapCompiler (encInput : Input ↪ List Bool)
    (encOutput : Output ↪ List Bool)
    (compiler : NativeCompiler mapValue encInput encOutput) :
    NativeCompiler (List.map mapValue) (encList encInput) (encList encOutput) :=
  ((listMapStreamCompiler encInput encOutput compiler).comp
    (listMapMarshalCompiler encInput)).ofOutputEq fun _ => rfl

/-- Every encoded input occurrence is charged by the retained list map. -/
theorem listBits_le_time_listMapStreamCompiler (encInput : Input ↪ List Bool)
    (encOutput : Output ↪ List Bool)
    (compiler : NativeCompiler mapValue encInput encOutput) (input : Unit × List Input) :
    (encList encInput input.2).length ≤
      (listMapStreamCompiler encInput encOutput compiler).time input := by
  change (encList encInput input.2).length ≤
    streamFoldPairTime (listMapNextCompiler encInput)
      (listMapEmitCompiler encInput encOutput compiler) listMapFinishCompiler input
  simp only [streamFoldPairTime]
  omega

/-! ### Left-length zip -/

variable {Left : Type u} {Right : Type v} {Zipped : Type w}
  {zipValue : Left × Right → Zipped}

/-- Zip to the left list's length, using `default` after the right list is exhausted. -/
@[expose] def listZipWithLeft (default : Right) (f : Left × Right → Zipped) :
    List Left → List Right → List Zipped
  | [], _ => []
  | left :: lefts, rights =>
      f (left, rights.headD default) :: listZipWithLeft default f lefts rights.tail

/-- The right-list stream state advances by one framed occurrence per left element. -/
@[expose] noncomputable def listZipWithLeftNextCompiler
    (encLeft : Left ↪ List Bool) (encRight : Right ↪ List Bool) :
    NativeCompiler (fun input : List Right × Left => input.1.tail)
      (encPair (encList encRight) encLeft) (encList encRight) :=
  (listTailCompiler encRight).comp (first (encList encRight) encLeft)

/-- Apply and frame the named zip callback for one left-list occurrence. -/
@[expose] noncomputable def listZipWithLeftEmitCompiler (default : Right)
    (encLeft : Left ↪ List Bool) (encRight : Right ↪ List Bool)
    (encZipped : Zipped ↪ List Bool)
    (compiler : NativeCompiler zipValue (encPair encLeft encRight) encZipped) :
    NativeCompiler
      (fun input : List Right × Left => zipValue (input.2, input.1.headD default))
      (encPair (encList encRight) encLeft) (encFramed encZipped) := by
  let rights := first (encList encRight) encLeft
  let left := second (encList encRight) encLeft
  let right := (listHeadD default encRight).comp rights
  exact (framedValue encZipped).comp (compiler.comp (left.pair right))

/-- Left-length zip finalization emits no additional bits. -/
@[expose] noncomputable def listZipWithLeftFinishCompiler (encRight : Right ↪ List Bool) :
    NativeCompiler (Function.const (List Right) ([] : List Bool))
      (encList encRight) encBits :=
  const (encList encRight) encBits []

/-- Explicit peak callback workspace over the actual left-length zip rounds. -/
@[expose] noncomputable def listZipWithLeftSMax (default : Right)
    (encLeft : Left ↪ List Bool) (encRight : Right ↪ List Bool)
    (encZipped : Zipped ↪ List Bool)
    (compiler : NativeCompiler zipValue (encPair encLeft encRight) encZipped)
    (input : List Right × List Left) : ℕ :=
  let nextCompiler := listZipWithLeftNextCompiler encLeft encRight
  let emitCompiler := listZipWithLeftEmitCompiler default encLeft encRight encZipped compiler
  let finishCompiler := listZipWithLeftFinishCompiler encRight
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 (fun pair => pair.1.tail) input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak state/element length over the actual left-length zip rounds. -/
@[expose] def listZipWithLeftLMax (encLeft : Left ↪ List Bool)
    (encRight : Right ↪ List Bool) (input : List Right × List Left) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        (encList encRight
          (streamState input.1 (fun pair : List Right × Left => pair.1.tail) input.2 j)).length
      else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encLeft input.2[j]).length else 0)

/-- Retained left-length zip scan before input reordering. -/
@[expose] noncomputable def listZipWithLeftStreamCompiler (default : Right)
    (encLeft : Left ↪ List Bool) (encRight : Right ↪ List Bool)
    (encZipped : Zipped ↪ List Bool)
    (compiler : NativeCompiler zipValue (encPair encLeft encRight) encZipped) :
    NativeCompiler (fun input : List Right × List Left =>
      listZipWithLeft default zipValue input.2 input.1)
      (encPair (encList encRight) (encList encLeft)) (encList encZipped) := by
  let nextCompiler := listZipWithLeftNextCompiler encLeft encRight
  let emitCompiler := listZipWithLeftEmitCompiler default encLeft encRight encZipped compiler
  let finishCompiler := listZipWithLeftFinishCompiler encRight
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := listZipWithLeftSMax default encLeft encRight encZipped compiler)
    (lMax := listZipWithLeftLMax encLeft encRight)
  · rintro ⟨rights, lefts⟩
    induction lefts generalizing rights with
    | nil => rfl
    | cons left lefts ih =>
        cases rights <;>
          simp [streamEmit, listZipWithLeft, encFramed_apply, encList_cons, ih]
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair :=
          (streamState input.1 (fun pair : List Right × Left => pair.1.tail) input.2 j,
            input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [listZipWithLeftSMax, nextCompiler, emitCompiler, finishCompiler, hj,
      dite_true] using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        (encList encRight
          (streamState input.1 (fun pair : List Right × Left => pair.1.tail) input.2 j)).length
        else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    simpa only [hj, dite_true] using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encLeft input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    simpa only [hj, dite_true] using hsup

/-- Retained left-length zip, including the charged input reordering pass. -/
@[expose] noncomputable def listZipWithLeftCompiler (default : Right)
    (encLeft : Left ↪ List Bool) (encRight : Right ↪ List Bool)
    (encZipped : Zipped ↪ List Bool)
    (compiler : NativeCompiler zipValue (encPair encLeft encRight) encZipped) :
    NativeCompiler (fun input : List Left × List Right =>
      listZipWithLeft default zipValue input.1 input.2)
      (encPair (encList encLeft) (encList encRight)) (encList encZipped) := by
  let lefts := first (encList encLeft) (encList encRight)
  let rights := second (encList encLeft) (encList encRight)
  exact ((listZipWithLeftStreamCompiler default encLeft encRight encZipped compiler).comp
    (rights.pair lefts)).ofOutputEq fun _ => rfl

/-! ### Unary-indexed replacement -/

/-- Control state for unary-indexed list replacement. -/
abbrev ListReplaceState (Value : Type u) := ℕ × (Bool × Value)

/-- Update the unary countdown after emitting one list element. -/
@[expose] def listReplaceNext : ListReplaceState Value × Value → ListReplaceState Value
  | ((remaining, done, replacement), _value) =>
      if done then (remaining, done, replacement)
      else if remaining = 0 then (0, true, replacement)
      else (remaining - 1, false, replacement)

/-- Emit the replacement at the selected occurrence and the original element elsewhere. -/
@[expose] def listReplaceEmit : ListReplaceState Value × Value → Value
  | ((remaining, done, replacement), value) =>
      if done then value else if remaining = 0 then replacement else value

/-- Once replacement is complete, the stream emits each remaining element unchanged. -/
theorem streamEmit_listReplace_done (encValue : Value ↪ List Bool)
    (remaining : ℕ) (replacement : Value) (list : List Value) :
    streamEmit listReplaceNext (fun input => frame (encValue (listReplaceEmit input)))
      (remaining, true, replacement) list = encList encValue list := by
  induction list with
  | nil => rfl
  | cons element list ih =>
      have hemit : listReplaceEmit ((remaining, true, replacement), element) = element := by
        simp [listReplaceEmit]
      have hnext : listReplaceNext ((remaining, true, replacement), element) =
          (remaining, true, replacement) := by
        simp [listReplaceNext]
      rw [streamEmit, hemit, hnext, ih, encList_cons]

/-- The replacement stream agrees with `List.modify`; an out-of-range index changes nothing. -/
theorem streamEmit_listReplace (encValue : Value ↪ List Bool) (replacement : Value) :
    ∀ (index : ℕ) (list : List Value),
      streamEmit listReplaceNext (fun input => frame (encValue (listReplaceEmit input)))
          (index, false, replacement) list =
        encList encValue (list.modify index fun _ => replacement) := by
  intro index list
  induction list generalizing index with
  | nil => simp only [streamEmit, List.modify_nil, encList_nil]
  | cons element list ih =>
      cases index with
      | zero =>
          have hemit : listReplaceEmit ((0, false, replacement), element) = replacement := by
            simp [listReplaceEmit]
          have hnext : listReplaceNext ((0, false, replacement), element) =
              (0, true, replacement) := by
            simp [listReplaceNext]
          have hmodify : (element :: list).modify 0 (fun _ => replacement) =
              replacement :: list := rfl
          rw [streamEmit, hemit, hnext,
            streamEmit_listReplace_done encValue 0 replacement list, hmodify, encList_cons]
      | succ index =>
          have hemit : listReplaceEmit ((index + 1, false, replacement), element) = element := by
            simp [listReplaceEmit]
          have hnext : listReplaceNext ((index + 1, false, replacement), element) =
              (index, false, replacement) := by
            simp [listReplaceNext]
          have hmodify : (element :: list).modify (index + 1) (fun _ => replacement) =
              element :: list.modify index (fun _ => replacement) := rfl
          rw [streamEmit, hemit, hnext, ih index, hmodify, encList_cons]

/-- Retained per-occurrence state update for unary-indexed replacement. -/
@[expose] noncomputable def listReplaceNextCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler listReplaceNext
      (encPair (encPair encUnary (encPair encBool encValue)) encValue)
      (encPair encUnary (encPair encBool encValue)) := by
  let encState := encPair encUnary (encPair encBool encValue)
  let encInput := encPair encState encValue
  let state := first encState encValue
  let remaining := (first encUnary (encPair encBool encValue)).comp state
  let tail := (second encUnary (encPair encBool encValue)).comp state
  let done := (first encBool encValue).comp tail
  let replacement := (second encBool encValue).comp tail
  let doneTest := boolToTest.comp done
  let atIndex := unaryIsZeroTest.comp remaining
  let completed := (const encInput encUnary 0).pair
    ((const encInput encBool true).pair replacement)
  let countdown := (unaryPred.comp remaining).pair
    ((const encInput encBool false).pair replacement)
  refine (ite doneTest state (ite atIndex completed countdown)).ofOutputEq ?_
  rintro ⟨⟨remaining, done, replacement⟩, element⟩
  cases done <;> cases remaining <;> simp [listReplaceNext, encState]

/-- Retained per-occurrence emitter for unary-indexed replacement. -/
@[expose] noncomputable def listReplaceEmitCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler listReplaceEmit
      (encPair (encPair encUnary (encPair encBool encValue)) encValue) encValue := by
  let encState := encPair encUnary (encPair encBool encValue)
  let state := first encState encValue
  let element := second encState encValue
  let remaining := (first encUnary (encPair encBool encValue)).comp state
  let tail := (second encUnary (encPair encBool encValue)).comp state
  let done := (first encBool encValue).comp tail
  let replacement := (second encBool encValue).comp tail
  let doneTest := boolToTest.comp done
  let atIndex := unaryIsZeroTest.comp remaining
  refine (ite doneTest element (ite atIndex replacement element)).ofOutputEq ?_
  rintro ⟨⟨remaining, done, replacement⟩, element⟩
  cases done <;> cases remaining <;> simp [listReplaceEmit]

/-- Replacement finalization emits no extra bits. -/
@[expose] noncomputable def listReplaceFinishCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (Function.const (ListReplaceState Value) ([] : List Bool))
      (encPair encUnary (encPair encBool encValue)) encBits :=
  const (encPair encUnary (encPair encBool encValue)) encBits []

/-- Explicit peak lifted-callback workspace over the actual replacement scan. -/
@[expose] noncomputable def listReplaceSMax (encValue : Value ↪ List Bool)
    (input : ListReplaceState Value × List Value) : ℕ :=
  let nextCompiler := listReplaceNextCompiler encValue
  let emitCompiler := (framedValue encValue).comp (listReplaceEmitCompiler encValue)
  let finishCompiler := listReplaceFinishCompiler encValue
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 listReplaceNext input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak encoded state/element length over the actual replacement scan. -/
@[expose] def listReplaceLMax (encValue : Value ↪ List Bool)
    (input : ListReplaceState Value × List Value) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        ((encPair encUnary (encPair encBool encValue))
          (streamState input.1 listReplaceNext input.2 j)).length else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encValue input.2[j]).length else 0)

/-- Retained unary-indexed replacement scan before input marshalling. -/
@[expose] noncomputable def listReplaceStreamCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun ((index, done, replacement), list) =>
        if done then list else list.modify index fun _ => replacement)
      (encPair (encPair encUnary (encPair encBool encValue)) (encList encValue))
      (encList encValue) := by
  let nextCompiler := listReplaceNextCompiler encValue
  let emitCompiler := (framedValue encValue).comp (listReplaceEmitCompiler encValue)
  let finishCompiler := listReplaceFinishCompiler encValue
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := listReplaceSMax encValue) (lMax := listReplaceLMax encValue)
  · rintro ⟨⟨index, done, replacement⟩, list⟩
    cases done with
    | false =>
        change encList encValue (list.modify index fun _ => replacement) =
          streamEmit listReplaceNext (fun input => frame (encValue (listReplaceEmit input)))
            (index, false, replacement) list ++ []
        rw [streamEmit_listReplace, List.append_nil]
    | true =>
        change encList encValue list =
          streamEmit listReplaceNext (fun input => frame (encValue (listReplaceEmit input)))
            (index, true, replacement) list ++ []
        rw [streamEmit_listReplace_done, List.append_nil]
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair := (streamState input.1 listReplaceNext input.2 j, input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [listReplaceSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        ((encPair encUnary (encPair encBool encValue))
          (streamState input.1 listReplaceNext input.2 j)).length else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    simpa only [hj, dite_true] using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encValue input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    simpa only [hj, dite_true] using hsup

/-- Retained marshalling from `(list, unary index, replacement)` to replacement stream state. -/
@[expose] noncomputable def listReplaceMarshalCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun (list, index, replacement) => ((index, false, replacement), list))
      (encPair (encList encValue) (encPair encUnary encValue))
      (encPair (encPair encUnary (encPair encBool encValue)) (encList encValue)) := by
  let encInput := encPair (encList encValue) (encPair encUnary encValue)
  let list := first (encList encValue) (encPair encUnary encValue)
  let tail := second (encList encValue) (encPair encUnary encValue)
  let index := (first encUnary encValue).comp tail
  let replacement := (second encUnary encValue).comp tail
  let state := index.pair ((const encInput encBool false).pair replacement)
  exact state.pair list

/-- Unary-indexed replacement, including marshalling and a full charged list scan. -/
@[expose] noncomputable def listReplaceUnaryCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun (list, index, replacement) => list.modify index fun _ => replacement)
      (encPair (encList encValue) (encPair encUnary encValue)) (encList encValue) :=
  ((listReplaceStreamCompiler encValue).comp
    (listReplaceMarshalCompiler encValue)).ofOutputEq fun _ => rfl

/-- Every input occurrence is charged even when the replacement index is out of range. -/
theorem listBits_le_time_listReplaceStreamCompiler (encValue : Value ↪ List Bool)
    (input : ListReplaceState Value × List Value) :
    (encList encValue input.2).length ≤
      (listReplaceStreamCompiler encValue).time input := by
  change (encList encValue input.2).length ≤
    streamFoldPairTime (listReplaceNextCompiler encValue)
      ((framedValue encValue).comp (listReplaceEmitCompiler encValue))
      (listReplaceFinishCompiler encValue) input
  simp only [streamFoldPairTime]
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
