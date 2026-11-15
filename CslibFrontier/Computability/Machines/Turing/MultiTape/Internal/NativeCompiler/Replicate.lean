/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold

/-!
# Named native unary replication

This module retains unary-driven list replication. A two-pass finite transducer expands every
unary input symbol into the standard three-bit frame of `true`; a concrete stream fold then emits
one framed copy of the supplied value per token. The conversion is charged explicitly because a
unary word and a standard encoded list are not the same representation.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryTrueListCompiler`: convert a unary count to a
  standard encoded list of `true` tokens.
* `Turing.MultiTapeTM.Internal.NativeCompiler.replicateUnaryCompiler`: retain replication of an
  arbitrary encoded value by a unary count.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- First expansion pass: every unary symbol becomes the two-bit seed `[true, false]`. -/
def unaryFrameSeedT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [true, false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma unaryFrameSeedT_q₀ : unaryFrameSeedT.q₀ = () := rfl

private lemma unaryFrameSeedT_step (bit : Bool) :
    unaryFrameSeedT.step () bit = ((), [true, false]) := by
  cases bit <;> rfl

private lemma unaryFrameSeedT_final : unaryFrameSeedT.final () = [] := rfl

/-- Second expansion pass: seed `true` doubles and seed `false` closes the frame. -/
def unaryFrameExpandT : Transducer Bool Unit where
  q₀ := ()
  step _ bit := ((), if bit then [true, true] else [false])
  final _ := []
  length_step_le _ bit := by cases bit <;> simp
  length_final_le _ := by simp

private lemma unaryFrameExpandT_q₀ : unaryFrameExpandT.q₀ = () := rfl

private lemma unaryFrameExpandT_step (bit : Bool) :
    unaryFrameExpandT.step () bit = ((), if bit then [true, true] else [false]) := by
  cases bit <;> rfl

/-- Semantic word produced by the seed expansion. -/
def unaryFrameSeed (count : ℕ) : List Bool :=
  (List.replicate count [true, false]).flatten

/-- Semantic word produced by the frame expansion. -/
def unaryFrameExpand (word : List Bool) : List Bool :=
  word.flatMap fun bit => if bit then [true, true] else [false]

theorem unaryFrameSeedT_run (count : ℕ) :
    unaryFrameSeedT.run unaryFrameSeedT.q₀ (encUnary count) = unaryFrameSeed count := by
  induction count with
  | zero =>
      simp only [unaryFrameSeedT_q₀, encUnary_apply, List.replicate_zero,
        Transducer.run_nil, unaryFrameSeedT_final, unaryFrameSeed, List.flatten_nil]
  | succ count ih =>
      rw [unaryFrameSeedT_q₀, encUnary_apply, List.replicate_succ, Transducer.run_cons,
        unaryFrameSeedT_step]
      rw [show unaryFrameSeedT.run () (List.replicate count true) = unaryFrameSeed count by
        simpa only [unaryFrameSeedT_q₀, encUnary_apply] using ih]
      simp [unaryFrameSeed, List.replicate_succ]

theorem unaryFrameExpandT_run (word : List Bool) :
    unaryFrameExpandT.run unaryFrameExpandT.q₀ word = unaryFrameExpand word := by
  rw [unaryFrameExpandT_q₀]
  induction word with
  | nil => rfl
  | cons bit word ih =>
      rw [Transducer.run_cons, unaryFrameExpandT_step]
      cases bit <;> simp [unaryFrameExpand, ih]

/-- Expanding the seeds yields exactly the standard encoded list of `count` true bits. -/
theorem unaryFrameExpand_seed (count : ℕ) :
    unaryFrameExpand (unaryFrameSeed count) = encList encBool (List.replicate count true) := by
  induction count with
  | zero => simp [unaryFrameExpand, unaryFrameSeed]
  | succ count ih =>
      have hseed :
          unaryFrameSeed (count + 1) = [true, false] ++ unaryFrameSeed count := by
        simp only [unaryFrameSeed, List.replicate_succ, List.flatten_cons]
      have hexpand :
          unaryFrameExpand ([true, false] ++ unaryFrameSeed count) =
            frame (encBool true) ++ unaryFrameExpand (unaryFrameSeed count) := by
        simp [unaryFrameExpand, frame]
      rw [hseed, hexpand, ih, List.replicate_succ, encList_cons]

/-- Retained conversion from unary count to a standard framed list of true tokens. -/
@[expose] noncomputable def unaryTrueListCompiler :
    NativeCompiler (fun count => List.replicate count true) encUnary (encList encBool) := by
  let seedCompiler : NativeCompiler unaryFrameSeed encUnary encBits :=
    ofTransducer unaryFrameSeedT unitStateEncoding fun count => by
      simpa only [encBits_apply] using unaryFrameSeedT_run count
  let expandCompiler : NativeCompiler unaryFrameExpand encBits encBits :=
    ofTransducer unaryFrameExpandT unitStateEncoding fun word => by
      simpa only [encBits_apply] using unaryFrameExpandT_run word
  exact (expandCompiler.comp seedCompiler).ofOutputEq fun count => by
    simpa only [encBits_apply] using (unaryFrameExpand_seed count).symm

universe u

variable {Value : Type u}

/-- Stream next-state callback for replication: retain the value unchanged. -/
@[expose] noncomputable def replicateNextCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler Prod.fst (encPair encValue encBool) encValue :=
  first encValue encBool

/-- Stream emission callback for replication: emit one framed value. -/
@[expose] noncomputable def replicateEmitCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler Prod.fst (encPair encValue encBool) (encFramed encValue) :=
  (framedValue encValue).comp (first encValue encBool)

/-- Replication finalization emits no additional bits. -/
@[expose] noncomputable def replicateFinishCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (Function.const Value ([] : List Bool)) encValue encBits :=
  const encValue encBits []

/-- Explicit peak lifted-callback workspace over the actual replication rounds. -/
@[expose] noncomputable def replicateSMax (encValue : Value ↪ List Bool)
    (input : Value × List Bool) : ℕ :=
  let nextCompiler := replicateNextCompiler encValue
  let emitCompiler := replicateEmitCompiler encValue
  let finishCompiler := replicateFinishCompiler encValue
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 Prod.fst input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak encoded state/token length over the actual replication rounds. -/
@[expose] def replicateLMax (encValue : Value ↪ List Bool) (input : Value × List Bool) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        (encValue (streamState input.1 Prod.fst input.2 j)).length
      else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encBool input.2[j]).length else 0)

/-- The retained replication stream before unary-token marshalling. -/
@[expose] noncomputable def replicateStreamCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : Value × List Bool => List.replicate input.2.length input.1)
      (encPair encValue (encList encBool)) (encList encValue) := by
  let nextCompiler := replicateNextCompiler encValue
  let emitCompiler := replicateEmitCompiler encValue
  let finishCompiler := replicateFinishCompiler encValue
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := replicateSMax encValue) (lMax := replicateLMax encValue)
  · rintro ⟨value, bits⟩
    induction bits generalizing value with
    | nil => rfl
    | cons bit bits ih =>
        simpa [List.replicate_succ, streamEmit, encFramed_apply, encList_cons] using ih value
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
    simpa only [replicateSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        (encValue (streamState input.1 Prod.fst input.2 j)).length else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    have hbound :
        (encValue (streamState input.1 Prod.fst input.2 j)).length ≤
          (Finset.range (input.2.length + 1)).sup fun j =>
            if hj : j ≤ input.2.length then
              (encValue (streamState input.1 Prod.fst input.2 j)).length else 0 := by
      simpa only [hj, dite_true] using hsup
    exact hbound.trans (Nat.le_max_left _ _)
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encBool input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    have hbound :
        (encBool input.2[j]).length ≤
          (Finset.range input.2.length).sup fun j =>
            if hj : j < input.2.length then (encBool input.2[j]).length else 0 := by
      simpa only [hj, dite_true] using hsup
    exact hbound.trans (Nat.le_max_right _ _)

/-- Retained marshalling from a unary count to the stream's standard framed-token list. -/
@[expose] noncomputable def replicateMarshalCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : Value × ℕ => (input.1, List.replicate input.2 true))
      (encPair encValue encUnary) (encPair encValue (encList encBool)) :=
  (first encValue encUnary).pair (unaryTrueListCompiler.comp (second encValue encUnary))

/-- Retained unary-driven replication, including the charged unary-to-framed-list conversion. -/
@[expose] noncomputable def replicateUnaryCompiler (encValue : Value ↪ List Bool) :
    NativeCompiler (fun input : Value × ℕ => List.replicate input.2 input.1)
      (encPair encValue encUnary) (encList encValue) :=
  ((replicateStreamCompiler encValue).comp (replicateMarshalCompiler encValue)).ofOutputEq
    fun input => by simp

end Turing.MultiTapeTM.Internal.NativeCompiler
