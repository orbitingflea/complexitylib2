/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelZipTransducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-!
# Named native encoded-word equality

This module retains the direct one-work-tape zip machine used to compare two encoded words. The
first framed word is copied to a work tape; the two words are then scanned in lockstep, including
the distinction between a missing symbol and either Boolean symbol. The tidy wrapper and its
cleanup are part of the retained machine and of the exact resource formulas.

`wordEqBool` emits `encBool`. Branching clients use `wordEqTest`, which explicitly composes the
charged `boolToTest` conversion instead of treating `[false]` as the empty false-test word.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.ofZipTransducer`: retain a direct zip transducer.
* `Turing.MultiTapeTM.Internal.NativeCompiler.wordEqBool`: equality with one-bit output.
* `Turing.MultiTapeTM.Internal.NativeCompiler.wordEqTest`: equality with empty/nonempty test output.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

universe u v

/-- A constructor view of the direct zip-machine control states. -/
def zipStateToSum {State : Type} : ZipTransducer.State State →
    Fin 3 ⊕ (State × Option Bool) ⊕ Bool
  | .copy => .inl 0
  | .copyBit => .inl 1
  | .rewind => .inl 2
  | .zip state pending => .inr (.inl (state, pending))
  | .flush bit => .inr (.inr bit)

/-- The constructor view of zip-machine states is injective. -/
theorem zipStateToSum_injective {State : Type} :
    Function.Injective (zipStateToSum : ZipTransducer.State State →
      Fin 3 ⊕ (State × Option Bool) ⊕ Bool) := by
  intro left right h
  cases left <;> cases right <;> simp_all [zipStateToSum]

/-- Constructive encoding of the direct zip-machine control states. -/
@[expose] def zipStateEncoding {State : Type} (stateEncoding : State ↪ ℕ) :
    ZipTransducer.State State ↪ ℕ :=
  (⟨zipStateToSum, zipStateToSum_injective⟩ :
      ZipTransducer.State State ↪ Fin 3 ⊕ (State × Option Bool) ⊕ Bool) |>.trans
    (sumStateEncoding Fin.valEmbedding
      (sumStateEncoding
        (prodStateEncoding stateEncoding (optionStateEncoding Universal.eBit))
        Universal.eBit))

/-- Retain a zip transducer through the direct machine and the existing tidy normal form. The
clock and workspace expose the kernel bound and every cleanup term. -/
@[expose] noncomputable def ofZipTransducer {Alpha : Type u} {Beta : Type v}
    {Gamma : Type*} {State : Type}
    [Fintype State]
    {f : Alpha × Beta → Gamma} (encFirst : Alpha ↪ List Bool) (encSecond : Beta ↪ List Bool)
    (encOut : Gamma ↪ List Bool) (transducer : ZipTransducer State)
    (stateEncoding : State ↪ ℕ)
    (run_eq : ∀ input, transducer.run transducer.q₀ (encFirst input.1) (encSecond input.2) =
      encOut (f input)) :
    NativeCompiler f (encPair encFirst encSecond) encOut := by
  let clearCount := (List.finRange 1).length
  let RawState := ZipTransducer.State State
  let CompilerState := ((Option RawState ⊕ ClearListState clearCount) ⊕ RewindState)
  letI : Fintype RawState := Fintype.ofFinite RawState
  letI : Fintype (ClearListState clearCount) := Fintype.ofFinite (ClearListState clearCount)
  letI : Fintype CompilerState := inferInstance
  exact {
    tapeCount := 1 + 1
    State := CompilerState
    machine := tidy false true transducer.toTM
    stateEncoding := sumStateEncoding
      (sumStateEncoding (optionStateEncoding (zipStateEncoding stateEncoding))
        (clearListStateEncoding clearCount))
      rewindStateEncoding
    time := fun input =>
      let inputLength := (encPair encFirst encSecond input).length
      let rawSpace := (encFirst input.1).length + 2
      2 * (3 * inputLength + 1) + 3 * rawSpace + 2 * 1 + 4
    workspace := fun input =>
      let rawSpace := (encFirst input.1).length + 2
      2 * rawSpace + 2 * 1 * (3 * rawSpace + 2 * 1 + 3)
    computes := fun input => by
      have h := transducer.computesInTimeAndSpace_toTM
        (encFirst input.1) (encSecond input.2)
      have htidy := h.computesTidily_tidy (m₀ := false) (m₁ := true) (by decide)
      simpa only [encPair_apply, run_eq input] using htidy
  }

/-- The retained zip compiler uses the direct zip machine under the tidy wrapper. -/
theorem machine_ofZipTransducer {Alpha : Type u} {Beta : Type v}
    {Gamma : Type*} {State : Type}
    [Fintype State]
    {f : Alpha × Beta → Gamma} (encFirst : Alpha ↪ List Bool) (encSecond : Beta ↪ List Bool)
    (encOut : Gamma ↪ List Bool) (transducer : ZipTransducer State)
    (stateEncoding : State ↪ ℕ)
    (run_eq : ∀ input, transducer.run transducer.q₀ (encFirst input.1) (encSecond input.2) =
      encOut (f input)) :
    (ofZipTransducer encFirst encSecond encOut transducer stateEncoding run_eq).machine =
      tidy false true transducer.toTM :=
  rfl

/-- Compare two words, remembering whether their lengths and every symbol agree. -/
def wordEqT : ZipTransducer Bool where
  q₀ := true
  step equal symbols := (equal && decide (symbols.1 = symbols.2), [])
  final equal := [equal]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The word-equality zip transducer emits the one-bit Boolean equality result. -/
theorem wordEqT_run (equal : Bool) : ∀ first second : List Bool,
    wordEqT.run equal first second = [equal && decide (first = second)]
  | [], [] => by
      cases equal <;>
        simp only [ZipTransducer.run_nil_nil, wordEqT, Bool.false_and,
          Bool.true_and, decide_true]
  | bit :: first, [] => by
      rw [ZipTransducer.run_cons_nil, wordEqT_run]
      cases equal <;> simp [wordEqT]
  | [], bit :: second => by
      rw [ZipTransducer.run_nil_cons, wordEqT_run]
      cases equal <;> simp [wordEqT]
  | firstBit :: first, secondBit :: second => by
      rw [ZipTransducer.run_cons_cons, wordEqT_run]
      cases equal <;> cases firstBit <;> cases secondBit <;> simp [wordEqT]

/-- The word-equality transducer, started in its designated initial state, decides equality of
its two input words. -/
theorem wordEqT_run_q₀ (first second : List Bool) :
    wordEqT.run wordEqT.q₀ first second = [decide (first = second)] := by
  change wordEqT.run true first second = [decide (first = second)]
  simpa only [Bool.true_and] using wordEqT_run true first second

/-- Equality of two values under a shared injective encoding, with one-bit Boolean output. -/
@[expose] noncomputable def wordEqBool {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun input : Alpha × Alpha => decide (enc input.1 = enc input.2))
      (encPair enc enc) encBool :=
  ofZipTransducer enc enc encBool wordEqT Universal.eBit fun input => by
    change wordEqT.run wordEqT.q₀ (enc input.1) (enc input.2) =
      [decide (enc input.1 = enc input.2)]
    exact wordEqT_run_q₀ (enc input.1) (enc input.2)

/-- Equality in the empty/nonempty branch-test encoding, with the conversion explicitly retained. -/
@[expose] noncomputable def wordEqTest {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun input : Alpha × Alpha => decide (enc input.1 = enc input.2))
      (encPair enc enc) encTest :=
  boolToTest.comp (wordEqBool enc)

end Turing.MultiTapeTM.Internal.NativeCompiler
