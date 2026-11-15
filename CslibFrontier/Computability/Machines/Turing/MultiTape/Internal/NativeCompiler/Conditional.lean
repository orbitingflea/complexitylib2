/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelIte
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler

/-!
# Named native conditionals

This module retains the existing direct conditional machine as a `NativeCompiler`. Its Boolean
condition is encoded by `encTest`, so an empty word selects the false branch and a nonempty word
selects the true branch. The resulting compiler records the actual nested finite state, its
constructive encoding, and every constant in the kernel conditional theorem.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.ite`: direct conditional composition of three named
  compilers.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.machine_ite`: the retained machine is definitionally
  `Turing.MultiTapeTM.iteTM` applied to the three supplied machines.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Direct conditional composition of a named condition and two named branches. The condition
emits `encTest`; no semantic Boolean callback is hidden behind the assembled machine. -/
@[expose] noncomputable def ite {Alpha Beta : Type*} {condition : Alpha → Bool}
    {ifTrue ifFalse : Alpha → Beta} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (conditionCompiler : NativeCompiler condition encIn encTest)
    (trueCompiler : NativeCompiler ifTrue encIn encOut)
    (falseCompiler : NativeCompiler ifFalse encIn encOut) :
    NativeCompiler (fun input => if condition input then ifTrue input else ifFalse input)
      encIn encOut := by
  let CompilerState :=
    ((conditionCompiler.State ⊕ RewindWorkState) ⊕
      Option (trueCompiler.State ⊕ falseCompiler.State) ⊕ Unit ⊕ RewindWorkState)
  letI := conditionCompiler.stateFintype
  letI := trueCompiler.stateFintype
  letI := falseCompiler.stateFintype
  letI : Fintype CompilerState := inferInstance
  exact {
    tapeCount := max conditionCompiler.tapeCount
      (max trueCompiler.tapeCount falseCompiler.tapeCount) + 1
    State := CompilerState
    machine := iteTM conditionCompiler.machine trueCompiler.machine falseCompiler.machine
    stateEncoding := sumStateEncoding
      (sumStateEncoding conditionCompiler.stateEncoding rewindWorkStateEncoding)
      (sumStateEncoding
        (optionStateEncoding
          (sumStateEncoding trueCompiler.stateEncoding falseCompiler.stateEncoding))
        (sumStateEncoding unitStateEncoding rewindWorkStateEncoding))
    time := fun input => conditionCompiler.time input +
      (if condition input then trueCompiler.time input else falseCompiler.time input) +
      4 * (encTest (condition input)).length + 6
    workspace := fun input => conditionCompiler.workspace input +
      (if condition input then trueCompiler.workspace input else falseCompiler.workspace input) +
      3 * (encTest (condition input)).length +
      5 * max conditionCompiler.tapeCount
        (max trueCompiler.tapeCount falseCompiler.tapeCount) + 10
    computes := fun input => by
      cases hcondition : condition input with
      | false =>
          have h := (conditionCompiler.computes input).ite
            (tm₁ := trueCompiler.machine) (tm₂ := falseCompiler.machine)
            (y := encOut (ifFalse input))
            (t₁ := trueCompiler.time input) (s₁ := trueCompiler.workspace input)
            (t₂ := falseCompiler.time input) (s₂ := falseCompiler.workspace input)
            (fun hne => (hne (by simp only [hcondition, encTest_false])).elim)
            (fun _ => falseCompiler.computes input)
          simpa only [hcondition, Bool.false_eq_true, ↓reduceIte, encTest_false,
            List.length_nil, Nat.mul_zero, Nat.add_zero] using h
      | true =>
          have h := (conditionCompiler.computes input).ite
            (tm₁ := trueCompiler.machine) (tm₂ := falseCompiler.machine)
            (y := encOut (ifTrue input))
            (t₁ := trueCompiler.time input) (s₁ := trueCompiler.workspace input)
            (t₂ := falseCompiler.time input) (s₂ := falseCompiler.workspace input)
            (fun _ => trueCompiler.computes input)
            (fun heq => by
              simp only [hcondition, encTest_true, List.cons_ne_nil] at heq)
          simpa only [hcondition, ↓reduceIte, encTest_true, List.cons_ne_nil,
            List.length_singleton] using h
  }

/-- Conditional composition retains the actual kernel conditional. -/
theorem machine_ite {Alpha Beta : Type*} {condition : Alpha → Bool}
    {ifTrue ifFalse : Alpha → Beta} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (conditionCompiler : NativeCompiler condition encIn encTest)
    (trueCompiler : NativeCompiler ifTrue encIn encOut)
    (falseCompiler : NativeCompiler ifFalse encIn encOut) :
    (ite conditionCompiler trueCompiler falseCompiler).machine =
      iteTM conditionCompiler.machine trueCompiler.machine falseCompiler.machine :=
  rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
