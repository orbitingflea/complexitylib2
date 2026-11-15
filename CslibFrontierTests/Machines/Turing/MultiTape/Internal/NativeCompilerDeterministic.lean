/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Deterministic

/-! Checked boundary clients for retained deterministic universal steps. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerDeterministic

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal Turing.MultiTapeTM.Internal
  Turing.MultiTapeTM.Internal.NativeCompiler

/-- Halted and missing-transition configurations take their exact non-scanning/local-halt paths. -/
example :
    let description : Desc := ⟨0, 0, []⟩
    let halted : SCfg := ⟨none, 1, []⟩
    let active : SCfg := ⟨some 0, 1, []⟩
    (Universal.stepWith description halted none).1.state = none ∧
      (Universal.stepWith description halted none).1.inputPos = 1 ∧
      (Universal.stepWith description halted none).2 = none ∧
      (Universal.stepWith description active none).1.state = none := by
  decide

/-- First-match order, action application and emitted output are retained. -/
example :
    let cfg : SCfg := ⟨some 0, 1, []⟩
    let key : Key := ⟨0, none, []⟩
    let firstAction : Act := ⟨0, [], some 3, some 1⟩
    let secondAction : Act := ⟨0, [], some 4, some 2⟩
    let description : Desc := ⟨0, 0, [(key, firstAction), (key, secondAction)]⟩
    (Universal.stepWith description cfg none).1.state = some 1 ∧
      (Universal.stepWith description cfg none).1.inputPos = 1 ∧
      (Universal.stepWith description cfg none).2 = some 3 ∧
      stepWithCompiler.outputBits (description, cfg, none) =
        (encPair eCfg eSym (Universal.stepWith description cfg none)).length := by
  decide

/-- Complete stepping includes retained input-symbol lookup at both blank boundaries. -/
example :
    let cfg : SCfg := ⟨some 0, 0, []⟩
    let description : Desc := ⟨0, 0, []⟩
    stepCompiler.outputBits (description, [], cfg) =
      (encPair eCfg eSym (Universal.step description [] cfg)).length :=
  rfl

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerDeterministic
