/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional

set_option linter.privateModule false

/-! Checked clients for the named native conditional. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerConditional

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

private noncomputable def condition :
    NativeCompiler (Function.const ℕ true) encUnary encTest :=
  const encUnary encTest true

private noncomputable def trueBranch :
    NativeCompiler (Function.const ℕ 1) encUnary encUnary :=
  const encUnary encUnary 1

private noncomputable def falseBranch :
    NativeCompiler (Function.const ℕ 0) encUnary encUnary :=
  const encUnary encUnary 0

/-- The chosen branch is charged once, alongside the named condition and conditional overhead. -/
example (input : ℕ) :
    (ite condition trueBranch falseBranch).time input =
      condition.time input + trueBranch.time input + 10 :=
  rfl

/-- The assembled compiler exposes the exact retained conditional machine. -/
example :
    (ite condition trueBranch falseBranch).machine =
      iteTM condition.machine trueBranch.machine falseBranch.machine :=
  machine_ite condition trueBranch falseBranch

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerConditional
