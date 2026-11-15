/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Equality

/-! Checked clients for retained encoded-word equality. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerEquality

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Equality is nonconstant and distinguishes the Boolean and branch-test output encodings. -/
example :
    (wordEqBool encUnary).outputBits (2, 2) = 1 ∧
      (wordEqBool encUnary).outputBits (2, 3) = 1 ∧
      (wordEqTest encUnary).outputBits (2, 2) = 1 ∧
      (wordEqTest encUnary).outputBits (2, 3) = 0 := by
  decide

/-- The exact direct-kernel resource formulas remain visible. -/
example :
    (wordEqBool encUnary).time (2, 3) =
      2 * (3 * (encPair encUnary encUnary (2, 3)).length + 1) +
        3 * ((encUnary 2).length + 2) + 2 * 1 + 4 ∧
      (wordEqBool encUnary).workspace (2, 3) =
        2 * ((encUnary 2).length + 2) +
          2 * 1 * (3 * ((encUnary 2).length + 2) + 2 * 1 + 3) :=
  ⟨rfl, rfl⟩

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerEquality
