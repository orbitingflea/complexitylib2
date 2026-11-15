/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Comparison

/-! Checked boundary clients for retained unary comparison. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerComparison

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Strict comparison handles both zero boundaries and unequal nonzero lengths. -/
example :
    unaryLtBool.outputBits (0, 0) = 1 ∧ unaryLtBool.outputBits (0, 1) = 1 ∧
      unaryLtTest.outputBits (0, 0) = 0 ∧ unaryLtTest.outputBits (0, 1) = 1 ∧
      unaryLtTest.outputBits (3, 2) = 0 := by
  decide

/-- The retained comparison still exposes the direct tidy zip machine. -/
example : unaryLtBool.machine = tidy false true unaryLtT.toTM :=
  machine_ofZipTransducer encUnary encUnary encBool unaryLtT Universal.eBit fun input =>
    unaryLtT_run input.1 input.2

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerComparison
