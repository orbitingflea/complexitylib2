/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate

/-! Checked boundary clients for retained unary-driven replication. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerReplicate

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Unary token conversion handles zero and charges standard list framing. -/
example :
    unaryTrueListCompiler.outputBits 0 = 0 ∧ unaryTrueListCompiler.outputBits 3 = 9 := by
  decide

/-- Replication handles zero and nonzero counts with exact standard-list output framing. -/
example :
    (replicateUnaryCompiler encUnary).outputBits (4, 0) = 0 ∧
      (replicateUnaryCompiler encUnary).outputBits (4, 2) = 18 := by
  decide

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerReplicate
