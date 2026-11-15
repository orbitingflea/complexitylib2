/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatch

/-! Checked nonconstant clients for retained streaming first-match lookup. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerFirstMatch

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Lookup preserves the first match and distinguishes missing keys. -/
example :
    firstMatch (([] : List (ℕ × ℕ)), 1) = none ∧
      firstMatch ([(1, 7), (2, 8), (1, 9)], 1) = some 7 ∧
      firstMatch ([(1, 7), (2, 8), (1, 9)], 2) = some 8 ∧
      firstMatch ([(1, 7), (2, 8), (1, 9)], 3) = none := by
  decide

/-- Output framing is the standard option tag followed by the retained value encoding. -/
example :
    (firstMatchCompiler encUnary encUnary).outputBits ([], 1) = 0 ∧
      (firstMatchCompiler encUnary encUnary).outputBits ([(1, 7), (2, 8), (1, 9)], 1) = 8 ∧
      (firstMatchCompiler encUnary encUnary).outputBits ([(1, 7)], 3) = 0 := by
  decide

/-- The retained clock charges the actual encoded table, even after an early first match. -/
example :
    (encList (encPair encUnary encUnary) [(1, 7), (2, 8), (1, 9)]).length ≤
      (firstMatchCompiler encUnary encUnary).time ([(1, 7), (2, 8), (1, 9)], 1) :=
  tableBits_le_time_firstMatchCompiler encUnary encUnary
    ([(1, 7), (2, 8), (1, 9)], 1)

/-- The streaming phase exposes concrete finite-supremum peak formulas. -/
example (input : FirstMatchState ℕ × List (ℕ × ℕ)) :
    (firstMatchStreamCompiler encUnary encUnary).workspace input =
      streamFoldPairWorkspace
        (firstMatchNextCompiler encUnary encUnary)
        (firstMatchEmitCompiler encUnary encUnary)
        (firstMatchFinishCompiler encUnary encUnary)
        (firstMatchSMax encUnary encUnary) (firstMatchLMax encUnary encUnary) input :=
  rfl

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerFirstMatch
