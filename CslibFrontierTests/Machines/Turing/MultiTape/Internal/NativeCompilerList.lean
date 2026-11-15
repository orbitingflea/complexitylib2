/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List

/-! Checked boundary clients for retained binary-indexed list access. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerList

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Standard-list construction and tail retain framing boundaries. -/
example :
    (listConsCompiler encUnary).outputBits (3, [1, 2]) = 15 ∧
      (listTailCompiler encUnary).outputBits [3, 1, 2] = 8 ∧
      (listTailCompiler encUnary).outputBits [] = 0 ∧
      (listAppendCompiler encUnary).outputBits ([1], [2]) = 8 ∧
      (optionToListCompiler encUnary).outputBits (some 2) = 5 ∧
      (optionToListCompiler encUnary).outputBits none = 0 := by
  decide

/-- Binary-indexed access covers empty, in-range and out-of-range scans. -/
example :
    (listGet?NatCompiler encUnary).outputBits ([], 0) = 0 ∧
      (listGet?NatCompiler encUnary).outputBits ([3, 4], 0) = 4 ∧
      (listGet?NatCompiler encUnary).outputBits ([3, 4], 2) = 0 ∧
      (listGetDNatCompiler 9 encUnary).outputBits ([], 0) = 9 ∧
      (listGetDNatCompiler 9 encUnary).outputBits ([3, 4], 0) = 3 ∧
      (listGetDNatCompiler 9 encUnary).outputBits ([3, 4], 1) = 4 ∧
      (listGetDNatCompiler 9 encUnary).outputBits ([3, 4], 2) = 9 := by
  decide

/-- The complete clock visibly charges the encoded list scan. -/
example (input : List ℕ × ℕ) :
    (encList encUnary input.1).length ≤ (listGetDNatCompiler 9 encUnary).time input :=
  listBits_le_time_listGetDNatCompiler 9 encUnary input

/-- List mapping executes the named callback once per occurrence and preserves list order. -/
example :
    (listMapCompiler encUnary encUnary unaryPred).outputBits [3, 0, 2] = 9 := by
  decide

/-- Left-length zip preserves extra left entries through the explicit right default. -/
example :
    listZipWithLeft 0 Prod.fst [1, 2] [3] = [1, 2] ∧
      (listZipWithLeftCompiler 0 encUnary encUnary encUnary
        (NativeCompiler.first encUnary encUnary)).outputBits ([1, 2], [3]) = 8 := by
  decide

/-- Unary replacement changes one in-range occurrence and leaves out-of-range lists unchanged. -/
example :
    (listReplaceUnaryCompiler encUnary).outputBits ([1, 2, 3], 1, 4) = 19 ∧
      (listReplaceUnaryCompiler encUnary).outputBits ([1, 2, 3], 3, 4) = 15 := by
  decide

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerList
