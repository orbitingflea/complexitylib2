/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Sum

/-! Checked boundary clients for retained standard-sum destructors. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerSum

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Sum destructors read the actual tag and use explicit defaults on the opposite constructor. -/
example :
    (sumTag encUnary encBool).outputBits (Sum.inl 3) = 1 ∧
      (sumTag encUnary encBool).outputBits (Sum.inr true) = 1 ∧
      (sumLeftD 5 encUnary encBool).outputBits (Sum.inl 3) = 3 ∧
      (sumLeftD 5 encUnary encBool).outputBits (Sum.inr true) = 5 ∧
      (sumRightD false encUnary encBool).outputBits (Sum.inl 3) = 1 ∧
      (sumRightD false encUnary encBool).outputBits (Sum.inr true) = 1 := by
  decide

/-- Total list access covers empty, in-range and out-of-range unary indices. -/
example :
    (optionGetD 9 encUnary).outputBits none = 9 ∧
      (optionGetD 9 encUnary).outputBits (some 3) = 3 ∧
      (listHeadD 9 encUnary).outputBits [] = 9 ∧
      (listHeadD 9 encUnary).outputBits [3, 4] = 3 ∧
      (listGetDUnary 9 encUnary).outputBits ([3, 4], 1) = 4 ∧
      (listGetDUnary 9 encUnary).outputBits ([3, 4], 2) = 9 := by
  decide

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerSum
