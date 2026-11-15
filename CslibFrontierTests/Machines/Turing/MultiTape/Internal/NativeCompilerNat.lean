/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Nat

/-! Checked boundary clients for retained binary-natural primitives. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerNat

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Successor and saturating predecessor cover the zero and carry/borrow boundaries. -/
example :
    natSucc.outputBits 0 = 1 ∧ natSucc.outputBits 3 = 3 ∧
      natPred.outputBits 0 = 0 ∧ natPred.outputBits 4 = 2 := by
  decide

/-- The Boolean and branch-test zero encodings remain distinct and explicit. -/
example :
    natIsZeroBool.outputBits 0 = 1 ∧ natIsZeroBool.outputBits 1 = 1 ∧
      natIsZeroTest.outputBits 0 = 1 ∧ natIsZeroTest.outputBits 1 = 0 := by
  decide

/-- The exact zero-work streaming clock is retained by each transducer wrapper. -/
example (n : ℕ) :
    natSucc.time n = 4 * (encNat n).length + 8 ∧ natSucc.workspace n = 0 :=
  ⟨rfl, rfl⟩

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerNat
