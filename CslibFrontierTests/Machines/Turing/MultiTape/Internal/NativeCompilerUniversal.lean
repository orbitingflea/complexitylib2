/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Universal

/-! Checked branch clients for retained deterministic-universal primitives. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerUniversal

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal Turing.MultiTapeTM.Internal
  Turing.MultiTapeTM.Internal.NativeCompiler

/-- Signed-unary tag and payload access distinguishes nonnegative and negative constructors. -/
example :
    intUnaryPayloadCompiler.outputBits (4 : ℤ) = 4 ∧
      intUnaryPayloadCompiler.outputBits (-3 : ℤ) = 2 ∧
      intUnaryNonnegativeTest.outputBits (4 : ℤ) = 1 ∧
      intUnaryNonnegativeTest.outputBits (-3 : ℤ) = 0 ∧
      intSucc.outputBits (-1 : ℤ) = 1 ∧ intPred.outputBits (0 : ℤ) = 1 := by
  decide

/-- Work-tape reading maps the retained zipper callback across every tape. -/
example :
    tapeRead.outputBits ⟨0, [], []⟩ = 0 ∧
      tapeRead.outputBits ⟨0, [], [some 4]⟩ = 5 ∧
      reads.outputBits [⟨0, [], [some 1]⟩, ⟨0, [], []⟩] = 6 := by
  decide

/-- Tape updates cover missing actions and a concrete write. -/
example :
    let tape : Tape := ⟨0, [], [some 1]⟩
    tapeApply.outputBits (tape, some (some 4), .zero) =
        (eTape (tape.write (some 4))).length ∧
      applyTapes.outputBits ([tape], []) = (encList eTape [tape]).length := by
  decide

/-- Input lookup covers the left blank, word cells, and the right blank. -/
example :
    inputSymbol.outputBits ([5, 2], 0) = 0 ∧
      inputSymbol.outputBits ([5, 2], 1) = 6 ∧
      inputSymbol.outputBits ([5, 2], 2) = 3 ∧
      inputSymbol.outputBits ([5, 2], 3) = 0 := by
  decide

/-- Every movement branch includes the two right-boundary cases. -/
example :
    moveInput.outputBits (3, none, .zero) = 2 ∧
      moveInput.outputBits (3, none, .neg) = 2 ∧
      moveInput.outputBits (0, none, .pos) = 1 ∧
      moveInput.outputBits (3, some 7, .pos) = 3 ∧
      moveInput.outputBits (3, none, .pos) = 2 := by
  decide

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerUniversal
