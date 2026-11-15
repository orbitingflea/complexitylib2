/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold

/-! Checked clients for retained native streaming folds. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerStreamFold

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- The framed-value reader removes framing without decoding the payload. -/
example :
    frameValueReader.read false (frame [true, false] ++ [false]) =
      ([true, false], (frame [true, false]).length) :=
  read_frameValueReader [true, false] [false]

/-- Callback lifting exposes the exact kernel constants used by the stream construction. -/
example (input : List Bool) :
    inputFromWordTime unaryDecoder input = unaryDecoder.time input + 4 ∧
      onWordsTime unaryDecoder input =
        unaryDecoder.time input + unaryDecoder.outputBits input + 6 :=
  ⟨rfl, rfl⟩

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerStreamFold
