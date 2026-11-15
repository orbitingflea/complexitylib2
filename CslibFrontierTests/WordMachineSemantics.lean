/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (word-machine semantic regressions)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.WordMachines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelReverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

/-! # Empty and nonempty word-machine behavior -/

open Turing.MultiTapeTM Internal.WordMachines

example : (mapT Bool.not).run () [true, false] = [false, true] := rfl
example : (mapT Bool.not).run () [] = [] := rfl
example : dropLastT.run none [true, false, true] = [true, false] := rfl
example : dropLastT.run none [] = [] := rfl
example : Internal.DecoderWords.unaryLengthT.run () [false, true, false] =
    [true, true, true] := rfl
example : (lastBitT (encOption encBool) (by intro q; cases q <;> simp)).run none [] =
    encOption encBool none := rfl
example : (lastBitT Option.toList (by intro q; cases q <;> simp)).run none
    [true, false] = [false] := rfl
example : (reverseInput Bool).ComputesInTimeAndSpace [] [] 2 0 :=
  ReverseInput.computesInTimeAndSpace []
example : (reverseInput Bool).ComputesInTimeAndSpace [true, false] [false, true] 6 0 :=
  ReverseInput.computesInTimeAndSpace [true, false]
