/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod

/-! Ordinary-module clients of the positive-modulus and total modular-power certificates. -/

public section

namespace CslibFrontierTests.PowModPlain

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^ (p.2 + 1) % (2 * p.2 + 3))
    (encPair encNat encNat) encNat :=
  ComputableInPolyTime.binary_powMod (by fun_prop)
    (ComputableInPolyTime.binary_add' (by fun_prop) (.const 1))
    (ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_mul' (.const 2) (by fun_prop)) (.const 3))
    fun _ => Nat.succ_pos _

example : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => powMod p.2.2 p.1 p.2.1)
    (encPair encNat (encPair encNat encNat)) encNat :=
  computableInPolyTime_powMod (by fun_prop) (by fun_prop) (by fun_prop)

example : powMod 0 7 5 = 1 := by decide +kernel

example : powMod 1 7 0 = 0 := by decide +kernel

example : powMod 13 7 5 = 11 := by decide +kernel

end CslibFrontierTests.PowModPlain
