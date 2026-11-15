/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ZMod/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.Basic

/-!
# Casts of natural-number expressions to `ZMod`

Programs that work on natural numbers subtract a residue `b` modulo `q` as `q - b % q`, which
avoids truncated subtraction below zero. This module shows that the cast of `q - b % q` to
`ZMod q` is `-b`, and that the cast of `q - 1` is `-1`.

## Main results

* `ZMod.natCast_sub_mod_eq_neg`: `((q - b % q : ℕ) : ZMod q) = -b` for `q ≠ 0`.
* `ZMod.natCast_self_sub_one`: `((q - 1 : ℕ) : ZMod q) = -1` for `q ≠ 0`.
-/

public section

namespace ZMod

/-- For `q ≠ 0`, the natural number `q - b % q` casts to `-b` in `ZMod q`. -/
theorem natCast_sub_mod_eq_neg (q b : ℕ) [NeZero q] :
    ((q - b % q : ℕ) : ZMod q) = -(b : ZMod q) := by
  rw [Nat.cast_sub (Nat.mod_lt _ (NeZero.pos q)).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

/-- For `q ≠ 0`, the natural number `q - 1` casts to `-1` in `ZMod q`. -/
theorem natCast_self_sub_one (q : ℕ) [NeZero q] : ((q - 1 : ℕ) : ZMod q) = -1 := by
  rw [Nat.cast_pred (NeZero.pos q), ZMod.natCast_self, zero_sub]

end ZMod
