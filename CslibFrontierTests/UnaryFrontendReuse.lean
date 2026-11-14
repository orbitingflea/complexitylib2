/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (unary frontend certificate reuse regression)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-! Computed unary counts exercise subtraction, comparison and raw-word access together. -/

open Turing.MultiTapeTM

-- Mirrors the computed-index access and comparison in Bimatrix.decodeT₁.
example {α : Type} {enc : α ↪ List Bool} {word : α → List Bool} {n k : α → ℕ}
    (hw : ComputableInPolyTime word enc encBits)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a =>
      (word a).getD (n a - k a) true && decide (n a ≤ k a)) enc encBool := by
  have hsub := ComputableInPolyTime.unary_sub.comp (hn.prod hk)
  exact ComputableInPolyTime.bool_and.comp
    (((ComputableInPolyTime.bitsGetD true).comp (hw.prod hsub)).prod
      (ComputableInPolyTime.unary_le' hn hk))

-- Empty words and out-of-range indices use the requested fallback.
example : ([] : List Bool).getD (0 - 3) true = true := rfl
example : ([false] : List Bool).getD (5 - 1) true = true := rfl
example : ([true] : List Bool).getD (1 - 3) false = true := rfl
