/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Minimum and maximum of computed binary naturals

These plain rules fix both intermediate number encodings. They extract the local binary-order
certificates used by `Classes.IP.PSPACE`, so other clients can reuse the same arithmetic.
Automation registration stays local to clients that require it.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}

/-- Maximum of two computed binary naturals. -/
theorem binary_max' (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun x => max (left x) (right x)) input encNat := by
  simp only [max_def]
  exact ite_decide (binary_le' hl hr) hr hl

/-- Minimum of two computed binary naturals. -/
theorem binary_min' (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun x => min (left x) (right x)) input encNat := by
  simp only [min_def]
  exact ite_decide (binary_le' hl hr) hl hr

end Turing.MultiTapeTM.ComputableInPolyTime
