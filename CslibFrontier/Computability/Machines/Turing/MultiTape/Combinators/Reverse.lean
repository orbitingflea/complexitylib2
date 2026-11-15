/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelReverse
import Mathlib.Tactic.TypeStar

/-! # Encoded input reversal

Resource facades for the shared two-state input-reversal machine.
-/

namespace Turing.MultiTapeTM

/-- Reverse the encoded input with the two-state zero-workspace machine. -/
public theorem computableInTimeAndSpace_reverse {α β : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (hf : ∀ a, encOut (f a) = (encIn a).reverse) :
    ComputableInTimeAndSpace f encIn encOut
      (fun a => 2 * (encIn a).length + 2) (fun _ => 0) :=
  ⟨0, Bool, inferInstance, reverseInput Bool, fun a =>
    hf a ▸ ReverseInput.computesInTimeAndSpace (encIn a)⟩

/-- Any function whose encoding reverses the encoded input is tidily computable in
`2 * (encIn a).length + 2` steps and zero work-tape space. -/
public theorem computableTidilyInTimeAndSpace_reverse {α β : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (hf : ∀ a, encOut (f a) = (encIn a).reverse) :
    ComputableTidilyInTimeAndSpace f encIn encOut
      (fun a => 2 * (encIn a).length + 2) (fun _ => 0) :=
  ⟨0, Bool, inferInstance, reverseInput Bool, fun a =>
    hf a ▸ ReverseInput.computesTidily (encIn a)⟩

end Turing.MultiTapeTM
