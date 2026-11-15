/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Degree-one bounds for tagged sum constructors

Prepending the fixed Boolean tag bit to the payload encoding has a direct degree-one certificate,
without any finite-domain or inhabitance assumption on either summand.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.inl`, `.inr`: direct degree-one tagged sum injections.

## References

Uses Christian Reitwiessner's native degree/resource calculus (`ComputableInDegree.append`).
-/

public section

namespace Turing.MultiTapeTM.ComputableInDegree

universe u v

variable {α : Type u} {β : Type v}

/-- A left sum tag has a direct degree-one implementation. -/
@[fun_prop]
theorem inl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.inl (α := α) (β := β)) left (encSum left right) 1 1 := by
  have hid : ComputableInDegree (fun a : α => a) left left 1 1 := .id'
  exact ((const (encMid := encBool) false).append hid (fun _ => rfl)).mono

/-- A right sum tag has a direct degree-one implementation. -/
@[fun_prop]
theorem inr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.inr (α := α) (β := β)) right (encSum left right) 1 1 := by
  have hid : ComputableInDegree (fun a : β => a) right right 1 1 := .id'
  exact ((const (encMid := encBool) true).append hid (fun _ => rfl)).mono

end Turing.MultiTapeTM.ComputableInDegree
