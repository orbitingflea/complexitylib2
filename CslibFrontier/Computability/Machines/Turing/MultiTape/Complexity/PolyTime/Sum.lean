/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds

/-!
# Polynomial-time sum constructors

The two injections retain the supplied payload encoding and add its tag bit. Their certificates
reuse the linear time and space certificates of `ComputableInO.inl` and `.inr`, forgetting
only their explicit bounds. There is no finite-domain assumption on either summand.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.sumInl`, `.sumInr`: tagged sum construction.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type}

/-- Tag an encoded value as belonging to the left summand. -/
@[fun_prop]
theorem sumInl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inl (α := α) (β := β)) left (encSum left right) :=
  (ComputableInO.inl left right).computableInPolyTime .self .self

/-- Tag an encoded value as belonging to the right summand. -/
@[fun_prop]
theorem sumInr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inr (α := α) (β := β)) right (encSum left right) :=
  (ComputableInO.inr left right).computableInPolyTime .self .self

end Turing.MultiTapeTM.ComputableInPolyTime
