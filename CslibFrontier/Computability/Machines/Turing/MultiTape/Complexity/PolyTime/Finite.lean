/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeFinitePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time finite case analysis

An efficiently computed finite tag selects a branch retaining the original input. Both the tag
encoding and output encoding are arbitrary. The finite type and all branch machines are fixed
independently of runtime input; this does not enumerate a family whose size grows with the input.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.finite_cases`,
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases`: finite dispatch with captured input.

## References

Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableTidilyInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableTidilyInPolyTime (branch choice) input output) :
    ComputableTidilyInPolyTime (fun a => branch (tag a) a) input output :=
  (ComputableInPolyTime.finite_cases htag.computableInPolyTime fun choice =>
    (hbranch choice).computableInPolyTime).tidy

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
