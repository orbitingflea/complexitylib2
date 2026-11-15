/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.List.Fold

/-!
# Plain polynomial-time finite case analysis

A fixed finite tag selects a branch retaining the original input, with arbitrary tag and output
encodings and no default inhabitant requirement. This module provides
`Turing.MultiTapeTM.ComputableInPolyTime.finite_cases` without importing the higher tidy calculus.

## References

Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableInPolyTime (branch choice) input output) :
    ComputableInPolyTime (fun a => branch (tag a) a) input output := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInPolyTime (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        simpa only [List.foldr_cons, decide_eq_true_eq] using
          (htag.decide_eq' (const choice)).ite (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Turing.MultiTapeTM.ComputableInPolyTime
