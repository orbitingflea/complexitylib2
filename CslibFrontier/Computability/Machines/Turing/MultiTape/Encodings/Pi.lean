/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.OfFn
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Encodings of fixed finite tables

A function on a fixed finite index type is stored as a framed list of all its values. Values may
have unbounded encodings, such as words or tapes. Every entry and its framing contribute to size.

## Main definitions

* `Turing.MultiTapeTM.encPi`: store a finite family in a fixed index order.

## Main results

* `Turing.MultiTapeTM.length_le_encPi`: bound an entry by its enclosing table.
* `Turing.MultiTapeTM.length_encPi_le`: bound the whole table from the sizes of its entries.

## References

Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing framed list encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Index Value : Type} [Fintype Index]

/-- Encode a family by listing every entry in a fixed order, independently of runtime inputs. -/
noncomputable def encPi (enc : Value ↪ List Bool) : (Index → Value) ↪ List Bool where
  toFun values := encList enc (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i)))
  inj' := by
    intro values others h
    have heq := List.ofFn_injective ((encList enc).injective h)
    funext i
    simpa using congrFun heq (Fintype.equivFin Index i)

@[simp] theorem encPi_apply (enc : Value ↪ List Bool) (values : Index → Value) :
    encPi enc values = encList enc
      (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i))) := rfl

/-- Every encoded entry is no longer than its enclosing finite table. -/
theorem length_le_encPi (enc : Value ↪ List Bool) (values : Index → Value) (i : Index) :
    (enc (values i)).length ≤ (encPi enc values).length := by
  rw [encPi_apply]
  apply SizedListEncoding.length_elem_le (encA := enc) (encL := encList enc)
  rw [List.mem_ofFn]
  exact ⟨Fintype.equivFin Index i, by simp⟩

/-- The table encoding charges every entry, including its list framing. -/
theorem length_encPi_le (enc : Value ↪ List Bool) (values : Index → Value)
    {bound : ℕ} (hbound : ∀ i, (enc (values i)).length ≤ bound) :
    (encPi enc values).length ≤ Fintype.card Index * (2 * bound + 1) := by
  simpa only [encPi_apply, List.length_ofFn] using length_encList_le enc
    (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i)))
    (fun value hvalue => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hvalue; exact hbound _)

end Turing.MultiTapeTM
