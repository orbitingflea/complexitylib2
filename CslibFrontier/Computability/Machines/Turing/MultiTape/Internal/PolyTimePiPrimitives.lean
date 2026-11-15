/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeFinitePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds

/-!
# Direct finite-table construction, lookup and update

The fixed index order and framed-list representation are unchanged. Construction, lookup and
update reuse the parameterized resource certificates in `Complexity.BigO.Pi`; finite runtime
dispatch retains the full captured input in each branch. The direct proofs introduce no default
inhabitant requirement on the value or index type.
-/

public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- Construct a list of a fixed number of efficiently computed entries. -/
@[fun_prop]
theorem ofFn {count : ℕ} {values : α → Fin count → Value}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input enc) :
    ComputableInPolyTime (fun a => List.ofFn (values a)) input (encList enc) := by
  classical
  choose d e hd using fun i => (hvalues i).exists_degree
  have hbound : PolyBounded (fun a => (input a).length)
      (fun a => (input a).length + ∑ i, ((input a).length + 1) ^ d i) :=
    PolyBounded.self.add (.sum Finset.univ fun i _ =>
      (PolyBounded.self.add (.const 1)).pow (d i))
  exact (ComputableInO.ofFn fun i => (hd i).inO).computableInPolyTime hbound hbound

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
@[fun_prop]
theorem pi [Fintype Index] {values : α → Index → Value}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input enc) :
    ComputableInPolyTime values input (encPi enc) :=
  (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq (fun _ => rfl)

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableInPolyTime (fun values : Index → Value => values i) (encPi enc) enc :=
  (ComputableInO.pi_apply enc i).computableInPolyTime .self .self

/-- Update a fixed table entry while charging for all preserved entries. -/
@[fun_prop]
theorem pi_update [Fintype Index] [DecidableEq Index]
    {values : α → Index → Value} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hvalue : ComputableInPolyTime value input enc) (i : Index) :
    ComputableInPolyTime (fun a => Function.update (values a) i (value a))
      input (encPi enc) :=
  ((ComputableInO.pi_update enc i).computableInPolyTime .self .self).comp
    (hvalues.prod hvalue)

/-- Read a computed index of a fixed finite table, charging the index and all stored entries. -/
theorem pi_apply' [Fintype Index] {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) input enc :=
  hindex.finite_cases (fun i => (pi_apply enc i).comp hvalues)

/-- Update a computed index while retaining and charging every other entry. -/
@[fun_prop]
theorem pi_update' [Fintype Index] [DecidableEq Index] {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding)
    (hvalue : ComputableInPolyTime value input enc) :
    ComputableInPolyTime (fun a => Function.update (values a) (index a) (value a))
      input (encPi enc) := hindex.finite_cases (fun i => pi_update hvalues hvalue i)

end Turing.MultiTapeTM.ComputableInPolyTime
