/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Defs
public import Complexity.DataStructure.StateTransition

/-!
# Specification of a Resizable Array of `b`-Bit Items

`DynamicArray.spec b` specifies a resizable array (dynamic array) holding `b`-bit natural numbers
(`Fits b x`, i.e., `x < 2 ^ b`). The abstract state is `List ℕ`, initialized at the empty list `[]`,
supporting four operations:

* `append x`: append a `b`-bit item `x` to the end of the array (`xs ↦ xs ++ [x]`).
* `pop`: remove and return the last item of the array (`xs ↦ xs.dropLast`, returning `xs.getLast?`).
* `read i`: read the item at index `i < xs.length` (`xs.getD i 0`).
* `write i x`: overwrite the item at index `i < xs.length` with a `b`-bit item `x` (`xs.set i x`).

## Main definitions

* `DynamicArray.Op`, `DynamicArray.Op.Result`: operations and their return types.
* `DynamicArray.stepFn`, `DynamicArray.valid`: transition function and input admissibility.
* `DynamicArray.spec`: deterministic `StateTransitionSpec` for a resizable array of `b`-bit items.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.4][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.DynamicArray

open Cslib.WordRAM Cslib.DataStructure

/-- Abstract state of a resizable array: the list of stored items in index order. -/
abbrev State : Type := List ℕ

/-- The empty array state `[]`. -/
abbrev empty : State := []

/-- Operations on a resizable array of `b`-bit items. -/
inductive Op where
  /-- Append `x` to the end of the array. -/
  | append (x : ℕ)
  /-- Remove and return the last item (`none` if empty). -/
  | pop
  /-- Read the item at index `i`. -/
  | read (i : ℕ)
  /-- Overwrite index `i` with `x`. -/
  | write (i x : ℕ)

/-- Result type of each `DynamicArray.Op`. -/
abbrev Op.Result : Op → Type
  | .append _ => Unit
  | .pop => Option ℕ
  | .read _ => ℕ
  | .write _ _ => Unit

/-- Deterministic transition function for a resizable array. -/
def stepFn (xs : State) : (o : Op) → State × o.Result
  | .append x => (xs ++ [x], ())
  | .pop => (xs.dropLast, xs.getLast?)
  | .read i => (xs, xs.getD i 0)
  | .write i x => (xs.set i x, ())

/-- Admissibility of an array operation for `b`-bit items (`Fits b x`):
* `append x` requires `Fits b x`;
* `pop` is always admissible;
* `read i` requires `i < xs.length`;
* `write i x` requires `i < xs.length ∧ Fits b x`. -/
def valid (b : ℕ) (xs : State) : Op → Prop
  | .append x => Fits b x
  | .pop => True
  | .read i => i < xs.length
  | .write i x => i < xs.length ∧ Fits b x

/-- State-transition specification of a resizable array of `b`-bit items without a capacity cap. -/
abbrev spec (b : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn stepFn (valid b)

@[simp]
theorem stepFn_append (xs : State) (x : ℕ) :
    stepFn xs (.append x) = (xs ++ [x], ()) := rfl

@[simp]
theorem stepFn_pop (xs : State) :
    stepFn xs .pop = (xs.dropLast, xs.getLast?) := rfl

@[simp]
theorem stepFn_read (xs : State) (i : ℕ) :
    stepFn xs (.read i) = (xs, xs.getD i 0) := rfl

@[simp]
theorem stepFn_write (xs : State) (i x : ℕ) :
    stepFn xs (.write i x) = (xs.set i x, ()) := rfl

@[simp]
theorem valid_append (b : ℕ) (xs : State) (x : ℕ) :
    valid b xs (.append x) ↔ Fits b x := Iff.rfl

@[simp]
theorem valid_pop (b : ℕ) (xs : State) :
    valid b xs .pop ↔ True := Iff.rfl

@[simp]
theorem valid_read (b : ℕ) (xs : State) (i : ℕ) :
    valid b xs (.read i) ↔ i < xs.length := Iff.rfl

@[simp]
theorem valid_write (b : ℕ) (xs : State) (i x : ℕ) :
    valid b xs (.write i x) ↔ i < xs.length ∧ Fits b x := Iff.rfl

/-- Length of the array after one operation. -/
theorem length_stepFn_fst (xs : State) (o : Op) :
    (stepFn xs o).1.length =
      match o with
      | .append _ => xs.length + 1
      | .pop => xs.length - 1
      | .read _ => xs.length
      | .write _ _ => xs.length := by
  cases o <;> simp [stepFn]

end Cslib.DataStructure.DynamicArray
