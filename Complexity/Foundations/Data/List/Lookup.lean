/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Defaulted list lookup and updates

## Main results

* `List.getD_mem_or`, `List.getD_idxOf`: a defaulted lookup returns a member or the default,
  and returns a member at its first index.
* `List.getD_set_self`, `List.getD_set_ne`: reading an updated entry or an unchanged entry.
* `List.forall_mem_set_of_forall_mem`, `List.getD_le_of_forall_le`: preserve invariants under
  updates and bound defaulted reads of numeric register files.
* `List.getD_map_range`: read a function tabulated over a bounded range.
* `List.map_range_eq_ofFn`: runtime tabulation agrees with the finite coordinate view.
* `List.find?_range_getD_eq_sInf`: the least index below `m` passing a test, or `m`, as a search
  over a range.
-/

@[expose] public section

/-- Reading the updated entry of a list. -/
theorem List.getD_set_self {α : Type*} {l : List α} {i : ℕ} {x d : α} (h : i < l.length) :
    (l.set i x).getD i d = x := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_set_self]

/-- Reading another entry of an updated list. -/
theorem List.getD_set_ne {α : Type*} {l : List α} {i j : ℕ} {x d : α} (h : i ≠ j) :
    (l.set i x).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- A property of all the entries of a list holds of all the entries of an update by a value
having it. -/
theorem List.forall_mem_set_of_forall_mem {α : Type*} {p : α → Prop} {l : List α} {i : ℕ} {x : α}
    (h : ∀ a ∈ l, p a) (hx : p x) : ∀ a ∈ l.set i x, p a := fun a ha => by
  rcases List.mem_or_eq_of_mem_set ha with ha | rfl
  · exact h a ha
  · exact hx

/-- The entries of a list of numbers at most `B`, read with default `0`, are at most `B`. -/
theorem List.getD_le_of_forall_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) (j : ℕ) :
    l.getD j 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hj : l[j]? with _ | a
  · exact Nat.zero_le _
  · exact h a (List.mem_of_getElem? hj)

/-- A defaulted lookup returns a member of the list or the default value. -/
theorem List.getD_mem_or {α : Type*} (l : List α) (j : ℕ) (d : α) :
    l.getD j d ∈ l ∨ l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[j]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

/-- Looking up the first index of a member of a list returns that member. -/
theorem List.getD_idxOf {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {x : α} (hx : x ∈ l)
    (d : α) : l.getD (l.idxOf x) d = x := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 hx), List.getElem_idxOf]

/-- Reading a mapped range at a valid index applies the map to that index. -/
theorem List.getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- Tabulating a natural-indexed function over a range agrees with its finite coordinate view. -/
theorem List.map_range_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

/-- The least index below `m` passing a test, or `m`, as a search over `List.range m`. -/
theorem List.find?_range_getD_eq_sInf (m : ℕ) (p : ℕ → Bool) :
    ((List.range m).find? p).getD m = sInf {i | i = m ∨ p i = true} := by
  set v := ((List.range m).find? p).getD m with hv
  have hmem : v ∈ {i | i = m ∨ p i = true} ∧ ∀ i < v, i ∉ {i | i = m ∨ p i = true} := by
    cases hf : (List.range m).find? p with
    | none =>
      rw [hv, hf, Option.getD_none]
      rw [List.find?_eq_none] at hf
      refine ⟨Or.inl rfl, fun i hi hmem => ?_⟩
      rcases hmem with rfl | h
      · exact lt_irrefl _ hi
      · exact hf i (List.mem_range.mpr hi) h
    | some i₀ =>
      rw [hv, hf, Option.getD_some]
      obtain ⟨hp, k, hk, hki, hmin⟩ := List.find?_eq_some_iff_getElem.mp hf
      rw [List.getElem_range] at hki
      subst hki
      rw [List.length_range] at hk
      refine ⟨Or.inr hp, fun i hi hmem => ?_⟩
      rcases hmem with rfl | h
      · omega
      · have := hmin i hi
        simp_all
  exact le_antisymm (not_lt.mp fun h => hmem.2 _ h (Nat.sInf_mem ⟨v, hmem.1⟩)) (Nat.sInf_le hmem.1)
