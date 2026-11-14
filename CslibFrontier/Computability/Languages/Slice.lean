/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Languages/Slice.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Languages.Slice

/-!
# Slices of Boolean combinations of languages and encoded problems

The slices of the empty and the full language (as `0` or `⊥`, and `⊤`), of complements, unions
and intersections, together with the slice indicator `Language.encodesMember` for problems with
an injective encoding `enc : α ↪ List β`.

## Main definitions

* `Language.encodes`, `Language.encodesMember`: the words of length `n` in the image of an encoding
  `enc : α ↪ List β`, and the indicator of encoded members of a set `A : Set α`.

## Main results

* `Language.slice_zero`, `Language.slice_bot`, `Language.slice_top`: slices of the empty and full
  languages.
* `Language.slice_compl`, `Language.slice_sup`, `Language.slice_inf`: slices of complements,
  unions, and intersections.
* `Language.encodesMember_eq_true_iff`, `Language.mem_iff_of_slice_eq_encodesMember`:
  characterization of `encodesMember` on encoded instances and agreement with `Language.slice`.
-/

public section

namespace Language

variable {α β : Type*} {L M : Language α} {n : ℕ} {x : Fin n → α}

/-- The slices of the empty language `0` are `false` everywhere. -/
@[simp] theorem slice_zero : (0 : Language α).slice n x = false :=
  Bool.eq_false_iff.2 fun h => notMem_zero _ (slice_eq_true_iff.1 h)

/-- The slices of the empty language `⊥` are `false` everywhere. -/
@[simp] theorem slice_bot : (⊥ : Language α).slice n x = false :=
  slice_zero

/-- The slices of the full language `⊤` are `true` everywhere. -/
@[simp] theorem slice_top : (⊤ : Language α).slice n x = true := slice_eq_true_iff.2 trivial

/-- The slice of a complement is the negation of the slice. -/
@[simp] theorem slice_compl : Lᶜ.slice n x = !L.slice n x := by
  cases h : L.slice n x
  · exact slice_eq_true_iff.2 fun hm => by simp [slice_eq_true_iff.2 hm] at h
  · exact Bool.eq_false_iff.2 fun h' => (slice_eq_true_iff.1 h') (slice_eq_true_iff.1 h)

/-- The slice of a union is the disjunction of the slices. -/
@[simp] theorem slice_sup : (L ⊔ M).slice n x = (L.slice n x || M.slice n x) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, slice_eq_true_iff, slice_eq_true_iff, slice_eq_true_iff]
  exact Iff.rfl

/-- The slice of an intersection is the conjunction of the slices. -/
@[simp] theorem slice_inf : (L ⊓ M).slice n x = (L.slice n x && M.slice n x) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, slice_eq_true_iff, slice_eq_true_iff, slice_eq_true_iff]
  exact Iff.rfl

section Encoded

variable {enc : α ↪ List β} {A : Set α}

/-- The words of length `n` that encode an instance under `enc`. -/
@[expose] def encodes (enc : α ↪ List β) (n : ℕ) : Set (Fin n → β) :=
  {x | ∃ a, enc a = List.ofFn x}

open scoped Classical in
/-- Whether the word `x : Fin n → β` encodes a member of `A` under `enc`. -/
noncomputable def encodesMember (enc : α ↪ List β) (A : Set α) (n : ℕ) : (Fin n → β) → Bool :=
  fun x => decide (∃ a ∈ A, enc a = List.ofFn x)

/-- On a word `x` encoding `a`, `encodesMember enc A n x` is `true` iff `a ∈ A`. -/
theorem encodesMember_eq_true_iff {x : Fin n → β} {a : α}
    (ha : enc a = List.ofFn x) : encodesMember enc A n x = true ↔ a ∈ A := by
  rw [encodesMember, @decide_eq_true_iff _ (Classical.propDecidable _)]
  exact ⟨fun ⟨b, hb, hba⟩ => enc.injective (hba.trans ha.symm) ▸ hb, fun h => ⟨a, h, ha⟩⟩

/-- A language agreeing with `encodesMember enc A` on encoded words contains exactly the encodings
of the members of `A`. -/
theorem mem_iff_of_slice_eq_encodesMember {L : Language β}
    (h : ∀ n, ∀ x ∈ encodes enc n, L.slice n x = encodesMember enc A n x) (a : α) :
    a ∈ A ↔ enc a ∈ L := by
  have hx : List.ofFn (fun i : Fin (enc a).length => (enc a)[i]) = enc a := List.ofFn_getElem
  rw [← encodesMember_eq_true_iff hx.symm, ← h _ _ ⟨a, hx.symm⟩, Language.slice_eq_true_iff, hx]

end Encoded

end Language
