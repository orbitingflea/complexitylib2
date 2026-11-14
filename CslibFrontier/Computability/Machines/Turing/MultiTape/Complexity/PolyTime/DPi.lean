/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Polynomial-time dependent and canonical-order finite table operations

The types of entries may depend on the table index. Each entry has its own encoding; the encoded
words form an ordinary finite table. Construction, fixed-index lookup and update therefore reuse
the existing finite-table calculus without requiring a decoder for any entry encoding.

For canonical-order `Fin count` tables encoded with `encFinFn` and indices encoded with
`encFinEnum (Fin count)`, construction reuses `ComputableInPolyTime.ofFn` directly via the
definitional identity `encFinFn_apply`, and fixed or computed lookups reuse `List.getD_ofFn` and
`finite_cases` without requiring a default inhabitant on the value type.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.dpi`: construct a dependent finite table.
* `Turing.MultiTapeTM.ComputableInPolyTime.dpi_apply`: read a fixed entry.
* `Turing.MultiTapeTM.ComputableInPolyTime.dpi_update`: replace a fixed entry.
* `Turing.MultiTapeTM.ComputableInPolyTime.finVal`: read `i.val` from `encFinEnum (Fin count)`.
* `Turing.MultiTapeTM.ComputableInPolyTime.ofFn_finFn`,
  `Turing.MultiTapeTM.ComputableInPolyTime.finFn`: convert to `List.ofFn` and construct a
  canonical-order `Fin count` table via `ofFn`.
* `Turing.MultiTapeTM.ComputableInPolyTime.finFn_apply`,
  `Turing.MultiTapeTM.ComputableInPolyTime.finFn_apply'`: fixed and computed index access for
  `encFinFn`.

## References

Extends the finite-table calculus in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α Index : Type} {Value : Index → Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : ∀ i, Value i ↪ List Bool}

/-- Construct a fixed dependent family, retaining the original input for each entry. -/
@[fun_prop]
theorem dpi {values : α → ∀ i, Value i}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input (enc i)) :
    ComputableInPolyTime values input (encDPi enc) :=
  (pi (fun i => (hvalues i).of_enc_eq (encD := encBits)
    (g := fun a => enc i (values a i)) (fun _ => rfl))).of_enc_eq (fun _ => rfl)

/-- Read a fixed dependent-table entry, charging the stored prefix and requiring no default. -/
@[fun_prop]
theorem dpi_apply (enc : ∀ i, Value i ↪ List Bool) (i : Index) :
    ComputableInPolyTime (fun values : ∀ j, Value j => values i)
      (encDPi enc) (enc i) := by
  have htable : ComputableInPolyTime
      (fun values : ∀ j, Value j => fun j => enc j (values j))
      (encDPi enc) (encPi encBits) := of_eq (fun _ => rfl)
  exact ((pi_apply encBits i).comp htable).of_enc_eq (fun _ => rfl)

/-- Update one dependent-table entry while retaining and charging all other entries. -/
@[fun_prop]
theorem dpi_update [DecidableEq Index] {values : α → ∀ i, Value i} {i : Index}
    {value : α → Value i}
    (hvalues : ComputableInPolyTime values input (encDPi enc))
    (hvalue : ComputableInPolyTime value input (enc i)) :
    ComputableInPolyTime (fun a => Function.update (values a) i (value a))
      input (encDPi enc) := by
  apply dpi
  intro j
  by_cases h : j = i
  · subst j
    simpa using hvalue
  · simpa only [Function.update_of_ne h, Function.comp_def] using (dpi_apply enc j).comp hvalues

/-- Reading the underlying natural number `i.val` of `i : Fin count` encoded with
`encFinEnum (Fin count)` is polynomial-time. -/
@[fun_prop]
theorem finVal {count : ℕ} {γ : Type} {encIn : γ ↪ List Bool} {g : γ → Fin count}
    (hg : ComputableInPolyTime g encIn (encFinEnum (Fin count))) :
    ComputableInPolyTime (fun a => (g a).val) encIn encUnary :=
  hg.of_enc_eq fun a => (encFinEnum_fin_apply (g a)).symm

/-- Converting a canonical-order `Fin count → Value` table encoded with `encFinFn count enc` to
`List.ofFn` is polynomial-time. -/
@[fun_prop]
theorem ofFn_finFn {count : ℕ} {Value γ : Type} {enc : Value ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → Fin count → Value}
    (hg : ComputableInPolyTime g encIn (encFinFn count enc)) :
    ComputableInPolyTime (fun a => List.ofFn (g a)) encIn (encList enc) :=
  hg.of_enc_eq fun _ => rfl

/-- Construct a canonical-order `Fin count → Value` table by computing each entry, retaining the
original input in each computation. Reuses `ComputableInPolyTime.ofFn` followed by the definitional
identity `encFinFn_apply`. -/
@[fun_prop]
theorem finFn {count : ℕ} {Value γ : Type} {enc : Value ↪ List Bool}
    {encIn : γ ↪ List Bool} {values : γ → Fin count → Value}
    (hvalues : ∀ i : Fin count, ComputableInPolyTime (fun a => values a i) encIn enc) :
    ComputableInPolyTime values encIn (encFinFn count enc) :=
  (ofFn hvalues).of_enc_eq fun _ => rfl

/-- Read a fixed entry of a canonical-order `Fin count → Value` table, charging the stored prefix
without requiring a default value. Uses `List.getD_ofFn` on the underlying framed list. -/
@[fun_prop]
theorem finFn_apply {count : ℕ} {Value : Type} (enc : Value ↪ List Bool) (i : Fin count) :
    ComputableInPolyTime (fun values : Fin count → Value => values i)
      (encFinFn count enc) enc := by
  classical
  cases isEmpty_or_nonempty Value with
  | inl hempty =>
    let : IsEmpty (Fin count → Value) := ⟨fun values => isEmptyElim (values i)⟩
    exact of_finite _
  | inr hnonempty =>
    have hlist : ComputableInPolyTime (fun values : Fin count → Value => List.ofFn values)
        (encFinFn count enc) (encList enc) := of_eq (fun _ => rfl)
    simpa only [List.getD_ofFn] using
      listGetDWithInput hlist (const i.val) (Classical.choice hnonempty)

/-- Read a computed index of a canonical-order `Fin count → Value` table, charging the index and
stored entries without requiring a default value. -/
theorem finFn_apply' {count : ℕ} {Value γ : Type} {indexEncoding : Fin count ↪ List Bool}
    {enc : Value ↪ List Bool} {encIn : γ ↪ List Bool}
    {values : γ → Fin count → Value} {index : γ → Fin count}
    (hvalues : ComputableInPolyTime values encIn (encFinFn count enc))
    (hindex : ComputableInPolyTime index encIn indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) encIn enc :=
  hindex.finite_cases fun i => (finFn_apply enc i).comp hvalues

end Turing.MultiTapeTM.ComputableInPolyTime
