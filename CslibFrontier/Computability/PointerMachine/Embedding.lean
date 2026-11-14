/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Basic

/-!
# Injective heap embeddings

An embedding preserves registers and all source records while allowing extra target records.
Its address map is injective only on the allocated source heap. Creating a record extends that
map at the fresh source address, leaving all old addresses unchanged.

## Main definitions

* `Record.relabel`: transport a record's pointers along an address map.
* `State.Embeds`: an injective embedding of one valid heap into another.

## Main results

* `State.Embeds.next`: embeddings preserve control decisions, including pointer equality.
* `State.Embeds.effect`: every instruction preserves an embedding, extending its address map
  on allocation.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- Rename a record's pointers without changing its data. -/
@[expose] def Record.relabel (f : ℕ → ℕ) (n : Record M L) : Record M L :=
  { n with ptr := fun r => (n.ptr r).map f }

/-- A valid source heap embedded in a valid target heap, with identical control and data.
The target may have additional records; the map is constrained only on allocated source
addresses. -/
structure State.Embeds (f : ℕ → ℕ) (x y : State M L) : Prop where
  /-- Source pointers specify records. -/
  source_valid : x.Valid
  /-- Target pointers specify records. -/
  target_valid : y.Valid
  /-- Control is unchanged. -/
  pc : x.pc = y.pc
  /-- Data registers are unchanged. -/
  data : x.data = y.data
  /-- Pointer registers are transported by the map. -/
  ptr : ∀ r, y.ptr r = (x.ptr r).map f
  /-- Distinct allocated source addresses remain distinct. -/
  injective : ∀ ⦃a b⦄, a < x.heap.length → b < x.heap.length → f a = f b → a = b
  /-- Allocated source addresses have allocated images. -/
  bound : ∀ ⦃a⦄, a < x.heap.length → f a < y.heap.length
  /-- Every source record occurs at its image with its pointers transported. -/
  heap : ∀ ⦃a⦄, a < x.heap.length → y.heap[f a]? = (x.heap[a]?).map (Record.relabel f)

namespace State.Embeds

variable {f : ℕ → ℕ} {x y : State M L} (h : Embeds f x y)

include h

/-- Changing both control labels preserves an embedding. -/
theorem with_pc (p : ℕ) : Embeds f { x with pc := p } { y with pc := p } :=
  { h with pc := rfl }

/-- Embeddings preserve the record obtained by following any register. -/
theorem deref (r : Fin L.ptrRegs) : y.deref r = (x.deref r).map (Record.relabel f) := by
  simp only [State.deref, h.ptr]
  cases hp : x.ptr r with
  | none => rfl
  | some a =>
    simpa using h.heap (h.source_valid.1 r a hp)

/-- Pointer equality in registers is both preserved and reflected. -/
theorem ptr_eq_iff (r s : Fin L.ptrRegs) : y.ptr r = y.ptr s ↔ x.ptr r = x.ptr s := by
  rw [h.ptr, h.ptr]
  cases hr : x.ptr r <;> cases hs : x.ptr s <;> simp only [Option.map_none,
    Option.map_some, Option.some.injEq, reduceCtorEq]
  next a b =>
    exact ⟨h.injective (h.source_valid.1 r a hr) (h.source_valid.1 s b hs), congrArg f⟩

/-- The next control label is unchanged by a heap embedding. -/
theorem next (i : Instr M L) : i.next x = i.next y := by
  cases i <;> simp [Instr.next, h.pc, h.data, h.ptr_eq_iff]

private theorem setPtr (r : Fin L.ptrRegs) (p : Pointer)
    (hp : ∀ a, p = some a → a < x.heap.length) :
    Embeds f (x.setPtr r p) (y.setPtr r (p.map f)) where
  source_valid := by
    refine ⟨fun s a hs => ?_, h.source_valid.2⟩
    simp only [State.setPtr, Function.update_apply] at hs ⊢
    split_ifs at hs <;> first | exact hp a hs | exact h.source_valid.1 s a hs
  target_valid := by
    refine ⟨fun s a hs => ?_, h.target_valid.2⟩
    simp only [State.setPtr, Function.update_apply] at hs ⊢
    split_ifs at hs
    · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact h.bound (hp b hb)
    · exact h.target_valid.1 s a hs
  pc := h.pc
  data := h.data
  ptr s := by
    simp only [State.setPtr, Function.update_apply, h.ptr]
    split_ifs <;> rfl
  injective := h.injective
  bound := h.bound
  heap := h.heap

private theorem setData (s : Fin L.dataRegs) (v : M.Value) :
    Embeds f (x.setData s v) (y.setData s v) :=
  { h with data := by simp [State.setData, h.data] }

private theorem modify (r : Fin L.ptrRegs) (g g' : Record M L → Record M L)
    (hx : (x.modify r g).Valid) (hy : (y.modify r g').Valid)
    (hg : ∀ n ∈ x.heap, g' (n.relabel f) = (g n).relabel f) :
    Embeds f (x.modify r g) (y.modify r g') where
  source_valid := hx
  target_valid := hy
  pc := by simp only [State.modify]; split <;> simp_all [h.ptr, h.pc]
  data := by simp [h.data]
  ptr s := by simp [h.ptr]
  injective := by simpa using h.injective
  bound := by simpa using h.bound
  heap := by
    intro a ha
    simp only [State.length_heap_modify] at ha
    simp only [State.modify, h.ptr]
    cases hp : x.ptr r with
    | none => exact h.heap ha
    | some b =>
      have hb := h.source_valid.1 r b hp
      have heq : f b = f a ↔ b = a := ⟨h.injective hb ha, congrArg f⟩
      simp only [Option.map_some, List.getElem?_modify, heq, h.heap ha]
      by_cases hba : b = a
      · subst b
        cases hn : x.heap[a]? with
        | none => simp
        | some n => simp [hg n (List.mem_of_getElem? hn)]
      · simp [hba]

private theorem relabel_congr {g : ℕ → ℕ}
    (hg : ∀ a, a < x.heap.length → g a = f a) {n : Record M L} (hn : n ∈ x.heap) :
    n.relabel g = n.relabel f := by
  change { n with ptr := fun r => (n.ptr r).map g } =
    { n with ptr := fun r => (n.ptr r).map f }
  congr 1
  funext r
  exact Option.map_congr fun a ha => hg a (h.source_valid.2 n hn r a ha)

private theorem create (r : Fin L.ptrRegs) :
    ∃ g, (∀ a, a < x.heap.length → g a = f a) ∧
      Embeds g ((Instr.create r).effect x) ((Instr.create r).effect y) := by
  let g := Function.update f x.heap.length y.heap.length
  have hg (a) (ha : a < x.heap.length) : g a = f a :=
    Function.update_of_ne (Nat.ne_of_lt ha) _ _
  have hfresh : g x.heap.length = y.heap.length := Function.update_self ..
  refine ⟨g, hg, ?_⟩
  refine {
    source_valid := Instr.effect_valid h.source_valid
    target_valid := Instr.effect_valid h.target_valid
    pc := h.pc
    data := h.data
    ptr := ?_
    injective := ?_
    bound := ?_
    heap := ?_ }
  · intro s
    simp only [Instr.effect, State.setPtr, Function.update_apply]
    split_ifs with hs
    · simp [hfresh]
    · exact (h.ptr s).trans (Option.map_congr fun a ha => hg a (h.source_valid.1 s a ha)).symm
  · intro a b ha hb hab
    simp only [Instr.effect, List.length_append, List.length_singleton] at ha hb
    by_cases ha' : a < x.heap.length <;> by_cases hb' : b < x.heap.length
    · exact h.injective ha' hb' (by simpa only [hg a ha', hg b hb'] using hab)
    · have hb'' : b = x.heap.length := by omega
      rw [hb'', hfresh, hg a ha'] at hab
      have := h.bound ha'
      omega
    · have ha'' : a = x.heap.length := by omega
      rw [ha'', hfresh, hg b hb'] at hab
      have := h.bound hb'
      omega
    · omega
  · intro a ha
    simp only [Instr.effect, List.length_append, List.length_singleton] at ha ⊢
    by_cases ha' : a < x.heap.length
    · rw [hg a ha']
      exact Nat.lt_succ_of_lt (h.bound ha')
    · have : a = x.heap.length := by omega
      simp [this, hfresh]
  · intro a ha
    simp only [Instr.effect, List.length_append, List.length_singleton] at ha
    change (y.heap ++ [Record.blank])[g a]? =
      ((x.heap ++ [Record.blank])[a]?).map (Record.relabel g)
    by_cases ha' : a < x.heap.length
    · rw [hg a ha']
      rw [List.getElem?_append_left (h.bound ha'), List.getElem?_append_left ha', h.heap ha']
      cases hn : x.heap[a]? with
      | none => rfl
      | some n => simp [h.relabel_congr hg (List.mem_of_getElem? hn)]
    · have : a = x.heap.length := by omega
      simp [this, hfresh, Record.relabel, Record.blank]

/-- Every instruction preserves heap embeddings. Allocation extends the map at the fresh
source address and leaves its values on all previously allocated source addresses unchanged. -/
theorem effect (i : Instr M L) :
    ∃ g, (∀ a, a < x.heap.length → g a = f a) ∧ Embeds g (i.effect x) (i.effect y) := by
  cases i with
  | create r => exact h.create r
  | null r => exact ⟨f, fun _ _ => rfl, h.setPtr r none (by simp)⟩
  | movePtr r r' =>
    refine ⟨f, fun _ _ => rfl, ?_⟩
    simpa only [Instr.effect, h.ptr] using h.setPtr r (x.ptr r') (h.source_valid.1 r')
  | moveData s s' =>
    refine ⟨f, fun _ _ => rfl, ?_⟩
    simpa only [Instr.effect, h.data] using h.setData s (x.data s')
  | op o s s₁ s₂ =>
    refine ⟨f, fun _ _ => rfl, ?_⟩
    simpa only [Instr.effect, h.data] using h.setData s (M.evalOp o (x.data s₁) (x.data s₂))
  | loadPtr r field base =>
    refine ⟨f, fun _ _ => rfl, ?_⟩
    simp only [Instr.effect, h.deref]
    cases hn : x.deref base with
    | none => exact h
    | some n =>
      obtain ⟨a, _, ha⟩ := State.deref_eq_some.mp hn
      exact h.setPtr r (n.ptr field) (h.source_valid.2 n (List.mem_of_getElem? ha) field)
  | loadData s field base =>
    refine ⟨f, fun _ _ => rfl, ?_⟩
    simp only [Instr.effect, h.deref]
    cases hn : x.deref base with
    | none => exact h
    | some n => exact h.setData s (n.data field)
  | storePtr field base r =>
    refine ⟨f, fun _ _ => rfl, h.modify base _ _
      (Instr.effect_valid (i := .storePtr field base r) h.source_valid)
      (Instr.effect_valid (i := .storePtr field base r) h.target_valid) ?_⟩
    intro n _
    simp only [Record.relabel, h.ptr]
    congr 1
    funext s
    simp only [Function.update_apply]
    split_ifs <;> rfl
  | storeData field base s =>
    refine ⟨f, fun _ _ => rfl, h.modify base _ _
      (Instr.effect_valid (i := .storeData field base s) h.source_valid)
      (Instr.effect_valid (i := .storeData field base s) h.target_valid) ?_⟩
    intro n _
    simp [Record.relabel, h.data]
  | goto _ => exact ⟨f, fun _ _ => rfl, h⟩
  | ifPtrEq _ _ _ => exact ⟨f, fun _ _ => rfl, h⟩
  | ifTest _ _ _ _ => exact ⟨f, fun _ _ => rfl, h⟩
  | halt => exact ⟨f, fun _ _ => rfl, h⟩

end State.Embeds

end Cslib.PointerMachine
