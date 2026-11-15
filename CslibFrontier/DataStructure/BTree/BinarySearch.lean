/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Rank

/-!
# Binary in-node search in classic B-trees

`lookupM` and `rankM` scan the keys of a node from the left. This file gives the variant that
searches a node by bisection: `slotBinM` probes the middle key and continues in the keys before
or after it, and `lookupBinM` and `rankBinM` use the position it finds to stop at a key or to
choose the child to descend into. The trees are those of [CLRS2009], Chapter 18; the bisection
and the proofs here are original to this development.

As in `Lookup`, each operation is defined once over a monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, and the pure operations are the
`Id` instantiations. The node's keys are held in a list, so bisection saves comparisons and
nothing else: walking to the middle of the list is uncharged in the node-visit and comparison
cost models. Costs are stated in `Comparisons.BinarySearch`.

Bisection is correct only on sorted keys. `slotBin_eq_slot` shows that it finds the position
that the linear `slot` finds when the keys are strictly increasing, and `lookupBin_eq_lookup`
and `rankBin_eq_rank` transfer this to trees with sorted entries, in particular well-formed
ones. On other inputs the binary operations are unspecified.

The definitions use well-founded recursion and are not exposed. `slotBinM_nil` and
`slotBinM_cons`, `lookupBinM_leaf` and `lookupBinM_node`, and `rankBinM_leaf` and
`rankBinM_node` are their equations; `simp` with them evaluates the operations on concrete
trees.

## Main definitions

* `slotBinM`, `slotBin`: within-node binary search for the first key not below the query.
* `lookupBinM`, `lookupBin`: lookup using `slotBinM` at each node.
* `rankBinM`, `rankBin`: rank using `slotBinM` at each node.

## Main results

* `Cslib.IsMonadHom.map_slotBinM`, `Cslib.IsMonadHom.map_lookupBinM`,
  `Cslib.IsMonadHom.map_rankBinM`: a monad morphism commutes with the operations.
* `slotBin_eq_slot`: on strictly increasing keys, binary and linear in-node search agree.
* `lookupBin_eq_lookup`, `rankBin_eq_rank`: on a tree with sorted entries, lookup and rank by
  binary in-node search are `lookup` and `rank`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
-/

public section

universe w

namespace Cslib.DataStructure.BTree

/-- Induction on B-trees with one hypothesis for all children of a node. -/
private theorem induction_children {α β : Type} {motive : BTree α β → Prop} (leaf : motive .leaf)
    (node : ∀ (first : BTree α β) (rest : List (Triple α β)),
      (∀ c ∈ (node first rest).children, motive c) → motive (.node first rest)) :
    ∀ tr, motive tr := by
  intro tr
  induction tr with
  | leaf => exact leaf
  | node first rest ih₁ ih₂ =>
    refine node first rest fun c hc => ?_
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    exacts [ih₁, ih₂ e he]

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Within-node binary search: probe the middle key, continue in the keys before it when the
query is not above it, and in the keys after it otherwise. On sorted keys the result is the
position of the first key not below `k`, as for `slotM`. One comparison per probe. -/
def slotBinM (le : α → α → m Bool) (k : α) (rest : List (Triple α β)) : m ℕ :=
  match h : rest[rest.length / 2]? with
  | none => pure 0
  | some e => do
    if ← le k e.1 then
      slotBinM le k (rest.take (rest.length / 2))
    else
      return (← slotBinM le k (rest.drop (rest.length / 2 + 1))) + (rest.length / 2 + 1)
termination_by rest.length
decreasing_by
  all_goals
    have := (List.getElem?_eq_some_iff.1 h).1
    simp only [List.length_take, List.length_drop]
    omega

/-- Lookup with binary in-node search. `visit` fires once at each node. The search finds the
position `i` of the first key not below `k`, tests that key for equality with one more
comparison, and otherwise descends into the child before it, which is the `i`-th child when the
first child is counted as the zeroth. -/
def lookupBinM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m (Option β)
  | .leaf => pure none
  | .node first rest => do
    visit
    let i ← slotBinM le k rest
    let hit ← (match rest[i]? with
      | some e => le e.1 k
      | none => pure false)
    if hit then
      pure (rest[i]?.map Triple.val)
    else
      match _ : (node first rest).children[i]? with
      | some c => lookupBinM le visit k c
      | none => pure none
termination_by tr => sizeOf tr
decreasing_by exact sizeOf_lt_of_mem_children (List.mem_of_getElem? ‹_›)

/-- Rank with binary in-node search. `visit` fires once at each node. The search finds the
position `i` of the first key not below `k`; the `i` children before the `i`-th child, each
followed by a separator, hold only keys below `k`, and the search descends into the `i`-th
child, counting the first child as the zeroth. Sizes of subtrees are uncharged client
computation, as in `rankM`. -/
def rankBinM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m ℕ
  | .leaf => pure 0
  | .node first rest => do
    visit
    let i ← slotBinM le k rest
    let below ← (match _ : (node first rest).children[i]? with
      | some c => rankBinM le visit k c
      | none => pure 0)
    return (((node first rest).children.take i).map (·.size + 1)).sum + below
termination_by tr => sizeOf tr
decreasing_by exact sizeOf_lt_of_mem_children (List.mem_of_getElem? ‹_›)

/-- The search in a node without keys stops at position zero, without a comparison. -/
@[simp] theorem slotBinM_nil (le : α → α → m Bool) (k : α) :
    slotBinM le k ([] : List (Triple α β)) = pure 0 := by
  rw [slotBinM]
  rfl

/-- The search in a node with keys probes the middle key and continues in the keys before it or
after it. -/
theorem slotBinM_cons (le : α → α → m Bool) (k : α) (e : Triple α β) (l : List (Triple α β)) :
    slotBinM le k (e :: l) = (do
      if ← le k ((e :: l)[(l.length + 1) / 2]'(by simp only [List.length_cons]; omega)).1 then
        slotBinM le k ((e :: l).take ((l.length + 1) / 2))
      else
        return (← slotBinM le k ((e :: l).drop ((l.length + 1) / 2 + 1))) +
          ((l.length + 1) / 2 + 1)) := by
  rw [slotBinM]
  split
  next h =>
    have := List.getElem?_eq_none_iff.1 h
    simp only [List.length_cons] at this
    omega
  next e' h =>
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 h
    rfl

/-- Lookup in the empty tree fails, without a visit. -/
theorem lookupBinM_leaf (le : α → α → m Bool) (visit : m Unit) (k : α) :
    lookupBinM le visit k (.leaf : BTree α β) = pure none := by
  rw [lookupBinM]

/-- Lookup at a node: visit it, search its keys, test the key found for equality, and otherwise
descend into the child before it. -/
theorem lookupBinM_node (le : α → α → m Bool) (visit : m Unit) (k : α) (first : BTree α β)
    (rest : List (Triple α β)) :
    lookupBinM le visit k (.node first rest) = (do
      visit
      let i ← slotBinM le k rest
      let hit ← (match rest[i]? with
        | some e => le e.1 k
        | none => pure false)
      if hit then
        pure (rest[i]?.map Triple.val)
      else
        match (node first rest).children[i]? with
        | some c => lookupBinM le visit k c
        | none => pure none) := by
  rw [lookupBinM]
  refine bind_congr fun _ => bind_congr fun i => bind_congr fun hit => ?_
  split
  · rfl
  · split <;> split <;> simp_all

/-- Rank in the empty tree is zero, without a visit. -/
theorem rankBinM_leaf (le : α → α → m Bool) (visit : m Unit) (k : α) :
    rankBinM le visit k (.leaf : BTree α β) = pure 0 := by
  rw [rankBinM]

/-- Rank at a node: visit it, search its keys, count the children and separators before the
position found, and descend into the child at that position. -/
theorem rankBinM_node (le : α → α → m Bool) (visit : m Unit) (k : α) (first : BTree α β)
    (rest : List (Triple α β)) :
    rankBinM le visit k (.node first rest) = (do
      visit
      let i ← slotBinM le k rest
      let below ← (match (node first rest).children[i]? with
        | some c => rankBinM le visit k c
        | none => pure 0)
      return (((node first rest).children.take i).map (·.size + 1)).sum + below) := by
  rw [rankBinM]
  refine bind_congr fun _ => bind_congr fun i => ?_
  congr 1
  split <;> split <;> simp_all

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the within-node binary search. -/
theorem _root_.Cslib.IsMonadHom.map_slotBinM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (k : α) (rest : List (Triple α β)) :
    f (slotBinM le k rest) = slotBinM (fun a b => f (le a b)) k rest := by
  induction hn : rest.length using Nat.strong_induction_on generalizing rest with
  | _ n ih =>
    rcases rest with _ | ⟨e, l⟩
    · simp [hf.map_pure]
    · simp only [List.length_cons] at hn
      simp [slotBinM_cons, hf.map_bind, hf.map_pure, apply_ite f,
        ih _ (by simp only [List.length_take]; omega) ((e :: l).take ((l.length + 1) / 2)) rfl,
        ih _ (by simp only [List.length_drop]; omega) (l.drop ((l.length + 1) / 2)) rfl]

/-- A monad morphism commutes with lookup by binary in-node search. -/
theorem _root_.Cslib.IsMonadHom.map_lookupBinM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (lookupBinM le visit k tr) = lookupBinM (fun a b => f (le a b)) (f visit) k tr := by
  induction tr using induction_children with
  | leaf => simp [lookupBinM_leaf, hf.map_pure]
  | node first rest ih =>
    simp only [lookupBinM_node, hf.map_bind, hf.map_slotBinM]
    refine bind_congr fun _ => bind_congr fun i => ?_
    rcases hc : (node first rest).children[i]? with _ | c
    · rcases hi : rest[i]? with _ | e <;> simp [hf.map_pure, apply_ite f]
    · have := ih c (List.mem_of_getElem? hc)
      rcases hi : rest[i]? with _ | e <;> simp [hf.map_pure, apply_ite f, this]

/-- A monad morphism commutes with rank by binary in-node search. -/
theorem _root_.Cslib.IsMonadHom.map_rankBinM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (rankBinM le visit k tr) = rankBinM (fun a b => f (le a b)) (f visit) k tr := by
  induction tr using induction_children with
  | leaf => simp [rankBinM_leaf, hf.map_pure]
  | node first rest ih =>
    simp only [rankBinM_node, hf.map_bind, hf.map_slotBinM]
    refine bind_congr fun _ => bind_congr fun i => ?_
    rcases hc : (node first rest).children[i]? with _ | c
    · simp [hf.map_pure]
    · simp [hf.map_pure, ih c (List.mem_of_getElem? hc)]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Pure within-node binary search: the `Id` instantiation of `slotBinM`. -/
def slotBin (k : α) (rest : List (Triple α β)) : ℕ := Id.run (slotBinM leI k rest)

/-- Pure lookup by binary in-node search: the `Id` instantiation of `lookupBinM`. -/
def lookupBin (k : α) (tr : BTree α β) : Option β := Id.run (lookupBinM leI (pure ()) k tr)

/-- Pure rank by binary in-node search: the `Id` instantiation of `rankBinM`. -/
def rankBin (k : α) (tr : BTree α β) : ℕ := Id.run (rankBinM leI (pure ()) k tr)

/-- `slotBin` is the `Id` instantiation of `slotBinM`. -/
theorem slotBin_def (k : α) (rest : List (Triple α β)) :
    slotBin k rest = Id.run (slotBinM leI k rest) := (rfl)

/-- `lookupBin` is the `Id` instantiation of `lookupBinM`. -/
theorem lookupBin_def (k : α) : lookupBin k tr = Id.run (lookupBinM leI (pure ()) k tr) := (rfl)

/-- `rankBin` is the `Id` instantiation of `rankBinM`. -/
theorem rankBin_def (k : α) : rankBin k tr = Id.run (rankBinM leI (pure ()) k tr) := (rfl)

/-- Lookup by binary in-node search in the empty tree fails. -/
@[simp] theorem lookupBin_leaf (k : α) : lookupBin k (.leaf : BTree α β) = none := by
  simp [lookupBin, lookupBinM_leaf]

/-- Lookup by binary in-node search at a node: stop at the key found by the search when it
equals the query, and otherwise descend into the child before it. -/
theorem lookupBin_node (k : α) (first : BTree α β) (rest : List (Triple α β)) :
    lookupBin k (.node first rest) =
      if rest[slotBin k rest]?.any (fun e => decide (e.1 ≤ k)) then
        rest[slotBin k rest]?.map Triple.val
      else (node first rest).children[slotBin k rest]?.bind (lookupBin k) := by
  simp only [lookupBin, slotBin, lookupBinM_node, leI, pure_bind, Id.run_bind]
  repeat' split
  all_goals simp_all [lookupBin]

/-- Rank by binary in-node search in the empty tree is zero. -/
@[simp] theorem rankBin_leaf (k : α) : rankBin k (.leaf : BTree α β) = 0 := by
  simp [rankBin, rankBinM_leaf]

/-- Rank by binary in-node search at a node: the children before the position found by the
search, each with its separator, and the rank in the child at that position. -/
theorem rankBin_node (k : α) (first : BTree α β) (rest : List (Triple α β)) :
    rankBin k (.node first rest) =
      (((node first rest).children.take (slotBin k rest)).map (·.size + 1)).sum +
        ((node first rest).children[slotBin k rest]?.map (rankBin k)).getD 0 := by
  simp only [rankBin, slotBin, rankBinM_node, pure_bind, Id.run_bind]
  rcases hc : (node first rest).children[Id.run (slotBinM leI k rest)]? with _ | c <;>
    simp [rankBin]

/-! ### Agreement with linear search on sorted keys -/

/-- On strictly increasing keys, binary search finds the position that linear search finds. On
other lists it is unspecified. -/
theorem slotBin_eq_slot (k : α) {rest : List (Triple α β)}
    (hs : (rest.map (·.1)).Pairwise (· < ·)) : slotBin k rest = slot k rest := by
  induction hn : rest.length using Nat.strong_induction_on generalizing rest with
  | _ n ih =>
    rcases hrest : rest with _ | ⟨e₀, l⟩
    · simp [slotBin]
    · have hlt : rest.length / 2 < rest.length := by
        rw [hrest, List.length_cons]
        omega
      have hstep : slotBin k rest = if k ≤ rest[rest.length / 2].1 then
          slotBin k (rest.take (rest.length / 2))
          else slotBin k (rest.drop (rest.length / 2 + 1)) + (rest.length / 2 + 1) := by
        subst hrest
        rw [slotBin, slotBinM_cons]
        by_cases hk : k ≤ ((e₀ :: l)[(l.length + 1) / 2]'(by
          simp only [List.length_cons]; omega)).1 <;> simp [slotBin, leI, hk]
      have hsplit : rest = rest.take (rest.length / 2) ++
          rest[rest.length / 2] :: rest.drop (rest.length / 2 + 1) := by
        simp
      rw [← hrest, hstep, slot_eq_findIdx]
      generalize hl₁ : rest.take (rest.length / 2) = l₁ at hsplit ⊢
      generalize hl₂ : rest.drop (rest.length / 2 + 1) = l₂ at hsplit ⊢
      generalize rest[rest.length / 2] = e at hsplit ⊢
      have hlen₁ : l₁.length = rest.length / 2 := by rw [← hl₁, List.length_take]; omega
      have hlen₂ : l₂.length < rest.length := by rw [← hl₂, List.length_drop]; omega
      have hs' := hs
      rw [hsplit] at hs'
      simp only [List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons]
        at hs'
      obtain ⟨h₁, ⟨-, h₂⟩, h₁₂⟩ := hs'
      conv_rhs => rw [hsplit, List.findIdx_append, List.findIdx_cons]
      by_cases hk : k ≤ e.1
      · simp only [hk, decide_true, ↓reduceIte]
        rw [ih _ (by omega) h₁ rfl, slot_eq_findIdx]
        have := List.findIdx_le_length (p := fun e => decide (k ≤ e.1)) (xs := l₁)
        split <;> omega
      · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [ih _ (by omega) h₂ rfl, slot_eq_findIdx]
        have hnone : l₁.findIdx (fun e => decide (k ≤ e.1)) = l₁.length :=
          List.findIdx_eq_length.2 fun x hx => by
            have := h₁₂ x.1 (List.mem_map_of_mem hx) e.1 (by simp)
            simpa using this.trans (lt_of_not_ge hk)
        simp only [hnone, lt_irrefl, ↓reduceIte]
        omega

/-- The keys of a node with sorted entries are strictly increasing. -/
private theorem pairwise_keys_of_isSortedAssoc {first : BTree α β} {rest : List (Triple α β)}
    (h : (node first rest).toList.IsSortedAssoc) : (rest.map (·.1)).Pairwise (· < ·) := by
  have hsub : ∀ rest : List (Triple α β),
      (rest.map fun e => (e.1, e.val)).Sublist (toListRest rest) := fun rest => by
    induction rest with
    | nil => simp
    | cons e rest ih =>
      obtain ⟨k', v, c⟩ := e
      rw [toListRest_cons]
      exact (ih.trans (List.sublist_append_right _ _)).cons_cons _
  have := h.sublist ((hsub rest).trans (List.sublist_append_right _ _))
  simpa [List.isSortedAssoc_iff_pairwise, Function.comp_def] using this

/-- Linear lookup at a node, through the position found by the within-node search. -/
private theorem lookup_node_eq_slot (k : α) (first : BTree α β) (rest : List (Triple α β)) :
    lookup k (.node first rest) =
      if rest[slot k rest]?.any (fun e => decide (e.1 ≤ k)) then
        rest[slot k rest]?.map Triple.val
      else (node first rest).children[slot k rest]?.bind (lookup k) := by
  induction rest generalizing first with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k <;> simp [hk, hk']
    · simp [hk, ih c]

/-- Linear rank at a node, through the position found by the within-node search. -/
private theorem rank_node_eq_slot (k : α) (first : BTree α β) (rest : List (Triple α β)) :
    rank k (.node first rest) =
      (((node first rest).children.take (slot k rest)).map (·.size + 1)).sum +
        ((node first rest).children[slot k rest]?.map (rank k)).getD 0 := by
  induction rest generalizing first with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    by_cases hk : k ≤ k'
    · simp [hk]
    · simp [hk, ih c]
      omega

/-- On a tree with sorted entries, lookup by binary in-node search is lookup. -/
theorem lookupBin_eq_lookup (h : tr.toList.IsSortedAssoc) (k : α) :
    lookupBin k tr = lookup k tr := by
  induction tr using induction_children with
  | leaf => simp
  | node first rest ih =>
    rw [lookupBin_node, lookup_node_eq_slot, slotBin_eq_slot k (pairwise_keys_of_isSortedAssoc h)]
    congr 1
    rcases hc : (node first rest).children[slot k rest]? with _ | c
    · rfl
    · have hmem := List.mem_of_getElem? hc
      simpa using ih c hmem (h.sublist (toList_sublist_of_mem_children hmem))

/-- On a tree with sorted entries, rank by binary in-node search is rank. -/
theorem rankBin_eq_rank (h : tr.toList.IsSortedAssoc) (k : α) : rankBin k tr = rank k tr := by
  induction tr using induction_children with
  | leaf => simp
  | node first rest ih =>
    rw [rankBin_node, rank_node_eq_slot, slotBin_eq_slot k (pairwise_keys_of_isSortedAssoc h)]
    congr 2
    rcases hc : (node first rest).children[slot k rest]? with _ | c
    · rfl
    · have hmem := List.mem_of_getElem? hc
      simpa using ih c hmem (h.sublist (toList_sublist_of_mem_children hmem))

end Pure

end Cslib.DataStructure.BTree
