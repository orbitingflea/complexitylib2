/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.BinarySearch
public import CslibFrontier.DataStructure.BTree.Comparisons.Query
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence

/-!
# Comparison costs of B-tree queries with binary in-node search

This file instantiates `lookupBinM` and `rankBinM` in CSLib's query-complexity framework, at
`FreeM (LEQuery α)` with the comparison query `LEQuery.ask` and the trivial `visit := pure ()`,
as `Comparisons.Query` does for the linear scans. Every key comparison is a query.

Bisecting `n` keys takes at most `⌈log₂ (n + 1)⌉` comparisons, on any list and under any
oracle (`countQueries_slotBinM_le`). A node of a well-formed tree of minimum degree `t` holds at
most `2 * t - 1` keys, so the search costs at most `⌈log₂ (2 * t)⌉` comparisons per node. Rank
needs nothing more; lookup spends one further comparison to test the key found for equality.
`le_mul_height_of_node_le` sums the per-node cost along the descent. The bounds hold for every
oracle, since the shape of the tree does not depend on the answers. Under `orderOracle` the
programs evaluate to the pure `lookupBin` and `rankBin`, which are `lookup` and `rank` on trees
with sorted entries (`lookupBin_eq_lookup`, `rankBin_eq_rank`).

The linear scans of `Comparisons.Query` are bounded by `2 * t * height` comparisons, so
bisection replaces the factor `2 * t` by `⌈log₂ (2 * t)⌉ + 1`. The statements are original to
this development; no lower bound is proved here.

## Main definitions

* `lookupBinQ`, `rankBinQ`: lookup and rank by binary in-node search, counting comparisons.

## Main results

* `countQueries_slotBinM_le`: bisecting `n` keys makes at most `⌈log₂ (n + 1)⌉` comparisons.
* `countQueries_lookupBinQ_le`, `lookupBinQ_upperBound`: `lookupBinQ` makes at most
  `(⌈log₂ (2 * t)⌉ + 1) * height` comparisons on a well-formed tree.
* `countQueries_rankBinQ_le`, `rankBinQ_upperBound`: `rankBinQ` makes at most
  `⌈log₂ (2 * t)⌉ * height` comparisons on a well-formed tree.
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BTree

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- Lookup by binary in-node search, issuing one query per key comparison. -/
def lookupBinQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option β) :=
  lookupBinM LEQuery.ask (pure ()) k tr

/-- `lookupBinQ` is the `FreeM (LEQuery α)` instantiation of `lookupBinM`. -/
theorem lookupBinQ_def (k : α) : lookupBinQ k tr = lookupBinM LEQuery.ask (pure ()) k tr := (rfl)

/-- Rank by binary in-node search, issuing one query per key comparison. -/
def rankBinQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) ℕ :=
  rankBinM LEQuery.ask (pure ()) k tr

/-- `rankBinQ` is the `FreeM (LEQuery α)` instantiation of `rankBinM`. -/
theorem rankBinQ_def (k : α) : rankBinQ k tr = rankBinM LEQuery.ask (pure ()) k tr := (rfl)

section Transfer

variable [LinearOrder α]

/-- Under the order's oracle, `lookupBinQ` evaluates to the pure `lookupBin`. -/
@[simp] theorem eval_lookupBinQ (k : α) :
    (lookupBinQ k tr).eval orderOracle = lookupBin k tr := by
  simpa [lookupBinQ, lookupBin_def] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_lookupBinM LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `rankBinQ` evaluates to the pure `rankBin`. -/
@[simp] theorem eval_rankBinQ (k : α) : (rankBinQ k tr).eval orderOracle = rankBin k tr := by
  simpa [rankBinQ, rankBin_def] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval orderOracle).map_rankBinM LEQuery.ask (pure ()) k tr)

end Transfer

/-! ### Comparison counts -/

variable (oracle : {ι : Type} → LEQuery α ι → ι)

/-- The within-node binary search makes at most `⌈log₂ (n + 1)⌉` comparisons on `n` keys, sorted
or not, under every oracle. -/
theorem countQueries_slotBinM_le (k : α) (rest : List (Triple α β)) :
    (slotBinM LEQuery.ask k rest).countQueries oracle ≤ Nat.clog 2 (rest.length + 1) := by
  induction hn : rest.length using Nat.strong_induction_on generalizing rest with
  | _ n ih =>
    rcases rest with _ | ⟨e, l⟩
    · simp
    · simp only [List.length_cons] at hn
      have h₁ := ih _ (by simp only [List.length_take, List.length_cons]; omega)
        ((e :: l).take ((l.length + 1) / 2)) rfl
      have h₂ := ih _ (by simp only [List.length_drop, List.length_cons]; omega)
        ((e :: l).drop ((l.length + 1) / 2 + 1)) rfl
      simp only [slotBinM_cons, bind_pure_comp, FreeM.countQueries_bind, FreeM.countQueries_lift,
        ↓FreeM.countQueries_ite, FreeM.eval_lift, FreeM.countQueries_map]
      have ht := Nat.clog_two_lt_clog_two_of_le_half (m := n + 1)
        (k := ((e :: l).take ((l.length + 1) / 2)).length + 1) (by omega)
        (by simp only [List.length_take, List.length_cons]; omega)
      have hd := Nat.clog_two_lt_clog_two_of_le_half (m := n + 1)
        (k := ((e :: l).drop ((l.length + 1) / 2 + 1)).length + 1) (by omega)
        (by simp only [List.length_drop, List.length_cons]; omega)
      split <;> omega

/-- The within-node binary search of a node with at most `2 * t - 1` keys makes at most
`⌈log₂ (2 * t)⌉` comparisons. -/
private theorem countQueries_slotBinM_le_of_length_le (ht : 0 < t) (k : α)
    {rest : List (Triple α β)} (hl : rest.length ≤ 2 * t - 1) :
    (slotBinM LEQuery.ask k rest).countQueries oracle ≤ Nat.clog 2 (2 * t) :=
  (countQueries_slotBinM_le oracle k rest).trans (Nat.clog_mono_right 2 (by omega))

/-- Lookup by binary in-node search at a node makes one comparison beyond the within-node search
and what it makes in the child it descends into. -/
private theorem countQueries_lookupBinQ_node_le (ht : 0 < t) (k : α) (first : BTree α β)
    {rest : List (Triple α β)} (hl : rest.length ≤ 2 * t - 1) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (lookupBinQ k c).countQueries oracle ≤ B) :
    (lookupBinQ k (node first rest)).countQueries oracle ≤ Nat.clog 2 (2 * t) + 1 + B := by
  have hs := countQueries_slotBinM_le_of_length_le oracle ht k hl
  simp only [lookupBinQ] at hB ⊢
  rw [lookupBinM_node]
  simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, zero_add]
  generalize (slotBinM LEQuery.ask k rest).eval oracle = i
  rcases hc : (node first rest).children[i]? with _ | c
  · rcases hi : rest[i]? with _ | e <;> simp <;> grind
  · have := hB c (List.mem_of_getElem? hc)
    rcases hi : rest[i]? with _ | e <;> simp <;> grind

/-- Rank by binary in-node search at a node makes no comparison beyond the within-node search
and what it makes in the child it descends into. -/
private theorem countQueries_rankBinQ_node_le (ht : 0 < t) (k : α) (first : BTree α β)
    {rest : List (Triple α β)} (hl : rest.length ≤ 2 * t - 1) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (rankBinQ k c).countQueries oracle ≤ B) :
    (rankBinQ k (node first rest)).countQueries oracle ≤ Nat.clog 2 (2 * t) + B := by
  have hs := countQueries_slotBinM_le_of_length_le oracle ht k hl
  simp only [rankBinQ] at hB ⊢
  rw [rankBinM_node]
  simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, zero_add]
  generalize (slotBinM LEQuery.ask k rest).eval oracle = i
  rcases hc : (node first rest).children[i]? with _ | c
  · simp
    omega
  · have := hB c (List.mem_of_getElem? hc)
    simp
    omega

variable [LinearOrder α]

/-- Lookup by binary in-node search in a well-formed tree makes at most `⌈log₂ (2 * t)⌉ + 1`
comparisons per level, under every oracle. -/
theorem countQueries_lookupBinQ_le (h : IsWF t tr) (k : α) :
    (lookupBinQ k tr).countQueries oracle ≤ (Nat.clog 2 (2 * t) + 1) * tr.height :=
  le_mul_height_of_node_le (by simp [lookupBinQ, lookupBinM_leaf])
    (fun first _ _ hl hB =>
      countQueries_lookupBinQ_node_le oracle (by have := h.two_le; omega) k first hl hB)
    h.rootKeys_le h.occupied_of_mem_children

/-- Rank by binary in-node search in a well-formed tree makes at most `⌈log₂ (2 * t)⌉`
comparisons per level, under every oracle. -/
theorem countQueries_rankBinQ_le (h : IsWF t tr) (k : α) :
    (rankBinQ k tr).countQueries oracle ≤ Nat.clog 2 (2 * t) * tr.height :=
  le_mul_height_of_node_le (by simp [rankBinQ, rankBinM_leaf])
    (fun first _ _ hl hB =>
      countQueries_rankBinQ_node_le oracle (by have := h.two_le; omega) k first hl hB)
    h.rootKeys_le h.occupied_of_mem_children

end Comparisons

/-! ### Upper bounds over all oracles -/

section UpperBounds

variable {α β : Type} [LinearOrder α] {t : ℕ}

/-- Lookup by binary in-node search makes at most `⌈log₂ (2 * t)⌉ + 1` comparisons at each of at
most `height` nodes. -/
theorem lookupBinQ_upperBound :
    UpperBound (fun p : WFInput α β t => lookupBinQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => (Nat.clog 2 (2 * t) + 1) * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_lookupBinQ_le oracle p.property p.val.2

/-- Rank by binary in-node search makes at most `⌈log₂ (2 * t)⌉` comparisons at each of at most
`height` nodes. -/
theorem rankBinQ_upperBound :
    UpperBound (fun p : WFInput α β t => rankBinQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => Nat.clog 2 (2 * t) * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_rankBinQ_le oracle p.property p.val.2

end UpperBounds

end Cslib.DataStructure.BTree
