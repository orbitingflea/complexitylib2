/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeModel
public import CslibFrontierTests.SubconstantParams
public meta import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.StorageNode

/-!
# Multi-Level Subconstant-Redundancy Dictionary Tree Tests

Exercises (reusing schedule fixtures `sublinearRegime`, `sublinearConcentrationReady`, and
`smallDepth3Sched` from `CslibFrontierTests.SubconstantParams`):
1. `SubconstantRedundancy.StorageNode`:
   - executable `#eval` traces of `WaitingList`, `StorageTable` (`Section 5.6` metadata separation
     `locateSlot`), and `rootValPoolCap` conservation (`rootKeyCount_le_rootValPoolCap`);
2. `SubconstantRedundancy.TreeModel`:
   - `SeedAssignment` routing bijections and Section 5.6 `dfsSubtreeMeta` exact descendant coverage
     and node count on depth `3`;
   - end-to-end dictionary trace (`initTree`, `insert`, overwrite, `query`, `delete`, absent
     `delete`) preserving `WellFormed`;
   - `Algorithm 3` (`deleteAndGetQuotient_spec`) and the pure reconstruction/local-splice step of
     `Algorithm 4` under supplied validated seeds (`rehashSubtree` strict locality and
     `wellFormedPadded_rehashSubtree`).
-/

public section

namespace CslibFrontierTests.SubconstantTreeModel

open Cslib
open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SubconstantRedundancy
open CslibFrontierTests.SubconstantParams
open scoped BigOperators Finset

/-! ## 1. Executable Node Storage & Section 5.6 Metadata Separation (`StorageNode`) -/

-- Concrete `#eval` trace of `WaitingList` (`empty`, `push`, `lookup`, `pop`, `remove`).
/-- info: (some 5, some 2, none, (3, 5), none, some 2) -/
#guard_msgs in
#eval!
  let w0 := WaitingList.empty 3 4 2
  let w1 := w0.push ⟨2, by decide⟩ ⟨2, by decide⟩
    (by rw [← w0.card_dom]; simp [w0]) (by simp [w0])
  let w2 := w1.push ⟨3, by decide⟩ ⟨5, by decide⟩
    (by rw [← w1.card_dom]; simp [w1, w0]) (by simp [w1, w0])
  let lk3 := (w2.lookup ⟨3, by decide⟩).map Fin.val
  let lk2 := (w2.lookup ⟨2, by decide⟩).map Fin.val
  let lk0 := (w2.lookup ⟨0, by decide⟩).map Fin.val
  let popped := w2.pop (⟨⟨3, by decide⟩, by simp [w2, w1]⟩)
  let headPair := (popped.1.1.val, popped.1.2.val)
  let afterPop3 := (popped.2.lookup ⟨3, by decide⟩).map Fin.val
  let afterPop2 := (popped.2.lookup ⟨2, by decide⟩).map Fin.val
  (lk3, lk2, lk0, headPair, afterPop3, afterPop2)

-- Concrete `#eval` trace of `StorageTable` separating `StorageTableMeta.locateSlot`
-- (`Section 5.6`) from `(quot, val)` payload slots across `insert`, `overwrite`, and `delete`.
/-- info: (some 0, some (3, 1), some 0, some (3, 2), none, some (1, 0)) -/
#guard_msgs in
#eval!
  let t0 := StorageTable.empty 3 2 (Q := 4) (V := 4) (by decide) (by decide)
  let t1 := t0.insert ⟨5, by decide⟩ (⟨3, by decide⟩, ⟨1, by decide⟩)
    (by simp [t0]) (by simp [t0])
  let t2 := t1.insert ⟨2, by decide⟩ (⟨1, by decide⟩, ⟨0, by decide⟩)
    (by simp [t1, t0]) (by simp [t1, t0])
  let slotBefore := (t2.tableMeta.locateSlot ⟨5, by decide⟩).map Fin.val
  let qBefore := (t2.query ⟨5, by decide⟩).map fun p => (p.1.val, p.2.val)
  let t3 := t2.overwrite ⟨5, by decide⟩ (⟨3, by decide⟩, ⟨2, by decide⟩)
    (by simp [t2, t1])
  let slotAfter := (t3.tableMeta.locateSlot ⟨5, by decide⟩).map Fin.val
  let qAfter := (t3.query ⟨5, by decide⟩).map fun p => (p.1.val, p.2.val)
  let t4 := t3.delete ⟨5, by decide⟩
  let qDel := (t4.query ⟨5, by decide⟩).map fun p => (p.1.val, p.2.val)
  let qRem := (t4.query ⟨2, by decide⟩).map fun p => (p.1.val, p.2.val)
  (slotBefore, qBefore, slotAfter, qAfter, qDel, qRem)

-- Concrete `rootValPoolCap` conservation check on `smallDepth3Sched`:
-- `8` leaves (`1` key each) + `4` inner nodes (`1` key each) = `12` non-root keys, leaving
-- `rootValPoolCap = 16 - 4 * 3 = 4` root value slots for up to `16` active keys.
example : smallDepth3Sched.rootValPoolCap = 4 := by decide

example {rootKeys totalActive : ℕ}
    (hpart : smallDepth3Sched.numNodes 3 * smallDepth3Sched.nLow 3 +
      (∑ ℓ ∈ Finset.Ico 2 3, smallDepth3Sched.numNodes ℓ * smallDepth3Sched.tableCap ℓ) +
        rootKeys = totalActive)
    (hcap : totalActive ≤ 16) :
    rootKeys ≤ smallDepth3Sched.rootValPoolCap :=
  smallDepth3Sched.rootKeys_le_rootValPoolCap hpart hcap

example {scheme : DynamicMatching.Scheme
      (2 ^ smallDepth3Sched.idBits smallDepth3Sched.depth)
      (smallDepth3Sched.nLow smallDepth3Sched.depth)}
    {st : smallDepth3Sched.TreeState}
    {d : smallDepth3Sched.PaddedDict} {storeLvl : Fin smallDepth3Sched.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) :
    st.rootKeyCount ≤ smallDepth3Sched.rootValPoolCap :=
  st.rootKeyCount_le_rootValPoolCap hwf

/-! ## 2. Multi-Level Tree Operations, `Algorithm 3`, `Algorithm 4` & DFS Metadata -/

-- Level-coordinate bijection and Section 5.6 DFS pre-order subtree metadata count and descendant
-- coverage on `smallDepth3Sched` (`1` level-2 inner node + `2` level-3 leaf children = `3` items).
theorem smallDepth3_routing_and_dfs_meta (st : smallDepth3Sched.TreeState)
    (u₂ : Fin (smallDepth3Sched.numNodes 2)) (b : Fin (2 ^ smallDepth3Sched.branchBits 2)) :
    Function.Bijective (st.seeds.levelCoordEquiv 2 (by decide) (by decide)) ∧
    (st.dfsSubtreeMeta 2 (by decide) (by decide) u₂).length = 3 ∧
    st.nodeMeta 3 (by decide) (by decide) (smallDepth3Sched.childNodeEquiv 2 (u₂, b)) ∈
      st.dfsSubtreeMeta 2 (by decide) (by decide) u₂ := by
  refine ⟨(st.seeds.levelCoordEquiv 2 (by decide) (by decide)).bijective, ?_, ?_⟩
  · rw [st.length_dfsSubtreeMeta (by decide) (by decide) u₂]
    decide
  · rw [st.mem_dfsSubtreeMeta_iff]
    exact ⟨3, by decide, by decide, smallDepth3Sched.childNodeEquiv 2 (u₂, b),
      (smallDepth3Sched.inSubtree_step_iff u₂ _).mpr
        (Or.inr ⟨b, smallDepth3Sched.inSubtree_refl _⟩), rfl⟩

/-- End-to-end dictionary trace on `canonicalSchedule sublinearRegime` exercising `initTree`,
fresh `insert`s, in-place key overwrite, present-key `delete`, and absent-key `delete`, verifying
both `WellFormed` preservation and exact `query` outputs at every step. -/
theorem endToEnd_dictionary_trace
    (scheme : DynamicMatching.Scheme
      (2 ^ (canonicalSchedule sublinearRegime).idBits (canonicalSchedule sublinearRegime).depth)
      ((canonicalSchedule sublinearRegime).nLow (canonicalSchedule sublinearRegime).depth)) :
    let P := canonicalSchedule sublinearRegime
    let hcr := sublinearConcentrationReady
    let hU : 4 ≤ P.univ := by
      rw [canonicalSchedule_univ sublinearRegime]
      have h2n : 2 * testN ≤ testU := sublinearRegime.two_mul_n_le_univ
      have hn2 : 2 ≤ testN := sublinearRegime.two_le_n
      omega
    let k₁ : Fin P.univ := ⟨0, by omega⟩
    let k₂ : Fin P.univ := ⟨1, by omega⟩
    let k₃ : Fin P.univ := ⟨2, by omega⟩
    let v₁ : Fin P.valBound := ⟨1, by
      rw [canonicalSchedule_valBound sublinearRegime]
      change 1 < 2 ^ 64; decide⟩
    let v₂ : Fin P.valBound := ⟨2, by
      rw [canonicalSchedule_valBound sublinearRegime]
      change 2 < 2 ^ 64; decide⟩
    let v₁' : Fin P.valBound := ⟨3, by
      rw [canonicalSchedule_valBound sublinearRegime]
      change 3 < 2 ^ 64; decide⟩
    let st0 := P.initTree hcr scheme
    let st1 := st0.insert hcr scheme k₁ v₁
    let st2 := st1.insert hcr scheme k₂ v₂
    let st3 := st2.insert hcr scheme k₁ v₁'
    let st4 := st3.delete hcr scheme k₂
    let st5 := st4.delete hcr scheme k₃
    st0.query scheme k₁ = none ∧
    st2.query scheme k₁ = some 1 ∧
    st2.query scheme k₂ = some 2 ∧
    st3.query scheme k₁ = some 3 ∧
    st3.query scheme k₂ = some 2 ∧
    st4.query scheme k₁ = some 3 ∧
    st4.query scheme k₂ = none ∧
    st5.query scheme k₁ = some 3 ∧
    st5.query scheme k₃ = none ∧
    ∃ dict5, st5.WellFormed scheme dict5 := by
  intro P hcr hU k₁ k₂ k₃ v₁ v₂ v₁' st0 st1 st2 st3 st4 st5
  have hk12 : k₁ ≠ k₂ := by decide
  have hk13 : k₁ ≠ k₃ := by decide
  have hcap2 : 2 < P.cap := by
    rw [canonicalSchedule_cap sublinearRegime]
    have h4 : 4 ≤ thresholdLogN 1 1 := ValidRegime.four_le_thresholdLogN 1 1
    have h16 : 16 ≤ testN :=
      (by decide : 16 ≤ 2 ^ 4).trans
        ((Nat.pow_le_pow_right Nat.two_pos h4).trans sublinearRegime.n_ge_threshold)
    omega
  have hwf0 := P.wellFormed_initTree hcr scheme
  have hc0 : (Dictionary.dom (Dictionary.empty P.univ)).card < P.cap := by
    have hempty : Dictionary.dom (Dictionary.empty P.univ) = ∅ := by
      ext u; simp [Dictionary.dom, Dictionary.empty]
    rw [hempty]; exact Nat.zero_lt_of_lt hcap2
  have hwf1 := st0.wellFormed_insert hcr hwf0 k₁ v₁ (Or.inr hc0)
  have hdom1 : Dictionary.dom (Function.update (Dictionary.empty P.univ) k₁ (some v₁.val)) ⊆
      {k₁} := by
    intro u hu
    simp only [Dictionary.dom, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hu ⊢
    by_contra hne
    rw [Function.update_of_ne hne] at hu
    simp [Dictionary.empty] at hu
  have hc1 :
      (Dictionary.dom (Function.update (Dictionary.empty P.univ) k₁ (some v₁.val))).card <
        P.cap :=
    (Finset.card_le_card hdom1).trans_lt (by simpa using Nat.lt_trans Nat.one_lt_two hcap2)
  have hwf2 := st1.wellFormed_insert hcr hwf1 k₂ v₂ (Or.inr hc1)
  have hk1_mem2 : k₁ ∈ Dictionary.dom
      (Function.update (Function.update (Dictionary.empty P.univ) k₁ (some v₁.val))
        k₂ (some v₂.val)) := by
    simp [Dictionary.dom, Function.update_of_ne hk12]
  have hwf3 := st2.wellFormed_insert hcr hwf2 k₁ v₁' (Or.inl hk1_mem2)
  have hwf4 := st3.wellFormed_delete hcr hwf3 k₂
  have hwf5 := st4.wellFormed_delete hcr hwf4 k₃
  have hq0 : ∀ u, st0.query scheme u = none := P.query_initTree hcr scheme
  have hq1 : ∀ u, st1.query scheme u = Function.update (st0.query scheme) k₁ (some 1) u :=
    st0.query_insert hcr hwf0 k₁ v₁ (Or.inr hc0)
  have hq2 : ∀ u, st2.query scheme u = Function.update (st1.query scheme) k₂ (some 2) u :=
    st1.query_insert hcr hwf1 k₂ v₂ (Or.inr hc1)
  have hq3 : ∀ u, st3.query scheme u = Function.update (st2.query scheme) k₁ (some 3) u :=
    st2.query_insert hcr hwf2 k₁ v₁' (Or.inl hk1_mem2)
  have hq4 : ∀ u, st4.query scheme u = Function.update (st3.query scheme) k₂ none u :=
    st3.query_delete hcr hwf3 k₂
  have hq5 : ∀ u, st5.query scheme u = Function.update (st4.query scheme) k₃ none u :=
    st4.query_delete hcr hwf4 k₃
  refine ⟨hq0 k₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, _, hwf5⟩
  · rw [hq2 k₁, Function.update_of_ne hk12, hq1 k₁, Function.update_self]
  · rw [hq2 k₂, Function.update_self]
  · rw [hq3 k₁, Function.update_self]
  · rw [hq3 k₂, Function.update_of_ne hk12.symm, hq2 k₂, Function.update_self]
  · rw [hq4 k₁, Function.update_of_ne hk12, hq3 k₁, Function.update_self]
  · rw [hq4 k₂, Function.update_self]
  · rw [hq5 k₁, Function.update_of_ne hk13, hq4 k₁, Function.update_of_ne hk12, hq3 k₁,
      Function.update_self]
  · rw [hq5 k₃, Function.update_self]

/-- Direct instantiation of `Algorithm 3` (`deleteAndGetQuotient_spec`) and the pure
reconstruction/local-splice step of `Algorithm 4` under supplied validated seeds (`rehashSubtree`
locality and `wellFormedPadded_rehashSubtree`) on any `TreeSchedule`. -/
theorem deleteAndGetQuotient_and_rehashSubtree_specs
    {P : TreeSchedule}
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {z : Fin P.paddedUniv} {vz : Fin P.valBound} (hdz : d z = some vz)
    (hloads : ∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ P.depth),
      P.nLow j <
        (st.seeds.activeAt (P.paddedDom d) j hj
          (P.ancestorAt hj (st.seeds.nodeAt P.depth le_rfl z))).card)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (v_leaf : Fin (P.numNodes P.depth)) (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ P.depth v_leaf) :
    let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
    let delRes := st.deleteAndGetQuotient scheme P.depth h1d le_rfl
      (st.seeds.nodeAt P.depth le_rfl z) (st.seeds.idAt P.depth h1d le_rfl z)
    let st_reh := st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
    delRes.2 = (st.seeds.quotAt P.depth h1d le_rfl z, vz) ∧
    st_reh.leaves v_leaf = st.leaves v_leaf ∧
    (∃ storeLvl', st_reh.WellFormedPadded scheme d storeLvl') := by
  intro h1d delRes st_reh
  have hz : z ∈ P.paddedDom d := (P.mem_paddedDom_iff d z).mpr (by simp [hdz])
  obtain ⟨hq, hv, _, _⟩ := TreeSchedule.TreeState.deleteAndGetQuotient_spec hwf P.depth h1d le_rfl
    _ z vz hdz rfl (hwf.storeLvl_bounds z hz).2 hloads
  exact ⟨Prod.ext hq hv,
    st.rehashSubtree_untouched_leaves hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' v_leaf hnot_sub,
    st.wellFormedPadded_rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'⟩


end SubconstantTreeModel

end CslibFrontierTests
