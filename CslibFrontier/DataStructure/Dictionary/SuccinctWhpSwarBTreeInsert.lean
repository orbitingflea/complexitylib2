/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTreeSpec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Top-Down Split-Only SWAR B+-Tree Insertion and `ValidWhpSlice` Bundle

This module completes the functional correctness and Overmars split-potential proof for
`descendSplitToLeaf` and `btreeInsert`, packages the slice-level `ValidSlice` invariant, and
specializes all bounds to `SuccinctWhp` parameters (`ValidWhpSlice`).

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidSlice`:
  slice-level ordered-map and Overmars split-potential invariant.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice`:
  specialization of `ValidSlice` to `(fpBitsWhp n_max, valLaneBitsWhp n_max, tMinWhp n_max)`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeInsert_subtree_spec`:
  top-level subtree specification of `btreeInsert`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.lookup_eq`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.delete_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.update_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.insert_spec`:
  exact ordered-map refinement and preservation of `ValidWhpSlice` across all four operations.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.alloc_and_height_lt`:
  every `ValidWhpSlice` with `insCount ≤ 8 * (scaleWhp n_max) ^ 12` at `whpThreshold c ≤ n_max`
  satisfies `sl.alloc + hMaxBTree + 4 < nSliceWhp n_max` and tree height `< hMaxBTree`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Finset
open scoped BigOperators

/-! ## Section 1: Inductive correctness and potential bound for `descendSplitToLeaf` -/

/-- Lift an inductive insertion result `(sl', T_c')` on child `r_b` of a valid branch
`.branch idx m cs_b` to the whole branch, preserving `ValidSubtree` and the local Overmars
potential inequality. -/
private theorem lift_branch_child_insert {isRoot : Bool} {fpBits W_val tMin idx m lo hi q val : ℕ}
    {sl_b sl' : BTreeSlice} {mapFn : ℕ → Option ℕ} {cs_b : Fin (m + 1) → BTreeTree}
    {r_b : Fin (m + 1)} {T_c' : BTreeTree}
    (hv_b : ValidSubtree isRoot fpBits W_val tMin sl_b.alloc sl_b.nodes lo hi mapFn
      (.branch idx m cs_b))
    (hother_b : ∀ i : Fin (m + 1), i ≠ r_b →
      ∀ q', childLo (fpBits + 2) lo (sl_b.nodes idx).keysWord i.val ≤ q' →
        q' ≤ childHi (fpBits + 2) hi m (sl_b.nodes idx).keysWord i.val → q' ≠ q)
    (halloc_le : sl_b.alloc ≤ sl'.alloc)
    (hfr : ∀ v, v < sl_b.alloc → v ∉ (cs_b r_b).nodeSet → sl'.nodes v = sl_b.nodes v)
    (hrt_c : T_c'.rootIdx = (cs_b r_b).rootIdx)
    (hht_c : T_c'.height = (cs_b r_b).height)
    (hns_c : ∀ v ∈ T_c'.nodeSet, v ∈ (cs_b r_b).nodeSet ∨ sl_b.alloc ≤ v)
    (hpot_c : (tMin - 2) * (sl'.alloc - sl_b.alloc) + 2 * T_c'.potential tMin ≤
      2 * (cs_b r_b).potential tMin + 2)
    (hv_c' : ValidSubtree false fpBits W_val tMin sl'.alloc sl'.nodes
      (childLo (fpBits + 2) lo (sl_b.nodes idx).keysWord r_b.val)
      (childHi (fpBits + 2) hi m (sl_b.nodes idx).keysWord r_b.val)
      (Function.update mapFn q (some val)) T_c') :
    (∀ v, v < sl_b.alloc → v ∉ (BTreeTree.branch idx m cs_b).nodeSet →
      sl'.nodes v = sl_b.nodes v) ∧
    ∃ T' : BTreeTree,
      T'.rootIdx = idx ∧
      T'.height = (BTreeTree.branch idx m cs_b).height ∧
      (∀ v ∈ T'.nodeSet, v ∈ (BTreeTree.branch idx m cs_b).nodeSet ∨ sl_b.alloc ≤ v) ∧
      (tMin - 2) * (sl'.alloc - sl_b.alloc) + 2 * T'.potential tMin ≤
        2 * (BTreeTree.branch idx m cs_b).potential tMin + 2 ∧
      ValidSubtree isRoot fpBits W_val tMin sl'.alloc sl'.nodes lo hi
        (Function.update mapFn q (some val)) T' := by
  obtain ⟨hidx, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono,
    hnot, hdisj, hht, hcs⟩ := hv_b
  let cs' : Fin (m + 1) → BTreeTree := Function.update cs_b r_b T_c'
  have hht_eq : ∀ i, (cs' i).height = (cs_b i).height := fun i => by
    dsimp only [cs']
    by_cases hi : i = r_b
    · subst hi; simp [hht_c]
    · simp [hi]
  have hrt_eq : ∀ i, (cs' i).rootIdx = (cs_b i).rootIdx := fun i => by
    dsimp only [cs']
    by_cases hi : i = r_b
    · subst hi; simp [hrt_c]
    · simp [hi]
  have hidx_eq : sl'.nodes idx = sl_b.nodes idx := hfr idx hidx (hnot r_b)
  refine ⟨fun v hv_lt hv_not => hfr v hv_lt (fun hvc =>
    hv_not (mem_insert_of_mem (mem_biUnion.mpr ⟨r_b, mem_univ r_b, hvc⟩))),
    .branch idx m cs', rfl, ?_, ?_, ?_, ?_⟩
  · simp only [BTreeTree.height, hht_eq]
  · intro v hv_in
    rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
    rcases hv_in with rfl | ⟨i, _, hvi⟩
    · left; simp [BTreeTree.nodeSet]
    · dsimp only [cs'] at hvi
      by_cases hi : i = r_b
      · subst hi
        rw [Function.update_self] at hvi
        rcases hns_c v hvi with hv_old | hv_ge
        · left; exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ i, hv_old⟩)
        · right; exact hv_ge
      · rw [Function.update_of_ne hi] at hvi
        left; exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ i, hvi⟩)
  · simp only [BTreeTree.potential]
    have hsum1 := Finset.add_sum_erase univ (fun i => (cs' i).potential tMin) (mem_univ r_b)
    have hsum2 := Finset.add_sum_erase univ (fun i => (cs_b i).potential tMin) (mem_univ r_b)
    have her_eq : ∑ i ∈ univ.erase r_b, (cs' i).potential tMin =
        ∑ i ∈ univ.erase r_b, (cs_b i).potential tMin :=
      sum_congr rfl fun i hi => by
        dsimp only [cs']
        rw [Function.update_of_ne (mem_erase.mp hi).1]
    rw [← hsum1, ← hsum2, her_eq]
    dsimp only [cs']
    rw [Function.update_self]
    omega
  · dsimp only [ValidSubtree]
    rw [hidx_eq]
    refine ⟨hidx.trans_le halloc_le, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono,
      ?_, ?_, ?_, ?_⟩
    · intro i hmem
      dsimp only [cs'] at hmem
      by_cases hi : i = r_b
      · subst hi
        rw [Function.update_self] at hmem
        rcases hns_c idx hmem with h1 | h2
        · exact hnot i h1
        · omega
      · rw [Function.update_of_ne hi] at hmem
        exact hnot i hmem
    · intro i j hij
      dsimp only [cs']
      by_cases hi : i = r_b
      · subst hi
        have hj : j ≠ i := hij.symm
        rw [Function.update_self, Function.update_of_ne hj, Finset.disjoint_left]
        intro v hvi hvj
        have hvj_lt : v < sl_b.alloc := ((hcs j).2.leafCount_le_card_nodeSet).1 v hvj
        rcases hns_c v hvi with hvi_old | hv_ge
        · exact Finset.disjoint_left.mp (hdisj i j hij) hvi_old hvj
        · omega
      · by_cases hj : j = r_b
        · subst hj
          rw [Function.update_of_ne hi, Function.update_self, Finset.disjoint_left]
          intro v hvi hvj
          have hvi_lt : v < sl_b.alloc := ((hcs i).2.leafCount_le_card_nodeSet).1 v hvi
          rcases hns_c v hvj with hvj_old | hv_ge
          · exact Finset.disjoint_left.mp (hdisj i j hij) hvi hvj_old
          · omega
        · rw [Function.update_of_ne hi, Function.update_of_ne hj]
          exact hdisj i j hij
    · intro i
      rw [hht_eq i, hht_eq ⟨0, Nat.succ_pos m⟩]
      exact hht i
    · intro i
      rw [hrt_eq i]
      refine ⟨(hcs i).1, ?_⟩
      dsimp only [cs']
      by_cases hi : i = r_b
      · subst hi; rw [Function.update_self]; exact hv_c'
      · rw [Function.update_of_ne hi]
        refine ((hcs i).2).frame halloc_le (fun v hv_in => ?_) (fun q' hq1 hq2 => ?_)
        · have hv_lt : v < sl_b.alloc := ((hcs i).2.leafCount_le_card_nodeSet).1 v hv_in
          have hv_not : v ∉ (cs_b r_b).nodeSet :=
            Finset.disjoint_left.mp (hdisj i r_b hi) hv_in
          exact hfr v hv_lt hv_not
        · exact Function.update_of_ne (hother_b i hi q' hq1 hq2) _ _

/-- Full inductive specification of `descendSplitToLeaf` followed by `finishLeafInsert` on any
non-full valid subtree `T`. -/
theorem finishLeafInsert_descendSplitToLeaf_spec {isRoot : Bool}
    {fpBits W_val tMin lo hi q val fuel : ℕ} {sl : BTreeSlice} {mapFn : ℕ → Option ℕ}
    {T : BTreeTree}
    (ht3 : 3 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2)) (hval : val < 2 ^ W_val)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi)
    (hv : ValidSubtree isRoot fpBits W_val tMin sl.alloc sl.nodes lo hi mapFn T)
    (hnonfull : metaCount (sl.nodes T.rootIdx).metaWord < 2 * tMin - 1)
    (hfuel : T.height ≤ fuel) (halloc_val : sl.alloc + T.height ≤ 2 ^ W_val) :
    let p := descendSplitToLeaf fpBits W_val tMin fuel sl T.rootIdx q
    let sl' := finishLeafInsert fpBits W_val tMin p.1 p.2 q val
    sl.alloc ≤ sl'.alloc ∧
      sl'.root = sl.root ∧
      (∀ v, v < sl.alloc → v ∉ T.nodeSet → sl'.nodes v = sl.nodes v) ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = T.rootIdx ∧
        T'.height = T.height ∧
        (∀ v ∈ T'.nodeSet, v ∈ T.nodeSet ∨ sl.alloc ≤ v) ∧
        (tMin - 2) * (sl'.alloc - sl.alloc) + 2 * T'.potential tMin ≤
          2 * T.potential tMin + 2 ∧
        ValidSubtree isRoot fpBits W_val tMin sl'.alloc sl'.nodes lo hi
          (Function.update mapFn q (some val)) T' := by
  have hleaf_case : ∀ {f : ℕ} {isR : Bool} {s_l : BTreeSlice} {lo' hi' idx cnt : ℕ},
      hi' < 2 ^ fpBits → lo' ≤ q → q ≤ hi' →
      ValidSubtree isR fpBits W_val tMin s_l.alloc s_l.nodes lo' hi' mapFn (.leaf idx cnt) →
      metaCount (s_l.nodes idx).metaWord < 2 * tMin - 1 →
      let p := descendSplitToLeaf fpBits W_val tMin f s_l idx q
      let sl' := finishLeafInsert fpBits W_val tMin p.1 p.2 q val
      s_l.alloc ≤ sl'.alloc ∧
        sl'.root = s_l.root ∧
        (∀ v, v < s_l.alloc → v ∉ (BTreeTree.leaf idx cnt).nodeSet → sl'.nodes v = s_l.nodes v) ∧
        ∃ T' : BTreeTree,
          T'.rootIdx = idx ∧
          T'.height = 0 ∧
          (∀ v ∈ T'.nodeSet, v ∈ (BTreeTree.leaf idx cnt).nodeSet ∨ s_l.alloc ≤ v) ∧
          (tMin - 2) * (sl'.alloc - s_l.alloc) + 2 * T'.potential tMin ≤
            2 * (BTreeTree.leaf idx cnt).potential tMin + 2 ∧
          ValidSubtree isR fpBits W_val tMin sl'.alloc sl'.nodes lo' hi'
            (Function.update mapFn q (some val)) T' := by
    intro f isR s_l lo' hi' idx cnt hhi' hqlo' hqhi' hv' hnf'
    have hdesc : descendSplitToLeaf fpBits W_val tMin f s_l idx q = (s_l, idx) := by
      cases f with
      | zero => rfl
      | succ f0 => simp [descendSplitToLeaf, hv'.2.1]
    dsimp only
    rw [hdesc]
    dsimp only
    have hcnt_lt : cnt < 2 * tMin - 1 := by
      rw [hv'.2.1, metaCount_mkNodeMeta] at hnf'
      exact hnf'
    obtain ⟨halloc_eq, hrt_eq, hframe_leaf, cnt', hcnt'_le, hv_leaf'⟩ :=
      finishLeafInsert_leaf_spec (by omega) hcap hval hhi' hqlo' hqhi' hv' hcnt_lt
    refine ⟨halloc_eq.symm.le, hrt_eq, fun v _ hv_not => ?_,
      .leaf idx cnt', rfl, rfl, fun v hv_in => Or.inl hv_in, ?_, hv_leaf'⟩
    · exact hframe_leaf v (by simpa only [BTreeTree.nodeSet, mem_singleton] using hv_not)
    · rw [halloc_eq, Nat.sub_self, Nat.mul_zero, zero_add]
      simp only [BTreeTree.potential]
      omega
  induction fuel generalizing T isRoot sl lo hi with
  | zero =>
    cases T with
    | leaf idx cnt =>
      exact hleaf_case hhi hqlo hqhi hv hnonfull
    | branch idx cnt cs =>
      simp [BTreeTree.height] at hfuel
  | succ fuel' ih =>
    cases T with
    | leaf idx cnt =>
      exact hleaf_case hhi hqlo hqhi hv hnonfull
    | branch idx cnt cs =>
    obtain ⟨hr_le, hclo_q, hq_chi, hother⟩ :=
      branch_child_routing (by omega) hcap hv hhi hqlo hqhi
    obtain ⟨hidx, hmeta, hdeg, _, hkw, hvw, hlo0, hhi_last, hmono,
      hnot, hdisj, hht, hcs⟩ := hv
    dsimp only [BTreeTree.rootIdx] at hnonfull ⊢
    have hcnt_lt : cnt < 2 * tMin - 1 := by
      rw [hmeta, metaCount_mkNodeMeta] at hnonfull
      exact hnonfull
    set W_key := fpBits + 2
    set nd := sl.nodes idx
    set r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    let r_fin : Fin (cnt + 1) := ⟨r, Nat.lt_succ_of_le hr_le⟩
    set childIdx := (cs r_fin).rootIdx
    have hval_r : laneGet W_val nd.valsWord r = childIdx := (hcs r_fin).1
    have hchi_le : childHi W_key hi cnt nd.keysWord r ≤ hi := by
      unfold childHi
      split_ifs with hrc
      · rcases eq_or_lt_of_le (by omega : r ≤ cnt - 1) with heq | hlt
        · rw [heq]; exact hhi_last.le
        · exact (hmono r (cnt - 1) hlt (by omega)).le.trans hhi_last.le
      · exact le_rfl
    have hht_c : (cs r_fin).height + 1 = (BTreeTree.branch idx cnt cs).height := by
      rw [BTreeTree.height_branch_of_eq hht, hht r_fin, Nat.add_comm]
    have hcnt_c_le : metaCount (sl.nodes childIdx).metaWord ≤ 2 * tMin - 1 := by
      have hvc := (hcs r_fin).2
      cases hrc_eq : cs r_fin with
      | leaf cidx ccnt =>
        rw [hrc_eq] at hvc
        have hcidx : childIdx = cidx := by dsimp [childIdx]; rw [hrc_eq, BTreeTree.rootIdx]
        rw [hcidx, hvc.2.1, metaCount_mkNodeMeta]
        exact hvc.2.2.1
      | branch cidx ccnt ccs =>
        rw [hrc_eq] at hvc
        have hcidx : childIdx = cidx := by dsimp [childIdx]; rw [hrc_eq, BTreeTree.rootIdx]
        rw [hcidx, hvc.2.1, metaCount_mkNodeMeta]
        exact hvc.2.2.2.1
    by_cases hfull_c : metaCount (sl.nodes childIdx).metaWord = 2 * tMin - 1
    · -- Subcase B: child `r_fin` is full — split `cs r_fin` into `(leftT, sep, rightT)` first!
      have hstep : descendSplitToLeaf fpBits W_val tMin (fuel' + 1) sl idx q =
          let (leftNd, sep, rightNd) := splitFullNode fpBits W_val tMin (sl.nodes childIdx)
          let rightIdx := sl.alloc
          let parentNd' : BTreeNode :=
            ⟨mkNodeMeta false (cnt + 1),
              wordInsertAt W_key r sep nd.keysWord,
              wordInsertAt W_val (r + 1) rightIdx nd.valsWord⟩
          let nodes1 := Function.update sl.nodes childIdx leftNd
          let nodes2 := Function.update nodes1 rightIdx rightNd
          let nodes3 := Function.update nodes2 idx parentNd'
          let sl_mid : BTreeSlice := { sl with alloc := sl.alloc + 1, nodes := nodes3 }
          let nextChild := if sep < q then rightIdx else childIdx
          descendSplitToLeaf fpBits W_val tMin fuel' sl_mid nextChild q := by
        dsimp only [descendSplitToLeaf]
        have hcond : (metaCount (sl.nodes childIdx).metaWord == 2 * tMin - 1) = true := by
          simp [hfull_c]
        rw [hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hnd_eq : sl.nodes idx = nd := rfl
        rw [hnd_eq]
        change (let r0 := swarRank fpBits (2 * tMin) cnt q nd.keysWord
          let childIdx0 := laneGet W_val nd.valsWord r0
          if (metaCount (sl.nodes childIdx0).metaWord == 2 * tMin - 1) = true then _ else _) = _
        have hr_eq : swarRank fpBits (2 * tMin) cnt q nd.keysWord = r := rfl
        dsimp only
        rw [hr_eq, hval_r, hcond]
        simp only [↓reduceIte]
        rfl
      set res := splitFullNode fpBits W_val tMin (sl.nodes childIdx)
      set leftNd := res.1
      set sep := res.2.1
      set rightNd := res.2.2
      set rightIdx := sl.alloc
      set parentNd' : BTreeNode :=
        ⟨mkNodeMeta false (cnt + 1),
          wordInsertAt W_key r sep nd.keysWord,
          wordInsertAt W_val (r + 1) rightIdx nd.valsWord⟩
      set nodes1 := Function.update sl.nodes childIdx leftNd
      set nodes2 := Function.update nodes1 rightIdx rightNd
      set nodes3 := Function.update nodes2 idx parentNd'
      set sl_mid : BTreeSlice := { sl with alloc := sl.alloc + 1, nodes := nodes3 }
      have hstep' : descendSplitToLeaf fpBits W_val tMin (fuel' + 1) sl idx q =
          descendSplitToLeaf fpBits W_val tMin fuel' sl_mid
            (if sep < q then rightIdx else childIdx) q := hstep
      rw [hstep']
      have hchild_lt : childIdx < sl.alloc :=
        ((hcs r_fin).2.leafCount_le_card_nodeSet).1 childIdx (cs r_fin).rootIdx_mem_nodeSet
      have hchild_ne_idx : childIdx ≠ idx := fun heq =>
        hnot r_fin (heq ▸ (cs r_fin).rootIdx_mem_nodeSet)
      have hidx_ne_r : idx ≠ rightIdx := by dsimp [rightIdx]; omega
      have hlr_ne : childIdx ≠ rightIdx := by dsimp [rightIdx]; omega
      have hl_nd : nodes3 childIdx = (splitFullNode fpBits W_val tMin (sl.nodes childIdx)).1 := by
        dsimp only [nodes3, nodes2, nodes1]
        rw [Function.update_of_ne hchild_ne_idx, Function.update_of_ne hlr_ne,
          Function.update_self]
      have hr_nd : nodes3 rightIdx =
          (splitFullNode fpBits W_val tMin (sl.nodes childIdx)).2.2 := by
        dsimp only [nodes3, nodes2]
        rw [Function.update_of_ne hidx_ne_r.symm, Function.update_self]
      have herase : ∀ v ∈ (cs r_fin).nodeSet.erase childIdx,
          nodes3 v = sl.nodes v ∧ v ≠ childIdx ∧ v ≠ rightIdx := by
        intro v hv_er
        obtain ⟨hv_ne_c, hv_mem⟩ := mem_erase.mp hv_er
        have hv_lt : v < sl.alloc := ((hcs r_fin).2.leafCount_le_card_nodeSet).1 v hv_mem
        have hv_ne_r : v ≠ rightIdx := by dsimp [rightIdx]; omega
        have hv_ne_idx : v ≠ idx := fun heq => hnot r_fin (heq ▸ hv_mem)
        refine ⟨?_, hv_ne_c, hv_ne_r⟩
        dsimp only [nodes3, nodes2, nodes1]
        rw [Function.update_of_ne hv_ne_idx, Function.update_of_ne hv_ne_r,
          Function.update_of_ne hv_ne_c]
      obtain ⟨leftT, rightT, hrtL, hrtR, hcntL_le, hcntR_eq, hhtL, hhtR, hsubL, hsubR,
        hdisjLR, hclo_sep, hsep_chi, hpotLR, hvL, hvR⟩ :=
        splitFullNode_spec (alloc' := sl_mid.alloc) (nodes' := nodes3)
          (leftIdx := childIdx) (rightIdx := rightIdx) (by omega) (hcs r_fin).2 hfull_c
          (by dsimp [sl_mid]; omega) (by dsimp [sl_mid]; omega)
          (by dsimp [sl_mid, rightIdx]; omega) hlr_ne hl_nd hr_nd herase
      have hsep_eq : (splitFullNode fpBits W_val tMin (sl.nodes (cs r_fin).rootIdx)).2.1 = sep :=
        rfl
      have hr_fin_val : r_fin.val = r := rfl
      rw [hsep_eq, hr_fin_val] at hclo_sep hsep_chi
      -- Construct the intermediate valid branch `T_mid` on `sl_mid` with `cnt + 1` separators
      let cs_mid : Fin (cnt + 1 + 1) → BTreeTree := fun i =>
        if i.val < r then cs ⟨min i.val cnt, Nat.lt_succ_of_le (min_le_right _ _)⟩
        else if i.val = r then leftT
        else if i.val = r + 1 then rightT
        else cs ⟨min (i.val - 1) cnt, Nat.lt_succ_of_le (min_le_right _ _)⟩
      have hcs_lt : ∀ (i : Fin (cnt + 1 + 1)) (hi : i.val < r),
          cs_mid i = cs ⟨i.val, by omega⟩ := fun i hi => by
        dsimp only [cs_mid]
        simp only [hi, ↓reduceIte]
        congr 1
        ext
        exact min_eq_left (by omega)
      have hcs_eq_r : ∀ (i : Fin (cnt + 1 + 1)), i.val = r → cs_mid i = leftT := fun i hi => by
        dsimp only [cs_mid]
        simp [hi]
      have hcs_eq_r1 : ∀ (i : Fin (cnt + 1 + 1)), i.val = r + 1 → cs_mid i = rightT :=
        fun i hi => by
          dsimp only [cs_mid]
          rw [hi]
          have hn1 : ¬(r + 1 < r) := by omega
          simp [hn1]
      have hcs_gt : ∀ (i : Fin (cnt + 1 + 1)) (hi : r + 1 < i.val),
          cs_mid i = cs ⟨i.val - 1, by omega⟩ := fun i hi => by
        dsimp only [cs_mid]
        have hn1 : ¬(i.val < r) := by omega
        have hn2 : i.val ≠ r := by omega
        have hn3 : i.val ≠ r + 1 := by omega
        simp only [hn1, hn2, hn3, ↓reduceIte]
        congr 1
        ext
        exact min_eq_left (by omega)
      have hsep_lt_W : sep < 2 ^ W_key :=
        ((hsep_chi.trans_le hchi_le).trans hhi).trans
          (Nat.pow_lt_pow_right (by decide) (by dsimp [W_key]; omega))
      have hright_lt_val : rightIdx < 2 ^ W_val := by dsimp [rightIdx]; omega
      have hht_mid : ∀ i : Fin (cnt + 1 + 1),
          (cs_mid i).height = (cs_mid ⟨0, Nat.succ_pos _⟩).height := by
        have hval0_mid :
            (cs_mid ⟨0, Nat.succ_pos _⟩).height = (cs ⟨0, Nat.succ_pos cnt⟩).height := by
          by_cases h0r : 0 < r
          · rw [hcs_lt ⟨0, Nat.succ_pos _⟩ h0r]
          · rw [hcs_eq_r ⟨0, Nat.succ_pos _⟩ (by dsimp; omega), hhtL]
            exact hht r_fin
        intro i
        rw [hval0_mid]
        by_cases hi1 : i.val < r
        · rw [hcs_lt i hi1]; exact hht ⟨i.val, by omega⟩
        · by_cases hi2 : i.val = r
          · rw [hcs_eq_r i hi2, hhtL]; exact hht r_fin
          · by_cases hi3 : i.val = r + 1
            · rw [hcs_eq_r1 i hi3, hhtR]; exact hht r_fin
            · rw [hcs_gt i (by omega)]; exact hht ⟨i.val - 1, by omega⟩
      have hv_mid : ValidSubtree isRoot fpBits W_val tMin sl_mid.alloc sl_mid.nodes lo hi
          mapFn (.branch idx (cnt + 1) cs_mid) := by
        dsimp only [ValidSubtree]
        have hnd3_idx : sl_mid.nodes idx = parentNd' := Function.update_self idx parentNd' nodes2
        rw [hnd3_idx]
        refine ⟨by dsimp [sl_mid]; omega, rfl, ?_, by omega,
          wordInsertAt_lt hr_le hsep_lt_W hkw,
          wordInsertAt_lt (by omega) hright_lt_val hvw,
          ?_, ?_, ?_, ?_, ?_, hht_mid, ?_⟩
        · cases isRoot
          · simp only [Bool.false_eq_true, ↓reduceIte] at hdeg ⊢; omega
          · simp only [↓reduceIte]; omega
        · dsimp only [parentNd']
          rw [laneGet_wordInsertAt hsep_lt_W]
          by_cases h0r : 0 < r
          · simp only [h0r, ↓reduceIte]; exact hlo0
          · have hr0 : r = 0 := by omega
            rw [hr0]
            simp only [lt_irrefl, ↓reduceIte]
            unfold childLo at hclo_sep
            simp only [hr0, ↓reduceIte] at hclo_sep
            exact hclo_sep
        · dsimp only [parentNd']
          rw [Nat.add_sub_cancel, laneGet_wordInsertAt hsep_lt_W]
          by_cases hrc : r < cnt
          · have h1 : ¬(cnt < r) := by omega
            have h2 : cnt ≠ r := by omega
            simp only [h1, h2, ↓reduceIte]; exact hhi_last
          · have hrc_eq : r = cnt := by omega
            have hnlt_c : ¬(cnt < cnt) := lt_irrefl cnt
            rw [hrc_eq]
            simp only [hnlt_c, ↓reduceIte]
            unfold childHi at hsep_chi
            rw [hrc_eq] at hsep_chi
            simp only [hnlt_c, ↓reduceIte] at hsep_chi
            exact hsep_chi
        · intro i j hij hj
          dsimp only [parentNd']
          rw [laneGet_wordInsertAt hsep_lt_W, laneGet_wordInsertAt hsep_lt_W]
          have hsep_gt_prev : ∀ k < r, laneGet W_key nd.keysWord k < sep := fun k hkr => by
            have hr_nz : r ≠ 0 := by omega
            unfold childLo at hclo_sep
            simp only [hr_nz, ↓reduceIte] at hclo_sep
            rcases eq_or_lt_of_le (by omega : k ≤ r - 1) with rfl | hlt_k
            · omega
            · exact (hmono k (r - 1) hlt_k (by omega)).trans_le (by omega)
          have hsep_lt_next : ∀ k, r ≤ k → k < cnt → sep < laneGet W_key nd.keysWord k :=
            fun k hrk hkc => by
              have hr_lt_c : r < cnt := by omega
              unfold childHi at hsep_chi
              simp only [hr_lt_c, ↓reduceIte] at hsep_chi
              rcases eq_or_lt_of_le hrk with rfl | hlt_k
              · exact hsep_chi
              · exact hsep_chi.trans (hmono r k hlt_k hkc)
          split_ifs with hir hieq hjr hjeq
          · exact hmono i j hij (by omega)
          · exact hsep_gt_prev i hir
          · exact (hsep_gt_prev i hir).trans (hsep_lt_next (j - 1) (by omega) (by omega))
          · omega
          · omega
          · exact hsep_lt_next (j - 1) (by omega) (by omega)
          · omega
          · omega
          · exact hmono (i - 1) (j - 1) (by omega) (by omega)
        · intro i hmem
          by_cases hi1 : i.val < r
          · rw [hcs_lt i hi1] at hmem; exact hnot ⟨i.val, by omega⟩ hmem
          · by_cases hi2 : i.val = r
            · rw [hcs_eq_r i hi2] at hmem
              have hsub := hsubL hmem
              rw [mem_insert, mem_erase] at hsub
              rcases hsub with heq | ⟨_, hm⟩
              · exact hchild_ne_idx heq.symm
              · exact hnot r_fin hm
            · by_cases hi3 : i.val = r + 1
              · rw [hcs_eq_r1 i hi3] at hmem
                have hsub := hsubR hmem
                rw [mem_insert, mem_erase] at hsub
                rcases hsub with heq | ⟨_, hm⟩
                · exact hidx_ne_r heq
                · exact hnot r_fin hm
              · rw [hcs_gt i (by omega)] at hmem
                exact hnot ⟨i.val - 1, by omega⟩ hmem
        · -- Disjointness of `cs_mid i` and `cs_mid j` for `i ≠ j`
          have hsubL_c : leftT.nodeSet ⊆ (cs r_fin).nodeSet := by
            intro v hv_in
            have h1 := hsubL hv_in
            rw [mem_insert, mem_erase] at h1
            rcases h1 with rfl | ⟨_, hm⟩
            · exact (cs r_fin).rootIdx_mem_nodeSet
            · exact hm
          have hsubR_c : rightT.nodeSet ⊆ insert rightIdx (cs r_fin).nodeSet := by
            intro v hv_in
            have h1 := hsubR hv_in
            rw [mem_insert, mem_erase] at h1
            rcases h1 with rfl | ⟨_, hm⟩
            · exact mem_insert_self _ _
            · exact mem_insert_of_mem hm
          have hdisj_unsplit_LR : ∀ k : Fin (cnt + 1), k ≠ r_fin →
              Disjoint (cs k).nodeSet leftT.nodeSet ∧
              Disjoint (cs k).nodeSet rightT.nodeSet := fun k hkne => by
            refine ⟨(hdisj k r_fin hkne).mono_right hsubL_c, Finset.disjoint_left.mpr ?_⟩
            intro v hvk hvR
            have hv_lt : v < sl.alloc := ((hcs k).2.leafCount_le_card_nodeSet).1 v hvk
            have h1 := hsubR_c hvR
            rw [mem_insert] at h1
            rcases h1 with rfl | hm
            · dsimp only [rightIdx] at hv_lt; omega
            · exact Finset.disjoint_left.mp (hdisj k r_fin hkne) hvk hm
          intro i j hij
          have hij_val : i.val ≠ j.val := Fin.val_ne_of_ne hij
          by_cases hi1 : i.val < r
          · rw [hcs_lt i hi1]
            by_cases hj1 : j.val < r
            · rw [hcs_lt j hj1]
              exact hdisj ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (Fin.ne_of_val_ne hij_val)
            · by_cases hj2 : j.val = r
              · rw [hcs_eq_r j hj2]
                exact (hdisj_unsplit_LR ⟨i.val, by omega⟩
                  (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).1
              · by_cases hj3 : j.val = r + 1
                · rw [hcs_eq_r1 j hj3]
                  exact (hdisj_unsplit_LR ⟨i.val, by omega⟩
                    (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).2
                · rw [hcs_gt j (by omega)]
                  exact hdisj ⟨i.val, by omega⟩ ⟨j.val - 1, by omega⟩
                    (Fin.ne_of_val_ne (by dsimp; omega))
          · by_cases hi2 : i.val = r
            · rw [hcs_eq_r i hi2]
              by_cases hj1 : j.val < r
              · rw [hcs_lt j hj1]
                exact ((hdisj_unsplit_LR ⟨j.val, by omega⟩
                  (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).1).symm
              · by_cases hj2 : j.val = r
                · omega
                · by_cases hj3 : j.val = r + 1
                  · rw [hcs_eq_r1 j hj3]; exact hdisjLR
                  · rw [hcs_gt j (by omega)]
                    exact ((hdisj_unsplit_LR ⟨j.val - 1, by omega⟩
                      (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).1).symm
            · by_cases hi3 : i.val = r + 1
              · rw [hcs_eq_r1 i hi3]
                by_cases hj1 : j.val < r
                · rw [hcs_lt j hj1]
                  exact ((hdisj_unsplit_LR ⟨j.val, by omega⟩
                    (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).2).symm
                · by_cases hj2 : j.val = r
                  · rw [hcs_eq_r j hj2]; exact hdisjLR.symm
                  · by_cases hj3 : j.val = r + 1
                    · omega
                    · rw [hcs_gt j (by omega)]
                      exact ((hdisj_unsplit_LR ⟨j.val - 1, by omega⟩
                        (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).2).symm
              · rw [hcs_gt i (by omega)]
                by_cases hj1 : j.val < r
                · rw [hcs_lt j hj1]
                  exact hdisj ⟨i.val - 1, by omega⟩ ⟨j.val, by omega⟩
                    (Fin.ne_of_val_ne (by dsimp; omega))
                · by_cases hj2 : j.val = r
                  · rw [hcs_eq_r j hj2]
                    exact (hdisj_unsplit_LR ⟨i.val - 1, by omega⟩
                      (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).1
                  · by_cases hj3 : j.val = r + 1
                    · rw [hcs_eq_r1 j hj3]
                      exact (hdisj_unsplit_LR ⟨i.val - 1, by omega⟩
                        (Fin.ne_of_val_ne (by dsimp [r_fin]; omega))).2
                    · rw [hcs_gt j (by omega)]
                      exact hdisj ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
                        (Fin.ne_of_val_ne (by dsimp; omega))
        · -- Child `rootIdx` and `ValidSubtree` for each `i : Fin (cnt + 2)`
          have hsibling_frame : ∀ k : Fin (cnt + 1), k ≠ r_fin →
              ∀ v ∈ (cs k).nodeSet, sl_mid.nodes v = sl.nodes v := fun k hkne v hvk => by
            have hv_lt : v < sl.alloc := ((hcs k).2.leafCount_le_card_nodeSet).1 v hvk
            have hv_ne_idx : v ≠ idx := fun heq => hnot k (heq ▸ hvk)
            have hv_ne_r : v ≠ rightIdx := by dsimp [rightIdx]; omega
            have hv_ne_c : v ≠ childIdx := fun heq =>
              Finset.disjoint_left.mp (hdisj k r_fin hkne) hvk
                (heq ▸ (cs r_fin).rootIdx_mem_nodeSet)
            dsimp only [sl_mid, nodes3, nodes2, nodes1]
            rw [Function.update_of_ne hv_ne_idx, Function.update_of_ne hv_ne_r,
              Function.update_of_ne hv_ne_c]
          intro i
          dsimp only [parentNd']
          rw [laneGet_wordInsertAt hright_lt_val]
          by_cases hi1 : i.val < r
          · rw [hcs_lt i hi1]
            have hir1 : i.val < r + 1 := by omega
            simp only [hir1, ↓reduceIte]
            refine ⟨(hcs ⟨i.val, by omega⟩).1, ?_⟩
            have hclo_eq : childLo W_key lo (wordInsertAt W_key r sep nd.keysWord) i.val =
                childLo W_key lo nd.keysWord i.val := by
              unfold childLo
              split_ifs with hi0
              · rfl
              · rw [laneGet_wordInsertAt hsep_lt_W]; simp [show i.val - 1 < r by omega]
            have hchi_eq : childHi W_key hi (cnt + 1)
                (wordInsertAt W_key r sep nd.keysWord) i.val =
                childHi W_key hi cnt nd.keysWord i.val := by
              unfold childHi
              have h1 : i.val < cnt + 1 := by omega
              have h2 : i.val < cnt := by omega
              simp only [h1, h2, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, hi1]
            rw [hclo_eq, hchi_eq]
            exact ((hcs ⟨i.val, by omega⟩).2).frame (by dsimp [sl_mid]; omega)
              (hsibling_frame ⟨i.val, by omega⟩ (Fin.ne_of_val_ne (by dsimp [r_fin]; omega)))
              (fun _ _ _ => rfl)
          · by_cases hi2 : i.val = r
            · rw [hcs_eq_r i hi2, hi2]
              have hr1_lt : r < r + 1 := Nat.lt_succ_self r
              refine ⟨by simp [hr1_lt, hval_r, hrtL], ?_⟩
              have hclo_eq : childLo W_key lo (wordInsertAt W_key r sep nd.keysWord) r =
                  childLo W_key lo nd.keysWord r := by
                unfold childLo
                split_ifs with hr0
                · rfl
                · rw [laneGet_wordInsertAt hsep_lt_W]; simp [show r - 1 < r by omega]
              have hchi_eq : childHi W_key hi (cnt + 1)
                  (wordInsertAt W_key r sep nd.keysWord) r = sep := by
                unfold childHi
                have h1 : r < cnt + 1 := by omega
                simp only [h1, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, lt_irrefl]
              rw [hclo_eq, hchi_eq]
              exact hvL
            · by_cases hi3 : i.val = r + 1
              · rw [hcs_eq_r1 i hi3, hi3]
                refine ⟨by simp [hrtR], ?_⟩
                have hclo_eq : childLo W_key lo (wordInsertAt W_key r sep nd.keysWord) (r + 1) =
                    sep + 1 := by
                  unfold childLo
                  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
                    laneGet_wordInsertAt hsep_lt_W, lt_irrefl]
                have hchi_eq : childHi W_key hi (cnt + 1)
                    (wordInsertAt W_key r sep nd.keysWord) (r + 1) =
                    childHi W_key hi cnt nd.keysWord r := by
                  unfold childHi
                  by_cases hrc : r < cnt
                  · have h1 : r + 1 < cnt + 1 := by omega
                    have h2 : ¬(r + 1 < r) := by omega
                    have h3 : r + 1 ≠ r := by omega
                    simp only [h1, hrc, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, h2, h3,
                      Nat.add_sub_cancel]
                  · have h1 : ¬(r + 1 < cnt + 1) := by omega
                    simp only [h1, hrc, ↓reduceIte]
                rw [hclo_eq, hchi_eq]
                exact hvR
              · rw [hcs_gt i (by omega)]
                have hnir1 : ¬(i.val < r + 1) := by omega
                have hne1 : i.val ≠ r + 1 := hi3
                simp only [hnir1, hne1, ↓reduceIte]
                refine ⟨(hcs ⟨i.val - 1, by omega⟩).1, ?_⟩
                have hclo_eq : childLo W_key lo (wordInsertAt W_key r sep nd.keysWord) i.val =
                    childLo W_key lo nd.keysWord (i.val - 1) := by
                  unfold childLo
                  have hiz : i.val ≠ 0 := by omega
                  have hi1z : i.val - 1 ≠ 0 := by omega
                  have hnlt : ¬(i.val - 1 < r) := by omega
                  have hne : i.val - 1 ≠ r := by omega
                  simp only [hiz, hi1z, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, hnlt, hne]
                have hchi_eq : childHi W_key hi (cnt + 1)
                    (wordInsertAt W_key r sep nd.keysWord) i.val =
                    childHi W_key hi cnt nd.keysWord (i.val - 1) := by
                  unfold childHi
                  by_cases hic : i.val < cnt + 1
                  · have hic1 : i.val - 1 < cnt := by omega
                    have hnlt : ¬(i.val < r) := by omega
                    have hne : i.val ≠ r := by omega
                    simp only [hic, hic1, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, hnlt, hne]
                  · have hic1 : ¬(i.val - 1 < cnt) := by omega
                    simp only [hic, hic1, ↓reduceIte]
                rw [hclo_eq, hchi_eq]
                exact ((hcs ⟨i.val - 1, by omega⟩).2).frame (by dsimp [sl_mid]; omega)
                  (hsibling_frame ⟨i.val - 1, by omega⟩
                    (Fin.ne_of_val_ne (by dsimp [r_fin]; omega)))
                  (fun _ _ _ => rfl)
      -- Potential drop from `T` to `T_mid`
      have hpot_mid : 2 * (BTreeTree.branch idx (cnt + 1) cs_mid).potential tMin + (tMin - 2) ≤
          2 * (BTreeTree.branch idx cnt cs).potential tMin := by
        simp only [BTreeTree.potential]
        let r1 : Fin (cnt + 1 + 1) := ⟨r + 1, by omega⟩
        have hsucc_eq : ∀ k : Fin (cnt + 1),
            cs_mid (r1.succAbove k) = Function.update cs r_fin leftT k := fun k => by
          unfold Fin.succAbove
          by_cases hlt : k.castSucc < r1
          · have hk_le : k.val ≤ r := by
              change k.val < r + 1 at hlt; omega
            simp only [hlt, ↓reduceIte]
            rcases eq_or_lt_of_le hk_le with heq | hk_lt
            · have hk_eq : k = r_fin := Fin.ext heq
              subst hk_eq
              rw [Function.update_self]
              exact hcs_eq_r _ rfl
            · have hk_ne : k ≠ r_fin := Fin.ne_of_val_ne hk_lt.ne
              rw [Function.update_of_ne hk_ne]
              exact hcs_lt _ hk_lt
          · have hk_gt : r < k.val := by
              change ¬(k.val < r + 1) at hlt; omega
            have hk_ne : k ≠ r_fin := Fin.ne_of_val_ne hk_gt.ne'
            simp only [hlt, ↓reduceIte]
            rw [Function.update_of_ne hk_ne, hcs_gt _ (by dsimp; omega)]
            congr 1
        rw [Fin.sum_univ_succAbove _ r1]
        have hr1_eq : cs_mid r1 = rightT := hcs_eq_r1 r1 rfl
        rw [hr1_eq, sum_congr rfl fun k _ => congrArg (BTreeTree.potential tMin) (hsucc_eq k)]
        have hsum1 := Finset.add_sum_erase univ
          (fun k => (Function.update cs r_fin leftT k).potential tMin) (mem_univ r_fin)
        have hsum2 := Finset.add_sum_erase univ
          (fun k => (cs k).potential tMin) (mem_univ r_fin)
        have her_eq : ∑ k ∈ univ.erase r_fin,
            (Function.update cs r_fin leftT k).potential tMin =
            ∑ k ∈ univ.erase r_fin, (cs k).potential tMin :=
          sum_congr rfl fun k hk => by rw [Function.update_of_ne (mem_erase.mp hk).1]
        rw [← hsum1, ← hsum2, her_eq, Function.update_self]
        omega
      -- Now descend into the non-full target child `r_next` of `T_mid` on `sl_mid`!
      obtain ⟨hr_mid_le, hclo_mid_q, hq_chi_mid, hother_mid⟩ :=
        branch_child_routing (by omega) hcap hv_mid hhi hqlo hqhi
      let r_next : Fin (cnt + 1 + 1) :=
        ⟨swarRank fpBits (2 * tMin) (cnt + 1) q (sl_mid.nodes idx).keysWord,
          Nat.lt_succ_of_le hr_mid_le⟩
      have hr_next_val : r_next.val = if sep < q then r + 1 else r := by
        have hnd3_idx : sl_mid.nodes idx = parentNd' := Function.update_self idx parentNd' nodes2
        by_contra hne_rn
        have hq_ne := hother_mid ⟨if sep < q then r + 1 else r, by split_ifs <;> omega⟩
          (by dsimp; exact Ne.symm hne_rn) q
        rw [hnd3_idx] at hq_ne
        dsimp only [parentNd'] at hq_ne
        by_cases hsq : sep < q
        · simp only [hsq, ↓reduceIte] at hq_ne
          have h1 : childLo W_key lo (wordInsertAt W_key r sep nd.keysWord) (r + 1) ≤ q := by
            unfold childLo
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
              laneGet_wordInsertAt hsep_lt_W, lt_irrefl]
            omega
          have h2 : q ≤ childHi W_key hi (cnt + 1)
              (wordInsertAt W_key r sep nd.keysWord) (r + 1) := by
            unfold childHi
            by_cases hrc : r < cnt
            · have ha : r + 1 < cnt + 1 := by omega
              have hb : ¬(r + 1 < r) := by omega
              have hc : r + 1 ≠ r := by omega
              simp only [ha, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, hb, hc,
                Nat.add_sub_cancel]
              unfold childHi at hq_chi; simpa [hrc] using hq_chi
            · have ha : ¬(r + 1 < cnt + 1) := by omega
              simp only [ha, ↓reduceIte]; exact hqhi
          exact hq_ne h1 h2 rfl
        · simp only [hsq, ↓reduceIte] at hq_ne
          have h1 : childLo W_key lo (wordInsertAt W_key r sep nd.keysWord) r ≤ q := by
            unfold childLo
            split_ifs with hr0
            · exact hqlo
            · rw [laneGet_wordInsertAt hsep_lt_W]; simp only [show r - 1 < r by omega, ↓reduceIte]
              unfold childLo at hclo_q; simpa [hr0] using hclo_q
          have h2 : q ≤ childHi W_key hi (cnt + 1)
              (wordInsertAt W_key r sep nd.keysWord) r := by
            unfold childHi
            have ha : r < cnt + 1 := by omega
            simp only [ha, ↓reduceIte, laneGet_wordInsertAt hsep_lt_W, lt_irrefl]
            omega
          exact hq_ne h1 h2 rfl
      have hnext_rt : (if sep < q then rightIdx else childIdx) = (cs_mid r_next).rootIdx := by
        by_cases hsq : sep < q
        · simp only [hsq, ↓reduceIte] at hr_next_val ⊢
          rw [hcs_eq_r1 r_next hr_next_val, hrtR]
        · simp only [hsq, ↓reduceIte] at hr_next_val ⊢
          rw [hcs_eq_r r_next hr_next_val, hrtL]
      have hnext_nonfull : metaCount (sl_mid.nodes (cs_mid r_next).rootIdx).metaWord <
          2 * tMin - 1 := by
        rw [← hnext_rt]
        by_cases hsq : sep < q
        · simp only [hsq, ↓reduceIte]; dsimp only [sl_mid]; omega
        · simp only [hsq, ↓reduceIte]; dsimp only [sl_mid]; omega
      have hnext_ht : (cs_mid r_next).height = (cs r_fin).height := by
        by_cases hsq : sep < q
        · simp only [hsq, ↓reduceIte] at hr_next_val
          rw [hcs_eq_r1 r_next hr_next_val, hhtR]
        · simp only [hsq, ↓reduceIte] at hr_next_val
          rw [hcs_eq_r r_next hr_next_val, hhtL]
      have hchi_mid_le :
          childHi W_key hi (cnt + 1) (sl_mid.nodes idx).keysWord r_next.val ≤ hi := by
        obtain ⟨_, _, _, _, _, _, _, hhi_m, hmono_m, _, _, _, _⟩ := hv_mid
        unfold childHi
        split_ifs with hlt_m
        · rcases eq_or_lt_of_le (by omega : r_next.val ≤ cnt) with heq | hlt'
          · rw [heq]; exact hhi_m.le
          · exact (hmono_m r_next.val cnt hlt' (by omega)).le.trans hhi_m.le
        · exact le_rfl
      rw [hnext_rt]
      obtain ⟨halloc_rec, hrt_rec, hfr_rec, T_c', hrt_Tc', hht_Tc', hns_Tc', hpot_Tc', hv_Tc'⟩ :=
        ih (hchi_mid_le.trans_lt hhi) hclo_mid_q hq_chi_mid
          (hv_mid.2.2.2.2.2.2.2.2.2.2.2.2 r_next).2 hnext_nonfull
          (by rw [hnext_ht]; omega) (by rw [hnext_ht]; dsimp [sl_mid]; omega)
      obtain ⟨hfr_mid, T', hrt_T', hht_T', hns_T', hpot_T', hv_T'⟩ :=
        lift_branch_child_insert hv_mid
          (fun i hi => hother_mid i (Fin.val_ne_of_ne hi))
          halloc_rec hfr_rec hrt_Tc' hht_Tc' hns_Tc' hpot_Tc' hv_Tc'
      have hsub_Tmid : ∀ v ∈ (BTreeTree.branch idx (cnt + 1) cs_mid).nodeSet,
          v ∈ (BTreeTree.branch idx cnt cs).nodeSet ∨ v = rightIdx := by
        intro v hv_in
        rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
        rcases hv_in with rfl | ⟨i, _, hvi⟩
        · left; simp [BTreeTree.nodeSet]
        · by_cases hi1 : i.val < r
          · rw [hcs_lt i hi1] at hvi
            left; exact mem_insert_of_mem (mem_biUnion.mpr ⟨⟨i.val, by omega⟩, mem_univ _, hvi⟩)
          · by_cases hi2 : i.val = r
            · rw [hcs_eq_r i hi2] at hvi
              have hs := hsubL hvi; rw [mem_insert, mem_erase] at hs
              rcases hs with rfl | ⟨_, hm⟩
              · left; exact mem_insert_of_mem
                  (mem_biUnion.mpr ⟨r_fin, mem_univ _, (cs r_fin).rootIdx_mem_nodeSet⟩)
              · left; exact mem_insert_of_mem (mem_biUnion.mpr ⟨r_fin, mem_univ _, hm⟩)
            · by_cases hi3 : i.val = r + 1
              · rw [hcs_eq_r1 i hi3] at hvi
                have hs := hsubR hvi; rw [mem_insert, mem_erase] at hs
                rcases hs with rfl | ⟨_, hm⟩
                · right; rfl
                · left; exact mem_insert_of_mem (mem_biUnion.mpr ⟨r_fin, mem_univ _, hm⟩)
              · rw [hcs_gt i (by omega)] at hvi
                left; exact mem_insert_of_mem
                  (mem_biUnion.mpr ⟨⟨i.val - 1, by omega⟩, mem_univ _, hvi⟩)
      have hht_Tmid_eq : (BTreeTree.branch idx (cnt + 1) cs_mid).height =
          (BTreeTree.branch idx cnt cs).height := by
        rw [BTreeTree.height_branch_of_eq hht_mid, BTreeTree.height_branch_of_eq hht]
        by_cases h0r : 0 < r
        · rw [hcs_lt ⟨0, Nat.succ_pos _⟩ h0r]
        · rw [hcs_eq_r ⟨0, Nat.succ_pos _⟩ (by dsimp; omega), hhtL]
          exact congrArg (1 + ·) (hht r_fin)
      refine ⟨(by dsimp [sl_mid]; omega : sl.alloc ≤ sl_mid.alloc).trans halloc_rec,
        hrt_rec, ?_, T', hrt_T', hht_T'.trans hht_Tmid_eq, ?_, ?_, hv_T'⟩
      · intro v hv_lt hv_not
        have hv_not_mid : v ∉ (BTreeTree.branch idx (cnt + 1) cs_mid).nodeSet := by
          intro hvm
          rcases hsub_Tmid v hvm with h1 | rfl
          · exact hv_not h1
          · dsimp only [rightIdx] at hv_lt; omega
        have h1 := hfr_mid v (by dsimp [sl_mid]; omega) hv_not_mid
        have hv_ne_idx : v ≠ idx := fun heq => hv_not (by subst heq; simp [BTreeTree.nodeSet])
        have hv_ne_r : v ≠ rightIdx := by dsimp [rightIdx]; omega
        have hv_ne_c : v ≠ childIdx := fun heq => hv_not (by
          subst heq
          exact mem_insert_of_mem
            (mem_biUnion.mpr ⟨r_fin, mem_univ _, (cs r_fin).rootIdx_mem_nodeSet⟩))
        rw [h1]
        dsimp only [sl_mid, nodes3, nodes2, nodes1]
        rw [Function.update_of_ne hv_ne_idx, Function.update_of_ne hv_ne_r,
          Function.update_of_ne hv_ne_c]
      · intro v hv_in
        rcases hns_T' v hv_in with hvm | hv_ge
        · rcases hsub_Tmid v hvm with h1 | rfl
          · left; exact h1
          · right; dsimp only [rightIdx]; exact le_rfl
        · right; dsimp only [sl_mid] at hv_ge; omega
      · set d_rec := descendSplitToLeaf fpBits W_val tMin fuel' sl_mid (cs_mid r_next).rootIdx q
        have hfinish_alloc : (finishLeafInsert fpBits W_val tMin d_rec.1 d_rec.2 q val).alloc =
            d_rec.1.alloc := by
          unfold finishLeafInsert
          dsimp only
          split_ifs <;> rfl
        have hgoal_eq :
            (finishLeafInsert fpBits W_val tMin d_rec.1 d_rec.2 q val).alloc - sl.alloc =
            (d_rec.1.alloc - sl_mid.alloc) + 1 := by
          rw [hfinish_alloc]
          have halloc_rec' : sl_mid.alloc ≤ d_rec.1.alloc := by
            rwa [hfinish_alloc] at halloc_rec
          dsimp only [sl_mid] at halloc_rec' ⊢
          omega
        change (tMin - 2) *
            ((finishLeafInsert fpBits W_val tMin d_rec.1 d_rec.2 q val).alloc - sl.alloc) +
              2 * T'.potential tMin ≤ _
        rw [hfinish_alloc] at hpot_T'
        rw [hgoal_eq, Nat.mul_add, mul_one]
        calc (tMin - 2) * (d_rec.1.alloc - sl_mid.alloc) + (tMin - 2) + 2 * T'.potential tMin
            = ((tMin - 2) * (d_rec.1.alloc - sl_mid.alloc) + 2 * T'.potential tMin) +
                (tMin - 2) := by ring
          _ ≤ (2 * (BTreeTree.branch idx (cnt + 1) cs_mid).potential tMin + 2) + (tMin - 2) :=
              Nat.add_le_add_right hpot_T' _
          _ = (2 * (BTreeTree.branch idx (cnt + 1) cs_mid).potential tMin + (tMin - 2)) + 2 := by
              ring
          _ ≤ 2 * (BTreeTree.branch idx cnt cs).potential tMin + 2 :=
              Nat.add_le_add_right hpot_mid 2
    · -- Subcase A: child `r_fin` is already non-full!
      have hstep : descendSplitToLeaf fpBits W_val tMin (fuel' + 1) sl idx q =
          descendSplitToLeaf fpBits W_val tMin fuel' sl childIdx q := by
        dsimp only [descendSplitToLeaf]
        have hcond : (metaCount (sl.nodes childIdx).metaWord == 2 * tMin - 1) = false := by
          simp [hfull_c]
        rw [hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hnd_eq : sl.nodes idx = nd := rfl
        rw [hnd_eq]
        change (let r0 := swarRank fpBits (2 * tMin) cnt q nd.keysWord
          let childIdx0 := laneGet W_val nd.valsWord r0
          if (metaCount (sl.nodes childIdx0).metaWord == 2 * tMin - 1) = true then _ else _) = _
        have hr_eq : swarRank fpBits (2 * tMin) cnt q nd.keysWord = r := rfl
        dsimp only
        rw [hr_eq, hval_r, hcond]
        simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hstep]
      have hnf_c : metaCount (sl.nodes (cs r_fin).rootIdx).metaWord < 2 * tMin - 1 := by
        dsimp only [childIdx] at hcnt_c_le hfull_c
        omega
      obtain ⟨halloc_rec, hrt_rec, hfr_rec, T_c', hrt_Tc', hht_Tc', hns_Tc', hpot_Tc', hv_Tc'⟩ :=
        ih (hchi_le.trans_lt hhi) hclo_q hq_chi (hcs r_fin).2
          hnf_c (by omega) (by omega)
      obtain ⟨hfr_all, T', hrt_T', hht_T', hns_T', hpot_T', hv_T'⟩ :=
        lift_branch_child_insert ⟨hidx, hmeta, hdeg, by omega, hkw, hvw, hlo0, hhi_last, hmono,
          hnot, hdisj, hht, hcs⟩
          (fun i hi => hother i (Fin.val_ne_of_ne hi))
          halloc_rec hfr_rec hrt_Tc' hht_Tc' hns_Tc' hpot_Tc' hv_Tc'
      exact ⟨halloc_rec, hrt_rec, hfr_all, T', hrt_T', hht_T', hns_T', hpot_T', hv_T'⟩

/-! ## Section 2: Full `btreeInsert` specification and `ValidSlice` invariant -/

/-- `btreeInsert` factors into `ensureRootSlice`, `splitRootIfFull`, `descendSplitToLeaf`, and
`finishLeafInsert`. -/
theorem btreeInsert_eq_finishLeafInsert (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (q val : ℕ) :
    btreeInsert fpBits W_val tMin sl q val =
      let sl0 := ensureRootSlice sl
      let sl1 := splitRootIfFull fpBits W_val tMin sl0
      let p := descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 sl1.root q
      finishLeafInsert fpBits W_val tMin p.1 p.2 q val :=
  rfl

/-- Top-level subtree specification of `btreeInsert` on an already-initialized slice (`1 ≤ alloc`):
increases height by at most `1` and Overmars split potential `(tMin - 2) * (alloc - 1) + 2 * pot`
by at most `2`. -/
theorem btreeInsert_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q val : ℕ}
    (ht3 : 3 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (halloc_val : sl.alloc + hMaxBTree + 2 < 2 ^ W_val)
    (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hht_lt : T.height < hMaxBTree)
    (hq : q < 2 ^ fpBits) (hval : val < 2 ^ W_val) :
    let sl' := btreeInsert fpBits W_val tMin sl q val
    1 ≤ sl'.alloc ∧
      sl'.alloc ≤ sl.alloc + hMaxBTree + 2 ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height ≤ T.height + 1 ∧
        (tMin - 2) * (sl'.alloc - 1) + 2 * T'.potential tMin ≤
          (tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin + 2 ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1)
          (Function.update mapFn q (some val)) T' := by
  have hens : ensureRootSlice sl = sl := by
    unfold ensureRootSlice
    have hnz : sl.alloc ≠ 0 := by omega
    simp [hnz]
  obtain ⟨ha1_pos, ha1_le, hrt1, T1, hT1_rt, hT1_nf, hT1_ht, hT1_pot, hv1⟩ :=
    splitRootIfFull_spec ht3 halloc_pos (by omega) hroot hv
  set sl1 := splitRootIfFull fpBits W_val tMin sl
  have hhi : 2 ^ fpBits - 1 < 2 ^ fpBits := Nat.sub_lt (Nat.two_pow_pos fpBits) (by decide)
  have hfuel1 : T1.height ≤ hMaxBTree := by omega
  have halloc1_val : sl1.alloc + T1.height ≤ 2 ^ W_val := by omega
  have hb_eq : btreeInsert fpBits W_val tMin sl q val =
      finishLeafInsert fpBits W_val tMin
        (descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 T1.rootIdx q).1
        (descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 T1.rootIdx q).2 q val := by
    unfold btreeInsert
    rw [hens]
    change finishLeafInsert fpBits W_val tMin
      (descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 sl1.root q).1
      (descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 sl1.root q).2 q val = _
    rw [← hT1_rt]
  change 1 ≤ (btreeInsert fpBits W_val tMin sl q val).alloc ∧
    (btreeInsert fpBits W_val tMin sl q val).alloc ≤ sl.alloc + hMaxBTree + 2 ∧
    ∃ T' : BTreeTree,
      T'.rootIdx = (btreeInsert fpBits W_val tMin sl q val).root ∧
      T'.height ≤ T.height + 1 ∧
      (tMin - 2) * ((btreeInsert fpBits W_val tMin sl q val).alloc - 1) + 2 * T'.potential tMin ≤
        (tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin + 2 ∧
      ValidSubtree true fpBits W_val tMin (btreeInsert fpBits W_val tMin sl q val).alloc
        (btreeInsert fpBits W_val tMin sl q val).nodes 0 (2 ^ fpBits - 1)
        (Function.update mapFn q (some val)) T'
  rw [hb_eq]
  obtain ⟨halloc_le2, hrt2, _, T', hT'_rt, hT'_ht, _, hpot2, hv'⟩ :=
    finishLeafInsert_descendSplitToLeaf_spec ht3 hcap hval hhi (Nat.zero_le q) (by omega)
      hv1 (by rwa [hT1_rt]) hfuel1 halloc1_val
  set p := descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 T1.rootIdx q
  set sl' := finishLeafInsert fpBits W_val tMin p.1 p.2 q val
  have hp_alloc_le : p.1.alloc ≤ sl1.alloc + hMaxBTree := by
    have hstep_alloc : ∀ (f cur : ℕ) (s : BTreeSlice),
        (descendSplitToLeaf fpBits W_val tMin f s cur q).1.alloc ≤ s.alloc + f := by
      intro f
      induction f with
      | zero => intro cur s; simp [descendSplitToLeaf]
      | succ f ihf =>
        intro cur s
        dsimp only [descendSplitToLeaf]
        by_cases h1 : metaIsLeaf (s.nodes cur).metaWord = true
        · simp only [h1, ↓reduceIte]; omega
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : (metaCount (s.nodes (laneGet W_val (s.nodes cur).valsWord
              (swarRank fpBits (2 * tMin) (metaCount (s.nodes cur).metaWord) q
                (s.nodes cur).keysWord))).metaWord == 2 * tMin - 1) = true
          · simp only [h2, ↓reduceIte]
            refine (ihf _ _).trans ?_
            dsimp only
            omega
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
            exact (ihf _ _).trans (by omega)
    exact hstep_alloc hMaxBTree T1.rootIdx sl1
  have hsl'_alloc_eq : sl'.alloc = p.1.alloc := by
    dsimp only [sl', finishLeafInsert]
    split_ifs <;> rfl
  have hcomb_alloc : sl'.alloc - 1 = (sl1.alloc - 1) + (sl'.alloc - sl1.alloc) := by omega
  refine ⟨by omega, by omega, T', hT'_rt.trans (hT1_rt.trans hrt2.symm), by omega, ?_, hv'⟩
  rw [hcomb_alloc, Nat.mul_add]
  calc (tMin - 2) * (sl1.alloc - 1) + (tMin - 2) * (sl'.alloc - sl1.alloc) + 2 * T'.potential tMin
      = (tMin - 2) * (sl1.alloc - 1) +
          ((tMin - 2) * (sl'.alloc - sl1.alloc) + 2 * T'.potential tMin) := by ring
    _ ≤ (tMin - 2) * (sl1.alloc - 1) + (2 * T1.potential tMin + 2) :=
        Nat.add_le_add_left hpot2 _
    _ = ((tMin - 2) * (sl1.alloc - 1) + 2 * T1.potential tMin) + 2 := by ring
    _ ≤ ((tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin) + 2 :=
        Nat.add_le_add_right hT1_pot 2

/-- Self-contained slice validity predicate coupling `BTreeSlice` (`alloc = 0` empty or `1 ≤ alloc`
rooted tree) with insertion count `insCount`. -/
@[expose] def ValidSlice (fpBits W_val tMin insCount : ℕ) (sl : BTreeSlice)
    (mapFn : ℕ → Option ℕ) : Prop :=
  (sl.alloc = 0 ∧ mapFn = fun _ => none) ∨
  (1 ≤ sl.alloc ∧
    ∃ T : BTreeTree,
      T.rootIdx = sl.root ∧
      (tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin ≤ 2 * insCount ∧
      ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)

/-- Every node inside a `ValidSubtree` automatically satisfies the packed bit-width bounds whenever
`1 ≤ tMin` and `4 * tMin ≤ 2 ^ metaBits`. -/
theorem ValidSubtree.node_bits_lt {isRoot : Bool} {metaBits fpBits W_val tMin alloc : ℕ}
    {nodes : ℕ → BTreeNode} {lo hi : ℕ} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht1 : 1 ≤ tMin) (hmeta_cap : 4 * tMin ≤ 2 ^ metaBits)
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    ∀ v ∈ T.nodeSet,
      (nodes v).metaWord < 2 ^ metaBits ∧
      (nodes v).keysWord < 2 ^ ((2 * tMin) * (fpBits + 2)) ∧
      (nodes v).valsWord < 2 ^ ((2 * tMin) * W_val) := by
  induction T generalizing isRoot lo hi with
  | leaf idx cnt =>
    obtain ⟨_, hmeta, hcnt, hkw, hvw, _⟩ := hv
    intro v hv_in
    rw [BTreeTree.nodeSet, mem_singleton] at hv_in
    subst hv_in
    refine ⟨?_, ?_, ?_⟩
    · rw [hmeta]; unfold mkNodeMeta; simp only [↓reduceIte]; omega
    · exact hkw.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    · exact hvw.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  | branch idx cnt cs ih =>
    obtain ⟨_, hmeta, _, hcnt, hkw, hvw, _, _, _, _, _, _, hcs⟩ := hv
    intro v hv_in
    rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
    rcases hv_in with rfl | ⟨i, _, hvi⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hmeta]; unfold mkNodeMeta; simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · exact hkw.trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      · exact hvw.trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    · exact ih i (hcs i).2 v hvi

/-- Unallocated slice (`alloc = 0`) satisfies `ValidSlice` for the empty map. -/
theorem validSlice_zero (fpBits W_val tMin insCount : ℕ) (nodes : ℕ → BTreeNode) :
    ValidSlice fpBits W_val tMin insCount ⟨0, 0, nodes⟩ (fun _ => none) :=
  Or.inl ⟨rfl, rfl⟩

/-! ## Section 3: Concrete `SuccinctWhpParams` instantiation (`ValidWhpSlice`) -/

/-- Concrete `SuccinctWhp` slice invariant at capacity `n_max` and insertion count `insCount`. -/
@[expose] def ValidWhpSlice (n_max insCount : ℕ) (sl : BTreeSlice)
    (mapFn : ℕ → Option ℕ) : Prop :=
  ValidSlice (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) insCount sl mapFn

/-- Parameter fit bounds for `ValidWhpSlice` when `whpThreshold c ≤ n_max`. -/
theorem whpSlice_param_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    3 ≤ tMinWhp n_max ∧
    4 * tMinWhp n_max ≤ 2 ^ nodeMetaBitsWhp n_max ∧
    2 * tMinWhp n_max < 2 ^ keyLaneBitsWhp n_max ∧
    nSliceWhp n_max < 2 ^ valLaneBitsWhp n_max := by
  have h8 := eight_le_tMinWhp hth
  have hm := bMinWhp_le_log hth
  have hbm := le_bMinWhp c
  have hell := one_le_ellWhp n_max
  have hn0 : n_max ≠ 0 := by have := whpThreshold_pos c; omega
  have hn4 : 4 ≤ n_max := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ Nat.log 2 n_max := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n_max := Nat.pow_log_le_self 2 hn0
  have ht_le_L : tMinWhp n_max ≤ scaleWhp n_max := by
    have ht_log : tMinWhp n_max ≤ Nat.log 2 n_max := by
      unfold tMinWhp
      exact max_le (by omega) (Nat.div_le_self _ _)
    have h1 : Nat.log 2 n_max ≤ Nat.clog 2 (max n_max 4) :=
      (Nat.log_mono_right (le_max_left n_max 4)).trans (Nat.log_le_clog 2 _)
    exact (ht_log.trans h1).trans (Nat.le_pow_clog Nat.one_lt_two _)
  have hmeta_lt : 4 * tMinWhp n_max ≤ 2 ^ nodeMetaBitsWhp n_max := by
    calc 4 * tMinWhp n_max ≤ 4 * scaleWhp n_max := Nat.mul_le_mul_left 4 ht_le_L
      _ = 2 ^ 2 * 2 ^ ellWhp n_max := rfl
      _ = 2 ^ (ellWhp n_max + 2) := by rw [← Nat.pow_add, add_comm]
      _ ≤ 2 ^ nodeMetaBitsWhp n_max := by
          unfold nodeMetaBitsWhp
          exact Nat.pow_le_pow_right (by decide) (by omega)
  have hkey_lt : 2 * tMinWhp n_max < 2 ^ keyLaneBitsWhp n_max := by
    have hpow : scaleWhp n_max ≤ 2 ^ fpBitsWhp n_max := by
      calc scaleWhp n_max = 2 ^ ellWhp n_max := rfl
        _ ≤ 2 ^ fpBitsWhp n_max := by
            unfold fpBitsWhp
            exact Nat.pow_le_pow_right (by decide) (by omega)
    have hfp_pos : 0 < 2 ^ fpBitsWhp n_max := Nat.two_pow_pos _
    calc 2 * tMinWhp n_max ≤ 2 * 2 ^ fpBitsWhp n_max :=
          Nat.mul_le_mul_left 2 (ht_le_L.trans hpow)
      _ < 4 * 2 ^ fpBitsWhp n_max := by omega
      _ = 2 ^ keyLaneBitsWhp n_max := by
          unfold keyLaneBitsWhp
          rw [Nat.pow_add]
          ring
  have hnslice_lt : nSliceWhp n_max < 2 ^ valLaneBitsWhp n_max := by
    have hL2 := two_le_scaleWhp n_max
    have hL12_ge : 4096 ≤ (scaleWhp n_max) ^ 12 := by
      calc 4096 = 2 ^ 12 := by decide
        _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
    have hdiv_le : 32 * (scaleWhp n_max) ^ 12 / (tMinWhp n_max - 1) ≤
        32 * (scaleWhp n_max) ^ 12 := Nat.div_le_self _ _
    have hval_pow : 2 ^ valLaneBitsWhp n_max = 256 * (scaleWhp n_max) ^ 12 := by
      have hsc : scaleWhp n_max = 2 ^ ellWhp n_max := rfl
      unfold valLaneBitsWhp
      rw [hsc, Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm _ 12]
      ring
    unfold nSliceWhp
    rw [hval_pow]
    omega
  exact ⟨by omega, hmeta_lt, hkey_lt, hnslice_lt⟩

/-- `64 ≤ nSliceWhp n_max` unconditionally. -/
theorem sixty_four_le_nSliceWhp (n_max : ℕ) : 64 ≤ nSliceWhp n_max := by
  unfold nSliceWhp
  exact Nat.le_add_left 64 _

/-- **Bounded allocation and height theorem (`ValidWhpSlice.alloc_and_height_lt`)**:
Whenever `whpThreshold c ≤ n_max` and `insCount ≤ 8 * (scaleWhp n_max) ^ 12`, any
`ValidWhpSlice n_max insCount sl mapFn` has `sl.alloc + hMaxBTree + 4 < nSliceWhp n_max`, and any
tree spine `T` witnessing it has `T.height < hMaxBTree`. -/
theorem ValidWhpSlice.alloc_and_height_lt {c n_max insCount : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (scaleWhp n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn) :
    sl.alloc + hMaxBTree + 4 < nSliceWhp n_max ∧
    ∀ T : BTreeTree,
      ValidSubtree true (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.alloc sl.nodes 0 (2 ^ fpBitsWhp n_max - 1) mapFn T →
      T.height < hMaxBTree := by
  have h8 := eight_le_tMinWhp hth
  have hcube := scaleWhp_le_tMinWhp_cubed hth
  have h64 := sixty_four_le_nSliceWhp n_max
  have halloc_lt : sl.alloc + hMaxBTree + 4 < nSliceWhp n_max := by
    rcases hv with ⟨h0, _⟩ | ⟨_, T, _, hpot, _⟩
    · rw [hMaxBTree_eq]
      omega
    · have h2t : tMinWhp n_max - 1 ≤ 2 * (tMinWhp n_max - 2) := by omega
      have hmul : (sl.alloc - 1) * (tMinWhp n_max - 1) ≤ 32 * (scaleWhp n_max) ^ 12 := by
        calc (sl.alloc - 1) * (tMinWhp n_max - 1)
            ≤ (sl.alloc - 1) * (2 * (tMinWhp n_max - 2)) := Nat.mul_le_mul_left _ h2t
          _ = 2 * ((tMinWhp n_max - 2) * (sl.alloc - 1)) := by ring
          _ ≤ 2 * (2 * insCount) := by omega
          _ ≤ 32 * (scaleWhp n_max) ^ 12 := by omega
      have hdiv : sl.alloc - 1 ≤ 32 * (scaleWhp n_max) ^ 12 / (tMinWhp n_max - 1) :=
        (Nat.le_div_iff_mul_le (by omega)).mpr hmul
      set q_div := 32 * (scaleWhp n_max) ^ 12 / (tMinWhp n_max - 1)
      have hns_def : nSliceWhp n_max = q_div + 64 := rfl
      rw [hMaxBTree_eq]
      omega
  refine ⟨halloc_lt, fun T hT => ?_⟩
  by_contra hge
  have h42 : 42 ≤ T.height := by rw [hMaxBTree_eq] at hge; omega
  have hleaf_ge : 2 * (tMinWhp n_max) ^ 41 ≤ T.leafCount := by
    calc 2 * (tMinWhp n_max) ^ 41
        ≤ 2 * (tMinWhp n_max) ^ (T.height - 1) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ T.leafCount := hT.two_mul_pow_height_sub_one_le_leafCount (by omega) (by omega)
  have hleaf_le : T.leafCount ≤ sl.alloc :=
    (hT.leafCount_le_card_nodeSet).2.trans hT.card_nodeSet_le_alloc
  have hns_lt := (whpSlice_param_bounds hth).2.2.2
  have hval_pow : 2 ^ valLaneBitsWhp n_max = 256 * (scaleWhp n_max) ^ 12 := by
    have hsc : scaleWhp n_max = 2 ^ ellWhp n_max := rfl
    unfold valLaneBitsWhp
    rw [hsc, Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm _ 12]
    ring
  have h256_le : 256 ≤ 2 * (tMinWhp n_max) ^ 3 := by
    calc 256 ≤ 2 * 8 ^ 3 := by decide
      _ ≤ 2 * (tMinWhp n_max) ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h8 3)
  have hL12_le : (scaleWhp n_max) ^ 12 ≤ (tMinWhp n_max) ^ 36 := by
    calc (scaleWhp n_max) ^ 12 ≤ ((tMinWhp n_max) ^ 3) ^ 12 := Nat.pow_le_pow_left hcube 12
      _ = (tMinWhp n_max) ^ 36 := by rw [← Nat.pow_mul]
  have halloc_lt_pow : sl.alloc < 2 * (tMinWhp n_max) ^ 39 := by
    calc sl.alloc < nSliceWhp n_max := by omega
      _ < 2 ^ valLaneBitsWhp n_max := hns_lt
      _ = 256 * (scaleWhp n_max) ^ 12 := hval_pow
      _ ≤ (2 * (tMinWhp n_max) ^ 3) * (tMinWhp n_max) ^ 36 := Nat.mul_le_mul h256_le hL12_le
      _ = 2 * (tMinWhp n_max) ^ 39 := by rw [mul_assoc, ← Nat.pow_add]
  have h39_le_41 : 2 * (tMinWhp n_max) ^ 39 ≤ 2 * (tMinWhp n_max) ^ 41 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by decide))
  omega

/-- Lookup on a `ValidWhpSlice` returns `mapFn q` for every `q < 2 ^ fpBitsWhp n_max`. -/
theorem ValidWhpSlice.lookup_eq {c n_max insCount q : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (scaleWhp n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q = mapFn q := by
  obtain ⟨ht3, _, hkey_lt, _⟩ := whpSlice_param_bounds hth
  obtain ⟨_, hht_bound⟩ := hv.alloc_and_height_lt hth hins
  rcases hv with ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, _, hT⟩
  · simp [btreeLookup, h0]
  · exact btreeLookup_eq_of_subtree (by omega) hkey_lt ha_pos hrt hT (hht_bound T hT).le hq

/-- Deletion on a `ValidWhpSlice` preserves `ValidWhpSlice` at the same `insCount`. -/
theorem ValidWhpSlice.delete_spec {c n_max insCount q : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (scaleWhp n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    ValidWhpSlice n_max insCount
      (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q)
      (Function.update mapFn q none) := by
  obtain ⟨ht3, _, hkey_lt, _⟩ := whpSlice_param_bounds hth
  obtain ⟨_, hht_bound⟩ := hv.alloc_and_height_lt hth hins
  rcases hv with ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hpot, hT⟩
  · have hdel : btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q = sl := by
      simp [btreeDelete, h0]
    have hupd : Function.update (fun _ : ℕ => (none : Option ℕ)) q none = fun _ => none := by
      ext x; by_cases hx : x = q <;> simp [hx]
    rw [hdel, hupd]
    exact Or.inl ⟨h0, rfl⟩
  · obtain ⟨halloc_eq, T', hrt', _, hpot', hT'⟩ :=
      btreeDelete_subtree_spec (by omega) hkey_lt ha_pos hrt hT (hht_bound T hT).le hq
    refine Or.inr ⟨halloc_eq ▸ ha_pos, T', hrt', ?_, hT'⟩
    rw [halloc_eq]
    omega

/-- In-place value update on a `ValidWhpSlice` preserves `ValidWhpSlice` at the same `insCount`. -/
theorem ValidWhpSlice.update_spec {c n_max insCount q newVal : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (scaleWhp n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : newVal < 2 ^ valLaneBitsWhp n_max) :
    ValidWhpSlice n_max insCount
      (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal)
      (if (mapFn q).isSome then Function.update mapFn q (some newVal) else mapFn) := by
  obtain ⟨ht3, _, hkey_lt, _⟩ := whpSlice_param_bounds hth
  obtain ⟨_, hht_bound⟩ := hv.alloc_and_height_lt hth hins
  rcases hv with ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hpot, hT⟩
  · have hupd_sl :
        btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal = sl := by
      simp [btreeUpdate, h0]
    rw [hupd_sl]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact Or.inl ⟨h0, rfl⟩
  · obtain ⟨halloc_eq, T', hrt', _, hpot', hT'⟩ :=
      btreeUpdate_subtree_spec (by omega) hkey_lt ha_pos hrt hT (hht_bound T hT).le hq hval
    refine Or.inr ⟨halloc_eq ▸ ha_pos, T', hrt', ?_, hT'⟩
    rw [halloc_eq]
    omega

/-- Insertion on a `ValidWhpSlice` produces a `ValidWhpSlice` at `insCount + 1` with `alloc <
nSliceWhp n_max`! -/
theorem ValidWhpSlice.insert_spec {c n_max insCount q val : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (scaleWhp n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : val < 2 ^ valLaneBitsWhp n_max) :
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val
    sl'.alloc < nSliceWhp n_max ∧
    ValidWhpSlice n_max (insCount + 1) sl' (Function.update mapFn q (some val)) := by
  obtain ⟨ht3, _, hkey_lt, hns_lt⟩ := whpSlice_param_bounds hth
  obtain ⟨halloc_lt, hht_bound⟩ := hv.alloc_and_height_lt hth hins
  have h64 := sixty_four_le_nSliceWhp n_max
  rcases hv with ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hpot, hT⟩
  · -- Empty `alloc = 0` slice: `ensureRootSlice` creates a valid 0-key leaf at `alloc = 1`!
    let sl0 := ensureRootSlice sl
    have hsl0_alloc : sl0.alloc = 1 := by simp [sl0, ensureRootSlice, h0]
    have hsl0_root : (BTreeTree.leaf 0 0).rootIdx = sl0.root := by
      simp [BTreeTree.rootIdx, sl0, ensureRootSlice, h0]
    have hv0 : ValidSubtree true (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl0.alloc sl0.nodes 0 (2 ^ fpBitsWhp n_max - 1) (fun _ => none) (.leaf 0 0) := by
      dsimp only [ValidSubtree, sl0, ensureRootSlice]
      simp only [h0, ↓reduceIte, Function.update_self]
      refine ⟨by omega, trivial, by omega, by positivity, by positivity,
        fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ => Or.inr ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), trivial⟩⟩
    have hns_min : 1 + hMaxBTree + 2 < nSliceWhp n_max := by rw [hMaxBTree_eq]; omega
    have halloc0_val : sl0.alloc + hMaxBTree + 2 < 2 ^ valLaneBitsWhp n_max := by
      rw [hsl0_alloc]
      exact hns_min.trans hns_lt
    have hens : ensureRootSlice sl0 = sl0 := by
      unfold ensureRootSlice
      simp [hsl0_alloc]
    have hins_eq : btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val =
        btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl0 q val := by
      unfold btreeInsert
      rw [hens]
    change (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val).alloc <
        nSliceWhp n_max ∧
      ValidWhpSlice n_max (insCount + 1)
        (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val)
        (Function.update (fun _ : ℕ => (none : Option ℕ)) q (some val))
    rw [hins_eq]
    obtain ⟨ha'_pos, ha'_le, T', hrt', _, hpot', hT'⟩ :=
      btreeInsert_subtree_spec ht3 hkey_lt (by omega) halloc0_val hsl0_root hv0
        (by simp [BTreeTree.height, hMaxBTree_eq]) hq hval
    have hpot0 : (BTreeTree.leaf 0 0).potential (tMinWhp n_max) = 0 := by
      simp [BTreeTree.potential]
    rw [hsl0_alloc, Nat.sub_self, Nat.mul_zero, hpot0] at hpot'
    refine ⟨by omega, Or.inr ⟨ha'_pos, T', hrt', by omega, hT'⟩⟩
  · have halloc_val : sl.alloc + hMaxBTree + 2 < 2 ^ valLaneBitsWhp n_max :=
      (by omega : sl.alloc + hMaxBTree + 2 < nSliceWhp n_max).trans hns_lt
    obtain ⟨ha'_pos, ha'_le, T', hrt', _, hpot', hT'⟩ :=
      btreeInsert_subtree_spec ht3 hkey_lt ha_pos halloc_val hrt hT (hht_bound T hT) hq hval
    refine ⟨by omega, Or.inr ⟨ha'_pos, T', hrt', by omega, hT'⟩⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
