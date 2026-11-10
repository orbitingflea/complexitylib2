/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.SuccinctWhpSwarBTree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subtree Correctness and Node-Splitting Lemmas for the SWAR B+-Tree

This module proves sorted SWAR rank routing (`swarRank_sorted_spec`, `branch_child_routing`),
subtree lookup, deletion, and in-place value update (`btreeLookup_eq_of_subtree`,
`btreeDelete_subtree_spec`, `btreeUpdate_subtree_spec`), unified proactive full-node splitting
(`splitFullNode_spec`, `splitRootIfFull_spec`), and leaf insertion (`finishLeafInsert_leaf_spec`)
for the top-down split-only SWAR B+-tree defined in
`Complexity.DataStructure.Dictionary.SuccinctWhpSwarBTree`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.finishLeafInsert`:
  leaf insertion/overwrite post-step of `btreeInsert`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeLookup_eq_of_subtree`:
  exact lookup agreement `btreeLookup ... sl q = mapFn q`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeDelete_subtree_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeUpdate_subtree_spec`:
  preservation of `ValidSubtree` and non-increasing `potential` under deletion and update.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.splitFullNode_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.splitRootIfFull_spec`:
  proactive node splitting with Overmars' split-potential drop.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.finishLeafInsert_leaf_spec`:
  exact map refinement and count bound for leaf insertion/overwrite.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Finset
open scoped BigOperators

/-! ## Section 1: Sorted SWAR rank characterization, descent, lookup, delete, and update -/

/-- Partition property of `swarRank` on a strictly increasing lane array:
`r ≤ cnt`, lanes `< r` are `< q`, and lanes `r .. cnt - 1` are `≥ q`. -/
theorem swarRank_sorted_spec {fpBits capLanes cnt q keysWord : ℕ}
    (hcnt : cnt < capLanes) (hcap : capLanes < 2 ^ (fpBits + 2))
    (hq : q < 2 ^ fpBits) (hkw : keysWord < 2 ^ (cnt * (fpBits + 2)))
    (hlanes : ∀ j < cnt, laneGet (fpBits + 2) keysWord j < 2 ^ fpBits)
    (hmono : ∀ i j, i < j → j < cnt →
      laneGet (fpBits + 2) keysWord i < laneGet (fpBits + 2) keysWord j) :
    let r := swarRank fpBits capLanes cnt q keysWord
    r ≤ cnt ∧
      (∀ j < r, laneGet (fpBits + 2) keysWord j < q) ∧
      (∀ j, r ≤ j → j < cnt → q ≤ laneGet (fpBits + 2) keysWord j) := by
  set W := fpBits + 2
  set S := (range cnt).filter fun j => laneGet W keysWord j < q
  have hr_eq : swarRank fpBits capLanes cnt q keysWord = #S :=
    swarRank_eq_count_lt hcnt hcap hq hkw hlanes
  dsimp only
  rw [hr_eq]
  refine ⟨(card_filter_le _ _).trans_eq (card_range cnt), fun j hj => ?_, fun j hrj hjc => ?_⟩
  · by_contra hnq
    have hsub : S ⊆ range j := by
      intro k hk
      obtain ⟨hk_mem, hk_lt⟩ := mem_filter.mp hk
      have hkc : k < cnt := mem_range.mp hk_mem
      rw [mem_range]
      by_contra hjk
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hjk) with rfl | hlt
      · exact hnq hk_lt
      · exact hnq ((hmono j k hlt hkc).trans hk_lt)
    have hle : #S ≤ j := (card_le_card hsub).trans_eq (card_range j)
    omega
  · by_contra hlt_q
    have hlt_q' : laneGet W keysWord j < q := Nat.lt_of_not_le hlt_q
    have hsub : range (j + 1) ⊆ S := by
      intro k hk
      have hkj : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
      refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
      rcases eq_or_lt_of_le hkj with rfl | hlt
      · exact hlt_q'
      · exact (hmono k j hlt hjc).trans hlt_q'
    have hle : j + 1 ≤ #S := (card_range (j + 1)).symm.trans_le (card_le_card hsub)
    omega

/-- Internal branch routing: `swarRank` selects the unique child interval `[childLo r, childHi r]`
containing `q`, and every other child interval is disjoint from `{q}`. -/
theorem branch_child_routing {isRoot : Bool} {fpBits W_val tMin alloc idx cnt lo hi q : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {cs : Fin (cnt + 1) → BTreeTree}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn (.branch idx cnt cs))
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi) :
    let W_key := fpBits + 2
    let nd := nodes idx
    let r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    r ≤ cnt ∧
      childLo W_key lo nd.keysWord r ≤ q ∧
      q ≤ childHi W_key hi cnt nd.keysWord r ∧
      (∀ i : Fin (cnt + 1), i.val ≠ r →
        ∀ q', childLo W_key lo nd.keysWord i.val ≤ q' →
          q' ≤ childHi W_key hi cnt nd.keysWord i.val → q' ≠ q) := by
  obtain ⟨_, _, hdeg, hcnt_le, hkw, _, hlo0, hhi_last, hmono, _, _, _, _⟩ := hv
  have hcnt1 : 1 ≤ cnt := by
    cases isRoot
    · simp only [Bool.false_eq_true, ↓reduceIte] at hdeg; omega
    · simpa only [↓reduceIte] using hdeg
  have hlanes : ∀ j < cnt, laneGet (fpBits + 2) (nodes idx).keysWord j < 2 ^ fpBits := by
    intro j hj
    rcases eq_or_lt_of_le (by omega : j ≤ cnt - 1) with rfl | hlt
    · exact hhi_last.trans hhi
    · exact ((hmono j (cnt - 1) hlt (by omega)).trans hhi_last).trans hhi
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec
    (capLanes := 2 * tMin) (by omega) hcap (hqhi.trans_lt hhi) hkw hlanes hmono
  set W_key := fpBits + 2
  set nd := nodes idx
  set r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
  refine ⟨hr_le, ?_, ?_, ?_⟩
  · unfold childLo
    split_ifs with hr0
    · exact hqlo
    · exact Nat.succ_le_of_lt (hlt_r (r - 1) (by omega))
  · unfold childHi
    split_ifs with hrc
    · exact hge_r r le_rfl hrc
    · exact hqhi
  · intro i hne q' hq'_lo hq'_hi heq
    subst heq
    rcases lt_or_gt_of_ne hne with hilt | higt
    · have hi_cnt : i.val < cnt := by omega
      unfold childHi at hq'_hi
      simp only [hi_cnt, ↓reduceIte] at hq'_hi
      have hkey_lt : laneGet W_key nd.keysWord i.val < q' := hlt_r i.val hilt
      omega
    · have hr_cnt : r < cnt := by omega
      have hge_q : q' ≤ laneGet W_key nd.keysWord r := hge_r r le_rfl hr_cnt
      have hi_nz : i.val ≠ 0 := by omega
      unfold childLo at hq'_lo
      simp only [hi_nz, ↓reduceIte] at hq'_lo
      rcases eq_or_lt_of_le (by omega : r ≤ i.val - 1) with heq_r | hlt_ri
      · rw [← heq_r] at hq'_lo
        omega
      · have hm := hmono r (i.val - 1) hlt_ri (by omega)
        omega

/-- Generic root-to-leaf structural lemma for `descendToLeaf`: reaches the unique leaf covering `q`,
and any valid in-place replacement of that leaf lifts back to the whole subtree `T` with identical
`rootIdx`, `nodeSet`, `height`, and bounded `potential`. -/
theorem descendToLeaf_reaches_leaf {isRoot : Bool} {fpBits W_val tMin alloc lo hi q fuel : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hfuel : T.height ≤ fuel) :
    ∃ cnt loL hiL,
      let leafIdx := descendToLeaf fpBits W_val tMin nodes fuel T.rootIdx q
      leafIdx ∈ T.nodeSet ∧
      lo ≤ loL ∧ loL ≤ q ∧ q ≤ hiL ∧ hiL ≤ hi ∧
      ValidSubtree false fpBits W_val tMin alloc nodes loL hiL mapFn (.leaf leafIdx cnt) ∧
      ∀ (cnt' : ℕ) (nd' : BTreeNode) (mapFn' : ℕ → Option ℕ),
        cnt' ≤ cnt →
        (∀ q', q' ≠ q → mapFn' q' = mapFn q') →
        ValidSubtree false fpBits W_val tMin alloc (Function.update nodes leafIdx nd')
          loL hiL mapFn' (.leaf leafIdx cnt') →
        ∃ T' : BTreeTree,
          T'.rootIdx = T.rootIdx ∧
          T'.nodeSet = T.nodeSet ∧
          T'.height = T.height ∧
          T'.potential tMin ≤ T.potential tMin ∧
          ValidSubtree isRoot fpBits W_val tMin alloc (Function.update nodes leafIdx nd')
            lo hi mapFn' T' := by
  induction T generalizing isRoot lo hi fuel with
  | leaf idx cnt =>
    have hdesc : descendToLeaf fpBits W_val tMin nodes fuel idx q = idx := by
      cases fuel with
      | zero => rfl
      | succ f =>
        simp only [descendToLeaf, hv.2.1, metaIsLeaf_mkNodeMeta, ↓reduceIte]
    refine ⟨cnt, lo, hi, ?_⟩
    dsimp only [BTreeTree.rootIdx]
    rw [hdesc]
    have hv_false : ValidSubtree false fpBits W_val tMin alloc nodes lo hi mapFn (.leaf idx cnt) :=
      hv
    refine ⟨by simp [BTreeTree.nodeSet], le_rfl, hqlo, hqhi, le_rfl, hv_false,
      fun cnt' nd' mapFn' hcnt_le _ hv_new => ⟨.leaf idx cnt', rfl, rfl, rfl, ?_, hv_new⟩⟩
    simp only [BTreeTree.potential]
    omega
  | branch idx cnt cs ih =>
    have hH1 : 1 ≤ (BTreeTree.branch idx cnt cs).height := by
      simp [BTreeTree.height]
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hr_le, hclo_q, hq_chi, hother⟩ :=
      branch_child_routing ht2 hcap hv hhi hqlo hqhi
    obtain ⟨hidx, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono,
      hnot, hdisj, hht, hcs⟩ := hv
    set W_key := fpBits + 2
    set nd := nodes idx
    set r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    let r_fin : Fin (cnt + 1) := ⟨r, Nat.lt_succ_of_le hr_le⟩
    have hdesc_step :
        descendToLeaf fpBits W_val tMin nodes (fuel' + 1) idx q =
          descendToLeaf fpBits W_val tMin nodes fuel' (cs r_fin).rootIdx q := by
      simp only [descendToLeaf]
      rw [hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [(hcs r_fin).1]
    have hclo_ge : lo ≤ childLo W_key lo nd.keysWord r := by
      unfold childLo
      split_ifs with hr0
      · exact le_rfl
      · rcases eq_or_lt_of_le (Nat.zero_le (r - 1)) with heq0 | hpos
        · rw [← heq0]; exact hlo0.trans (Nat.le_succ _)
        · exact (hlo0.trans (hmono 0 (r - 1) hpos (by omega)).le).trans (Nat.le_succ _)
    have hchi_le : childHi W_key hi cnt nd.keysWord r ≤ hi := by
      unfold childHi
      split_ifs with hrc
      · rcases eq_or_lt_of_le (by omega : r ≤ cnt - 1) with heq | hlt
        · rw [heq]; exact hhi_last.le
        · exact (hmono r (cnt - 1) hlt (by omega)).le.trans hhi_last.le
      · exact le_rfl
    have hfuel_c : (cs r_fin).height ≤ fuel' := by
      rw [BTreeTree.height_branch_of_eq hht] at hfuel
      rw [hht r_fin]
      omega
    obtain ⟨cntL, loL, hiL, hmem_c, hloL1, hloL_q, hq_hiL, hhiL1, hv_leaf, hlift_c⟩ :=
      ih r_fin (hcs r_fin).2 (hchi_le.trans_lt hhi) hclo_q hq_chi hfuel_c
    refine ⟨cntL, loL, hiL, ?_⟩
    dsimp only [BTreeTree.rootIdx]
    rw [hdesc_step]
    set leafIdx := descendToLeaf fpBits W_val tMin nodes fuel' (cs r_fin).rootIdx q
    refine ⟨mem_insert_of_mem (mem_biUnion.mpr ⟨r_fin, mem_univ r_fin, hmem_c⟩),
      hclo_ge.trans hloL1, hloL_q, hq_hiL, hhiL1.trans hchi_le, hv_leaf, ?_⟩
    intro cnt' nd' mapFn' hcnt_le' hmap_other hv_new
    obtain ⟨T_r', hroot_r, hset_r, hht_r, hpot_r, hv_r'⟩ :=
      hlift_c cnt' nd' mapFn' hcnt_le' hmap_other hv_new
    let cs' : Fin (cnt + 1) → BTreeTree := Function.update cs r_fin T_r'
    have hset_eq : ∀ i, (cs' i).nodeSet = (cs i).nodeSet := fun i => by
      dsimp only [cs']
      by_cases hi : i = r_fin
      · subst hi; simp [hset_r]
      · simp [hi]
    have hht_eq : ∀ i, (cs' i).height = (cs i).height := fun i => by
      dsimp only [cs']
      by_cases hi : i = r_fin
      · subst hi; simp [hht_r]
      · simp [hi]
    have hroot_eq : ∀ i, (cs' i).rootIdx = (cs i).rootIdx := fun i => by
      dsimp only [cs']
      by_cases hi : i = r_fin
      · subst hi; simp [hroot_r]
      · simp [hi]
    have hleaf_ne_idx : leafIdx ≠ idx := fun heq => hnot r_fin (heq ▸ hmem_c)
    have hnodes_idx : Function.update nodes leafIdx nd' idx = nodes idx :=
      Function.update_of_ne hleaf_ne_idx.symm nd' nodes
    refine ⟨.branch idx cnt cs', rfl, ?_, ?_, ?_, ?_⟩
    · simp only [BTreeTree.nodeSet, hset_eq]
    · simp only [BTreeTree.height, hht_eq]
    · simp only [BTreeTree.potential]
      refine Nat.add_le_add_left (sum_le_sum fun i _ => ?_) _
      dsimp only [cs']
      by_cases hi : i = r_fin
      · subst hi; simp [hpot_r]
      · simp [hi]
    · refine ⟨hidx, ?_, hdeg, hcnt_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hnodes_idx] using hmeta
      · simpa only [hnodes_idx] using hkw
      · simpa only [hnodes_idx] using hvw
      · simpa only [hnodes_idx] using hlo0
      · simpa only [hnodes_idx] using hhi_last
      · simpa only [hnodes_idx] using hmono
      · intro i; rw [hset_eq i]; exact hnot i
      · intro i j hij; rw [hset_eq i, hset_eq j]; exact hdisj i j hij
      · intro i; rw [hht_eq i, hht_eq ⟨0, Nat.succ_pos cnt⟩]; exact hht i
      · intro i
        rw [hnodes_idx, hroot_eq i]
        refine ⟨(hcs i).1, ?_⟩
        dsimp only [cs']
        by_cases hi : i = r_fin
        · subst hi; simpa using hv_r'
        · rw [Function.update_of_ne hi]
          refine ((hcs i).2).frame le_rfl (fun v hv_in => ?_) (fun q' hq1 hq2 => ?_)
          · have hne_v : v ≠ leafIdx := fun heq =>
              Finset.disjoint_left.mp (hdisj i r_fin hi) hv_in (heq ▸ hmem_c)
            exact Function.update_of_ne hne_v nd' nodes
          · exact hmap_other q' (hother i (Fin.val_ne_of_ne hi) q' hq1 hq2)

/-- Exact leaf lookup lemma: on any valid `.leaf leafIdx cnt` covering `[loL, hiL]` with
`loL ≤ q ≤ hiL < 2 ^ fpBits`, SWAR rank lookup returns `mapFn q`. -/
theorem leaf_lookup_eq {fpBits W_val tMin alloc leafIdx cnt loL hiL q : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ}
    (ht1 : 1 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree false fpBits W_val tMin alloc nodes loL hiL mapFn (.leaf leafIdx cnt))
    (hhiL : hiL < 2 ^ fpBits) (hqlo : loL ≤ q) (hqhi : q ≤ hiL) :
    let W_key := fpBits + 2
    let nd := nodes leafIdx
    let cnt_nd := metaCount nd.metaWord
    let r := swarRank fpBits (2 * tMin) cnt_nd q nd.keysWord
    (if r < cnt_nd && laneGet W_key nd.keysWord r == q then
      some (laneGet W_val nd.valsWord r)
    else none) = mapFn q := by
  obtain ⟨_, hmeta, hcnt_le, hkw, _, hbounds, hmono, href⟩ := hv
  have hlanes : ∀ j < cnt, laneGet (fpBits + 2) (nodes leafIdx).keysWord j < 2 ^ fpBits :=
    fun j hj => (hbounds j hj).2.trans_lt hhiL
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec
    (capLanes := 2 * tMin) (by omega) hcap (hqhi.trans_lt hhiL) hkw hlanes hmono
  dsimp only
  rw [hmeta, metaCount_mkNodeMeta]
  set W_key := fpBits + 2
  set nd := nodes leafIdx
  set r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
  rcases href q hqlo hqhi with ⟨r₀, hr₀_lt, hkey_r₀, hmap_r₀⟩ | ⟨hnone_keys, hmap_none⟩
  · have hr_eq : r = r₀ := by
      rcases lt_trichotomy r r₀ with hlt | rfl | hgt
      · have h1 := hge_r r le_rfl (hlt.trans hr₀_lt)
        have h2 := hmono r r₀ hlt hr₀_lt
        omega
      · rfl
      · have h1 := hlt_r r₀ hgt
        omega
    subst hr_eq
    simp [hr₀_lt, hkey_r₀, hmap_r₀]
  · have hcond : (r < cnt && laneGet W_key nd.keysWord r == q) = false := by
      by_cases hrc : r < cnt
      · simp [hrc, hnone_keys r hrc]
      · simp [hrc]
    rw [hcond]
    simp [hmap_none]

/-- Exact lookup specification on any valid subtree `T` with `T.height ≤ hMaxBTree`. -/
theorem btreeLookup_eq_of_subtree {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q : ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits) :
    btreeLookup fpBits W_val tMin sl q = mapFn q := by
  have hhi : 2 ^ fpBits - 1 < 2 ^ fpBits := Nat.sub_lt (Nat.two_pow_pos fpBits) (by decide)
  obtain ⟨cntL, loL, hiL, _, _, hloL_q, hq_hiL, hhiL_le, hv_leaf, _⟩ :=
    descendToLeaf_reaches_leaf ht2 hcap hv hhi (Nat.zero_le q) (by omega) hfuel
  unfold btreeLookup
  have hnz : sl.alloc ≠ 0 := by omega
  simp only [hnz, ↓reduceIte, ← hroot]
  exact leaf_lookup_eq (by omega) hcap hv_leaf (hhiL_le.trans_lt hhi) hloL_q hq_hiL

/-- Subtree deletion specification: `btreeDelete` preserves `ValidSubtree`, keeps `alloc` and
`height` unchanged, does not increase `potential`, and updates `mapFn` to
`Function.update mapFn q none`. -/
theorem btreeDelete_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q : ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits) :
    let sl' := btreeDelete fpBits W_val tMin sl q
    sl'.alloc = sl.alloc ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height = T.height ∧
        T'.potential tMin ≤ T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1)
          (Function.update mapFn q none) T' := by
  have hhi : 2 ^ fpBits - 1 < 2 ^ fpBits := Nat.sub_lt (Nat.two_pow_pos fpBits) (by decide)
  obtain ⟨cntL, loL, hiL, _, _, hloL_q, hq_hiL, hhiL_le, hv_leaf, hlift⟩ :=
    descendToLeaf_reaches_leaf ht2 hcap hv hhi (Nat.zero_le q) (by omega) hfuel
  have hnz : sl.alloc ≠ 0 := by omega
  set leafIdx := descendToLeaf fpBits W_val tMin sl.nodes hMaxBTree sl.root q
  rw [hroot] at hv_leaf hlift
  obtain ⟨hidx_lt, hmeta, hcnt_le, hkw, hvw, hbounds, hmono, href⟩ := hv_leaf
  have hlanes : ∀ j < cntL, laneGet (fpBits + 2) (sl.nodes leafIdx).keysWord j < 2 ^ fpBits :=
    fun j hj => (hbounds j hj).2.trans_lt (hhiL_le.trans_lt hhi)
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec
    (capLanes := 2 * tMin) (by omega) hcap hq hkw hlanes hmono
  set W_key := fpBits + 2
  set nd := sl.nodes leafIdx
  set r := swarRank fpBits (2 * tMin) cntL q nd.keysWord
  have hcnt_nd : metaCount nd.metaWord = cntL := by rw [hmeta, metaCount_mkNodeMeta]
  unfold btreeDelete
  simp only [hnz, ↓reduceIte]
  change (let leafIdx0 := leafIdx; _)
  dsimp only
  rw [hcnt_nd]
  by_cases hhit : r < cntL ∧ laneGet W_key nd.keysWord r = q
  · obtain ⟨hrc, hkey_eq⟩ := hhit
    have hcond : (r < cntL && laneGet W_key nd.keysWord r == q) = true := by
      simp [hrc, hkey_eq]
    rw [hcond]
    simp only [↓reduceIte]
    refine ⟨trivial, ?_⟩
    let nd' : BTreeNode :=
      ⟨mkNodeMeta true (cntL - 1),
        wordDeleteAt W_key r nd.keysWord,
        wordDeleteAt W_val r nd.valsWord⟩
    have hcnt_eq : cntL - 1 + 1 = cntL := by omega
    have hv_new : ValidSubtree false fpBits W_val tMin sl.alloc
        (Function.update sl.nodes leafIdx nd') loL hiL
        (Function.update mapFn q none) (.leaf leafIdx (cntL - 1)) := by
      dsimp only [ValidSubtree]
      rw [Function.update_self]
      refine ⟨hidx_lt, rfl, by omega,
        wordDeleteAt_lt (by omega) (by rwa [hcnt_eq]),
        wordDeleteAt_lt (by omega) (by rwa [hcnt_eq]), ?_, ?_, ?_⟩
      · intro j hj
        dsimp only [nd']
        rw [laneGet_wordDeleteAt]
        split_ifs with hjr
        · exact hbounds j (by omega)
        · exact hbounds (j + 1) (by omega)
      · intro i j hij hjc
        dsimp only [nd']
        rw [laneGet_wordDeleteAt, laneGet_wordDeleteAt]
        split_ifs with hir hjr
        · exact hmono i j hij (by omega)
        · exact hmono i (j + 1) (by omega) (by omega)
        · omega
        · exact hmono (i + 1) (j + 1) (by omega) (by omega)
      · intro q' hq1 hq2
        dsimp only [nd']
        by_cases hqq : q' = q
        · subst q'
          right
          refine ⟨fun j hj => ?_, Function.update_self q none mapFn⟩
          rw [laneGet_wordDeleteAt]
          split_ifs with hjr
          · exact (hlt_r j hjr).ne
          · exact (hkey_eq ▸ hmono r (j + 1) (by omega) (by omega)).ne'
        · rw [Function.update_of_ne hqq]
          rcases href q' hq1 hq2 with ⟨j₀, hj₀, hkj₀, hmj₀⟩ | ⟨hno, hmno⟩
          · have hj₀_ne : j₀ ≠ r := fun he => hqq (hkj₀ ▸ he ▸ hkey_eq)
            left
            by_cases hj₀_lt : j₀ < r
            · refine ⟨j₀, by omega, ?_, ?_⟩
              · rw [laneGet_wordDeleteAt]; simp only [hj₀_lt, ↓reduceIte]; exact hkj₀
              · rw [laneGet_wordDeleteAt]; simp only [hj₀_lt, ↓reduceIte]; exact hmj₀
            · refine ⟨j₀ - 1, by omega, ?_, ?_⟩
              · have hge1 : ¬(j₀ - 1 < r) := by omega
                have hadd : j₀ - 1 + 1 = j₀ := by omega
                rw [laneGet_wordDeleteAt]; simp only [hge1, ↓reduceIte, hadd]; exact hkj₀
              · have hge1 : ¬(j₀ - 1 < r) := by omega
                have hadd : j₀ - 1 + 1 = j₀ := by omega
                rw [laneGet_wordDeleteAt]; simp only [hge1, ↓reduceIte, hadd]; exact hmj₀
          · right
            refine ⟨fun j hj => ?_, hmno⟩
            rw [laneGet_wordDeleteAt]
            split_ifs with hjr
            · exact hno j (by omega)
            · exact hno (j + 1) (by omega)
    obtain ⟨T', hrt', _, hht', hpot', hv'⟩ := hlift (cntL - 1) nd'
      (Function.update mapFn q none) (by omega) (fun q' hne => Function.update_of_ne hne _ _) hv_new
    exact ⟨T', hrt', hht', hpot', hv'⟩
  · have hcond : (r < cntL && laneGet W_key nd.keysWord r == q) = false := by
      by_cases hrc : r < cntL
      · have hne : laneGet W_key nd.keysWord r ≠ q := fun he => hhit ⟨hrc, he⟩
        simp [hrc, hne]
      · simp [hrc]
    rw [hcond]
    change sl.alloc = sl.alloc ∧ _
    have hmap_q_none : mapFn q = none := by
      rcases href q hloL_q hq_hiL with ⟨r₀, hr₀_lt, hkey_r₀, _⟩ | ⟨_, hmno⟩
      · exfalso
        have hr_eq : r = r₀ := by
          rcases lt_trichotomy r r₀ with hlt | rfl | hgt
          · have h1 := hge_r r le_rfl (hlt.trans hr₀_lt)
            have h2 := hmono r r₀ hlt hr₀_lt
            omega
          · rfl
          · have h1 := hlt_r r₀ hgt
            omega
        exact hhit ⟨hr_eq ▸ hr₀_lt, hr_eq ▸ hkey_r₀⟩
      · exact hmno
    have hupd_eq : Function.update mapFn q none = mapFn := by
      ext x
      by_cases hx : x = q
      · subst hx; simp [hmap_q_none]
      · simp [hx]
    refine ⟨rfl, T, hroot, rfl, le_rfl, ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, hupd_eq] using hv

/-- Subtree in-place value update specification: when `newVal < 2 ^ W_val`, `btreeUpdate` preserves
`ValidSubtree`, `alloc`, `height`, and `potential`, updating `mapFn q` to `some newVal` whenever `q`
is present (and leaving `mapFn` unchanged when `mapFn q = none`). -/
theorem btreeUpdate_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q newVal : ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits) (hval : newVal < 2 ^ W_val) :
    let sl' := btreeUpdate fpBits W_val tMin sl q newVal
    let mapFn' := if (mapFn q).isSome then Function.update mapFn q (some newVal) else mapFn
    sl'.alloc = sl.alloc ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height = T.height ∧
        T'.potential tMin ≤ T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1) mapFn' T' := by
  have hhi : 2 ^ fpBits - 1 < 2 ^ fpBits := Nat.sub_lt (Nat.two_pow_pos fpBits) (by decide)
  obtain ⟨cntL, loL, hiL, _, _, hloL_q, hq_hiL, hhiL_le, hv_leaf, hlift⟩ :=
    descendToLeaf_reaches_leaf ht2 hcap hv hhi (Nat.zero_le q) (by omega) hfuel
  have hnz : sl.alloc ≠ 0 := by omega
  set leafIdx := descendToLeaf fpBits W_val tMin sl.nodes hMaxBTree sl.root q
  rw [hroot] at hv_leaf hlift
  obtain ⟨hidx_lt, hmeta, hcnt_le, hkw, hvw, hbounds, hmono, href⟩ := hv_leaf
  have hlanes : ∀ j < cntL, laneGet (fpBits + 2) (sl.nodes leafIdx).keysWord j < 2 ^ fpBits :=
    fun j hj => (hbounds j hj).2.trans_lt (hhiL_le.trans_lt hhi)
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec
    (capLanes := 2 * tMin) (by omega) hcap hq hkw hlanes hmono
  set W_key := fpBits + 2
  set nd := sl.nodes leafIdx
  set r := swarRank fpBits (2 * tMin) cntL q nd.keysWord
  have hcnt_nd : metaCount nd.metaWord = cntL := by rw [hmeta, metaCount_mkNodeMeta]
  unfold btreeUpdate
  simp only [hnz, ↓reduceIte]
  change (let leafIdx0 := leafIdx; _)
  dsimp only
  rw [hcnt_nd]
  by_cases hhit : r < cntL ∧ laneGet W_key nd.keysWord r = q
  · obtain ⟨hrc, hkey_eq⟩ := hhit
    have hcond : (r < cntL && laneGet W_key nd.keysWord r == q) = true := by
      simp [hrc, hkey_eq]
    have hsome : (mapFn q).isSome = true := by
      rcases href q hloL_q hq_hiL with ⟨r₀, _, _, hmr₀⟩ | ⟨hno, _⟩
      · simp [hmr₀]
      · exact absurd hkey_eq (hno r hrc)
    rw [hcond, hsome]
    simp only [↓reduceIte]
    let nd' : BTreeNode := ⟨nd.metaWord, nd.keysWord, wordUpdateAt W_val r newVal nd.valsWord⟩
    have hv_new : ValidSubtree false fpBits W_val tMin sl.alloc
        (Function.update sl.nodes leafIdx nd') loL hiL
        (Function.update mapFn q (some newVal)) (.leaf leafIdx cntL) := by
      dsimp only [ValidSubtree]
      rw [Function.update_self]
      refine ⟨hidx_lt, hmeta, hcnt_le, hkw, wordUpdateAt_lt hrc hval hvw,
        hbounds, hmono, ?_⟩
      intro q' hq1 hq2
      dsimp only [nd']
      by_cases hqq : q' = q
      · subst hqq
        left
        refine ⟨r, hrc, hkey_eq, ?_⟩
        rw [Function.update_self, laneGet_wordUpdateAt hval]
        simp
      · rw [Function.update_of_ne hqq]
        rcases href q' hq1 hq2 with ⟨j₀, hj₀, hkj₀, hmj₀⟩ | ⟨hno, hmno⟩
        · have hj₀_ne : j₀ ≠ r := fun he => hqq (hkj₀ ▸ he ▸ hkey_eq)
          left
          refine ⟨j₀, hj₀, hkj₀, ?_⟩
          rw [laneGet_wordUpdateAt hval]
          simp [hj₀_ne, hmj₀]
        · right
          exact ⟨hno, hmno⟩
    obtain ⟨T', hrt', _, hht', hpot', hv'⟩ := hlift cntL nd'
      (Function.update mapFn q (some newVal)) le_rfl
      (fun q' hne => Function.update_of_ne hne _ _) hv_new
    exact ⟨trivial, T', hrt', hht', hpot', hv'⟩
  · have hcond : (r < cntL && laneGet W_key nd.keysWord r == q) = false := by
      by_cases hrc : r < cntL
      · have hne : laneGet W_key nd.keysWord r ≠ q := fun he => hhit ⟨hrc, he⟩
        simp [hrc, hne]
      · simp [hrc]
    have hmap_q_none : mapFn q = none := by
      rcases href q hloL_q hq_hiL with ⟨r₀, hr₀_lt, hkey_r₀, _⟩ | ⟨_, hmno⟩
      · exfalso
        have hr_eq : r = r₀ := by
          rcases lt_trichotomy r r₀ with hlt | rfl | hgt
          · have h1 := hge_r r le_rfl (hlt.trans hr₀_lt)
            have h2 := hmono r r₀ hlt hr₀_lt
            omega
          · rfl
          · have h1 := hlt_r r₀ hgt
            omega
        exact hhit ⟨hr_eq ▸ hr₀_lt, hr_eq ▸ hkey_r₀⟩
      · exact hmno
    rw [hcond]
    refine ⟨by simp, T, by simp [hroot], rfl, le_rfl, ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, hmap_q_none, Option.isSome_none] using hv

/-! ## Section 2: Proactive node splitting (`splitFullNode`, `splitRootIfFull`) -/

private theorem wordDropLow_lt {W a b word : ℕ} (hw : word < 2 ^ ((a + b) * W)) :
    wordDropLow W a word < 2 ^ (b * W) := by
  rw [wordDropLow_eq_div]
  refine Nat.div_lt_of_lt_mul ?_
  rwa [← Nat.pow_add, ← Nat.add_mul]

/-- Unified specification of `splitFullNode` on any full (`2 * tMin - 1`-key) valid subtree `T`
(leaf or internal branch), covering both `splitRootIfFull` (`leftIdx = alloc`,
`rightIdx = alloc + 1`) and `descendSplitToLeaf` (`leftIdx = T.rootIdx`, `rightIdx = alloc`). -/
theorem splitFullNode_spec {isRoot : Bool} {fpBits W_val tMin alloc alloc' lo hi : ℕ}
    {leftIdx rightIdx : ℕ} {nodes nodes' : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ}
    {T : BTreeTree}
    (ht2 : 2 ≤ tMin)
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T)
    (hfull : metaCount (nodes T.rootIdx).metaWord = 2 * tMin - 1)
    (halloc : alloc ≤ alloc')
    (hl_lt : leftIdx < alloc') (hr_lt : rightIdx < alloc') (hlr_ne : leftIdx ≠ rightIdx)
    (hl_nd : nodes' leftIdx = (splitFullNode fpBits W_val tMin (nodes T.rootIdx)).1)
    (hr_nd : nodes' rightIdx = (splitFullNode fpBits W_val tMin (nodes T.rootIdx)).2.2)
    (herase : ∀ v ∈ T.nodeSet.erase T.rootIdx,
      nodes' v = nodes v ∧ v ≠ leftIdx ∧ v ≠ rightIdx) :
    let res := splitFullNode fpBits W_val tMin (nodes T.rootIdx)
    let sep := res.2.1
    ∃ leftT rightT : BTreeTree,
      leftT.rootIdx = leftIdx ∧
      rightT.rootIdx = rightIdx ∧
      metaCount (nodes' leftIdx).metaWord ≤ tMin ∧
      metaCount (nodes' rightIdx).metaWord = tMin - 1 ∧
      leftT.height = T.height ∧
      rightT.height = T.height ∧
      leftT.nodeSet ⊆ insert leftIdx (T.nodeSet.erase T.rootIdx) ∧
      rightT.nodeSet ⊆ insert rightIdx (T.nodeSet.erase T.rootIdx) ∧
      Disjoint leftT.nodeSet rightT.nodeSet ∧
      lo ≤ sep ∧ sep < hi ∧
      leftT.potential tMin + rightT.potential tMin + (tMin - 1) ≤ T.potential tMin ∧
      ValidSubtree false fpBits W_val tMin alloc' nodes' lo sep mapFn leftT ∧
      ValidSubtree false fpBits W_val tMin alloc' nodes' (sep + 1) hi mapFn rightT := by
  cases T with
  | leaf idx cnt =>
    obtain ⟨_, hmeta, _, hkw, hvw, hbounds, hmono, href⟩ := hv
    dsimp only [BTreeTree.rootIdx] at hfull hl_nd hr_nd herase ⊢
    rw [hmeta, metaCount_mkNodeMeta] at hfull
    subst hfull
    have hsplit : splitFullNode fpBits W_val tMin (nodes idx) =
        (⟨mkNodeMeta true tMin,
            wordTakeLow (fpBits + 2) tMin (nodes idx).keysWord,
            wordTakeLow W_val tMin (nodes idx).valsWord⟩,
          laneGet (fpBits + 2) (nodes idx).keysWord (tMin - 1),
          ⟨mkNodeMeta true (tMin - 1),
            wordDropLow (fpBits + 2) tMin (nodes idx).keysWord,
            wordDropLow W_val tMin (nodes idx).valsWord⟩) := by
      unfold splitFullNode
      simp [hmeta]
    rw [hsplit] at hl_nd hr_nd ⊢
    dsimp only at hl_nd hr_nd ⊢
    set W_key := fpBits + 2
    set nd := nodes idx
    set sep := laneGet W_key nd.keysWord (tMin - 1)
    have hlo_sep : lo ≤ sep := (hbounds (tMin - 1) (by omega)).1
    have hsep_hi : sep < hi :=
      (hmono (tMin - 1) (2 * tMin - 2) (by omega) (by omega)).trans_le
        (hbounds (2 * tMin - 2) (by omega)).2
    have hcnt_sum : tMin + (tMin - 1) = 2 * tMin - 1 := by omega
    refine ⟨.leaf leftIdx tMin, .leaf rightIdx (tMin - 1), rfl, rfl, ?_, ?_,
      rfl, rfl, ?_, ?_, ?_, hlo_sep, hsep_hi, ?_, ?_, ?_⟩
    · rw [hl_nd, metaCount_mkNodeMeta]
    · rw [hr_nd, metaCount_mkNodeMeta]
    · simp [BTreeTree.nodeSet]
    · simp [BTreeTree.nodeSet]
    · simp [BTreeTree.nodeSet, hlr_ne]
    · simp only [BTreeTree.potential]; omega
    · dsimp only [ValidSubtree]
      rw [hl_nd]
      refine ⟨hl_lt, rfl, by omega, wordTakeLow_lt W_key tMin nd.keysWord,
        wordTakeLow_lt W_val tMin nd.valsWord, ?_, ?_, ?_⟩
      · intro j hj
        rw [laneGet_wordTakeLow]; simp only [hj, ↓reduceIte]
        refine ⟨(hbounds j (by omega)).1, ?_⟩
        rcases eq_or_lt_of_le (by omega : j ≤ tMin - 1) with rfl | hlt
        · exact le_rfl
        · exact (hmono j (tMin - 1) hlt (by omega)).le
      · intro i j hij hj
        rw [laneGet_wordTakeLow, laneGet_wordTakeLow]
        simp only [hij.trans hj, hj, ↓reduceIte]
        exact hmono i j hij (by omega)
      · intro q hq1 hq2
        rcases href q hq1 (hq2.trans hsep_hi.le) with ⟨r₀, hr₀, hkr₀, hmr₀⟩ | ⟨hno, hmno⟩
        · have hr₀_lt : r₀ < tMin := by
            by_contra hge
            have hgt : sep < laneGet W_key nd.keysWord r₀ :=
              hmono (tMin - 1) r₀ (by omega) hr₀
            omega
          left
          refine ⟨r₀, hr₀_lt, ?_, ?_⟩
          · rw [laneGet_wordTakeLow]; simp only [hr₀_lt, ↓reduceIte]; exact hkr₀
          · rw [laneGet_wordTakeLow]; simp only [hr₀_lt, ↓reduceIte]; exact hmr₀
        · right
          refine ⟨fun r hr => ?_, hmno⟩
          rw [laneGet_wordTakeLow]; simp only [hr, ↓reduceIte]
          exact hno r (by omega)
    · dsimp only [ValidSubtree]
      rw [hr_nd]
      refine ⟨hr_lt, rfl, by omega,
        wordDropLow_lt (by rwa [hcnt_sum]),
        wordDropLow_lt (by rwa [hcnt_sum]), ?_, ?_, ?_⟩
      · intro j hj
        rw [laneGet_wordDropLow]
        refine ⟨?_, (hbounds (tMin + j) (by omega)).2⟩
        have hgt := hmono (tMin - 1) (tMin + j) (by omega) (by omega)
        change sep + 1 ≤ laneGet W_key nd.keysWord (tMin + j)
        omega
      · intro i j hij hj
        rw [laneGet_wordDropLow, laneGet_wordDropLow]
        exact hmono (tMin + i) (tMin + j) (by omega) (by omega)
      · intro q hq1 hq2
        rcases href q (hlo_sep.trans (by omega)) hq2 with ⟨r₀, hr₀, hkr₀, hmr₀⟩ | ⟨hno, hmno⟩
        · have hr₀_ge : tMin ≤ r₀ := by
            by_contra hlt
            rcases eq_or_lt_of_le (by omega : r₀ ≤ tMin - 1) with rfl | hlt'
            · omega
            · have := hmono r₀ (tMin - 1) hlt' (by omega)
              omega
          left
          refine ⟨r₀ - tMin, by omega, ?_, ?_⟩
          · rw [laneGet_wordDropLow, Nat.add_sub_of_le hr₀_ge]; exact hkr₀
          · rw [laneGet_wordDropLow, Nat.add_sub_of_le hr₀_ge]; exact hmr₀
        · right
          refine ⟨fun r hr => ?_, hmno⟩
          rw [laneGet_wordDropLow]
          exact hno (tMin + r) (by omega)
  | branch idx cnt cs =>
    obtain ⟨_, hmeta, _, _, hkw, hvw, hlo0, hhi_last, hmono, hnot, hdisj, hht, hcs⟩ := hv
    dsimp only [BTreeTree.rootIdx] at hfull hl_nd hr_nd herase ⊢
    rw [hmeta, metaCount_mkNodeMeta] at hfull
    have hsplit : splitFullNode fpBits W_val tMin (nodes idx) =
        (⟨mkNodeMeta false (tMin - 1),
            wordTakeLow (fpBits + 2) (tMin - 1) (nodes idx).keysWord,
            wordTakeLow W_val tMin (nodes idx).valsWord⟩,
          laneGet (fpBits + 2) (nodes idx).keysWord (tMin - 1),
          ⟨mkNodeMeta false (tMin - 1),
            wordDropLow (fpBits + 2) tMin (nodes idx).keysWord,
            wordDropLow W_val tMin (nodes idx).valsWord⟩) := by
      unfold splitFullNode
      simp [hmeta]
    rw [hsplit] at hl_nd hr_nd ⊢
    dsimp only at hl_nd hr_nd ⊢
    set W_key := fpBits + 2
    set nd := nodes idx
    set sep := laneGet W_key nd.keysWord (tMin - 1)
    let leftCs : Fin ((tMin - 1) + 1) → BTreeTree := fun i => cs ⟨i.val, by omega⟩
    let rightCs : Fin ((tMin - 1) + 1) → BTreeTree := fun i => cs ⟨tMin + i.val, by omega⟩
    have hchild_mem_erase : ∀ k : Fin (cnt + 1), ∀ v ∈ (cs k).nodeSet,
        v ∈ (BTreeTree.branch idx cnt cs).nodeSet.erase idx := by
      intro k v hv_in
      have hv_ne : v ≠ idx := fun heq => hnot k (heq ▸ hv_in)
      exact mem_erase.mpr ⟨hv_ne, mem_insert_of_mem (mem_biUnion.mpr ⟨k, mem_univ k, hv_in⟩)⟩
    have hlo_sep : lo ≤ sep := by
      rcases eq_or_lt_of_le (Nat.zero_le (tMin - 1)) with heq0 | hpos
      · omega
      · exact hlo0.trans (hmono 0 (tMin - 1) hpos (by omega)).le
    have hsep_hi : sep < hi :=
      (hmono (tMin - 1) (cnt - 1) (by omega) (by omega)).trans hhi_last
    have hht_left : ∀ i : Fin ((tMin - 1) + 1),
        (leftCs i).height = (leftCs ⟨0, Nat.succ_pos _⟩).height := fun i => by
      dsimp only [leftCs]
      exact (hht ⟨i.val, by omega⟩).trans (hht ⟨0, Nat.succ_pos cnt⟩).symm
    have hht_right : ∀ i : Fin ((tMin - 1) + 1),
        (rightCs i).height = (rightCs ⟨0, Nat.succ_pos _⟩).height := fun i => by
      dsimp only [rightCs]
      exact (hht ⟨tMin + i.val, by omega⟩).trans (hht ⟨tMin, by omega⟩).symm
    have hsub_L : (BTreeTree.branch leftIdx (tMin - 1) leftCs).nodeSet ⊆
        insert leftIdx ((BTreeTree.branch idx cnt cs).nodeSet.erase idx) := by
      intro v hv_in
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
      rcases hv_in with rfl | ⟨i, _, hvi⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hchild_mem_erase ⟨i.val, by omega⟩ v hvi)
    have hsub_R : (BTreeTree.branch rightIdx (tMin - 1) rightCs).nodeSet ⊆
        insert rightIdx ((BTreeTree.branch idx cnt cs).nodeSet.erase idx) := by
      intro v hv_in
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
      rcases hv_in with rfl | ⟨i, _, hvi⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hchild_mem_erase ⟨tMin + i.val, by omega⟩ v hvi)
    refine ⟨.branch leftIdx (tMin - 1) leftCs, .branch rightIdx (tMin - 1) rightCs,
      rfl, rfl, ?_, ?_, ?_, ?_, hsub_L, hsub_R, ?_, hlo_sep, hsep_hi, ?_, ?_, ?_⟩
    · rw [hl_nd, metaCount_mkNodeMeta]; omega
    · rw [hr_nd, metaCount_mkNodeMeta]
    · rw [BTreeTree.height_branch_of_eq hht_left, BTreeTree.height_branch_of_eq hht]
    · rw [BTreeTree.height_branch_of_eq hht_right, BTreeTree.height_branch_of_eq hht]
      exact congrArg (1 + ·) (hht ⟨tMin + 0, by omega⟩)
    · rw [Finset.disjoint_left]
      intro v hvL hvR
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hvL hvR
      rcases hvL with rfl | ⟨i, _, hvi⟩
      · rcases hvR with heq | ⟨j, _, hvj⟩
        · exact hlr_ne heq
        · exact (herase _ (hchild_mem_erase ⟨tMin + j.val, by omega⟩ _ hvj)).2.1 rfl
      · rcases hvR with rfl | ⟨j, _, hvj⟩
        · exact (herase _ (hchild_mem_erase ⟨i.val, by omega⟩ _ hvi)).2.2 rfl
        · have hne_ij : (⟨i.val, by omega⟩ : Fin (cnt + 1)) ≠ ⟨tMin + j.val, by omega⟩ :=
            Fin.ne_of_val_ne (by dsimp; omega)
          exact Finset.disjoint_left.mp (hdisj _ _ hne_ij) hvi hvj
    · simp only [BTreeTree.potential]
      have hsum_split : ∑ i : Fin ((tMin - 1) + 1), (leftCs i).potential tMin +
          ∑ i : Fin ((tMin - 1) + 1), (rightCs i).potential tMin =
          ∑ k : Fin (cnt + 1), (cs k).potential tMin := by
        have hcast : (tMin - 1 + 1) + (tMin - 1 + 1) = cnt + 1 := by omega
        let e : Fin ((tMin - 1 + 1) + (tMin - 1 + 1)) ≃ Fin (cnt + 1) := finCongr hcast
        conv_rhs => rw [← Equiv.sum_comp e (fun k => (cs k).potential tMin), Fin.sum_univ_add]
        congr 1
        refine sum_congr rfl fun i _ => congrArg (fun k => (cs k).potential tMin) ?_
        ext; dsimp [e]; omega
      omega
    · dsimp only [ValidSubtree]
      rw [hl_nd]
      have ht1_eq : tMin - 1 + 1 = tMin := by omega
      refine ⟨hl_lt, rfl, by simp, by omega,
        wordTakeLow_lt W_key (tMin - 1) nd.keysWord,
        by rw [ht1_eq]; exact wordTakeLow_lt W_val tMin nd.valsWord,
        ?_, ?_, ?_, ?_, ?_, hht_left, ?_⟩
      · rw [laneGet_wordTakeLow]; simp only [show 0 < tMin - 1 by omega, ↓reduceIte]; exact hlo0
      · rw [laneGet_wordTakeLow]
        simp only [show tMin - 1 - 1 < tMin - 1 by omega, ↓reduceIte]
        exact hmono (tMin - 1 - 1) (tMin - 1) (by omega) (by omega)
      · intro i j hij hj
        rw [laneGet_wordTakeLow, laneGet_wordTakeLow]
        simp only [hij.trans hj, hj, ↓reduceIte]
        exact hmono i j hij (by omega)
      · intro i hmem
        exact (herase _ (hchild_mem_erase ⟨i.val, by omega⟩ _ hmem)).2.1 rfl
      · intro i j hij
        exact hdisj ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
          (Fin.ne_of_val_ne (by have := Fin.val_ne_of_ne hij; dsimp; omega))
      · intro i
        have hi_lt : i.val < tMin := by omega
        rw [laneGet_wordTakeLow]
        simp only [hi_lt, ↓reduceIte]
        refine ⟨(hcs ⟨i.val, by omega⟩).1, ?_⟩
        have hclo_eq : childLo W_key lo (wordTakeLow W_key (tMin - 1) nd.keysWord) i.val =
            childLo W_key lo nd.keysWord i.val := by
          unfold childLo
          split_ifs with hi0
          · rfl
          · rw [laneGet_wordTakeLow]
            simp [show i.val - 1 < tMin - 1 by omega]
        have hchi_eq : childHi W_key sep (tMin - 1)
            (wordTakeLow W_key (tMin - 1) nd.keysWord) i.val =
            childHi W_key hi cnt nd.keysWord i.val := by
          unfold childHi
          by_cases hilt : i.val < tMin - 1
          · have hilt_c : i.val < cnt := by omega
            simp only [hilt, hilt_c, ↓reduceIte, laneGet_wordTakeLow]
          · have hieq : i.val = tMin - 1 := by omega
            have hilt_c : i.val < cnt := by omega
            simp only [hilt, hilt_c, ↓reduceIte]
            rw [hieq]
        rw [hclo_eq, hchi_eq]
        exact ((hcs ⟨i.val, by omega⟩).2).frame halloc
          (fun v hv_in => (herase v (hchild_mem_erase ⟨i.val, by omega⟩ v hv_in)).1)
          (fun _ _ _ => rfl)
    · dsimp only [ValidSubtree]
      rw [hr_nd]
      have hcnt_k : tMin + (tMin - 1) = cnt := by omega
      have hcnt_v : tMin + ((tMin - 1) + 1) = cnt + 1 := by omega
      refine ⟨hr_lt, rfl, by simp, by omega,
        wordDropLow_lt (by rwa [hcnt_k]),
        wordDropLow_lt (by rwa [hcnt_v]),
        ?_, ?_, ?_, ?_, ?_, hht_right, ?_⟩
      · rw [laneGet_wordDropLow, Nat.add_zero]
        have hgt := hmono (tMin - 1) tMin (by omega) (by omega)
        change sep + 1 ≤ laneGet W_key nd.keysWord tMin
        omega
      · rw [laneGet_wordDropLow, show tMin + (tMin - 1 - 1) = cnt - 1 by omega]
        exact hhi_last
      · intro i j hij hj
        rw [laneGet_wordDropLow, laneGet_wordDropLow]
        exact hmono (tMin + i) (tMin + j) (by omega) (by omega)
      · intro i hmem
        exact (herase _ (hchild_mem_erase ⟨tMin + i.val, by omega⟩ _ hmem)).2.2 rfl
      · intro i j hij
        exact hdisj ⟨tMin + i.val, by omega⟩ ⟨tMin + j.val, by omega⟩
          (Fin.ne_of_val_ne (by have := Fin.val_ne_of_ne hij; dsimp; omega))
      · intro i
        rw [laneGet_wordDropLow]
        refine ⟨(hcs ⟨tMin + i.val, by omega⟩).1, ?_⟩
        have hclo_eq : childLo W_key (sep + 1) (wordDropLow W_key tMin nd.keysWord) i.val =
            childLo W_key lo nd.keysWord (tMin + i.val) := by
          unfold childLo
          by_cases hi0 : i.val = 0
          · have htnz : tMin ≠ 0 := by omega
            simp only [hi0, Nat.add_zero, htnz, ↓reduceIte]; rfl
          · have hnz : tMin + i.val ≠ 0 := by omega
            simp only [hi0, hnz, ↓reduceIte, laneGet_wordDropLow]
            rw [show tMin + (i.val - 1) = tMin + i.val - 1 by omega]
        have hchi_eq : childHi W_key hi (tMin - 1)
            (wordDropLow W_key tMin nd.keysWord) i.val =
            childHi W_key hi cnt nd.keysWord (tMin + i.val) := by
          unfold childHi
          by_cases hilt : i.val < tMin - 1
          · have hilt_c : tMin + i.val < cnt := by omega
            simp only [hilt, hilt_c, ↓reduceIte, laneGet_wordDropLow]
          · have hnlt_c : ¬(tMin + i.val < cnt) := by omega
            simp only [hilt, hnlt_c, ↓reduceIte]
        rw [hclo_eq, hchi_eq]
        exact ((hcs ⟨tMin + i.val, by omega⟩).2).frame halloc
          (fun v hv_in => (herase v (hchild_mem_erase ⟨tMin + i.val, by omega⟩ v hv_in)).1)
          (fun _ _ _ => rfl)

/-- Specification of `splitRootIfFull`: ensures the root is strictly non-full (`< 2 * tMin - 1`
keys), increases height by at most `1`, allocates at most `2` nodes, and never increases Overmars'
split potential `(tMin - 2) * (alloc - 1) + 2 * T.potential tMin` when `3 ≤ tMin`. -/
theorem splitRootIfFull_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht3 : 3 ≤ tMin) (halloc_pos : 1 ≤ sl.alloc) (halloc_val : sl.alloc + 1 < 2 ^ W_val)
    (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T) :
    let sl1 := splitRootIfFull fpBits W_val tMin sl
    1 ≤ sl1.alloc ∧ sl1.alloc ≤ sl.alloc + 2 ∧ sl1.root = sl.root ∧
      ∃ T1 : BTreeTree,
        T1.rootIdx = sl1.root ∧
        metaCount (sl1.nodes sl1.root).metaWord < 2 * tMin - 1 ∧
        T1.height ≤ T.height + 1 ∧
        (tMin - 2) * (sl1.alloc - 1) + 2 * T1.potential tMin ≤
          (tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl1.alloc sl1.nodes 0 (2 ^ fpBits - 1) mapFn T1 := by
  have hroot_lt : sl.root < sl.alloc := by
    rw [← hroot]
    exact (hv.leafCount_le_card_nodeSet).1 T.rootIdx T.rootIdx_mem_nodeSet
  have hcnt_le : metaCount (sl.nodes sl.root).metaWord ≤ 2 * tMin - 1 := by
    rw [← hroot]
    cases T with
    | leaf idx cnt =>
      obtain ⟨_, hmeta, hc, _⟩ := hv
      dsimp only [BTreeTree.rootIdx]; rw [hmeta, metaCount_mkNodeMeta]; exact hc
    | branch idx cnt cs =>
      obtain ⟨_, hmeta, _, hc, _⟩ := hv
      dsimp only [BTreeTree.rootIdx]; rw [hmeta, metaCount_mkNodeMeta]; exact hc
  dsimp only [splitRootIfFull]
  by_cases hfull : metaCount (sl.nodes sl.root).metaWord = 2 * tMin - 1
  · have hcond : (metaCount (sl.nodes sl.root).metaWord == 2 * tMin - 1) = true := by
      simp [hfull]
    rw [hcond]
    simp only [↓reduceIte]
    set res := splitFullNode fpBits W_val tMin (sl.nodes sl.root)
    set leftNd := res.1
    set sep := res.2.1
    set rightNd := res.2.2
    set leftIdx := sl.alloc
    set rightIdx := sl.alloc + 1
    set newVals := leftIdx + (rightIdx <<< W_val)
    set newRootNd : BTreeNode := ⟨mkNodeMeta false 1, sep, newVals⟩
    set nodes1 := Function.update sl.nodes leftIdx leftNd
    set nodes2 := Function.update nodes1 rightIdx rightNd
    set nodes3 := Function.update nodes2 sl.root newRootNd
    have hlr_ne : leftIdx ≠ rightIdx := by dsimp [leftIdx, rightIdx]; omega
    have hroot_ne_l : sl.root ≠ leftIdx := by dsimp [leftIdx]; omega
    have hroot_ne_r : sl.root ≠ rightIdx := by dsimp [rightIdx]; omega
    have hl_nd : nodes3 leftIdx = (splitFullNode fpBits W_val tMin (sl.nodes T.rootIdx)).1 := by
      dsimp only [nodes3, nodes2, nodes1]
      rw [Function.update_of_ne hroot_ne_l.symm, Function.update_of_ne hlr_ne,
        Function.update_self, hroot]
    have hr_nd : nodes3 rightIdx =
        (splitFullNode fpBits W_val tMin (sl.nodes T.rootIdx)).2.2 := by
      dsimp only [nodes3, nodes2]
      rw [Function.update_of_ne hroot_ne_r.symm, Function.update_self, hroot]
    have herase : ∀ v ∈ T.nodeSet.erase T.rootIdx,
        nodes3 v = sl.nodes v ∧ v ≠ leftIdx ∧ v ≠ rightIdx := by
      intro v hv_er
      obtain ⟨hv_ne_rt, hv_mem⟩ := mem_erase.mp hv_er
      have hv_lt : v < sl.alloc := (hv.leafCount_le_card_nodeSet).1 v hv_mem
      have hv_ne_l : v ≠ leftIdx := by dsimp [leftIdx]; omega
      have hv_ne_r : v ≠ rightIdx := by dsimp [rightIdx]; omega
      have hv_ne_slrt : v ≠ sl.root := by rwa [← hroot]
      refine ⟨?_, hv_ne_l, hv_ne_r⟩
      dsimp only [nodes3, nodes2, nodes1]
      rw [Function.update_of_ne hv_ne_slrt, Function.update_of_ne hv_ne_r,
        Function.update_of_ne hv_ne_l]
    obtain ⟨leftT, rightT, hrtL, hrtR, _, _, hhtL, hhtR, hsubL, hsubR,
      hdisjLR, hlo_sep, hsep_hi, hpotLR, hvL, hvR⟩ :=
      splitFullNode_spec (alloc' := sl.alloc + 2) (nodes' := nodes3)
        (leftIdx := leftIdx) (rightIdx := rightIdx) (by omega) hv
        (by rwa [hroot]) (by omega) (by dsimp [leftIdx]; omega) (by dsimp [rightIdx]; omega)
        hlr_ne hl_nd hr_nd herase
    rw [hroot] at hlo_sep hsep_hi hvL hvR
    let rootCs : Fin 2 → BTreeTree := fun i => if i.val = 0 then leftT else rightT
    have hht_root : ∀ i : Fin 2, (rootCs i).height = (rootCs ⟨0, by decide⟩).height := by
      intro i
      fin_cases i <;> simp [rootCs, hhtL, hhtR]
    refine ⟨by omega, le_rfl, trivial, .branch sl.root 1 rootCs, rfl, ?_, ?_, ?_, ?_⟩
    · dsimp only [nodes3]
      rw [Function.update_self, metaCount_mkNodeMeta]
      omega
    · rw [BTreeTree.height_branch_of_eq hht_root]
      dsimp only [rootCs]
      simp only [↓reduceIte, hhtL]
      omega
    · dsimp only [BTreeTree.potential]
      rw [Fin.sum_univ_two]
      dsimp only [rootCs, Fin.val_zero, Fin.val_one]
      simp only [↓reduceIte, one_ne_zero]
      have h1_sub : 1 - (tMin - 1) = 0 := by omega
      have halloc_sub : leftIdx + 2 - 1 = (leftIdx - 1) + 2 := by dsimp [leftIdx]; omega
      dsimp only [leftIdx] at halloc_sub ⊢
      rw [h1_sub, halloc_sub, Nat.mul_add]
      omega
    · dsimp only [ValidSubtree]
      have hnd3_rt : nodes3 sl.root = newRootNd := Function.update_self sl.root newRootNd nodes2
      rw [hnd3_rt]
      have hhi_fp : 2 ^ fpBits - 1 < 2 ^ (1 * (fpBits + 2)) := by
        rw [one_mul]
        exact (Nat.sub_lt (Nat.two_pow_pos fpBits) (by decide)).trans
          (Nat.pow_lt_pow_right (by decide) (by omega))
      have hnewVals_lt : newVals < 2 ^ ((1 + 1) * W_val) := by
        dsimp only [newVals]
        rw [Nat.shiftLeft_eq, show (1 + 1) * W_val = W_val + W_val by ring, Nat.pow_add]
        have hl_lt' : leftIdx < 2 ^ W_val := by dsimp [leftIdx]; omega
        have hr_le' : rightIdx + 1 ≤ 2 ^ W_val := by dsimp [rightIdx]; omega
        calc leftIdx + rightIdx * 2 ^ W_val
            < 2 ^ W_val + rightIdx * 2 ^ W_val := by omega
          _ = (rightIdx + 1) * 2 ^ W_val := by ring
          _ ≤ 2 ^ W_val * 2 ^ W_val := Nat.mul_le_mul_right _ hr_le'
      have hlane0_sep : laneGet (fpBits + 2) sep 0 = sep := by
        rw [laneGet_eq_div_mod, Nat.zero_mul, pow_zero, Nat.div_one]
        exact Nat.mod_eq_of_lt (hsep_hi.trans (by rw [← one_mul (fpBits + 2)]; exact hhi_fp))
      have hval0 : laneGet W_val newVals 0 = leftIdx := by
        dsimp only [newVals]
        rw [laneGet_eq_div_mod, Nat.zero_mul, pow_zero, Nat.div_one, Nat.shiftLeft_eq,
          Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by dsimp [leftIdx]; omega)
      have hval1 : laneGet W_val newVals 1 = rightIdx := by
        dsimp only [newVals]
        rw [laneGet_eq_div_mod, one_mul, Nat.shiftLeft_eq,
          Nat.add_mul_div_right _ _ (Nat.two_pow_pos W_val),
          Nat.div_eq_of_lt (by dsimp [leftIdx]; omega), Nat.zero_add]
        exact Nat.mod_eq_of_lt halloc_val
      refine ⟨by omega, rfl, by simp, by omega, hsep_hi.trans hhi_fp, hnewVals_lt,
        by dsimp only [newRootNd]; rw [hlane0_sep]; exact hlo_sep,
        by dsimp only [newRootNd]; rw [Nat.sub_self, hlane0_sep]; exact hsep_hi,
        fun i j hij hj => by omega, ?_, ?_, hht_root, ?_⟩
      · intro i hmem
        fin_cases i
        · dsimp only [rootCs] at hmem; simp only [↓reduceIte] at hmem
          have h1 := hsubL hmem
          rw [mem_insert, mem_erase] at h1
          rcases h1 with heq | ⟨hne, _⟩
          · exact hroot_ne_l heq
          · exact hne (hroot.symm)
        · dsimp only [rootCs] at hmem; simp only [one_ne_zero, ↓reduceIte] at hmem
          have h1 := hsubR hmem
          rw [mem_insert, mem_erase] at h1
          rcases h1 with heq | ⟨hne, _⟩
          · exact hroot_ne_r heq
          · exact hne (hroot.symm)
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · simpa [rootCs] using hdisjLR
        · simpa [rootCs] using hdisjLR.symm
        · exact absurd rfl hij
      · intro i
        fin_cases i
        · dsimp only [rootCs, newRootNd, childLo, childHi]
          simp only [↓reduceIte, zero_lt_one, hval0, hrtL, hlane0_sep]
          exact ⟨trivial, hvL⟩
        · dsimp only [rootCs, newRootNd, childLo, childHi]
          simp only [one_ne_zero, ↓reduceIte, lt_irrefl, Nat.sub_self,
            hval1, hrtR, hlane0_sep]
          exact ⟨trivial, hvR⟩
  · have hcond : (metaCount (sl.nodes sl.root).metaWord == 2 * tMin - 1) = false := by
      simp [hfull]
    rw [hcond]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨halloc_pos, by omega, trivial, T, hroot, by omega, by omega, le_rfl, hv⟩

/-- Leaf insertion/overwrite post-step of `btreeInsert`. -/
@[expose] def finishLeafInsert (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (leafIdx q val : ℕ) :
    BTreeSlice :=
  let W_key := fpBits + 2
  let leafNd := sl.nodes leafIdx
  let cnt := metaCount leafNd.metaWord
  let r := swarRank fpBits (2 * tMin) cnt q leafNd.keysWord
  if r < cnt && laneGet W_key leafNd.keysWord r == q then
    let leafNd' : BTreeNode :=
      ⟨leafNd.metaWord, leafNd.keysWord, wordUpdateAt W_val r val leafNd.valsWord⟩
    { sl with nodes := Function.update sl.nodes leafIdx leafNd' }
  else
    let leafNd' : BTreeNode :=
      ⟨mkNodeMeta true (cnt + 1),
        wordInsertAt W_key r q leafNd.keysWord,
        wordInsertAt W_val r val leafNd.valsWord⟩
    { sl with nodes := Function.update sl.nodes leafIdx leafNd' }

/-- Exact specification of `finishLeafInsert` on a non-full (`cnt < 2 * tMin - 1`) valid leaf. -/
theorem finishLeafInsert_leaf_spec {isRoot : Bool} {fpBits W_val tMin leafIdx cnt lo hi q val : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2)) (hval : val < 2 ^ W_val)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi)
    (hv : ValidSubtree isRoot fpBits W_val tMin sl.alloc sl.nodes lo hi mapFn (.leaf leafIdx cnt))
    (hnonfull : cnt < 2 * tMin - 1) :
    let sl' := finishLeafInsert fpBits W_val tMin sl leafIdx q val
    sl'.alloc = sl.alloc ∧
      sl'.root = sl.root ∧
      (∀ v, v ≠ leafIdx → sl'.nodes v = sl.nodes v) ∧
      ∃ cnt' : ℕ,
        cnt' ≤ cnt + 1 ∧
        ValidSubtree isRoot fpBits W_val tMin sl'.alloc sl'.nodes lo hi
          (Function.update mapFn q (some val)) (.leaf leafIdx cnt') := by
  obtain ⟨hidx_lt, hmeta, _, hkw, hvw, hbounds, hmono, href⟩ := hv
  have hlanes : ∀ j < cnt, laneGet (fpBits + 2) (sl.nodes leafIdx).keysWord j < 2 ^ fpBits :=
    fun j hj => (hbounds j hj).2.trans_lt hhi
  have hq_fp : q < 2 ^ fpBits := hqhi.trans_lt hhi
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec
    (capLanes := 2 * tMin) (by omega) hcap hq_fp hkw hlanes hmono
  dsimp only [finishLeafInsert]
  have hcnt_nd : metaCount (sl.nodes leafIdx).metaWord = cnt := by
    rw [hmeta, metaCount_mkNodeMeta]
  rw [hcnt_nd]
  set W_key := fpBits + 2
  set nd := sl.nodes leafIdx
  set r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
  by_cases hhit : r < cnt ∧ laneGet W_key nd.keysWord r = q
  · obtain ⟨hrc, hkey_eq⟩ := hhit
    have hcond : (r < cnt && laneGet W_key nd.keysWord r == q) = true := by
      simp [hrc, hkey_eq]
    rw [hcond]
    simp only [↓reduceIte]
    refine ⟨trivial, trivial, fun v hv_ne => Function.update_of_ne hv_ne _ _,
      cnt, Nat.le_succ cnt, ?_⟩
    dsimp only [ValidSubtree]
    rw [Function.update_self]
    refine ⟨hidx_lt, hmeta, by omega, hkw, wordUpdateAt_lt hrc hval hvw,
      hbounds, hmono, ?_⟩
    intro q' hq1 hq2
    by_cases hqq : q' = q
    · subst q'
      left
      refine ⟨r, hrc, hkey_eq, ?_⟩
      rw [Function.update_self, laneGet_wordUpdateAt hval]
      simp
    · rw [Function.update_of_ne hqq]
      rcases href q' hq1 hq2 with ⟨j₀, hj₀, hkj₀, hmj₀⟩ | ⟨hno, hmno⟩
      · have hj₀_ne : j₀ ≠ r := fun he => hqq (hkj₀ ▸ he ▸ hkey_eq)
        left
        refine ⟨j₀, hj₀, hkj₀, ?_⟩
        rw [laneGet_wordUpdateAt hval]
        simp [hj₀_ne, hmj₀]
      · right
        exact ⟨hno, hmno⟩
  · have hcond : (r < cnt && laneGet W_key nd.keysWord r == q) = false := by
      by_cases hrc : r < cnt
      · have hne : laneGet W_key nd.keysWord r ≠ q := fun he => hhit ⟨hrc, he⟩
        simp [hrc, hne]
      · simp [hrc]
    have hq_lt_W : q < 2 ^ W_key :=
      hq_fp.trans (Nat.pow_lt_pow_right (by decide) (by dsimp [W_key]; omega))
    have hgt_r : ∀ j, r ≤ j → j < cnt → q < laneGet W_key nd.keysWord j := by
      intro j hrj hjc
      have hle := hge_r j hrj hjc
      rcases eq_or_lt_of_le hle with heq | hlt
      · exfalso
        rcases eq_or_lt_of_le hrj with rfl | hlt_rj
        · exact hhit ⟨hjc, heq.symm⟩
        · have := hmono r j hlt_rj hjc
          have := hge_r r le_rfl (hlt_rj.trans hjc)
          omega
      · exact hlt
    rw [hcond]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, trivial, fun v hv_ne => Function.update_of_ne hv_ne _ _,
      cnt + 1, le_rfl, ?_⟩
    dsimp only [ValidSubtree]
    rw [Function.update_self]
    refine ⟨hidx_lt, rfl, by omega,
      wordInsertAt_lt hr_le hq_lt_W hkw,
      wordInsertAt_lt hr_le hval hvw, ?_, ?_, ?_⟩
    · intro j hj
      rw [laneGet_wordInsertAt hq_lt_W]
      split_ifs with hjr hjeq
      · exact hbounds j (by omega)
      · exact ⟨hqlo, hqhi⟩
      · exact hbounds (j - 1) (by omega)
    · intro i j hij hj
      rw [laneGet_wordInsertAt hq_lt_W, laneGet_wordInsertAt hq_lt_W]
      split_ifs with hir hieq hjr hjeq
      · exact hmono i j hij (by omega)
      · exact hlt_r i hir
      · exact (hlt_r i hir).trans (hgt_r (j - 1) (by omega) (by omega))
      · omega
      · omega
      · exact hgt_r (j - 1) (by omega) (by omega)
      · omega
      · omega
      · exact hmono (i - 1) (j - 1) (by omega) (by omega)
    · intro q' hq1 hq2
      by_cases hqq : q' = q
      · subst q'
        left
        refine ⟨r, by omega, ?_, ?_⟩
        · rw [laneGet_wordInsertAt hq_lt_W]; simp
        · rw [Function.update_self, laneGet_wordInsertAt hval]; simp
      · rw [Function.update_of_ne hqq]
        rcases href q' hq1 hq2 with ⟨j₀, hj₀, hkj₀, hmj₀⟩ | ⟨hno, hmno⟩
        · left
          by_cases hj₀_lt : j₀ < r
          · refine ⟨j₀, by omega, ?_, ?_⟩
            · rw [laneGet_wordInsertAt hq_lt_W]; simp [hj₀_lt, hkj₀]
            · rw [laneGet_wordInsertAt hval]; simp [hj₀_lt, hmj₀]
          · refine ⟨j₀ + 1, by omega, ?_, ?_⟩
            · have h1 : ¬(j₀ + 1 < r) := by omega
              have h2 : j₀ + 1 ≠ r := by omega
              rw [laneGet_wordInsertAt hq_lt_W]; simp [h1, h2, hkj₀]
            · have h1 : ¬(j₀ + 1 < r) := by omega
              have h2 : j₀ + 1 ≠ r := by omega
              rw [laneGet_wordInsertAt hval]; simp [h1, h2, hmj₀]
        · right
          refine ⟨fun j hj => ?_, hmno⟩
          rw [laneGet_wordInsertAt hq_lt_W]
          split_ifs with hjr hjeq
          · exact hno j (by omega)
          · exact Ne.symm hqq
          · exact hno (j - 1) (by omega)

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
