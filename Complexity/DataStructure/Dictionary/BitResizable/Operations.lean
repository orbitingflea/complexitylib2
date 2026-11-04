/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Layout

/-!
# Bit-Resizable Succinct Dictionary Primitives, Probe-Excess Bounds, and Bit Extensionality

This module establishes the probe-excess and uniform-expectation bounds on `BucketRepInv`, the
physical-to-dense inverse mapping (`physOfDense`) and canonical tail-to-dense bijection
(`tdCanon`, `dtCanon`), bit-level state extensionality (`bitMemoryState_eq_of_meta_and_items`),
and the concrete `BitRAM.Code .standard 12` word and dense-item primitives (`storeWordCode`,
`growWordStoreCode`, `shrinkWordCode`, `initEmptyCode`, `readFieldCode`, `writeFieldCode`,
`writeDenseItemCode`) under demonic `.grow`.

## Main definitions

* `physOfDense`, `tdCanon`, `dtCanon`: inverse dense-to-physical map and canonical circular
  bijection.
* `storeWordCode`, `growWordStoreCode`, `shrinkWordCode`, `initEmptyCode`: word-level and
  empty-initialization `BitRAM.Code .standard 12` programs under demonic `.grow`.
* `readFieldCode`, `writeFieldCode`, `writeDenseItemCode`: bit-field and dense-item read/write
  `BitRAM.Code` programs.

## Main results

* `chain_and_overflow_le_probeExcess_rep`, `tsum_uniform_probeExcess_rep_le_five`: per-key and
  expected probe-excess bounds under `BucketRepInv` and `EpochInv`.
* `physOfDense_denseOfPhys`, `bucketRepInv_of_fixed`: bridge between fixed-capacity
  `Succinct.BucketStateInv` and bit-resizable `BucketRepInv`.
* `bitMemoryState_eq_of_meta_and_items`: bit-extensionality of `BitMemory.State` from its metadata
  words `< epochMetaWords U w N` and its `n_t` dense items.
* `initEmptyCode_exec`: initializes `Rep U V w 0 default (Dynamic.empty U)` from `bitSize = 0` in
  `20` `BitRAM` instructions under demonic `.grow`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Probe-excess and uniform expectation bounds on `BucketRepInv` -/

/-- Under `BucketRepInv` for `Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs`,
the micro-chain length `(L b m).length` is at most `1 + microCollCount` and the bucket overflow
`bCount N gm b - effBucketCap N` is at most `1 + bucketOvfCount`, so their sum is at most
`2 + probeExcess`. -/
theorem chain_and_overflow_le_probeExcess_rep {U V w N : ℕ}
    (θ : Succinct.QuotHashSeed U N) {L : ℕ → ℕ → List ℕ}
    {s_abs : Dynamic.State U} {s_bit : BitMemory.State}
    (hinv : BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
      (Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs) s_bit)
    (u : Fin U) :
    let h1 := Succinct.hValOfSeed U N θ
    let b := feistelBucket (bucketBits N) h1 u.val
    let q := keyQuotient (bucketBits N) u.val
    let m := Succinct.mOfSeed U N θ q
    let gm := gmAtBit U w N s_bit.mem
    (L b m).length ≤
      1 + microCollCount N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u ∧
    Succinct.bCount N gm b - effBucketCap N ≤
      1 + bucketOvfCount N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u ∧
    (L b m).length + (Succinct.bCount N gm b - effBucketCap N) ≤
      2 + probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u ∧
    8 * (L b m).length + 6 * (Succinct.bCount N gm b - effBucketCap N) ≤
      14 + 8 * probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u := by
  classical
  intro h1 b q m gm
  have hb : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  have hm : m < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
  let qSlot (j : ℕ) : ℕ :=
    virtualQuotAt U V w N s_bit (Succinct.slotOf N gm b j)
  let uVal (j : ℕ) : ℕ :=
    feistelReconstruct (bucketBits N) h1 b (qSlot j)
  have hslot_key : ∀ j < Succinct.bCount N gm b,
      ∃ hu_j : uVal j < U,
        (⟨uVal j, hu_j⟩ : Fin U) ∈ Dynamic.dom s_abs ∧
        feistelBucket (bucketBits N) h1 (uVal j) = b ∧
        keyQuotient (bucketBits N) (uVal j) = qSlot j := by
    intro j hj
    have hsome := hinv.hmap_some b hb j hj
    change Succinct.bucketMapOfState U N h1 s_abs b (qSlot j) = some _ at hsome
    unfold Succinct.bucketMapOfState at hsome
    split_ifs at hsome with hcond
    refine ⟨hcond.1, Dictionary.mem_dom_iff_isSome.mpr (by rw [hsome]; rfl), ?_⟩
    exact feistelBucket_feistelReconstruct h1 hb (qSlot j)
  let keyAt (j : ℕ) : Fin U :=
    if hj : j < Succinct.bCount N gm b then
      ⟨uVal j, (hslot_key j hj).1⟩
    else
      u
  have hkeyAt_props : ∀ j (hj : j < Succinct.bCount N gm b),
      keyAt j ∈ Dynamic.dom s_abs ∧
      feistelBucketHash N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2 (keyAt j) =
        feistelBucketHash N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2 u ∧
      keyQuotient (bucketBits N) (keyAt j).val = qSlot j := by
    intro j hj
    have hval : (keyAt j).val = uVal j := by
      dsimp only [keyAt]
      rw [dite_eq_left hj]
    obtain ⟨hu_j, hdom, hb_j, hq_j⟩ := hslot_key j hj
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [keyAt]
      rw [dite_eq_left hj]
      exact hdom
    · apply Fin.ext
      rw [Succinct.feistelBucketHash_val_eq_hValOfSeed,
        Succinct.feistelBucketHash_val_eq_hValOfSeed, hval, hb_j]
    · rw [hval, hq_j]
  have hkeyAt_inj : ∀ j₁ < Succinct.bCount N gm b, ∀ j₂ < Succinct.bCount N gm b,
      keyAt j₁ = keyAt j₂ → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ heq
    have hq₁ := (hkeyAt_props j₁ hj₁).2.2
    have hq₂ := (hkeyAt_props j₂ hj₂).2.2
    rw [heq] at hq₁
    exact hinv.hnodup_q b hb j₁ hj₁ j₂ hj₂ (hq₁.symm.trans hq₂)
  have hlen : (L b m).length ≤
      1 + microCollCount N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u := by
    have hnodup : (L b m).Nodup := (hinv.hchains.1 b hb m hm).nodup
    have hcard_eq : (L b m).length = #(L b m).toFinset :=
      (List.toFinset_card_of_nodup hnodup).symm
    rw [hcard_eq]
    refine card_microSlots_le (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
      (Dynamic.dom s_abs) u (L b m).toFinset keyAt ?_ ?_
    · intro j₁ hj₁ j₂ hj₂ heq
      have hj₁_lt := ((hinv.hchain_mem b hb m hm j₁).mp (List.mem_toFinset.mp hj₁)).1
      have hj₂_lt := ((hinv.hchain_mem b hb m hm j₂).mp (List.mem_toFinset.mp hj₂)).1
      exact hkeyAt_inj j₁ hj₁_lt j₂ hj₂_lt heq
    · intro j hj
      obtain ⟨hj_lt, _, hm_j⟩ := (hinv.hchain_mem b hb m hm j).mp (List.mem_toFinset.mp hj)
      obtain ⟨hdom, hb_eq, hq_eq⟩ := hkeyAt_props j hj_lt
      refine ⟨hdom, (feistelMicroHash_eq_iff N _ _ θ.2 (keyAt j) u).mpr ⟨hb_eq, ?_⟩⟩
      apply Fin.ext
      rw [Succinct.feistelLocalMicro_val_eq_mOfSeed,
        Succinct.feistelLocalMicro_val_eq_mOfSeed, hq_eq]
      exact hm_j
  have hovf : Succinct.bCount N gm b - effBucketCap N ≤
      1 + bucketOvfCount N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u := by
    refine bucketOverflow_le (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
      (Dynamic.dom s_abs) u (fun j : Fin (Succinct.bCount N gm b) => keyAt j.val) ?_ ?_
    · intro j₁ j₂ heq
      exact Fin.ext (hkeyAt_inj j₁.val j₁.isLt j₂.val j₂.isLt heq)
    · intro j
      exact ⟨(hkeyAt_props j.val j.isLt).1, (hkeyAt_props j.val j.isLt).2.1⟩
  refine ⟨hlen, hovf, ?_, ?_⟩ <;>
  · unfold probeExcess
    omega

/-- Under `EpochInv U N (Dynamic.dom s_abs).card` and `0 < N`, the expected `probeExcess` over a
uniformly sampled quotient hash seed `θ : Succinct.QuotHashSeed U N` is at most `5`. -/
theorem tsum_uniform_probeExcess_rep_le_five {U N : ℕ} {s_abs : Dynamic.State U}
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card) (hN : 0 < N) (u : Fin U) :
    (∑' θ : Succinct.QuotHashSeed U N,
      (PMF.uniformOfFintype (Succinct.QuotHashSeed U N)) θ *
        (probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
          (Dynamic.dom s_abs) u : ℝ≥0∞)) ≤ 5 := by
  rcases hepoch with ⟨_, hN0⟩ | ⟨_, hlo, _, hnU⟩
  · omega
  · have herase : #((Dynamic.dom s_abs).erase u) ≤ N :=
      Finset.card_erase_le.trans hlo
    exact Succinct.tsum_uniform_probeExcess_reducedPolyHash_le_five hnU (Dynamic.dom s_abs) u herase

/-! ## Section 2: Physical-to-dense inverse (`physOfDense`), canonical `TailDenseInv`, and
bit-extensionality -/

/-- Inverse of `denseOfPhys`: maps a dense item index `d < n_t` back to its physical slot `< N`
in the fixed-capacity slot store. -/
@[expose]
def physOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < gm 0 * slabSize N then d
  else N - 1 - dt (d % maxTailItems N)

/-- Under `SlotStoreInv N gm` and `TailDenseInv N (gm 0) (gm 1) td dt`, `physOfDense N gm dt` is a
left inverse of `denseOfPhys N gm td` on all active slots `Succinct.slotOf N gm b j`. -/
theorem physOfDense_denseOfPhys {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (htd : TailDenseInv N (gm 0) (gm 1) td dt)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < Succinct.bCount N gm b) :
    physOfDense N gm dt (denseOfPhys N gm td (Succinct.slotOf N gm b j)) =
      Succinct.slotOf N gm b j := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · unfold physOfDense denseOfPhys
    simp only [hb0, ↓reduceIte]
  · have hb_ne : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
    have htail := hslot.multi_tail hb_pos
    have hslab := hslot.multi_slab hb_pos
    have htot := hslot.multi_total_le hb_pos
    have hK : 0 < slabSize N := slabSize_pos N
    unfold Succinct.bCount at hj
    simp only [hb_ne, ↓reduceIte, hb] at hj
    by_cases hj_slab : j < gm (Succinct.gmQIdx b) * slabSize N
    · have hs_lt : j / slabSize N < gm (Succinct.gmQIdx b) :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hp_lt : Succinct.slabPtrOf N gm b (j / slabSize N) < gm 0 := by
        rw [hslab.nslabs_eq]
        exact hslab.ptr_lt b hb _ hs_lt
      have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
      have hphys_lt : Succinct.slotOf N gm b j < gm 0 * slabSize N := by
        unfold Succinct.slotOf
        simp only [hb_ne, ↓reduceIte, hj_slab]
        have h1 : (Succinct.slabPtrOf N gm b (j / slabSize N) + 1) * slabSize N ≤
            gm 0 * slabSize N := Nat.mul_le_mul_right _ hp_lt
        rw [Nat.add_one_mul] at h1
        omega
      unfold denseOfPhys physOfDense
      simp only [hb_ne, ↓reduceIte, hphys_lt]
    · have hr_lt : j - gm (Succinct.gmQIdx b) * slabSize N < gm (Succinct.gmRIdx b) := by omega
      have ht_lt :
          gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N)) < gm 1 := by
        rw [htail.ntails_eq]
        exact htail.ptr_lt b hb _ hr_lt
      set t := gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N))
      have hphys_eq : Succinct.slotOf N gm b j = N - 1 - t := by
        unfold Succinct.slotOf
        simp only [hb_ne, ↓reduceIte, hj_slab]
        rfl
      have hphys_not_lt : ¬Succinct.slotOf N gm b j < gm 0 * slabSize N := by
        rw [hphys_eq]; omega
      have hsub_t : N - 1 - Succinct.slotOf N gm b j = t := by
        rw [hphys_eq]; omega
      have hd_eq : denseOfPhys N gm td (Succinct.slotOf N gm b j) =
          denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t) := by
        unfold denseOfPhys
        simp only [hb_ne, ↓reduceIte, hphys_not_lt, hsub_t]
      have hd_not_lt : ¬denseOfPhys N gm td (Succinct.slotOf N gm b j) < gm 0 * slabSize N := by
        rw [hd_eq]
        unfold denseOfCirc
        split_ifs <;> omega
      have hM_pos : 0 < maxTailItems N := by
        have := htail.ntails_le
        omega
      rw [physOfDense, ite_eq_right hb_ne, ite_eq_right hd_not_lt, hd_eq,
        denseOfCirc_mod hM_pos (htd.td_lt t ht_lt), htd.dt_td t ht_lt, hphys_eq]

/-- Canonical `TailDense` array for `(N, n_slabs, n_tails)`: maps active tail index `t < n_tails`
to `(n_slabs * slabSize N + t) % maxTailItems N`. -/
@[expose]
def tdCanon (N n_slabs n_tails t : ℕ) : ℕ :=
  if t < n_tails then (n_slabs * slabSize N + t) % maxTailItems N else 0

/-- Canonical `DenseTail` array for `(N, n_slabs, n_tails)`: maps circular residue
`c < maxTailItems N` to
`denseOfCirc (maxTailItems N) (n_slabs * slabSize N) c - n_slabs * slabSize N` when `< n_tails`. -/
@[expose]
def dtCanon (N n_slabs n_tails c : ℕ) : ℕ :=
  let base_tail := n_slabs * slabSize N
  let d := denseOfCirc (maxTailItems N) base_tail c
  if c < maxTailItems N ∧ d - base_tail < n_tails then d - base_tail else 0

/-- Whenever `n_tails ≤ maxTailItems N`, `(tdCanon N n_slabs n_tails, dtCanon N n_slabs n_tails)`
satisfies `TailDenseInv N n_slabs n_tails`. -/
theorem tailDenseInv_canon {N n_slabs n_tails : ℕ} (hle : n_tails ≤ maxTailItems N) :
    TailDenseInv N n_slabs n_tails (tdCanon N n_slabs n_tails) (dtCanon N n_slabs n_tails) where
  td_lt t ht := by
    have hM : 0 < maxTailItems N := by omega
    unfold tdCanon
    rw [ite_eq_left ht]
    exact Nat.mod_lt _ hM
  dense_lt t ht := by
    have hM : 0 < maxTailItems N := by omega
    unfold tdCanon
    rw [ite_eq_left ht,
      denseOfCirc_mod_self hM (Nat.le_add_right _ t) (by omega)]
    omega
  dt_td t ht := by
    have hM : 0 < maxTailItems N := by omega
    have htc : tdCanon N n_slabs n_tails t = (n_slabs * slabSize N + t) % maxTailItems N :=
      ite_eq_left ht
    have htc_lt : tdCanon N n_slabs n_tails t < maxTailItems N := by
      rw [htc]; exact Nat.mod_lt _ hM
    have hd_eq : denseOfCirc (maxTailItems N) (n_slabs * slabSize N)
        (tdCanon N n_slabs n_tails t) = n_slabs * slabSize N + t := by
      rw [htc]
      exact denseOfCirc_mod_self hM (Nat.le_add_right _ t) (by omega)
    unfold dtCanon
    dsimp only
    rw [hd_eq]
    have hsub : n_slabs * slabSize N + t - n_slabs * slabSize N = t := Nat.add_sub_cancel_left _ _
    rw [hsub, ite_eq_left ⟨htc_lt, ht⟩]
  owner_valid d hlo hhi := by
    have hM : 0 < maxTailItems N := by omega
    have hc_lt : d % maxTailItems N < maxTailItems N := Nat.mod_lt d hM
    have hd_eq : denseOfCirc (maxTailItems N) (n_slabs * slabSize N) (d % maxTailItems N) = d :=
      denseOfCirc_mod_self hM hlo (by omega)
    have hsub_lt : d - n_slabs * slabSize N < n_tails := by omega
    have hdt_eq : dtCanon N n_slabs n_tails (d % maxTailItems N) = d - n_slabs * slabSize N := by
      unfold dtCanon
      dsimp only
      rw [hd_eq, ite_eq_left ⟨hc_lt, hsub_lt⟩]
    rw [hdt_eq]
    refine ⟨hsub_lt, ?_⟩
    unfold tdCanon
    rw [ite_eq_left hsub_lt, Nat.add_sub_of_le hlo]

/-- Bridge theorem: any `s_bit : BitMemory.State` that agrees with a fixed-capacity state `s_fix`
satisfying `Succinct.BucketStateInv` on `gm`, `lm`, and active `(quot, val)` slots (via
`physOfDense`) satisfies `BucketRepInv`. -/
theorem bucketRepInv_of_fixed {U V w N base : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ}
    {s_fix : Memory.State} {s_bit : BitMemory.State}
    (hfix : Succinct.BucketStateInv U V w N (Succinct.hashSpace U w N) base mOf L B s_fix)
    (hgm : gmAtBit U w N s_bit.mem =
      Succinct.gmAt base U V w N (Succinct.hashSpace U w N) s_fix.mem)
    (hlm : lmAtBit U w N s_bit.mem =
      Succinct.lmAt base U V w N (Succinct.hashSpace U w N) s_fix.mem)
    (htd : TailDenseInv N (gmAtBit U w N s_bit.mem 0) (gmAtBit U w N s_bit.mem 1)
      (tdAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem))
    (hq : ∀ d < Succinct.totalSlots N (gmAtBit U w N s_bit.mem),
      denseQuotAt U V w N s_bit d =
        Succinct.quotAt base U w N (Succinct.hashSpace U w N) s_fix.mem
          (physOfDense N (gmAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem) d))
    (hv : ∀ d < Succinct.totalSlots N (gmAtBit U w N s_bit.mem),
      denseValAt U V w N s_bit d =
        Succinct.valAt base U V w N (Succinct.hashSpace U w N) s_fix.mem
          (physOfDense N (gmAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem) d)) :
    BucketRepInv U V w N mOf L B s_bit := by
  have hslot : Succinct.SlotStoreInv N (gmAtBit U w N s_bit.mem) := by
    rw [hgm]; exact hfix.hslot
  have hchains : Succinct.AllChainsValid N (lmAtBit U w N s_bit.mem) L := by
    rw [hlm]; exact hfix.hchains
  have hvq : ∀ b < numBuckets N, ∀ j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b,
      virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) =
        Succinct.quotAt base U w N (Succinct.hashSpace U w N) s_fix.mem
          (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) ∧
      virtualValAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) =
        Succinct.valAt base U V w N (Succinct.hashSpace U w N) s_fix.mem
          (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) := by
    intro b hb j hj
    have hphys_lt : Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j < N :=
      (Succinct.slotOf_lt_and_injective hslot).1 b hb j hj
    have hd_lt : denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)
        (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) <
        Succinct.totalSlots N (gmAtBit U w N s_bit.mem) :=
      (denseOfPhys_slotOf_lt_and_injective hslot htd).1 b hb j hj
    have hinv_pd := physOfDense_denseOfPhys hslot htd hb hj
    refine ⟨?_, ?_⟩
    · unfold virtualQuotAt
      rw [ite_eq_left hphys_lt, hq _ hd_lt, hinv_pd]
    · unfold virtualValAt
      rw [ite_eq_left hphys_lt, hv _ hd_lt, hinv_pd]
  refine ⟨hslot, htd, hchains,
    fun b hb m hm j => ?_,
    fun b hb j₁ hj₁ j₂ hj₂ heq => ?_,
    fun b hb j hj => ?_,
    fun b hb q => ?_⟩
  · rw [hfix.hchain_mem b hb m hm j, ← hgm]
    exact ⟨fun ⟨hj, hc, hm_eq⟩ => ⟨hj, hc, by rw [(hvq b hb j hj).1, hm_eq]⟩,
      fun ⟨hj, hc, hm_eq⟩ => ⟨hj, hc, by rw [← (hvq b hb j hj).1, hm_eq]⟩⟩
  · rw [(hvq b hb j₁ hj₁).1, (hvq b hb j₂ hj₂).1, hgm] at heq
    rw [hgm] at hj₁ hj₂
    exact hfix.hnodup_q b hb j₁ hj₁ j₂ hj₂ heq
  · rw [(hvq b hb j hj).1, (hvq b hb j hj).2, hgm]
    rw [hgm] at hj
    exact hfix.hmap_some b hb j hj
  · rw [hfix.hmap_dom b hb q, ← hgm]
    exact ⟨fun ⟨j, hj, hq_eq⟩ => ⟨j, hj, by rw [(hvq b hb j hj).1, hq_eq]⟩,
      fun ⟨j, hj, hq_eq⟩ => ⟨j, hj, by rw [← (hvq b hb j hj).1, hq_eq]⟩⟩

/-- **Bit-level state extensionality (`bitMemoryState_eq_of_meta_and_items`):**
any two well-formed `BitMemory.State`s with `bitSize = dictBitSize U V w N n_t` that agree on all
metadata words `a < epochMetaWords U w N` and on `denseQuotAt` and `denseValAt` for all `d < n_t`
are identical (`s₁ = s₂`). -/
theorem bitMemoryState_eq_of_meta_and_items {U V w N n_t : ℕ} {s₁ s₂ : BitMemory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hs₁ : s₁.WellFormed w) (hs₂ : s₂.WellFormed w)
    (hsz₁ : s₁.bitSize = dictBitSize U V w N n_t)
    (hsz₂ : s₂.bitSize = dictBitSize U V w N n_t)
    (hmeta : ∀ a < epochMetaWords U w N, s₁.mem a = s₂.mem a)
    (hitems : ∀ d < n_t,
      denseQuotAt U V w N s₁ d = denseQuotAt U V w N s₂ d ∧
      denseValAt U V w N s₁ d = denseValAt U V w N s₂ d) :
    s₁ = s₂ := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  ext a
  · apply word_eq_of_readBit_eq hw (hs₁.mem_fits a) (hs₂.mem_fits a)
    intro j hj
    set i := a * w + j
    by_cases hi_meta : i < epochMetaBits U w N
    · have ha_lt : a < epochMetaWords U w N := by
        unfold epochMetaBits at hi_meta
        exact (Nat.mul_lt_mul_right hw).mp (by omega)
      have hdiv : i / w = a := by
        dsimp only [i]
        rw [Nat.mul_comm a w, Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]
      simp only [readBit, Nat.zero_add, hdiv, hmeta a ha_lt]
    · by_cases hi_dict : i < dictBitSize U V w N n_t
      · have hpos_ib : 0 < itemBits U V N := by
          unfold dictBitSize at hi_dict
          rcases Nat.eq_zero_or_pos (itemBits U V N) with h0 | hpos
          · rw [h0, Nat.mul_zero] at hi_dict; omega
          · exact hpos
        set off := i - epochMetaBits U w N
        have hoff_lt : off < n_t * itemBits U V N := by
          unfold dictBitSize at hi_dict; omega
        set d := off / itemBits U V N
        set r := off % itemBits U V N
        have hd_lt : d < n_t :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hr_lt : r < itemBits U V N := Nat.mod_lt off hpos_ib
        have hdiv_mod : d * itemBits U V N + r = off := by
          dsimp only [d, r]
          rw [Nat.mul_comm]
          exact Nat.div_add_mod off (itemBits U V N)
        have hi_eq : i = itemBitOff U V w N d + r := by
          unfold itemBitOff
          dsimp only [off] at hdiv_mod
          omega
        by_cases hr_q : r < quotientBits U N
        · have h1 := readField_testBit hw 0 s₁.mem (a := itemQuotBitOff U V w N d) hqw r
          have h2 := readField_testBit hw 0 s₂.mem (a := itemQuotBitOff U V w N d) hqw r
          rw [ite_eq_left hr_q] at h1 h2
          have hq_eq : (denseQuotAt U V w N s₁ d).testBit r =
              (denseQuotAt U V w N s₂ d).testBit r :=
            congrArg (fun x => x.testBit r) (hitems d hd_lt).1
          unfold denseQuotAt BitMemory.State.getField at hq_eq
          rw [h1, h2] at hq_eq
          unfold itemQuotBitOff at hq_eq
          rwa [← hi_eq] at hq_eq
        · set r' := r - quotientBits U N
          have hr'_lt : r' < valBits V := by
            unfold itemBits at hr_lt; omega
          have h1 := readField_testBit hw 0 s₁.mem (a := itemValBitOff U V w N d) hvw r'
          have h2 := readField_testBit hw 0 s₂.mem (a := itemValBitOff U V w N d) hvw r'
          rw [ite_eq_left hr'_lt] at h1 h2
          have hv_eq : (denseValAt U V w N s₁ d).testBit r' =
              (denseValAt U V w N s₂ d).testBit r' :=
            congrArg (fun x => x.testBit r') (hitems d hd_lt).2
          unfold denseValAt BitMemory.State.getField at hv_eq
          rw [h1, h2] at hv_eq
          have hi_val : itemValBitOff U V w N d + r' = i := by
            unfold itemValBitOff
            omega
          rwa [hi_val] at hv_eq
      · have h1 : s₁.getBit w i = false := hs₁.zero_above i (by omega)
        have h2 : s₂.getBit w i = false := hs₂.zero_above i (by omega)
        exact h1.trans h2.symm
  · exact hsz₁.trans hsz₂.symm

/-! ## Section 3: Concrete `BitRAM.Code .standard 12` word and dense-item primitives -/

/-- Store constant `val` into word address `k` in `3` `BitRAM` instructions. -/
@[expose]
def storeWordCode (k val : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 k))
    (.seq (.op (.const 2 val))
      (.op (.store 1 2)))

/-- Execution certificate for `storeWordCode k val` when `(k + 1) * w ≤ x.bitSize`. -/
theorem storeWordCode_exec {w k val : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w)
    (hk_adm : (k + 1) * w ≤ x.bitSize) (hval : Fits w val) :
    BitRAM.DemonicExecWithin w (storeWordCode k val) x
      (fun y =>
        y.toBitMemoryState = ⟨Function.update x.mem k val, x.bitSize⟩ ∧
        y.WellFormed w ∧
        y.bitSize = x.bitSize) 3 := by
  have hsz_fits : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hk_fits : Fits w k := by
    have h1 : k < (k + 1) * w := by
      have : 1 * 1 ≤ (k + 1) * w := Nat.mul_le_mul (by omega) hw
      nlinarith
    exact Fits.of_le hsz_fits (by omega)
  have hadm : ((x.set 1 k).set 2 val).regs 1 < ((x.set 1 k).set 2 val).wordSize w := by
    change k < x.wordSize w
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    have hlt : k * w < x.wordSize w * w := by
      have : (k + 1) * w = k * w + w := by ring
      omega
    exact (Nat.mul_lt_mul_right hw).mp hlt
  refine DemonicExecWithin.step_const (T := 2) hk_fits ?_
  refine DemonicExecWithin.step_const (T := 1) hval ?_
  refine DemonicExecWithin.store hadm ?_
  let y := ((x.set 1 k).set 2 val).write k val
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, fun q => ?_, hx.mem_wf.bitSize_fits, fun i hi => ?_⟩
    · by_cases hi2 : i = 2
      · subst hi2; exact hval
      · by_cases hi1 : i = 1
        · subst hi1; exact hk_fits
        · simp only [y, BitRAM.Data.write, BitRAM.Data.set, Function.update_of_ne hi2,
            Function.update_of_ne hi1]
          exact hx.regs_fits i
    · change Fits w (Function.update x.mem k val q)
      by_cases hq : q = k
      · subst hq; rw [Function.update_self]; exact hval
      · rw [Function.update_of_ne hq]; exact hx.mem_wf.mem_fits q
    · change x.bitSize ≤ i at hi
      change readBit w 0 (Function.update x.mem k val) i = false
      unfold readBit
      rw [Nat.zero_add]
      have hdiv_ne : i / w ≠ k := by
        intro heq
        have hrem := Nat.mod_lt i hw
        have hdm := Nat.div_add_mod i w
        rw [heq] at hdm
        have : w * k + w = (k + 1) * w := by ring
        omega
      rw [Function.update_of_ne hdiv_ne]
      have hza := hx.mem_wf.zero_above i hi
      change readBit w 0 x.mem i = false at hza
      unfold readBit at hza
      rwa [Nat.zero_add] at hza
  exact ⟨rfl, hy_wf, rfl⟩

/-- Grow `x.bitSize` from `k * w` to `(k + 1) * w` by `w` bits under demonic `.grow` and overwrite
word `k` with `val` in `5` `BitRAM` instructions, eliminating all demonic bits in word `k`. -/
@[expose]
def growWordStoreCode (w k val : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 w))
    (.seq (.grow 1 1)
      (storeWordCode k val))

/-- **Demonic determinism of `growWordStoreCode`:**
when `x.bitSize = k * w`, growing by `w` bits and storing `val` at word `k` produces the exact
deterministic state `⟨Function.update x.mem k val, (k + 1) * w⟩` across all demonic `.grow`
branches in `5` `BitRAM` instructions. -/
theorem growWordStoreCode_exec {w k val : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w)
    (hsz : x.bitSize = k * w)
    (hfits : Fits w ((k + 1) * w)) (hval : Fits w val) :
    BitRAM.DemonicExecWithin w (growWordStoreCode w k val) x
      (fun y =>
        y.toBitMemoryState = ⟨Function.update x.mem k val, (k + 1) * w⟩ ∧
        y.WellFormed w ∧
        y.bitSize = (k + 1) * w) 5 := by
  have hw_fits : Fits w w := fits_self w
  have hgrow_fits : Fits w (x.bitSize + w) := by
    rw [hsz, ← Nat.add_one_mul]
    exact hfits
  have hcost : max 1 (w ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw le_rfl x.toBitMemoryState).le
  refine DemonicExecWithin.step_const (T := 4) hw_fits ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w x.toBitMemoryState (.grow w) s₁ x.bitSize ∧
        y₁ = ⟨Function.update (x.set 1 w).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 3)
    (.grow hgrow_fits hcost fun s₁ hs₁ => ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  let x₁ : BitRAM.Data 12 :=
    ⟨Function.update (x.set 1 w).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow w) hw hx.mem_wf hgrow_fits hs₁
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hx.mem_wf.bitSize_fits
    · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx.regs_fits i
  obtain ⟨hs₁_sz_raw, _, _, hpres₁, _⟩ := hs₁
  change s₁.bitSize = x.bitSize + w at hs₁_sz_raw
  have hs₁_sz : s₁.bitSize = (k + 1) * w := by
    rw [hs₁_sz_raw, hsz, Nat.add_one_mul]
  have hk_adm : (k + 1) * w ≤ x₁.bitSize := hs₁_sz.symm.le
  refine (storeWordCode_exec hw hx₁_wf hk_adm hval).mono (fun y ⟨hy_st, hy_wf, hy_sz⟩ => ?_) le_rfl
  have hmem_eq : Function.update s₁.mem k val = Function.update x.mem k val := by
    funext a
    by_cases ha : a = k
    · subst ha; simp only [Function.update_self]
    · simp only [Function.update_of_ne ha]
      apply word_eq_of_readBit_eq hw (hs₁_wf.mem_fits a) (hx.mem_wf.mem_fits a)
      intro j hj
      by_cases halt : a < k
      · have hi_lt : a * w + j < x.bitSize := by
          rw [hsz]
          have : (a + 1) * w ≤ k * w := Nat.mul_le_mul_right w halt
          rw [Nat.add_one_mul] at this
          omega
        exact hpres₁ (a * w + j) hi_lt
      · have hgt : k + 1 ≤ a := by omega
        have hi_ge : s₁.bitSize ≤ a * w + j := by
          rw [hs₁_sz]
          have : (k + 1) * w ≤ a * w := Nat.mul_le_mul_right w hgt
          omega
        have h1 : s₁.getBit w (a * w + j) = false := hs₁_wf.zero_above (a * w + j) hi_ge
        have hi_ge0 : x.toBitMemoryState.bitSize ≤ a * w + j := by
          change x.bitSize ≤ a * w + j
          rw [hsz]
          have : (k + 1) * w ≤ a * w := Nat.mul_le_mul_right w hgt
          rw [Nat.add_one_mul] at this
          omega
        have h2 : x.toBitMemoryState.getBit w (a * w + j) = false :=
          hx.mem_wf.zero_above (a * w + j) hi_ge0
        exact h1.trans h2.symm
  refine ⟨?_, hy_wf, hy_sz.trans hs₁_sz⟩
  rw [hy_st]
  ext a
  · exact congrFun hmem_eq a
  · exact hs₁_sz

/-- Shrink `x.bitSize` from `(k + 1) * w` to `k * w` by `w` bits in `2` `BitRAM` instructions. -/
@[expose]
def shrinkWordCode (w : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 w))
    (.shrink 1)

/-- Execution certificate for `shrinkWordCode w` when `x.bitSize = (k + 1) * w`. -/
theorem shrinkWordCode_exec {w k : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w) (hsz : x.bitSize = (k + 1) * w) :
    BitRAM.DemonicExecWithin w (shrinkWordCode w) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = k * w ∧
        ∀ a < k, y.mem a = x.mem a) 2 := by
  have hw_fits : Fits w w := fits_self w
  have hw_le : w ≤ x.bitSize := by
    rw [hsz, Nat.add_one_mul]
    omega
  have hcost : max 1 (w ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw le_rfl x.toBitMemoryState).le
  set s₁ := (BitMemory.stepFn w x.toBitMemoryState (.shrink w)).1
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink w) hw hx.mem_wf hw_le
  have hs₁_sz : s₁.bitSize = k * w := by
    change x.bitSize - w = k * w
    rw [hsz, Nat.add_one_mul]
    omega
  refine DemonicExecWithin.step_const (T := 1) hw_fits ?_
  refine DemonicExecWithin.shrink hw_le hcost ?_
  have hy_wf : (⟨(x.set 1 w).regs, s₁.mem, x.bitSize - w⟩ : BitRAM.Data 12).WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hw_fits
    · simp only [BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx.regs_fits i
  refine ⟨hy_wf, hs₁_sz, fun a ha => ?_⟩
  apply word_eq_of_readBit_eq hw (hs₁_wf.mem_fits a) (hx.mem_wf.mem_fits a)
  intro j hj
  have hi_lt : a * w + j < x.bitSize - w := by
    rw [hsz, Nat.add_one_mul]
    have : (a + 1) * w ≤ k * w := Nat.mul_le_mul_right w ha
    rw [Nat.add_one_mul] at this
    omega
  exact BitMemory.getBit_stepFn_shrink_of_lt hw x.toBitMemoryState w hi_lt

/-- Concrete `BitRAM.Code .standard 12` program initializing the empty bit-resizable dictionary
(`s_abs = Dynamic.empty U`, `N = 0`, `n_t = 0`) from `x.bitSize = 0` in `20` instructions under
demonic `.grow`. -/
@[expose]
def initEmptyCode (U V w : ℕ) : BitRAM.Code .standard 12 :=
  .seq (growWordStoreCode w 0 0)
    (.seq (growWordStoreCode w 1 0)
      (.seq (growWordStoreCode w 2 (itemBits U V 0))
        (growWordStoreCode w 3 (4 * w))))

/-- **Machine-level initialization certificate (`initEmptyCode_exec`):**
starting from any well-formed state `x : BitRAM.Data 12` with `x.bitSize = 0`, `initEmptyCode U V w`
executes in at most `20` `BitRAM` instructions across all demonic `.grow` branches and establishes
`Rep U V w 0 default (Dynamic.empty U) y.toBitMemoryState` with `y.bitSize = 4 * w`. -/
theorem initEmptyCode_exec {U V w : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hfits4 : Fits w (4 * w))
    (hx : x.WellFormed w) (hsz : x.bitSize = 0) :
    BitRAM.DemonicExecWithin w (initEmptyCode U V w) x
      (fun y =>
        Rep U V w 0 default (Dynamic.empty U) y.toBitMemoryState ∧
        y.bitSize = 4 * w ∧
        y.WellFormed w) 20 := by
  have h0_fits : Fits w 0 := fits_zero w
  have hib_fits : Fits w (itemBits U V 0) := by
    have hqw : quotientBits U 0 ≤ w := quotientBits_le_of_le_pow hU
    have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
    refine Fits.of_le hfits4 ?_
    unfold itemBits
    omega
  have hf1 : Fits w ((0 + 1) * w) := Fits.of_le hfits4 (by omega)
  have hf2 : Fits w ((1 + 1) * w) := Fits.of_le hfits4 (by omega)
  have hf3 : Fits w ((2 + 1) * w) := Fits.of_le hfits4 (by omega)
  have hf4 : Fits w ((3 + 1) * w) := hfits4
  refine .seq (T₁ := 5) (T₂ := 15)
    (growWordStoreCode_exec hw hx (by omega) hf1 h0_fits)
    (fun y₁ ⟨hy₁_st, hy₁_wf, hy₁_sz⟩ => ?_) (by omega)
  refine .seq (T₁ := 5) (T₂ := 10)
    (growWordStoreCode_exec hw hy₁_wf hy₁_sz hf2 h0_fits)
    (fun y₂ ⟨hy₂_st, hy₂_wf, hy₂_sz⟩ => ?_) (by omega)
  refine .seq (T₁ := 5) (T₂ := 5)
    (growWordStoreCode_exec hw hy₂_wf hy₂_sz hf3 hib_fits)
    (fun y₃ ⟨hy₃_st, hy₃_wf, hy₃_sz⟩ => ?_) (by omega)
  refine (growWordStoreCode_exec hw hy₃_wf hy₃_sz hf4 hfits4).mono
    (fun y ⟨hy_st, hy_wf, hy_sz⟩ => ?_) le_rfl
  have hm3 : y.mem 3 = 4 * w := by
    have h1 : y.mem 3 = Function.update y₃.mem 3 (4 * w) 3 :=
      congrArg (fun s : BitMemory.State => s.mem 3) hy_st
    simpa using h1
  have hm2 : y.mem 2 = itemBits U V 0 := by
    have h1 : y.mem 2 = Function.update y₃.mem 3 (4 * w) 2 :=
      congrArg (fun s : BitMemory.State => s.mem 2) hy_st
    have h2 : y₃.mem 2 = Function.update y₂.mem 2 (itemBits U V 0) 2 :=
      congrArg (fun s : BitMemory.State => s.mem 2) hy₃_st
    simpa using h1.trans h2
  have hm1 : y.mem 1 = 0 := by
    have h1 : y.mem 1 = Function.update y₃.mem 3 (4 * w) 1 :=
      congrArg (fun s : BitMemory.State => s.mem 1) hy_st
    have h2 : y₃.mem 1 = Function.update y₂.mem 2 (itemBits U V 0) 1 :=
      congrArg (fun s : BitMemory.State => s.mem 1) hy₃_st
    have h3 : y₂.mem 1 = Function.update y₁.mem 1 0 1 :=
      congrArg (fun s : BitMemory.State => s.mem 1) hy₂_st
    simpa using h1.trans (h2.trans h3)
  have hm0 : y.mem 0 = 0 := by
    have h1 : y.mem 0 = Function.update y₃.mem 3 (4 * w) 0 :=
      congrArg (fun s : BitMemory.State => s.mem 0) hy_st
    have h2 : y₃.mem 0 = Function.update y₂.mem 2 (itemBits U V 0) 0 :=
      congrArg (fun s : BitMemory.State => s.mem 0) hy₃_st
    have h3 : y₂.mem 0 = Function.update y₁.mem 1 0 0 :=
      congrArg (fun s : BitMemory.State => s.mem 0) hy₂_st
    have h4 : y₁.mem 0 = Function.update x.mem 0 0 0 :=
      congrArg (fun s : BitMemory.State => s.mem 0) hy₁_st
    simpa using h1.trans (h2.trans (h3.trans h4))
  have hcard0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    simp [Dynamic.dom, Dictionary.dom_empty]
  have hvb : Dynamic.ValuesBounded V (Dynamic.empty U) := by
    intro _ _ h
    simp [Dynamic.empty, Dictionary.empty] at h
  refine ⟨⟨hy_wf.mem_wf, ?_, ?_, hvb, ?_, hm1, hm2, ?_,
    fun h => by omega⟩, hy_sz, hy_wf⟩
  · change y.bitSize = dictBitSize U V w 0 (Dynamic.dom (Dynamic.empty U)).card
    rw [hcard0, hy_sz]
    simp [dictBitSize, epochMetaBits, epochMetaWords]
  · rw [hcard0]
    exact epochInv_zero U
  · rw [hcard0]
    exact hm0
  · change y.mem 3 = epochMetaBits U w 0
    simp only [epochMetaBits, epochMetaWords, ↓reduceIte]
    exact hm3

/-- Concrete `BitRAM.Code .standard 12` program reading a `b`-bit field at bit offset `off` into
register `r0` in `34` `BitRAM` instructions. -/
@[expose]
def readFieldCode (off b : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 off))
    (.seq (.op (.const 2 b))
      BitRAM.readBitsCode)

/-- Execution certificate for `readFieldCode off b`: executes in `34` instructions, setting
`y.regs 0 = x.toBitMemoryState.getField w off b` without modifying memory. -/
theorem readFieldCode_exec {w off b : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w) (hb : b ≤ w) (hend : off + b ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (readFieldCode off b) x
      (fun y =>
        y.regs 0 = x.toBitMemoryState.getField w off b ∧
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w) 34 := by
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hb
  have hsz_fits : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hoff_fits : Fits w off := Fits.of_le hsz_fits (by omega)
  refine DemonicExecWithin.step_const (T := 33) hoff_fits ?_
  refine DemonicExecWithin.step_const (T := 32) hb_fits ?_
  let x₁ : BitRAM.Data 12 := (x.set 1 off).set 2 b
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi2 : i = 2
    · subst hi2; exact hb_fits
    · by_cases hi1 : i = 1
      · subst hi1; exact hoff_fits
      · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi2, Function.update_of_ne hi1]
        exact hx.regs_fits i
  have hv_rd : BitMemory.valid w x₁.toBitMemoryState (.readBits (x₁.regs 1) (x₁.regs 2)) :=
    ⟨hb, hend⟩
  exact readBitsCode_exec_wf hw hx₁_wf hv_rd

/-- Concrete `BitRAM.Code .standard 12` program writing a `b`-bit value `val` at bit offset `off`
in `45` `BitRAM` instructions. -/
@[expose]
def writeFieldCode (off b val : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 off))
    (.seq (.op (.const 2 b))
      (.seq (.op (.const 3 val))
        BitRAM.writeBitsCode))

/-- Execution certificate for `writeFieldCode off b val`: executes in `45` instructions, updating
the `b`-bit field at bit offset `off` to `val` and preserving `bitSize` and `WellFormed w`. -/
theorem writeFieldCode_exec {w off b val : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w) (hb : b ≤ w) (hend : off + b ≤ x.bitSize)
    (hval : Fits b val) :
    BitRAM.DemonicExecWithin w (writeFieldCode off b val) x
      (fun y =>
        y.toBitMemoryState = ⟨writeFieldMem w 0 x.mem off b val, x.bitSize⟩ ∧
        y.WellFormed w) 45 := by
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hb
  have hsz_fits : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hoff_fits : Fits w off := Fits.of_le hsz_fits (by omega)
  have hval_fits : Fits w val := hval.mono hb
  refine DemonicExecWithin.step_const (T := 44) hoff_fits ?_
  refine DemonicExecWithin.step_const (T := 43) hb_fits ?_
  refine DemonicExecWithin.step_const (T := 42) hval_fits ?_
  let x₁ : BitRAM.Data 12 := (((x.set 1 off).set 2 b).set 3 val)
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi3 : i = 3
    · subst hi3; exact hval_fits
    · by_cases hi2 : i = 2
      · subst hi2; exact hb_fits
      · by_cases hi1 : i = 1
        · subst hi1; exact hoff_fits
        · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi3, Function.update_of_ne hi2,
            Function.update_of_ne hi1]
          exact hx.regs_fits i
  have hv_wr : BitMemory.valid w x₁.toBitMemoryState
      (.writeBits (x₁.regs 1) (x₁.regs 2) (x₁.regs 3)) :=
    ⟨hb, hend, hval⟩
  exact writeBitsCode_exec_wf hw hx₁_wf hv_wr

/-- Concrete `BitRAM.Code .standard 12` program writing `(q, v)` into dense item `d` in `90`
`BitRAM` instructions. -/
@[expose]
def writeDenseItemCode (U V w N d q v : ℕ) : BitRAM.Code .standard 12 :=
  .seq (writeFieldCode (itemQuotBitOff U V w N d) (quotientBits U N) q)
    (writeFieldCode (itemValBitOff U V w N d) (valBits V) v)

/-- Execution certificate for `writeDenseItemCode U V w N d q v`: executes in `90` instructions,
updating dense item `d < n_t` to `(q, v)` while preserving all other dense items `d' < n_t`
(`d' ≠ d`), all metadata words `a < epochMetaWords U w N`, `bitSize`, and `WellFormed w`. -/
theorem writeDenseItemCode_exec {U V w N n_t d q v : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (hd : d < n_t)
    (hsz : dictBitSize U V w N n_t ≤ x.bitSize)
    (hq : Fits (quotientBits U N) q) (hv : Fits (valBits V) v) :
    BitRAM.DemonicExecWithin w (writeDenseItemCode U V w N d q v) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = x.bitSize ∧
        denseQuotAt U V w N y.toBitMemoryState d = q ∧
        denseValAt U V w N y.toBitMemoryState d = v ∧
        (∀ d' < n_t, d' ≠ d →
          denseQuotAt U V w N y.toBitMemoryState d' =
            denseQuotAt U V w N x.toBitMemoryState d' ∧
          denseValAt U V w N y.toBitMemoryState d' =
            denseValAt U V w N x.toBitMemoryState d') ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a)) 90 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hd_end : itemBitOff U V w N (d + 1) ≤ x.bitSize := by
    have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
    simp only [itemBitOff, dictBitSize] at hsz ⊢
    omega
  have hq_end : itemQuotBitOff U V w N d + quotientBits U N ≤ x.bitSize := by
    rw [itemBitOff_succ] at hd_end
    simp only [itemQuotBitOff, itemBits] at hd_end ⊢
    omega
  have hv_end : itemValBitOff U V w N d + valBits V ≤ x.bitSize := by
    rwa [itemValBitOff_add_valBits]
  refine .seq (T₁ := 45) (T₂ := 45)
    (writeFieldCode_exec hw hx hqw hq_end hq)
    (fun y₁ ⟨hy₁_st, hy₁_wf⟩ => ?_) (by omega)
  have hy₁_sz : y₁.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy₁_st
  have hv_end₁ : itemValBitOff U V w N d + valBits V ≤ y₁.bitSize := by
    rw [hy₁_sz]; exact hv_end
  refine (writeFieldCode_exec hw hy₁_wf hvw hv_end₁ hv).mono
    (fun y ⟨hy_st, hy_wf⟩ => ?_) le_rfl
  have hy_sz : y.bitSize = x.bitSize :=
    (congrArg BitMemory.State.bitSize hy_st).trans hy₁_sz
  have hy_mem : y.mem =
      writeFieldMem w 0 (writeFieldMem w 0 x.mem (itemQuotBitOff U V w N d) (quotientBits U N) q)
        (itemValBitOff U V w N d) (valBits V) v := by
    have h1 : y.mem = writeFieldMem w 0 y₁.mem (itemValBitOff U V w N d) (valBits V) v :=
      congrArg BitMemory.State.mem hy_st
    have h2 : y₁.mem = writeFieldMem w 0 x.mem (itemQuotBitOff U V w N d) (quotientBits U N) q :=
      congrArg BitMemory.State.mem hy₁_st
    rw [h1, h2]
  have hqv_disj : itemQuotBitOff U V w N d + quotientBits U N ≤ itemValBitOff U V w N d ∨
      itemValBitOff U V w N d + valBits V ≤ itemQuotBitOff U V w N d := by
    left; simp only [itemValBitOff, itemQuotBitOff]; omega
  refine ⟨hy_wf, hy_sz, ?_, ?_, ?_, ?_⟩
  · unfold denseQuotAt BitMemory.State.getField
    change readField w 0 y.mem (itemQuotBitOff U V w N d) (quotientBits U N) = q
    rw [hy_mem, readField_writeFieldMem_of_disjoint hw _ hvw hqw hqv_disj,
      readField_writeFieldMem_same hw _ hqw hq]
  · unfold denseValAt BitMemory.State.getField
    change readField w 0 y.mem (itemValBitOff U V w N d) (valBits V) = v
    rw [hy_mem, readField_writeFieldMem_same hw _ hvw hv]
  · intro d' hd' hne
    have hdisj_item : itemBitOff U V w N d' + itemBits U V N ≤ itemBitOff U V w N d ∨
        itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N d' := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left
        have : (d' + 1) * itemBits U V N ≤ d * itemBits U V N := Nat.mul_le_mul_right _ hlt
        rw [← itemBitOff_succ]; simp only [itemBitOff]; omega
      · right
        have : (d + 1) * itemBits U V N ≤ d' * itemBits U V N := Nat.mul_le_mul_right _ hgt
        rw [← itemBitOff_succ]; simp only [itemBitOff]; omega
    have hq_disj1 : itemQuotBitOff U V w N d' + quotientBits U N ≤ itemValBitOff U V w N d ∨
        itemValBitOff U V w N d + valBits V ≤ itemQuotBitOff U V w N d' := by
      rcases hdisj_item with h1 | h2
      · left; simp only [itemQuotBitOff, itemValBitOff, itemBits] at h1 ⊢; omega
      · right; simp only [itemQuotBitOff, itemValBitOff, itemBits] at h2 ⊢; omega
    have hq_disj2 : itemQuotBitOff U V w N d' + quotientBits U N ≤ itemQuotBitOff U V w N d ∨
        itemQuotBitOff U V w N d + quotientBits U N ≤ itemQuotBitOff U V w N d' := by
      rcases hdisj_item with h1 | h2
      · left; simp only [itemQuotBitOff, itemBits] at h1 ⊢; omega
      · right; simp only [itemQuotBitOff, itemBits] at h2 ⊢; omega
    have hv_disj1 : itemValBitOff U V w N d' + valBits V ≤ itemValBitOff U V w N d ∨
        itemValBitOff U V w N d + valBits V ≤ itemValBitOff U V w N d' := by
      rcases hdisj_item with h1 | h2
      · left; simp only [itemValBitOff, itemBits] at h1 ⊢; omega
      · right; simp only [itemValBitOff, itemBits] at h2 ⊢; omega
    have hv_disj2 : itemValBitOff U V w N d' + valBits V ≤ itemQuotBitOff U V w N d ∨
        itemQuotBitOff U V w N d + quotientBits U N ≤ itemValBitOff U V w N d' := by
      rcases hdisj_item with h1 | h2
      · left; simp only [itemValBitOff, itemQuotBitOff, itemBits] at h1 ⊢; omega
      · right; simp only [itemValBitOff, itemQuotBitOff, itemBits] at h2 ⊢; omega
    refine ⟨?_, ?_⟩
    · unfold denseQuotAt BitMemory.State.getField
      change readField w 0 y.mem _ _ = readField w 0 x.mem _ _
      rw [hy_mem, readField_writeFieldMem_of_disjoint hw _ hvw hqw hq_disj1,
        readField_writeFieldMem_of_disjoint hw _ hqw hqw hq_disj2]
    · unfold denseValAt BitMemory.State.getField
      change readField w 0 y.mem _ _ = readField w 0 x.mem _ _
      rw [hy_mem, readField_writeFieldMem_of_disjoint hw _ hvw hvw hv_disj1,
        readField_writeFieldMem_of_disjoint hw _ hqw hvw hv_disj2]
  · intro a ha
    have ha_bits : (a + 1) * w ≤ itemBitOff U V w N d := by
      unfold itemBitOff epochMetaBits
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      omega
    rw [hy_mem]
    apply word_eq_of_readBit_eq hw
      (writeFieldMem_fits hw (writeFieldMem_fits hw hx.mem_wf.mem_fits hqw q) hvw v a)
      (hx.mem_wf.mem_fits a)
    intro j hj
    rw [readBit_writeFieldMem hw _ hvw (a * w + j)]
    have hnot1 : ¬(itemValBitOff U V w N d ≤ a * w + j ∧
        a * w + j < itemValBitOff U V w N d + valBits V) := by
      rw [Nat.add_one_mul] at ha_bits
      unfold itemValBitOff
      omega
    rw [ite_eq_right hnot1, readBit_writeFieldMem hw _ hqw (a * w + j)]
    have hnot2 : ¬(itemQuotBitOff U V w N d ≤ a * w + j ∧
        a * w + j < itemQuotBitOff U V w N d + quotientBits U N) := by
      rw [Nat.add_one_mul] at ha_bits
      unfold itemQuotBitOff
      omega
    rw [ite_eq_right hnot2]

end Cslib.DataStructure.Dictionary.BitResizable
