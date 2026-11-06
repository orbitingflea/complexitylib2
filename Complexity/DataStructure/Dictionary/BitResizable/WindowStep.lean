/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.InEpoch
public import Complexity.DataStructure.Dictionary.BitResizable.Query
public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Uniform `BitRAM` Programs for In-Epoch `insert` and `delete`

This module implements uniform `BitRAM.Code .standard 280` programs (`inEpochInsertRegCode` and
`inEpochDeleteRegCode`) for in-epoch insertions and deletions on the single-tape bit-resizable
succinct dictionary, proving that they maintain `FixedCoupled U V w N s_fix y.toBitMemoryState`
in lockstep with `Succinct.insertWithHashProg` and `Succinct.deleteFinishWithHashProg` with
`O(1)` amortized instruction count against `1967 * Succinct.slotPotential` plus `O(probeExcess)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.inEpochInsertRegCode`: uniform `BitRAM` program
  executing an in-epoch insertion (`r270 = u`, `r274 = v_new`).
* `Cslib.DataStructure.Dictionary.BitResizable.inEpochDeleteRegCode`: uniform `BitRAM` program
  executing an in-epoch deletion (`r270 = u`).

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.succinctSpace_le_dictBitSize`: unconditional space
  inequality `Succinct.space U V w N ≤ dictBitSize U V w N N` for `0 < w` and `0 < N`.
* `Cslib.DataStructure.Dictionary.BitResizable.inEpochInsertRegCode_exec`: couples
  `inEpochInsertRegCode` with `Succinct.insertWithHashProg`.
* `Cslib.DataStructure.Dictionary.BitResizable.inEpochDeleteRegCode_exec`: couples
  `inEpochDeleteRegCode` with `Succinct.deleteFinishWithHashProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Space inequality and `FixedCoupled` step helpers -/

private theorem div_ceil_le_self {A w : ℕ} (hw : 0 < w) : (A + w - 1) / w ≤ A := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp [Nat.div_eq_of_lt (by omega : w - 1 < w)]
  · have hle : A + w - 1 ≤ A * w := by
      have : A + w ≤ A * w + 1 := by nlinarith
      omega
    calc (A + w - 1) / w ≤ (A * w) / w := Nat.div_le_div_right hle
      _ = A := Nat.mul_div_cancel _ hw

private theorem packedWords_le_mul_add_two (N k : ℕ) {w : ℕ} (hw : 0 < w) :
    packedWords N k w ≤ N * k + 2 := by
  unfold packedWords
  have := div_ceil_le_self (A := N * k) hw
  omega

/-- For any `0 < w` and `0 < N`, the word footprint `Succinct.space U V w N` of the fixed-capacity
companion is at most `dictBitSize U V w N N`. -/
theorem succinctSpace_le_dictBitSize {U V w N : ℕ} (hw : 0 < w) (hN : 0 < N) :
    Succinct.space U V w N ≤ dictBitSize U V w N N := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hq := packedWords_le_mul_add_two N (quotientBits U N) hw
  have hv := packedWords_le_mul_add_two N (valBits V) hw
  have hmul : N * quotientBits U N + N * valBits V = N * itemBits U V N := by
    unfold itemBits; rw [Nat.mul_add]
  have hmeta_le : epochMetaWords U w N ≤ epochMetaBits U w N :=
    Nat.le_mul_of_pos_right _ hw
  unfold epochMetaWords at hmeta_le
  rw [ite_eq_right hN0] at hmeta_le
  unfold dictBitSize Succinct.space Succinct.totalSpace Succinct.offGM Succinct.offLM
    Succinct.offVal Succinct.offQuot
  omega

theorem dictEnv_of_fits_dictBitSize {U V w N : ℕ}
    (hw : 0 < w) (hN : 0 < N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_sz : Fits w (dictBitSize U V w N N)) :
    Succinct.DictParamsWf U V w N ∧
    Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0 ∧
    Fits w (offHash + Succinct.hashSpace U w N) := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hsp_le : 0 + Succinct.space U V w N ≤ dictBitSize U V w N N := by
    rw [Nat.zero_add]; exact succinctSpace_le_dictBitSize hw hN
  have hhash_le : offHash + Succinct.hashSpace U w N ≤ dictBitSize U V w N N := by
    have hmeta_le : epochMetaWords U w N ≤ epochMetaBits U w N :=
      Nat.le_mul_of_pos_right _ hw
    unfold epochMetaWords at hmeta_le
    rw [ite_eq_right hN0] at hmeta_le
    unfold dictBitSize offHash; omega
  exact ⟨⟨hw, hNU, hU, hV⟩, ⟨rfl, hfit_sz.of_le hsp_le⟩, hfit_sz.of_le hhash_le⟩

theorem bCount_sub_one_reach {N b : ℕ} {gm : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm) (hb : b < numBuckets N)
    (hbc_pos : 1 ≤ Succinct.bCount N gm b) :
    Succinct.bCount N gm b - 1 < effBucketCap N ∨
      gm (Succinct.gmQIdx b) * slabSize N ≤ Succinct.bCount N gm b - 1 := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · left
    have hle : Succinct.bCount N gm b ≤ N := Succinct.bCount_le_n_max hslot b
    have hlt : N < effBucketCap N := lt_effBucketCap_of_bucketBits_eq_zero hb0
    omega
  · right
    have hb_ne : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
    have hbc_eq : Succinct.bCount N gm b =
        gm (Succinct.gmQIdx b) * slabSize N + gm (Succinct.gmRIdx b) := by
      unfold Succinct.bCount; rw [ite_eq_right hb_ne, ite_eq_left hb]
    have hr_pos : 1 ≤ gm (Succinct.gmRIdx b) :=
      Succinct.pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc_pos
    omega

theorem metaAtBit_eq_of_epochMetaWords_eq {U w N : ℕ} (hw : 0 < w) (hN_pos : 0 < N)
    {m₁ m₂ : ℕ → ℕ} (hmeta : ∀ a < epochMetaWords U w N, m₁ a = m₂ a) :
    gmAtBit U w N m₁ = gmAtBit U w N m₂ ∧
    lmAtBit U w N m₁ = lmAtBit U w N m₂ ∧
    tdAtBit U w N m₁ = tdAtBit U w N m₂ ∧
    dtAtBit U w N m₁ = dtAtBit U w N m₂ := by
  refine ⟨funext fun i => ?_, funext fun ⟨c, j⟩ => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · unfold gmAtBit
    split_ifs with hi
    · exact readPacked_congr hw (fun a ha => hmeta a (by
        have hhi := ha.2
        rw [← offDT_add_eq_epochMetaWords hN_pos]
        unfold offDT offTD
        omega)) hi
    · rfl
  · unfold lmAtBit
    split_ifs with hcj
    · exact readPacked_congr hw (fun a ha => hmeta a (by
        have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
          Nat.mul_le_mul_right _ hcj.1
        have hhi := ha.2
        dsimp only at hhi hcj
        rw [← offDT_add_eq_epochMetaWords hN_pos]
        unfold offDT offTD offGM
        unfold offLMSub at hhi
        rw [lmSubWords_eq] at hmul hhi ⊢
        rw [Nat.add_one_mul] at hmul
        omega)) hcj.2
    · rfl
  · unfold tdAtBit
    split_ifs with hi
    · exact readPacked_congr hw (fun a ha => hmeta a
        (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT; omega)) hi
    · rfl
  · unfold dtAtBit
    split_ifs with hi
    · exact readPacked_congr hw (fun a ha => hmeta a
        (by rw [← offDT_add_eq_epochMetaWords hN_pos]; omega)) hi
    · rfl

theorem denseOfPhys_physByBase {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (hwin : WindowInv (maxTailItems N) (gm 0 * slabSize N) (gm 1) td dt)
    {d : ℕ} (hd : d < Succinct.totalSlots N gm) :
    denseOfPhys N gm td (physByBase N (gm 0 * slabSize N) dt d) = d := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · simp [denseOfPhys, physByBase, hb0]
  · have hb_ne : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
    have htot_eq : Succinct.totalSlots N gm = gm 0 * slabSize N + gm 1 := by
      unfold Succinct.totalSlots; rw [ite_eq_right hb_ne]
    have htot_le : gm 0 * slabSize N + gm 1 ≤ N := hslot.multi_total_le hb_pos
    have hnt_le : gm 1 ≤ maxTailItems N := (hslot.multi_tail hb_pos).ntails_le
    by_cases hlt : d < gm 0 * slabSize N
    · simp [denseOfPhys, physByBase, hb_ne, hlt]
    · have hlo : gm 0 * slabSize N ≤ d := Nat.le_of_not_lt hlt
      have hhi : d < gm 0 * slabSize N + gm 1 := by omega
      have hown := hwin.owner_valid d hlo hhi
      have hM_pos : 0 < maxTailItems N := by omega
      have hphys_not_lt : ¬(N - 1 - dt (d % maxTailItems N) < gm 0 * slabSize N) := by
        have := hown.1; omega
      have hsub : N - 1 - (N - 1 - dt (d % maxTailItems N)) = dt (d % maxTailItems N) := by
        have := hown.1; omega
      unfold physByBase denseOfPhys
      simp only [hb_ne, hlt, hphys_not_lt, ↓reduceIte, hsub, hown.2]
      exact denseOfCirc_mod_self hM_pos hlo (by omega)

theorem eq_denseOfPhys_iff_physByBase_eq {N b j : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (hwin : WindowInv (maxTailItems N) (gm 0 * slabSize N) (gm 1) td dt)
    (hb : b < numBuckets N) (hj : j < Succinct.bCount N gm b)
    {d : ℕ} (hd : d < Succinct.totalSlots N gm) :
    d = denseOfPhys N gm td (Succinct.slotOf N gm b j) ↔
      physByBase N (gm 0 * slabSize N) dt d = Succinct.slotOf N gm b j := by
  have htd : TailDenseInv N (gm 0) (gm 1) td dt :=
    (windowInv_iff_tailDenseInv N (gm 0) (gm 1) td dt).mp hwin
  constructor
  · rintro rfl
    exact physOfDense_denseOfPhys hslot htd hb hj
  · intro h
    rw [← h, denseOfPhys_physByBase hslot hwin hd]

/-- Update the value of dense item `r35` (`dense_found`) to `r274` (`v_new`) on an insert hit. -/
@[expose]
def insertHitRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 16 35))
  (.seq (.op (.copy 17 274))
        (writeDenseVRegCode 16 17))

theorem insertHitRegCode_fixedCoupled {U V w N b j_found phys_found v_new : ℕ}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hslot : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hb : b < numBuckets N)
    (hj : j_found < Succinct.bCount N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b)
    (hphys : phys_found = Succinct.slotOf N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b j_found)
    (hv_lt : v_new < 2 ^ valBits V)
    (hr35 : x.regs 35 = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem) phys_found)
    (hr274 : x.regs 274 = v_new)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N) :
    let h_space := Succinct.hashSpace U w N
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.writeValProg U V w N h_space ((0, phys_found), v_new))
    BitRAM.DemonicExecWithin w insertHitRegCode x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        FixedCoupled U V w N s' y.toBitMemoryState ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 57 := by
  intro h_space s'
  set gm := gmAtBit U w N x.toBitMemoryState.mem
  set td := tdAtBit U w N x.toBitMemoryState.mem
  set dt := dtAtBit U w N x.toBitMemoryState.mem
  set n_t := Succinct.totalSlots N gm
  set d_found := denseOfPhys N gm td phys_found
  have hgm_eq : gm = Succinct.gmAt 0 U V w N h_space s_fix.mem := hcpl.gm_eq
  have hslot_gm : Succinct.SlotStoreInv N gm := hgm_eq.symm ▸ hslot
  have hj_gm : j_found < Succinct.bCount N gm b := hgm_eq.symm ▸ hj
  have hphys_gm : phys_found = Succinct.slotOf N gm b j_found := by rw [hphys, ← hgm_eq]
  have hphys_lt : phys_found < N := by
    rw [hphys_gm]; exact (Succinct.slotOf_lt_and_injective hslot_gm).1 b hb j_found hj_gm
  have htd : TailDenseInv N (gm 0) (gm 1) td dt :=
    (windowInv_iff_tailDenseInv N (gm 0) (gm 1) td dt).mp hcpl.win_inv
  have hd_lt : d_found < n_t := by
    dsimp only [d_found]; rw [hphys_gm]
    exact (denseOfPhys_slotOf_lt_and_injective hslot_gm htd).1 b hb j_found hj_gm
  have eff := Succinct.writeValProg_effect (U := U) (V := V) (w := w) (n_max := N)
    (h_space := h_space) (base := 0) hw hphys_lt hv_lt s_fix
  unfold insertHitRegCode
  refine step_dExec_copy (v := d_found) (T := 56) hr35 ?_
  refine step_dExec_copy (v := v_new) (T := 55)
    (by simp +decide [BitRAM.Data.set, hr274]) ?_
  set s1 := (x.set 16 d_found).set 17 v_new
  have hs1_wf : s1.WellFormed w :=
    wf_set 17 (wf_set 16 hx (by
      dsimp only [d_found, gm, td, BitRAM.Data.toBitMemoryState]
      rw [← hr35]; exact hx.regs_fits 35))
      (hr274 ▸ hx.regs_fits 274)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (writeDenseVRegCode_frame (n_t := n_t) (by decide) (by decide) hw hU hV hs1_wf hs1_er
    hd_lt (by simp +decide [s1, BitRAM.Data.set]) (by simp +decide [s1, BitRAM.Data.set])
    hv_lt (by change itemBitOff U V w N n_t ≤ x.bitSize; rw [hsz]; rfl) hm2 hm3).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_v_eq, hy_v_ne, hy_q, hy_meta, hy_regs⟩ => ?_) le_rfl
  obtain ⟨hgm_y, hlm_y, htd_y, hdt_y⟩ :=
    metaAtBit_eq_of_epochMetaWords_eq hw hN_pos (m₂ := x.mem) hy_meta
  have hgm_y' : gmAtBit U w N y.mem = gm := hgm_y
  have htd_y' : tdAtBit U w N y.mem = td := htd_y
  have hdt_y' : dtAtBit U w N y.mem = dt := hdt_y
  have hwin : WindowInv (maxTailItems N) (gm 0 * slabSize N) (gm 1) td dt := hcpl.win_inv
  refine ⟨hy_wf, hy_er, hy_sz, ?_, hy_meta, fun r hr => ?_⟩
  · refine ⟨by dsimp only [BitRAM.Data.toBitMemoryState]
               rw [hgm_y, eff.2.2.2.2.2]; exact hcpl.gm_eq,
      by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hlm_y, eff.2.2.2.2.1]; exact hcpl.lm_eq,
      by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hgm_y', htd_y', hdt_y']; exact hwin,
      fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_y]; exact hcpl.td_lt i,
      fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hdt_y]; exact hcpl.dt_lt i,
      fun d hd => ?_,
      fun d hd => ?_⟩
    · dsimp only [BitRAM.Data.toBitMemoryState] at hd ⊢
      rw [hgm_y'] at hd
      rw [hgm_y', hdt_y', eff.2.2.1]
      exact (hy_q d hd).trans (hcpl.quot_eq d hd)
    · dsimp only [BitRAM.Data.toBitMemoryState] at hd ⊢
      rw [hgm_y'] at hd
      rw [hgm_y', hdt_y', eff.2.2.2.1]
      have hiff := eq_denseOfPhys_iff_physByBase_eq hslot_gm hwin hb hj_gm hd
      rw [← hphys_gm] at hiff
      by_cases heq : d = d_found
      · subst heq
        rw [hiff.mp rfl, Function.update_self]
        exact hy_v_eq
      · rw [Function.update_of_ne (mt hiff.mpr heq)]
        exact (hy_v_ne d hd heq).trans (hcpl.val_eq d hd)
  · rw [hy_regs r (by omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

theorem copyDenseItemRegCode_fixedCoupled {U V w N b j_del phys_del : ℕ}
    {rSrc rDst : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrSrc_ge : 20 ≤ rSrc.val) (hrDst_ge : 20 ≤ rDst.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hslot : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hb : b < numBuckets N)
    (hj_del : j_del < Succinct.bCount N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b)
    (hphys_del : phys_del = Succinct.slotOf N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b j_del)
    (hrSrc : x.regs rSrc = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem)
      (Succinct.slotOf N (gmAtBit U w N x.mem) b
        (Succinct.bCount N (gmAtBit U w N x.mem) b - 1)))
    (hrDst : x.regs rDst = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem) phys_del)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N) :
    let h_space := Succinct.hashSpace U w N
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.copyLastPayloadProg U V w N h_space ((0, b), phys_del))
    BitRAM.DemonicExecWithin w (copyDenseItemRegCode rSrc rDst) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        FixedCoupled U V w N s' y.toBitMemoryState ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 20 ≤ r.val → y.regs r = x.regs r)) 195 := by
  intro h_space s'
  set gm := gmAtBit U w N x.toBitMemoryState.mem
  set td := tdAtBit U w N x.toBitMemoryState.mem
  set dt := dtAtBit U w N x.toBitMemoryState.mem
  set n_t := Succinct.totalSlots N gm
  have hgm_eq : gm = Succinct.gmAt 0 U V w N h_space s_fix.mem := hcpl.gm_eq
  have hslot_gm : Succinct.SlotStoreInv N gm := hgm_eq.symm ▸ hslot
  have hj_del_gm : j_del < Succinct.bCount N gm b := hgm_eq.symm ▸ hj_del
  have hbc_pos : 1 ≤ Succinct.bCount N gm b := by omega
  have hbc_pos_fix : 1 ≤ Succinct.bCount N
      (Succinct.gmAt 0 U V w N h_space s_fix.mem) b := hgm_eq ▸ hbc_pos
  set j_last := Succinct.bCount N gm b - 1
  have hj_last_gm : j_last < Succinct.bCount N gm b := by omega
  set phys_last := Succinct.slotOf N gm b j_last
  have hphys_del_gm : phys_del = Succinct.slotOf N gm b j_del := by rw [hphys_del, ← hgm_eq]
  have hphys_del_lt : phys_del < N := by
    rw [hphys_del_gm]; exact (Succinct.slotOf_lt_and_injective hslot_gm).1 b hb j_del hj_del_gm
  have htd : TailDenseInv N (gm 0) (gm 1) td dt :=
    (windowInv_iff_tailDenseInv N (gm 0) (gm 1) td dt).mp hcpl.win_inv
  set d_del := denseOfPhys N gm td phys_del
  set d_last := denseOfPhys N gm td phys_last
  have hd_del_lt : d_del < n_t := by
    dsimp only [d_del]; rw [hphys_del_gm]
    exact (denseOfPhys_slotOf_lt_and_injective hslot_gm htd).1 b hb j_del hj_del_gm
  have hd_last_lt : d_last < n_t :=
    (denseOfPhys_slotOf_lt_and_injective hslot_gm htd).1 b hb j_last hj_last_gm
  obtain ⟨_, _, hq_c, hv_c, hlm_c, hgm_c⟩ :=
    Succinct.copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := N)
      (h_space := h_space) (base := 0) (b := b) (phys_del := phys_del) (s := s_fix)
      hw hslot hb hbc_pos_fix hphys_del_lt
  refine (copyDenseItemRegCode_exec (n_t := n_t) hrSrc_ge hrDst_ge hw hU hV hx her
    hd_last_lt hd_del_lt hrSrc hrDst
    (by rw [hsz]; rfl) hm2 hm3).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_q_eq, hy_v_eq, hy_other, hy_meta, hy_regs⟩ => ?_) le_rfl
  obtain ⟨hgm_y, hlm_y, htd_y, hdt_y⟩ :=
    metaAtBit_eq_of_epochMetaWords_eq hw hN_pos hy_meta
  have hgm_y' : gmAtBit U w N y.mem = gm := hgm_y
  have htd_y' : tdAtBit U w N y.mem = td := htd_y
  have hdt_y' : dtAtBit U w N y.mem = dt := hdt_y
  have hwin : WindowInv (maxTailItems N) (gm 0 * slabSize N) (gm 1) td dt := hcpl.win_inv
  have hphys_last_eq : physByBase N (gm 0 * slabSize N) dt d_last =
      Succinct.slotOf N (Succinct.gmAt 0 U V w N h_space s_fix.mem) b
        (Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s_fix.mem) b - 1) := by
    rw [← hgm_eq]
    exact (eq_denseOfPhys_iff_physByBase_eq hslot_gm hwin hb hj_last_gm hd_last_lt).mp rfl
  refine ⟨hy_wf, hy_er, hy_sz,
    ⟨by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hgm_y, hgm_c]; exact hcpl.gm_eq,
     by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hlm_y, hlm_c]; exact hcpl.lm_eq,
     by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hgm_y', htd_y', hdt_y']; exact hwin,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_y]; exact hcpl.td_lt i,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hdt_y]; exact hcpl.dt_lt i,
     fun d hd => ?_,
     fun d hd => ?_⟩,
    hy_meta, hy_regs⟩
  · dsimp only [BitRAM.Data.toBitMemoryState] at hd ⊢
    rw [hgm_y'] at hd
    rw [hgm_y', hdt_y', hq_c]
    have hiff := eq_denseOfPhys_iff_physByBase_eq hslot_gm hwin hb hj_del_gm hd
    rw [← hphys_del_gm] at hiff
    by_cases heq : d = d_del
    · subst heq
      rw [hiff.mp rfl, Function.update_self]
      exact hy_q_eq.trans ((hcpl.quot_eq d_last hd_last_lt).trans (by rw [hphys_last_eq]))
    · rw [Function.update_of_ne (mt hiff.mpr heq)]
      exact (hy_other d hd heq).1.trans (hcpl.quot_eq d hd)
  · dsimp only [BitRAM.Data.toBitMemoryState] at hd ⊢
    rw [hgm_y'] at hd
    rw [hgm_y', hdt_y', hv_c]
    have hiff := eq_denseOfPhys_iff_physByBase_eq hslot_gm hwin hb hj_del_gm hd
    rw [← hphys_del_gm] at hiff
    by_cases heq : d = d_del
    · subst heq
      rw [hiff.mp rfl, Function.update_self]
      exact hy_v_eq.trans ((hcpl.val_eq d_last hd_last_lt).trans (by rw [hphys_last_eq]))
    · rw [Function.update_of_ne (mt hiff.mpr heq)]
      exact (hy_other d hd heq).2.trans (hcpl.val_eq d hd)

theorem prependIfIndexedRegCode_fixedCoupled {U V w N b m j_new : ℕ}
    {rB rM rJ : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 23 ≤ rB.val) (hrM_ge : 23 ≤ rM.val) (hrJ_ge : 23 ≤ rJ.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (hj_n : j_new < N)
    (hold : Succinct.lmHead N
      (Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b m ≤ effBucketCap N)
    (hrB : x.regs rB = b) (hrM : x.regs rM = m) (hrJ : x.regs rJ = j_new) :
    let h_space := Succinct.hashSpace U w N
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new))
    BitRAM.DemonicExecWithin w (prependIfIndexedRegCode rB rM rJ) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        FixedCoupled U V w N s' y.toBitMemoryState ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 23 ≤ r.val → y.regs r = x.regs r)) 350 := by
  intro h_space s'
  refine (prependIfIndexedRegCode_exec hrB_ge hrM_ge hrJ_ge hw hN_pos hnU hU hx her hsz
    hb hm hj_n hcpl.lm_eq hold hrB hrM hrJ).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hgm_s', hq_s', hv_s',
      hy_gm, hy_td, hy_dt, hy_low, hy_items, hy_regs⟩ => ?_) le_rfl
  change gmAtBit U w N y.toBitMemoryState.mem = gmAtBit U w N x.toBitMemoryState.mem at hy_gm
  change tdAtBit U w N y.toBitMemoryState.mem = tdAtBit U w N x.toBitMemoryState.mem at hy_td
  change dtAtBit U w N y.toBitMemoryState.mem = dtAtBit U w N x.toBitMemoryState.mem at hy_dt
  exact ⟨hy_wf, hy_er, hy_sz,
    ⟨by rw [hy_gm, hgm_s']; exact hcpl.gm_eq,
     hy_lm,
     by rw [hy_gm, hy_td, hy_dt]; exact hcpl.win_inv,
     fun i => by rw [hy_td]; exact hcpl.td_lt i,
     fun i => by rw [hy_dt]; exact hcpl.dt_lt i,
     fun d hd => by
       rw [hy_gm] at hd
       rw [hy_gm, hy_dt, hq_s', (hy_items d).1]
       exact hcpl.quot_eq d hd,
     fun d hd => by
       rw [hy_gm] at hd
       rw [hy_gm, hy_dt, hv_s', (hy_items d).2]
       exact hcpl.val_eq d hd⟩,
    hy_td, hy_low, hy_regs⟩

theorem unlinkIfIndexedRegCode_fixedCoupled {U V w N b m j_del : ℕ}
    {rB rM rJ : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 23 ≤ rB.val) (hrM_ge : 23 ≤ rM.val) (hrJ_ge : 23 ≤ rJ.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (hj_n : j_del < N)
    (hbounds : j_del < effBucketCap N →
      Succinct.lmPrev N
        (Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b j_del ≤ effBucketCap N ∧
      Succinct.lmNext N
        (Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b j_del ≤ effBucketCap N)
    (hrB : x.regs rB = b) (hrM : x.regs rM = m) (hrJ : x.regs rJ = j_del) :
    let h_space := Succinct.hashSpace U w N
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.unlinkIfIndexedProg U V w N h_space (((0, b), m), j_del))
    BitRAM.DemonicExecWithin w (unlinkIfIndexedRegCode rB rM rJ) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        FixedCoupled U V w N s' y.toBitMemoryState ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 23 ≤ r.val → y.regs r = x.regs r)) 287 := by
  intro h_space s'
  refine (unlinkIfIndexedRegCode_exec hrB_ge hrM_ge hrJ_ge hw hN_pos hnU hU hx her hsz
    hb hm hj_n hcpl.lm_eq hbounds hrB hrM hrJ).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hgm_s', hq_s', hv_s',
      hy_gm, hy_td, hy_dt, hy_low, hy_items, hy_regs⟩ => ?_) le_rfl
  change gmAtBit U w N y.toBitMemoryState.mem = gmAtBit U w N x.toBitMemoryState.mem at hy_gm
  change tdAtBit U w N y.toBitMemoryState.mem = tdAtBit U w N x.toBitMemoryState.mem at hy_td
  change dtAtBit U w N y.toBitMemoryState.mem = dtAtBit U w N x.toBitMemoryState.mem at hy_dt
  exact ⟨hy_wf, hy_er, hy_sz,
    ⟨by rw [hy_gm, hgm_s']; exact hcpl.gm_eq,
     hy_lm,
     by rw [hy_gm, hy_td, hy_dt]; exact hcpl.win_inv,
     fun i => by rw [hy_td]; exact hcpl.td_lt i,
     fun i => by rw [hy_dt]; exact hcpl.dt_lt i,
     fun d hd => by
       rw [hy_gm] at hd
       rw [hy_gm, hy_dt, hq_s', (hy_items d).1]
       exact hcpl.quot_eq d hd,
     fun d hd => by
       rw [hy_gm] at hd
       rw [hy_gm, hy_dt, hv_s', (hy_items d).2]
       exact hcpl.val_eq d hd⟩,
    hy_td, hy_low, hy_regs⟩

theorem virtualQuotAt_slotOf_eq_quotAt {U V w N b j : ℕ}
    {s_fix : Memory.State} {s_bit : BitMemory.State}
    (hcpl : FixedCoupled U V w N s_fix s_bit)
    (hslot : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hb : b < numBuckets N)
    (hj : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b) :
    virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
        (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) := by
  have hslot_gm : Succinct.SlotStoreInv N (gmAtBit U w N s_bit.mem) :=
    hcpl.gm_eq.symm ▸ hslot
  have htd : TailDenseInv N (gmAtBit U w N s_bit.mem 0) (gmAtBit U w N s_bit.mem 1)
      (tdAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem) :=
    (windowInv_iff_tailDenseInv N _ _ _ _).mp hcpl.win_inv
  have hphys_lt : Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j < N :=
    (Succinct.slotOf_lt_and_injective hslot_gm).1 b hb j hj
  have hd_lt : denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)
      (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) <
      Succinct.totalSlots N (gmAtBit U w N s_bit.mem) :=
    (denseOfPhys_slotOf_lt_and_injective hslot_gm htd).1 b hb j hj
  unfold virtualQuotAt
  rw [ite_eq_left hphys_lt, hcpl.quot_eq _ hd_lt]
  exact congrArg (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem)
    (physOfDense_denseOfPhys hslot_gm htd hb hj)

theorem searchBucket_cond_iff {U V w N b q : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ}
    {s_fix : Memory.State} {s_bit : BitMemory.State}
    (hb_inv : Succinct.BucketStateInv U V w N (Succinct.hashSpace U w N) 0 mOf L B s_fix)
    (hcpl : FixedCoupled U V w N s_fix s_bit)
    (hb : b < numBuckets N) (hm_lt : mOf q < numMicroPerBucket N) :
    let gm := gmAtBit U w N s_bit.mem
    let gm_fix := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
    let m := mOf q
    ((∃ j ∈ L b m, virtualQuotAt U V w N s_bit (Succinct.slotOf N gm b j) = q) ∨
      (∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
        virtualQuotAt U V w N s_bit (Succinct.slotOf N gm b j) = q)) ↔
    (∃ j < Succinct.bCount N gm_fix b,
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
        (Succinct.slotOf N gm_fix b j) = q) := by
  intro gm gm_fix m
  have hgm : gmAtBit U w N s_bit.mem = gm_fix := hcpl.gm_eq
  refine Iff.trans ?_ (Succinct.searchBucket_exists_iff hb_inv hb rfl hm_lt)
  constructor
  · rintro (⟨j, hj_in, hq⟩ | ⟨j, hcap, hj_lt, hq⟩)
    · have hj_lt_fix : j < Succinct.bCount N gm_fix b :=
        ((hb_inv.hchain_mem b hb m hm_lt j).mp hj_in).1
      have hj_lt : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b := hgm.symm ▸ hj_lt_fix
      have hq' : Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
          (Succinct.slotOf N gm_fix b j) = q := by
        rw [← hgm, ← virtualQuotAt_slotOf_eq_quotAt hcpl hb_inv.hslot hb hj_lt]
        exact hq
      exact Or.inl ⟨j, hj_in, hq'⟩
    · have hj_lt_fix : j < Succinct.bCount N gm_fix b := hgm ▸ hj_lt
      have hq' : Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
          (Succinct.slotOf N gm_fix b j) = q := by
        rw [← hgm, ← virtualQuotAt_slotOf_eq_quotAt hcpl hb_inv.hslot hb hj_lt]
        exact hq
      exact Or.inr ⟨j, hcap, hj_lt_fix, hq'⟩
  · rintro (⟨j, hj_in, hq⟩ | ⟨j, hcap, hj_lt_fix, hq⟩)
    · have hj_lt_fix : j < Succinct.bCount N gm_fix b :=
        ((hb_inv.hchain_mem b hb m hm_lt j).mp hj_in).1
      have hj_lt : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b := hgm.symm ▸ hj_lt_fix
      have hq' : virtualQuotAt U V w N s_bit (Succinct.slotOf N gm b j) = q := by
        dsimp only [gm]
        rw [virtualQuotAt_slotOf_eq_quotAt hcpl hb_inv.hslot hb hj_lt, hgm, hq]
      exact Or.inl ⟨j, hj_in, hq'⟩
    · have hj_lt : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b := hgm.symm ▸ hj_lt_fix
      have hq' : virtualQuotAt U V w N s_bit (Succinct.slotOf N gm b j) = q := by
        dsimp only [gm]
        rw [virtualQuotAt_slotOf_eq_quotAt hcpl hb_inv.hslot hb hj_lt, hgm, hq]
      exact Or.inr ⟨j, hcap, hj_lt, hq'⟩

/-! ## Section 2: Uniform `BitRAM` program for in-epoch `insert` (`inEpochInsertRegCode`) -/

/-- Insert a new key-value pair `(q, v_new)` into bucket `b` (`r271 = q`, `r272 = b`, `r273 = m`,
`r274 = v_new`): reads `j_new = bCount N gm b` into `r275`, appends `(q, v_new)` via
`pushBackSlotRegCode 272 271 274`, and prepends `j_new` to micro-chain `(b, m)` via
`prependIfIndexedRegCode 272 273 275`. -/
@[expose]
def insertNewRegCode : BitRAM.Code .standard 280 :=
  .seq readBucketCountRegCode
  (.seq (.op (.copy 275 14))
  (.seq (pushBackSlotRegCode 272 271 274)
        (prependIfIndexedRegCode 272 273 275)))

theorem insertNewRegCode_exec {U V w N b q m v_new : ℕ}
    {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {mOf : ℕ → ℕ}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hb_inv : Succinct.BucketStateInv U V w N (Succinct.hashSpace U w N) 0 mOf L B s_fix)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (htot : Succinct.totalSlots N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) < N)
    (hq_lt : q < 2 ^ quotientBits U N) (hv_lt : v_new < 2 ^ valBits V)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hfits : Fits w (dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem) + 1)))
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hr271 : x.regs 271 = q) (hr272 : x.regs 272 = b)
    (hr273 : x.regs 273 = m) (hr274 : x.regs 274 = v_new) :
    let h_space := Succinct.hashSpace U w N
    let gm_fix := Succinct.gmAt 0 U V w N h_space s_fix.mem
    let j_new := Succinct.bCount N gm_fix b
    let s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v_new))
    let s' := (Memory.spec 0).clientState s₁
      (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new))
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w insertNewRegCode x
        (fun y =>
          y.WellFormed w ∧
          EpochRegs U V w N y ∧
          y.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y.mem)) ∧
          FixedCoupled U V w N s' y.toBitMemoryState ∧
          (∀ a < offLM U w N, y.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → r ≠ 275 → y.regs r = x.regs r)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm_fix + 4253 := by
  intro h_space gm_fix j_new s₁ s' gm'
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
    rw [hsz]; exact Nat.le_add_right _ _
  have hslot_gm : Succinct.SlotStoreInv N (gmAtBit U w N x.mem) :=
    hcpl.gm_eq.symm ▸ hb_inv.hslot
  have hj_new_eq : Succinct.bCount N (gmAtBit U w N x.mem) b = j_new :=
    congrArg (fun g => Succinct.bCount N g b) hcpl.gm_eq
  have hj_new_lt_n : j_new < N :=
    lt_of_le_of_lt (Succinct.bCount_le_totalSlots hb_inv.hslot b hb) htot
  have eff_pb := Succinct.pushBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := N)
    (h_space := h_space) (base := 0) (b := b) (q_val := q) (v_val := v_new)
    hw s_fix hb_inv.hslot hb htot hq_lt hv_lt
  have hold_s₁ : Succinct.lmHead N (Succinct.lmAt 0 U V w N h_space s₁.mem) b m ≤
      effBucketCap N := by
    rw [eff_pb.2.2.1]
    exact (hb_inv.hchains.1 b hb m hm).head_le_cap
  set s_mid := x.set 275 j_new
  have hs_mid_wf : s_mid.WellFormed w :=
    wf_set 275 hx (fits_of_le_N hw hnU hU (by omega))
  have hs_mid_er : EpochRegs U V w N s_mid :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s_mid, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  obtain ⟨T_pb0, _, hpot_pb0⟩ :=
    pushBackSlotRegCode_exec (rB := 272) (rQ := 271) (rV := 274) (s_fix := s_fix) (x := s_mid)
      (by decide) (by decide) (by decide) hw hN_pos hnU hU hV hs_mid_wf hs_mid_er hm2 hm3 hcpl
      hb_inv.hslot hb htot hsz hfits hq_lt hv_lt
      (by simp +decide [s_mid, BitRAM.Data.set, hr272])
      (by simp +decide [s_mid, BitRAM.Data.set, hr271])
      (by simp +decide [s_mid, BitRAM.Data.set, hr274])
  have hs_mid_gm : gmAtBit U w N s_mid.mem = gm_fix := hcpl.gm_eq
  rw [hs_mid_gm] at hpot_pb0
  set gm₁ := Succinct.gmAt 0 U V w N h_space s₁.mem
  set T_pb := 1967 * Succinct.slotPotential N gm_fix + 3800 - 1967 * Succinct.slotPotential N gm₁
  have hgm'_eq : gm' = gm₁ := by
    have eff_pr := Succinct.prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
      (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m) (j_new := j_new)
      hw hb hm hj_new_lt_n (hb_inv.hchains.of_lm_eq eff_pb.2.2.1)
      (fun m' hm' hj_in => by
        have hlt := ((hb_inv.hchain_mem b hb m' hm' j_new).mp hj_in).1
        dsimp only [j_new, gm_fix, h_space] at hlt; omega)
    exact eff_pr.2.2.2.2.1
  refine ⟨T_pb + 453, ?_, by rw [hgm'_eq]; dsimp only [T_pb, gm_fix, gm₁] at hpot_pb0 ⊢; omega⟩
  unfold insertNewRegCode
  refine .seq (T₁ := 102) (T₂ := T_pb + 351)
    (readBucketCountRegCode_exec hw hN_pos hnU hU hx her hsz_meta hslot_gm hb hr272)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_14, hy1_regs⟩ => ?_) (by omega)
  have hy1_14_eq : y1.regs 14 = j_new := hy1_14.trans hj_new_eq
  refine step_dExec_copy (v := j_new) (T := T_pb + 350) hy1_14_eq ?_
  set y1' := y1.set 275 j_new
  have hy1'_wf : y1'.WellFormed w :=
    wf_set 275 hy1_wf (hy1_14_eq ▸ hy1_wf.regs_fits 14)
  have hy1'_er : EpochRegs U V w N y1' :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [y1', BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hy1'_st : y1'.toBitMemoryState = x.toBitMemoryState := hy1_st
  have hy1'_mem : y1'.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1'_sz : y1'.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1'_hi : ∀ r : Fin 280, 20 ≤ r.val → r ≠ 275 → y1'.regs r = x.regs r := by
    intro r hr hne
    dsimp only [y1', BitRAM.Data.set]
    rw [Function.update_of_ne hne, hy1_regs r hr]
  obtain ⟨T_pb', hexec_pb', hpot_pb'⟩ :=
    pushBackSlotRegCode_exec (rB := 272) (rQ := 271) (rV := 274) (s_fix := s_fix) (x := y1')
      (by decide) (by decide) (by decide) hw hN_pos hnU hU hV hy1'_wf hy1'_er
      (by rw [hy1'_mem, hm2]) (by rw [hy1'_mem, hm3])
      (by rw [hy1'_st]; exact hcpl) hb_inv.hslot hb htot
      (by rw [hy1'_sz, hy1'_mem, hsz]) (by rw [hy1'_mem]; exact hfits) hq_lt hv_lt
      (by rw [hy1'_hi 272 (by decide) (by decide), hr272])
      (by rw [hy1'_hi 271 (by decide) (by decide), hr271])
      (by rw [hy1'_hi 274 (by decide) (by decide), hr274])
  have hT_le : T_pb' ≤ T_pb := by
    have hgm_x : gmAtBit U w N x.mem = gm_fix := hcpl.gm_eq
    rw [hy1'_mem, hgm_x] at hpot_pb'
    dsimp only [T_pb, gm_fix, gm₁, s₁, h_space] at hpot_pb' ⊢
    omega
  refine .seq (T₁ := T_pb) (T₂ := 350)
    (hexec_pb'.mono (fun z hz => hz) hT_le)
    (fun y2 ⟨hy2_wf, hy2_er, hy2_sz, hy2_cpl, hy2_low, hy2_regs⟩ => ?_) le_rfl
  have hy2_sz_meta : epochMetaBits U w N ≤ y2.bitSize := by
    rw [hy2_sz]; exact Nat.le_add_right _ _
  have hy2_272 : y2.regs 272 = b := by
    rw [hy2_regs 272 (by decide), hy1'_hi 272 (by decide) (by decide), hr272]
  have hy2_273 : y2.regs 273 = m := by
    rw [hy2_regs 273 (by decide), hy1'_hi 273 (by decide) (by decide), hr273]
  have hy2_275 : y2.regs 275 = j_new := by
    rw [hy2_regs 275 (by decide)]
    simp +decide [y1', BitRAM.Data.set]
  refine (prependIfIndexedRegCode_fixedCoupled (rB := 272) (rM := 273) (rJ := 275) (s_fix := s₁)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hy2_wf hy2_er hy2_cpl hy2_sz_meta
    hb hm hj_new_lt_n hold_s₁ hy2_272 hy2_273 hy2_275).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_cpl, _, hy_low, hy_regs⟩ => ?_) le_rfl
  have hy_gm : gmAtBit U w N y.mem = gm' := hy_cpl.gm_eq
  have hy2_gm : gmAtBit U w N y2.mem = gm₁ := hy2_cpl.gm_eq
  refine ⟨hy_wf, hy_er,
    by rw [hy_sz, hy2_sz, hy_gm, hgm'_eq, hy2_gm],
    hy_cpl,
    fun a ha => (hy_low a ha).trans ((hy2_low a ha).trans (congrFun hy1'_mem a)),
    fun r hr hne => (hy_regs r (by omega)).trans
      ((hy2_regs r hr).trans (hy1'_hi r (by omega) hne))⟩


/-- Uniform `BitRAM.Code .standard 280` program executing an in-epoch insertion (`r270 = u.val`,
`r274 = v_new`): splits `u.val` via `feistelSplitRegCode`, searches bucket `b` via
`searchBucketRegCode`, and dispatches to `insertNewRegCode` on a miss (`r32 = 0`) or
`insertHitRegCode` on a hit (`r32 ≠ 0`). -/
@[expose]
def inEpochInsertRegCode : BitRAM.Code .standard 280 :=
  .seq feistelSplitRegCode
  (.seq searchBucketRegCode
  (.seq (.op (.const 36 0))
        (.branch (.eq 32 36)
          insertNewRegCode
          insertHitRegCode)))

open Classical in
theorem inEpochInsertRegCode_exec {U V w N : ℕ}
    (hwf : Succinct.DictParamsWf U V w N)
    (henv : Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0)
    (hN_pos : 0 < N)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    (hdict : Succinct.DictStateInv U V w N 0 θ s_abs s_fix)
    (u : Fin U) (v_new : ℕ)
    (hvalid_op : (Dynamic.spec U V N).valid s_abs (.insert u v_new))
    {x : BitRAM.Data 280}
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hfit_cap : Fits w (dictBitSize U V w N N))
    (hr270 : x.regs 270 = u.val) (hr274 : x.regs 274 = v_new) :
    let h_q := Succinct.hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
    let prog := Succinct.insertWithHashProg U V w N (((0, u.val), v_new), h_q)
    let s' := (Memory.spec 0).clientState s_fix prog
    let h_space := Succinct.hashSpace U w N
    let gm_fix := Succinct.gmAt 0 U V w N h_space s_fix.mem
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w inEpochInsertRegCode x
        (fun y =>
          y.WellFormed w ∧
          EpochRegs U V w N y ∧
          y.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y.mem)) ∧
          FixedCoupled U V w N s' y.toBitMemoryState ∧
          (∀ a < offLM U w N, y.mem a = x.mem a)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm_fix + 147893 +
          350 * probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
            (Dynamic.dom s_abs) u := by
  intro h_q prog s' h_space gm_fix gm'
  rcases hwf with ⟨hw, hnU, hU, hV⟩
  obtain ⟨L, hb_inv⟩ := hdict.hbucket
  set h1 := Succinct.hValOfSeed U N θ
  set q := keyQuotient (bucketBits N) u.val
  set b := feistelBucket (bucketBits N) h1 u.val
  set m := Succinct.mOfSeed U N θ q
  set gm := gmAtBit U w N x.mem
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  have hm_lt : m < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
  have hq_lt : q < 2 ^ quotientBits U N := keyQuotient_lt_two_pow_quotientBits hnU u.isLt
  have hv_lt : v_new < 2 ^ valBits V :=
    lt_of_lt_of_le hvalid_op.2 (Nat.le_pow_clog (by decide) V)
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
    rw [hsz]; exact Nat.le_add_right _ _
  have hadm_meta : epochMetaWords U w N ≤ x.wordSize w :=
    epochMetaWords_le_wordSize_of_bitSize hw hsz_meta
  have hfit_meta : Fits w (epochMetaWords U w N) :=
    hfit_cap.of_le ((Nat.le_mul_of_pos_right _ hw).trans (Nat.le_add_right _ _))
  have hgm_eq : gm = gm_fix := hcpl.gm_eq
  have hlm_eq : lmAtBit U w N x.mem = Succinct.lmAt 0 U V w N h_space s_fix.mem := hcpl.lm_eq
  have hslot_gm : Succinct.SlotStoreInv N gm := hgm_eq.symm ▸ hb_inv.hslot
  have htd_gm : TailDenseInv N (gm 0) (gm 1) (tdAtBit U w N x.mem) (dtAtBit U w N x.mem) :=
    (windowInv_iff_tailDenseInv N (gm 0) (gm 1) _ _).mp hcpl.win_inv
  have hchain_gm : Succinct.IsDLChain N (Succinct.lmHead N (lmAtBit U w N x.mem) b m)
      (Succinct.lmPrev N (lmAtBit U w N x.mem) b)
      (Succinct.lmNext N (lmAtBit U w N x.mem) b) (L b m) := by
    rw [hlm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt_gm : ∀ j ∈ L b m, j < Succinct.bCount N gm b := by
    intro j hj
    rw [hgm_eq]
    exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  have hb_eq : (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1)) = b :=
    Succinct.and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q
  have hq_eq : u.val >>> bucketBits N = q := Nat.shiftRight_eq_div_pow u.val (bucketBits N)
  have hm_eq : h_q >>> bucketBits N = m := rfl
  have hs'_eq : s' = (Memory.spec 0).clientState s_fix
      (Succinct.insertBodyProg U V w N h_space ((((0, b), q), v_new), m)) := by
    refine congrArg ((Memory.spec 0).clientState s_fix) ?_
    change Succinct.insertBodyProg U V w N h_space
      ((((0, (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
        u.val >>> bucketBits N), v_new), h_q >>> bucketBits N) = _
    rw [hb_eq, hq_eq, hm_eq]
  have hsb := Succinct.searchBucketProg_bucket_spec hb_inv henv hb_lt rfl hm_lt (q_target := q)
  dsimp only at hsb
  set res := (Memory.spec 0).clientResult s_fix
    (Succinct.searchBucketProg U V w N h_space (((0, b), q), m))
  have hres := hsb.2.2
  have hrep_bit : BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
      (Succinct.bucketMapOfState U N h1 s_abs) x.toBitMemoryState :=
    bucketRepInv_of_fixedCoupled hb_inv hcpl
  have hprobe := chain_and_overflow_le_probeExcess_rep θ hrep_bit u
  obtain ⟨s_out, hs_out⟩ : ∃ s_out, s_out = s' := ⟨s', rfl⟩
  obtain ⟨gm_out, hgm_out⟩ : ∃ gm_out, gm_out = gm' := ⟨gm', rfl⟩
  obtain ⟨T_search, hT_search⟩ : ∃ T_search,
      T_search = 295 + 350 * (L b m).length + 287 * (Succinct.bCount N gm b - effBucketCap N) :=
    ⟨_, rfl⟩
  obtain ⟨T_ins, hT_ins⟩ : ∃ T_ins,
      T_ins = 1967 * Succinct.slotPotential N gm_fix + 4253 -
        1967 * Succinct.slotPotential N gm_out :=
    ⟨_, rfl⟩
  rw [← hs_out, ← hgm_out]
  refine ⟨142643 + T_search + 1 + (T_ins + 1), ?_, ?_⟩
  · unfold inEpochInsertRegCode
    refine .seq (T₁ := 142643) (T₂ := T_search + 1 + (T_ins + 1))
      (dExec_with_fits
        (feistelSplitRegCode_exec hN_pos hnU hU.le hfit_meta θ u.isLt x her hr270 hadm_meta
          hrep_hash) hx.regs_fits hx.mem_wf.mem_fits)
      (fun y1 ⟨⟨_, hy1_271, hy1_272, hy1_273, hy1_er, hy1_hi, hy1_mem, hy1_sz⟩,
        hy1_rfits, _⟩ => ?_) (by omega)
    have hy1_st : y1.toBitMemoryState = x.toBitMemoryState := by
      ext a
      · exact congrFun hy1_mem a
      · exact hy1_sz
    have hy1_wf : y1.WellFormed w := ⟨hy1_rfits, hy1_st ▸ hx.mem_wf⟩
    refine .seq (T₂ := T_ins + 1 + 1)
      (searchBucketRegCode_exec (b := b) (m := m) (q_target := q) (L := L b m) (x := y1)
        hw hN_pos hnU hU hy1_wf hy1_er
        (by rw [hy1_mem, hm1]) (by rw [hy1_mem, hm2]) (by rw [hy1_mem, hm3])
        (by rw [hy1_mem, hy1_sz, hsz])
        (by rw [hy1_mem]; exact hslot_gm) (by rw [hy1_mem]; exact htd_gm) hb_lt hm_lt
        (by rw [hy1_mem]; exact hchain_gm) (by rw [hy1_mem]; exact hc_lt_gm)
        hy1_271 hy1_272 hy1_273)
      (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_)
      (by rw [hy1_mem, hT_search]; dsimp only [gm]; omega)
    have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
    have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
    have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
    rw [hy1_st, hy1_mem] at hy2_res
    refine DemonicExecWithin.step_const (T := T_ins + 1) (fits_zero w) ?_
    set s2 := y2.set 36 0
    have hs2_wf : s2.WellFormed w := wf_set 36 hy2_wf (fits_zero w)
    have hs2_er : EpochRegs U V w N s2 :=
      hy2_er.congr_regs (fun r hr1 _ => by
        dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs2_271 : s2.regs 271 = q := by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by decide), hy2_hi 271 (by decide), hy1_271]
    have hs2_272 : s2.regs 272 = b := by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by decide), hy2_hi 272 (by decide), hy1_272]
    have hs2_273 : s2.regs 273 = m := by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by decide), hy2_hi 273 (by decide), hy1_273]
    have hs2_274 : s2.regs 274 = v_new := by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by decide), hy2_hi 274 (by decide), hy1_hi 274 (by decide), hr274]
    have hiff_cond :
        ((∃ j ∈ L b m,
            virtualQuotAt U V w N x.toBitMemoryState
              (Succinct.slotOf N (gmAtBit U w N x.mem) b j) = q) ∨
          ∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N (gmAtBit U w N x.mem) b ∧
            virtualQuotAt U V w N x.toBitMemoryState
              (Succinct.slotOf N (gmAtBit U w N x.mem) b j) = q) ↔
        ∃ j < Succinct.bCount N gm_fix b,
          Succinct.quotAt 0 U w N h_space s_fix.mem (Succinct.slotOf N gm_fix b j) = q :=
      searchBucket_cond_iff hb_inv hcpl hb_lt hm_lt (q := q)
    by_cases hex : ∃ j < Succinct.bCount N gm_fix b,
        Succinct.quotAt 0 U w N h_space s_fix.mem (Succinct.slotOf N gm_fix b j) = q
    · rw [ite_eq_left hex] at hres
      rw [ite_eq_left (hiff_cond.mpr hex)] at hy2_res
      rcases hres with ⟨hf1, hj_lt, hq_res, hphys_eq⟩
      obtain ⟨hy2_32, hy2_33_lt, _, hy2_q, hy2_34, hy2_35⟩ := hy2_res
      have hcond : ¬BitRAM.CondHolds (.eq 32 36) s2 := by
        change s2.regs 32 ≠ s2.regs 36
        simp +decide [s2, BitRAM.Data.set, hy2_32]
      have hj_eq : y2.regs 33 = res.1.2 := by
        have hgm_x : gmAtBit U w N x.mem =
            Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
        have hq33 : Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
            (Succinct.slotOf N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b
              (y2.regs 33)) = q := by
          rw [← hgm_x]
          exact (virtualQuotAt_slotOf_eq_quotAt hcpl hb_inv.hslot hb_lt hy2_33_lt).symm.trans hy2_q
        exact hb_inv.hnodup_q b hb_lt (y2.regs 33) (by rw [← hgm_x]; exact hy2_33_lt) res.1.2 hj_lt
          (hq33.trans hq_res.symm)
      have hs'_wv : s_out = (Memory.spec 0).clientState s_fix
          (Succinct.writeValProg U V w N h_space ((0, res.2), v_new)) := by
        rw [hs_out, hs'_eq]; unfold Succinct.insertBodyProg; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hsb.1]
        change (Memory.spec 0).clientState s_fix
          (if res.1.1 = 1 then Succinct.writeValProg U V w N h_space ((0, res.2), v_new)
           else Succinct.insertNewProg U V w N h_space ((((0, b), q), v_new), m)) = _
        rw [ite_eq_left hf1]
      have hphys_lt : res.2 < N := by
        rw [hphys_eq]; exact (Succinct.slotOf_lt_and_injective hb_inv.hslot).1 b hb_lt res.1.2 hj_lt
      have eff_wv := Succinct.writeValProg_effect (U := U) (V := V) (w := w) (n_max := N)
        (h_space := h_space) (base := 0) hw hphys_lt hv_lt s_fix
      have hgm'_eq : gm_out = gm_fix := by
        rw [hgm_out]; dsimp only [gm', gm_fix]; rw [← hs_out, hs'_wv, eff_wv.2.2.2.2.2]
      have h59_le : 57 + 2 ≤ T_ins + 1 := by rw [hT_ins, hgm'_eq]; omega
      have hs2_35 : s2.regs 35 =
          denseOfPhys N (gmAtBit U w N s2.mem) (tdAtBit U w N s2.mem) res.2 := by
        dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by decide), hy2_mem, hy2_35, hj_eq, hphys_eq]
        have hgm_x : gmAtBit U w N x.mem =
            Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
        rw [hgm_x]
      refine .branch_neg (T₀ := 57) hcond ?_ h59_le
      refine (insertHitRegCode_fixedCoupled hw hN_pos hU.le hV hs2_wf hs2_er
        (by change FixedCoupled U V w N s_fix y2.toBitMemoryState; rw [hy2_st_x]; exact hcpl)
        hb_inv.hslot hb_lt hj_lt hphys_eq hv_lt hs2_35 hs2_274
        (by change y2.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y2.mem))
            rw [hy2_sz, hy2_mem, hsz])
        (by change y2.mem 2 = _; rw [hy2_mem, hm2])
        (by change y2.mem 3 = _; rw [hy2_mem, hm3])).mono
        (fun y ⟨hy_wf, hy_er, hy_sz, hy_cpl, hy_meta, _⟩ => ?_) le_rfl
      have hy_gm : gmAtBit U w N y.mem =
          Succinct.gmAt 0 U V w N h_space
            ((Memory.spec 0).clientState s_fix
              (Succinct.writeValProg U V w N h_space ((0, res.2), v_new))).mem := hy_cpl.gm_eq
      exact ⟨hy_wf, hy_er,
        by rw [hy_sz]; change y2.bitSize = _
           rw [hy2_sz, hsz, hy_gm, eff_wv.2.2.2.2.2, hgm_eq],
        by rw [hs'_wv]; exact hy_cpl,
        fun a ha => (hy_meta a (by rw [← offDT_add_eq_epochMetaWords hN_pos]
                                   unfold offDT offTD offGM; omega)).trans (congrFun hy2_mem a)⟩
    · rw [ite_eq_right hex] at hres
      rw [ite_eq_right (mt hiff_cond.mp hex)] at hy2_res
      have hcond : BitRAM.CondHolds (.eq 32 36) s2 := by
        change s2.regs 32 = s2.regs 36
        simp +decide [s2, BitRAM.Data.set, hy2_res]
      have hB_eq : Succinct.bucketMapOfState U N h1 s_abs b q = s_abs u :=
        Succinct.bucketMapOfState_feistelBucket hnU h1 s_abs u
      have hnot_some : ¬(s_abs u).isSome := by
        rw [← hB_eq]; exact mt (hb_inv.hmap_dom b hb_lt q).mp hex
      have htot : Succinct.totalSlots N gm_fix < N := by
        rw [hdict.htot]; exact hvalid_op.1.symm.resolve_left hnot_some
      have htot_gm : Succinct.totalSlots N gm < N := hgm_eq.symm ▸ htot
      have hfits_next : Fits w (dictBitSize U V w N (Succinct.totalSlots N gm + 1)) :=
        hfit_cap.of_le (by
          unfold dictBitSize
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
      have hne1 : res.1.1 ≠ 1 := by omega
      let s₁ := (Memory.spec 0).clientState s_fix
        (Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v_new))
      let j_new := Succinct.bCount N gm_fix b
      have hs'_pr : s_out = (Memory.spec 0).clientState s₁
          (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new)) := by
        rw [hs_out, hs'_eq]; unfold Succinct.insertBodyProg Succinct.insertNewProg
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hsb.1]
        change (Memory.spec 0).clientState s_fix
          (if res.1.1 = 1 then Succinct.writeValProg U V w N h_space ((0, res.2), v_new)
           else do
             let tot ← Succinct.readTotalSlotsProg U V w N h_space 0
             if tot < N then do
               let j_new ← Succinct.readBucketCountProg U V w N h_space (0, b)
               Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v_new)
               Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new)
             else pure ()) = _
        rw [ite_eq_right hne1, StateTransitionSpec.clientState_bind,
          Succinct.clientState_readTotalSlotsProg, Succinct.clientResult_readTotalSlotsProg,
          ite_eq_left htot, StateTransitionSpec.clientState_bind,
          Succinct.clientState_readBucketCountProg,
          Succinct.clientResult_readBucketCountProg (0, b) s_fix hb_lt,
          StateTransitionSpec.clientState_bind]
      obtain ⟨T_new, hexec_new, hpot_new⟩ :=
        insertNewRegCode_exec hw hN_pos hnU hU hV hs2_wf hs2_er
          (by change FixedCoupled U V w N s_fix y2.toBitMemoryState; rw [hy2_st_x]; exact hcpl)
          hb_inv hb_lt hm_lt htot hq_lt hv_lt
          (by change y2.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y2.mem))
              rw [hy2_sz, hy2_mem, hsz])
          (by change Fits w (dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y2.mem) + 1))
              rw [hy2_mem]; exact hfits_next)
          (by change y2.mem 2 = _; rw [hy2_mem, hm2])
          (by change y2.mem 3 = _; rw [hy2_mem, hm3])
          hs2_271 hs2_272 hs2_273 hs2_274
      have hgm_out_pr : gm_out = Succinct.gmAt 0 U V w N h_space
          ((Memory.spec 0).clientState s₁
            (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new))).mem := by
        rw [hgm_out]; dsimp only [gm']; rw [← hs_out, hs'_pr]
      have hT_new_le : T_new ≤ T_ins := by
        rw [hT_ins, hgm_out_pr]
        dsimp only [gm_fix, s₁, j_new, h_space] at hpot_new ⊢
        omega
      refine .branch_pos (T₀ := T_ins) hcond ?_ (by omega)
      refine hexec_new.mono (fun y ⟨hy_wf, hy_er, hy_sz, hy_cpl, hy_low, _⟩ => ?_) hT_new_le
      exact ⟨hy_wf, hy_er, hy_sz, by rw [hs'_pr]; exact hy_cpl,
        fun a ha => (hy_low a ha).trans (congrFun hy2_mem a)⟩
  · have hpot_bound : 1967 * Succinct.slotPotential N gm_out ≤
        1967 * Succinct.slotPotential N gm_fix + 4253 := by
      by_cases hex : ∃ j < Succinct.bCount N gm_fix b,
          Succinct.quotAt 0 U w N h_space s_fix.mem (Succinct.slotOf N gm_fix b j) = q
      · rw [ite_eq_left hex] at hres
        rcases hres with ⟨hf1, hj_lt, _, hphys_eq⟩
        have hs'_wv : s_out = (Memory.spec 0).clientState s_fix
            (Succinct.writeValProg U V w N h_space ((0, res.2), v_new)) := by
          rw [hs_out, hs'_eq]; unfold Succinct.insertBodyProg; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, hsb.1]
          change (Memory.spec 0).clientState s_fix
            (if res.1.1 = 1 then Succinct.writeValProg U V w N h_space ((0, res.2), v_new)
             else Succinct.insertNewProg U V w N h_space ((((0, b), q), v_new), m)) = _
          rw [ite_eq_left hf1]
        have hphys_lt : res.2 < N := by
          rw [hphys_eq]
          exact (Succinct.slotOf_lt_and_injective hb_inv.hslot).1 b hb_lt res.1.2 hj_lt
        have eff_wv := Succinct.writeValProg_effect (U := U) (V := V) (w := w) (n_max := N)
          (h_space := h_space) (base := 0) hw hphys_lt hv_lt s_fix
        have hgm'_eq : gm_out = gm_fix := by
          rw [hgm_out]; dsimp only [gm', gm_fix]; rw [← hs_out, hs'_wv, eff_wv.2.2.2.2.2]
        rw [hgm'_eq]; omega
      · rw [ite_eq_right hex] at hres
        have hB_eq : Succinct.bucketMapOfState U N h1 s_abs b q = s_abs u :=
          Succinct.bucketMapOfState_feistelBucket hnU h1 s_abs u
        have hnot_some : ¬(s_abs u).isSome := by
          rw [← hB_eq]; exact mt (hb_inv.hmap_dom b hb_lt q).mp hex
        have htot : Succinct.totalSlots N gm_fix < N := by
          rw [hdict.htot]; exact hvalid_op.1.symm.resolve_left hnot_some
        have hne1 : res.1.1 ≠ 1 := by omega
        let s₁ := (Memory.spec 0).clientState s_fix
          (Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v_new))
        let j_new := Succinct.bCount N gm_fix b
        have hs'_pr : s_out = (Memory.spec 0).clientState s₁
            (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new)) := by
          rw [hs_out, hs'_eq]; unfold Succinct.insertBodyProg Succinct.insertNewProg
          simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, hsb.1]
          change (Memory.spec 0).clientState s_fix
            (if res.1.1 = 1 then Succinct.writeValProg U V w N h_space ((0, res.2), v_new)
             else do
               let tot ← Succinct.readTotalSlotsProg U V w N h_space 0
               if tot < N then do
                 let j_new ← Succinct.readBucketCountProg U V w N h_space (0, b)
                 Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v_new)
                 Succinct.prependIfIndexedProg U V w N h_space (((0, b), m), j_new)
               else pure ()) = _
          rw [ite_eq_right hne1, StateTransitionSpec.clientState_bind,
            Succinct.clientState_readTotalSlotsProg, Succinct.clientResult_readTotalSlotsProg,
            ite_eq_left htot, StateTransitionSpec.clientState_bind,
            Succinct.clientState_readBucketCountProg,
            Succinct.clientResult_readBucketCountProg (0, b) s_fix hb_lt,
            StateTransitionSpec.clientState_bind]
        have eff_pb := Succinct.pushBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := N)
          (h_space := h_space) (base := 0) (b := b) (q_val := q) (v_val := v_new)
          hw s_fix hb_inv.hslot hb_lt htot hq_lt hv_lt
        have hj_new_lt_n : j_new < N :=
          lt_of_le_of_lt (Succinct.bCount_le_totalSlots hb_inv.hslot b hb_lt) htot
        have eff_pr := Succinct.prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
          (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m) (j_new := j_new)
          hw hb_lt hm_lt hj_new_lt_n (hb_inv.hchains.of_lm_eq eff_pb.2.2.1)
          (fun m' hm' hj_in => by
            have hlt := ((hb_inv.hchain_mem b hb_lt m' hm' j_new).mp hj_in).1
            dsimp only [j_new, gm_fix, h_space] at hlt; omega)
        have hgm'_s1 : gm_out = Succinct.gmAt 0 U V w N h_space s₁.mem := by
          rw [hgm_out]; dsimp only [gm']; rw [← hs_out, hs'_pr, eff_pr.2.2.2.2.1]
        have hpot_s1 : Succinct.slotPotential N (Succinct.gmAt 0 U V w N h_space s₁.mem) ≤
            Succinct.slotPotential N gm_fix + 2 := by
          have hpb_pot := eff_pb.2.2.2.2.2.2.2.2.2.2
          dsimp only [s₁, gm_fix] at hpb_pot ⊢
          omega
        rw [hgm'_s1]; omega
    have hsum := hprobe.2.2.1
    rw [hT_search, hT_ins]
    dsimp only [BitRAM.Data.toBitMemoryState, b, q, m, h1, gm] at hsum hpot_bound ⊢
    omega

end Cslib.DataStructure.Dictionary.BitResizable
