/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.WindowStep
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Uniform `BitRAM` Program for In-Epoch `delete`

This module implements the uniform `BitRAM.Code .standard 280` program `inEpochDeleteRegCode` for
in-epoch deletions on the single-tape bit-resizable succinct dictionary, proving that it maintains
`FixedCoupled U V w N s_fix y.toBitMemoryState` in lockstep with
`Succinct.deleteFinishWithHashProg` with `O(1)` amortized instruction count against
`1967 * Succinct.slotPotential` plus `O(probeExcess)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.deletePrepLastRegCode`: read-only preparation for a
  found deletion (`143019` instructions).
* `Cslib.DataStructure.Dictionary.BitResizable.deleteExecFinishRegCode`: mutating execution for a
  found deletion.
* `Cslib.DataStructure.Dictionary.BitResizable.inEpochDeleteRegCode`: uniform `BitRAM` program
  executing an in-epoch deletion (`r270 = u.val`).

## Main results

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

/-! ## Section 1: Read-only preparation for a found deletion (`deletePrepLastRegCode`) -/

/-- Read-only preparation for a found deletion (`r272 = b`, `r273 = m`, `r33 = j_del`,
`r35 = dense_del`): saves `j_del` to `r275` and `dense_del` to `r276`, resolves
`j_last = bCount N gm b - 1` into `r277` and `dense_last` into `r278`, reads `q_last`, and
evaluates `m_last = Succinct.mOfSeed U N θ q_last` into `r279` in `143019` instructions. -/
@[expose]
def deletePrepLastRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 275 33))
  (.seq (.op (.copy 276 35))
  (.seq readBucketCountRegCode
  (.seq (.op (.const 15 1))
  (.seq (.op (.bin .sub 30 14 15))
  (.seq (.op (.copy 277 30))
  (.seq resolveIndexedSlotRegCode
  (.seq (.op (.copy 278 15))
  (.seq (.op (.copy 16 15))
  (.seq (readDenseQRegCode 16 1)
  (.seq evalHashRegCode
        (.op (.bin .shiftRight 279 2 245))))))))))))

theorem deletePrepLastRegCode_exec {U V w N b m j_del d_del : ℕ}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hfit_meta : Fits w (epochMetaWords U w N))
    (θ : Succinct.QuotHashSeed U N)
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hslot : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hb : b < numBuckets N) (hbc_pos : 1 ≤ Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr272 : x.regs 272 = b) (hr273 : x.regs 273 = m)
    (hr33 : x.regs 33 = j_del) (hr35 : x.regs 35 = d_del) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    let j_last := Succinct.bCount N gm b - 1
    let phys_last := Succinct.slotOf N gm b j_last
    let d_last := denseOfPhys N gm td phys_last
    let q_last := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem phys_last
    let m_last := Succinct.mOfSeed U N θ q_last
    BitRAM.DemonicExecWithin w deletePrepLastRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 272 = b ∧
        y.regs 273 = m ∧
        y.regs 275 = j_del ∧
        y.regs 276 = d_del ∧
        y.regs 277 = j_last ∧
        y.regs 278 = d_last ∧
        y.regs 279 = m_last) 143019 := by
  intro gm td j_last phys_last d_last q_last m_last
  have hgm_eq : gm = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
  have hslot_gm : Succinct.SlotStoreInv N gm := hgm_eq.symm ▸ hslot
  have htd_gm : TailDenseInv N (gm 0) (gm 1) td (dtAtBit U w N x.mem) :=
    (windowInv_iff_tailDenseInv N (gm 0) (gm 1) td _).mp hcpl.win_inv
  have hj_last_lt : j_last < Succinct.bCount N gm b := by dsimp only [j_last, gm]; omega
  have hj_last_reach : j_last < effBucketCap N ∨ gm (Succinct.gmQIdx b) * slabSize N ≤ j_last :=
    bCount_sub_one_reach hslot_gm hb hbc_pos
  have hd_last_lt : d_last < Succinct.totalSlots N gm :=
    (denseOfPhys_slotOf_lt_and_injective hslot_gm htd_gm).1 b hb j_last hj_last_lt
  have hq_last_eq : denseQuotAt U V w N x.toBitMemoryState d_last = q_last := by
    rw [hcpl.quot_eq d_last hd_last_lt]
    exact congrArg (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem)
      (physOfDense_denseOfPhys hslot_gm htd_gm hb hj_last_lt)
  have hq_last_lt : q_last < 2 ^ quotientBits U N :=
    Succinct.quotAt_lt 0 U w N (Succinct.hashSpace U w N) s_fix.mem phys_last
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
    rw [hsz]; exact Nat.le_add_right _ _
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_jlast : Fits w j_last :=
    fits_of_le_N hw hnU hU (by
      have := Succinct.bCount_le_n_max hslot_gm b; omega)
  unfold deletePrepLastRegCode
  refine step_dExec_copy (v := j_del) (T := 143018) hr33 ?_
  refine step_dExec_copy (v := d_del) (T := 143017)
    (by simp +decide [BitRAM.Data.set, hr35]) ?_
  set s1 := (x.set 275 j_del).set 276 d_del
  have hs1_mem : s1.mem = x.mem := rfl
  have hs1_wf : s1.WellFormed w :=
    wf_set 276 (wf_set 275 hx (hr33 ▸ hx.regs_fits 33)) (hr35 ▸ hx.regs_fits 35)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 102) (T₂ := 142915)
    (readBucketCountRegCode_exec hw hN_pos hnU hU hs1_wf hs1_er hsz_meta hslot_gm hb
      (by simp +decide [s1, BitRAM.Data.set, hr272]))
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_14, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  rw [hs1_mem] at hy1_14
  refine DemonicExecWithin.step_const (T := 142914) hfit_1 ?_
  refine step_dExec_bin (v := j_last) (T := 142913)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy1_14, j_last, gm]) hfit_jlast ?_
  refine step_dExec_copy (v := j_last) (T := 142912)
    (by simp +decide [BitRAM.Data.set]) ?_
  set s2 := ((y1.set 15 1).set 30 j_last).set 277 j_last
  have hs2_mem : s2.mem = x.mem := hy1_mem
  have hs2_sz : s2.bitSize = x.bitSize := hy1_sz
  have hs2_wf : s2.WellFormed w :=
    wf_set 277 (wf_set 30 (wf_set 15 hy1_wf hfit_1) hfit_jlast) hfit_jlast
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_272 : s2.regs 272 = b := by
    simp +decide [s2, BitRAM.Data.set, hy1_regs 272 (by decide), s1, hr272]
  have hs2_30 : s2.regs 30 = j_last := by simp +decide [s2, BitRAM.Data.set]
  refine .seq (T₁ := 230) (T₂ := 142682)
    (resolveIndexedSlotRegCode_exec hw hN_pos hnU hU hs2_wf hs2_er
      (by rw [hs2_mem, hm1])
      (by rw [hs2_sz]; exact hsz_meta)
      (by rw [hs2_mem]; exact hslot_gm)
      (by rw [hs2_mem]; exact htd_gm)
      hb (by rw [hs2_mem]; exact hj_last_lt) (by rw [hs2_mem]; exact hj_last_reach)
      hs2_272 hs2_30)
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, _, hy2_15, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  have hy2_15_eq : y2.regs 15 = d_last := by
    rw [hy2_15, hs2_mem]
  refine step_dExec_copy (v := d_last) (T := 142681) hy2_15_eq ?_
  refine step_dExec_copy (v := d_last) (T := 142680)
    (by simp +decide [BitRAM.Data.set, hy2_15_eq]) ?_
  set s3 := (y2.set 278 d_last).set 16 d_last
  have hs3_wf : s3.WellFormed w :=
    wf_set 16 (wf_set 278 hy2_wf (hy2_15_eq ▸ hy2_wf.regs_fits 15))
      (hy2_15_eq ▸ hy2_wf.regs_fits 15)
  have hs3_er : EpochRegs U V w N s3 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 42) (T₂ := 142638)
    (readDenseQRegCode_exec (d := d_last) (rD := 16) (rDst := 1) (by decide) hw hU.le hs3_wf hs3_er
      hd_last_lt (by simp +decide [s3, BitRAM.Data.set])
      (by change itemBitOff U V w N (Succinct.totalSlots N gm) ≤ y2.bitSize
          rw [hy2_sz, hsz]; rfl)
      (by change y2.mem 2 = _; rw [hy2_mem, hm2])
      (by change y2.mem 3 = _; rw [hy2_mem, hm3]))
    (fun y3 ⟨hy3_st, hy3_wf, hy3_1, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
  have hy3_er : EpochRegs U V w N y3 :=
    hs3_er.congr_regs (fun r hr1 _ =>
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy3_1_eq : y3.regs 1 = q_last := by
    rw [hy3_1]
    change denseQuotAt U V w N y2.toBitMemoryState d_last = q_last
    rw [hy2_st_x, hq_last_eq]
  have hy3_adm : epochMetaWords U w N ≤ y3.wordSize w :=
    epochMetaWords_le_wordSize_of_bitSize hw (by rw [hy3_sz]; exact hsz_meta)
  refine .seq (T₁ := 142637) (T₂ := 1)
    (dExec_with_fits
      (evalHashRegCode_exec hN_pos hnU hU.le hfit_meta θ hq_last_lt y3 hy3_er hy3_1_eq hy3_adm
        (by rw [hy3_mem]; exact hrep_hash))
      hy3_wf.regs_fits hy3_wf.mem_wf.mem_fits)
    (fun y4 ⟨⟨hy4_2, hy4_er, hy4_hi, hy4_mem, hy4_sz⟩, hy4_rfits, _⟩ => ?_) le_rfl
  have hy4_st_x : y4.toBitMemoryState = x.toBitMemoryState := by
    ext a
    · exact (congrFun hy4_mem a).trans (congrFun hy3_mem a)
    · exact hy4_sz.trans hy3_sz
  have hy4_wf : y4.WellFormed w := ⟨hy4_rfits, hy4_st_x ▸ hx.mem_wf⟩
  have hy4_245 : y4.regs 245 = bucketBits N := (hy4_er.active hN_pos).1
  have hhVal_lt : Fits w (Succinct.hValOfSeed U N θ q_last) := hy4_2 ▸ hy4_rfits 2
  have hfit_mlast : Fits w m_last := hhVal_lt.of_le (Nat.shiftRight_le _ _)
  refine dExec_bin (v := m_last)
    (by
      simp only [BinOp.eval, hy4_2, hy4_245]
      rfl)
    hfit_mlast ?_
  have hhi_y3 : ∀ r : Fin 280, 240 ≤ r.val → y4.regs r = s3.regs r :=
    fun r hr => (hy4_hi r hr).trans
      (hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  refine ⟨hy4_st_x, wf_set 279 hy4_wf hfit_mlast,
    hy4_er.congr_regs (fun r _ hr2 => by
      dsimp only [BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
    by simp +decide [BitRAM.Data.set, hhi_y3 272 (by decide), s3,
         hy2_regs 272 (by decide), hs2_272],
    by simp +decide [BitRAM.Data.set, hhi_y3 273 (by decide), s3, hy2_regs 273 (by decide), s2,
         hy1_regs 273 (by decide), s1, hr273],
    by simp +decide [BitRAM.Data.set, hhi_y3 275 (by decide), s3, hy2_regs 275 (by decide), s2,
         hy1_regs 275 (by decide), s1],
    by simp +decide [BitRAM.Data.set, hhi_y3 276 (by decide), s3, hy2_regs 276 (by decide), s2,
         hy1_regs 276 (by decide), s1],
    by simp +decide [BitRAM.Data.set, hhi_y3 277 (by decide), s3, hy2_regs 277 (by decide), s2],
    by simp +decide [BitRAM.Data.set, hhi_y3 278 (by decide), s3],
    by simp +decide [BitRAM.Data.set]⟩

/-! ## Section 2: Mutating execution for a found deletion (`deleteExecFinishRegCode`) -/

/-- Mutating execution for a found deletion (`r272 = b`, `r273 = m`, `r275 = j_del`,
`r276 = dense_del`, `r277 = j_last`, `r278 = dense_last`, `r279 = m_last`): unlinks `j_del`,
conditionally swaps the last bucket item into `j_del` when `j_del < j_last`, and pops the last
bucket slot via `popBackSlotRegCode 272`. -/
@[expose]
def deleteExecFinishRegCode : BitRAM.Code .standard 280 :=
  .seq (unlinkIfIndexedRegCode 272 273 275)
  (.branch (.lt 275 277)
    (.seq (unlinkIfIndexedRegCode 272 279 277)
    (.seq (copyDenseItemRegCode 278 276)
    (.seq (prependIfIndexedRegCode 272 279 275)
          (popBackSlotRegCode 272))))
    (popBackSlotRegCode 272))

theorem deleteExecFinishRegCode_exec {U V w N b m j_del phys_del m_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {mOf : ℕ → ℕ}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hb_inv : Succinct.BucketStateInv U V w N (Succinct.hashSpace U w N) 0 mOf L B s_fix)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (hm_last : m_last < numMicroPerBucket N)
    (hj_del : j_del < Succinct.bCount N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b)
    (hphys_del : phys_del = Succinct.slotOf N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b j_del)
    (hmem_del : j_del < effBucketCap N → j_del ∈ L b m)
    (hmem_last : Succinct.bCount N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b - 1 < effBucketCap N →
      Succinct.bCount N
        (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b - 1 ∈ L b m_last)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hr272 : x.regs 272 = b) (hr273 : x.regs 273 = m)
    (hr275 : x.regs 275 = j_del)
    (hr276 : x.regs 276 = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem) phys_del)
    (hr277 : x.regs 277 = Succinct.bCount N (gmAtBit U w N x.mem) b - 1)
    (hr278 : x.regs 278 = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem)
      (Succinct.slotOf N (gmAtBit U w N x.mem) b
        (Succinct.bCount N (gmAtBit U w N x.mem) b - 1)))
    (hr279 : x.regs 279 = m_last) :
    let h_space := Succinct.hashSpace U w N
    let gm_fix := Succinct.gmAt 0 U V w N h_space s_fix.mem
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.deleteFoundProg U V w N h_space ((((0, b), j_del), phys_del), (m, m_last)))
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w deleteExecFinishRegCode x
        (fun y =>
          y.WellFormed w ∧
          EpochRegs U V w N y ∧
          y.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y.mem)) ∧
          FixedCoupled U V w N s' y.toBitMemoryState ∧
          (∀ a < offLM U w N, y.mem a = x.mem a)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm_fix + 5923 := by
  intro h_space gm_fix s' gm'
  set j_last := Succinct.bCount N gm_fix b - 1
  have hgm_x : gmAtBit U w N x.mem = gm_fix := hcpl.gm_eq
  have hj_last_eq : Succinct.bCount N (gmAtBit U w N x.mem) b - 1 = j_last := by
    rw [hgm_x]
  have hr277_eq : x.regs 277 = j_last := hr277.trans hj_last_eq
  have hj_del_fix : j_del < Succinct.bCount N gm_fix b := hj_del
  have hbc_pos : 1 ≤ Succinct.bCount N gm_fix b := by omega
  have hj_last_lt : j_last < Succinct.bCount N gm_fix b := by omega
  have hj_del_n : j_del < N := lt_of_lt_of_le hj_del (Succinct.bCount_le_n_max hb_inv.hslot b)
  have hj_last_n : j_last < N := lt_of_lt_of_le hj_last_lt (Succinct.bCount_le_n_max hb_inv.hslot b)
  have hphys_del_lt : phys_del < N := by
    rw [hphys_del]; exact (Succinct.slotOf_lt_and_injective hb_inv.hslot).1 b hb j_del hj_del
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
    rw [hsz]; exact Nat.le_add_right _ _
  set s₁ := (Memory.spec 0).clientState s_fix
    (Succinct.unlinkIfIndexedProg U V w N h_space (((0, b), m), j_del))
  obtain ⟨_, _, _, _, hgm_u1, L₁, hval₁, hmem₁⟩ :=
    Succinct.unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := N)
      (h_space := h_space) (base := 0) (b := b) (m := m) (j_del := j_del)
      hw hb hm hj_del_n hb_inv.hchains hmem_del
  have hb_del : j_del < effBucketCap N →
      Succinct.lmPrev N (Succinct.lmAt 0 U V w N h_space s_fix.mem) b j_del ≤ effBucketCap N ∧
      Succinct.lmNext N (Succinct.lmAt 0 U V w N h_space s_fix.mem) b j_del ≤ effBucketCap N :=
    fun hj_cap => ⟨(hb_inv.hchains.1 b hb m hm).prev_le_cap (hmem_del hj_cap),
      (hb_inv.hchains.1 b hb m hm).next_le_cap (hmem_del hj_cap)⟩
  obtain ⟨s_out, hs_out⟩ : ∃ s_out, s_out = s' := ⟨s', rfl⟩
  obtain ⟨gm_out, hgm_out⟩ : ∃ gm_out, gm_out = gm' := ⟨gm', rfl⟩
  obtain ⟨T_pop, hT_pop⟩ :
      ∃ T_pop, T_pop =
        1967 * Succinct.slotPotential N gm_fix + 4802 - 1967 * Succinct.slotPotential N gm_out :=
    ⟨_, rfl⟩
  rw [← hs_out, ← hgm_out]
  refine ⟨287 + (832 + T_pop + 2), ?_, ?_⟩
  · unfold deleteExecFinishRegCode
    refine .seq (T₁ := 287) (T₂ := 832 + T_pop + 2)
      (unlinkIfIndexedRegCode_fixedCoupled (rB := 272) (rM := 273) (rJ := 275) (s_fix := s_fix)
        (by decide) (by decide) (by decide) hw hN_pos hnU hU hx her hcpl hsz_meta
        hb hm hj_del_n hb_del hr272 hr273 hr275)
      (fun y1 ⟨hy1_wf, hy1_er, hy1_sz, hy1_cpl, hy1_td, hy1_low, hy1_regs⟩ => ?_) le_rfl
    have hy1_gm : gmAtBit U w N y1.mem = gmAtBit U w N x.mem :=
      (hy1_cpl.gm_eq.trans hgm_u1).trans hgm_x.symm
    have hy1_sz_meta : epochMetaBits U w N ≤ y1.bitSize := by
      rw [hy1_sz]; exact hsz_meta
    have h2_lt : 2 < offLM U w N := by unfold offLM offHash; omega
    have h3_lt : 3 < offLM U w N := by unfold offLM offHash; omega
    have hy1_272 : y1.regs 272 = b := (hy1_regs 272 (by decide)).trans hr272
    have hy1_275 : y1.regs 275 = j_del := (hy1_regs 275 (by decide)).trans hr275
    have hy1_276 : y1.regs 276 =
        denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem) phys_del :=
      (hy1_regs 276 (by decide)).trans hr276
    have hy1_277 : y1.regs 277 = j_last := (hy1_regs 277 (by decide)).trans hr277_eq
    have hy1_278 : y1.regs 278 = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem)
        (Succinct.slotOf N (gmAtBit U w N x.mem) b
          (Succinct.bCount N (gmAtBit U w N x.mem) b - 1)) :=
      (hy1_regs 278 (by decide)).trans hr278
    have hy1_279 : y1.regs 279 = m_last := (hy1_regs 279 (by decide)).trans hr279
    by_cases hlt : j_del < j_last
    · have hcond : BitRAM.CondHolds (.lt 275 277) y1 := by
        change y1.regs 275 < y1.regs 277; rw [hy1_275, hy1_277]; exact hlt
      refine .branch_pos (T₀ := 832 + T_pop) hcond ?_ (by omega)
      have hmem_last₁ : j_last < effBucketCap N → j_last ∈ L₁ b m_last := fun hj_cap => by
        rw [hmem₁ b hb m_last hm_last j_last]
        exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
      have hb_last₁ : j_last < effBucketCap N →
          Succinct.lmPrev N (Succinct.lmAt 0 U V w N h_space s₁.mem) b j_last ≤ effBucketCap N ∧
          Succinct.lmNext N (Succinct.lmAt 0 U V w N h_space s₁.mem) b j_last ≤ effBucketCap N :=
        fun hj_cap => ⟨(hval₁.1 b hb m_last hm_last).prev_le_cap (hmem_last₁ hj_cap),
          (hval₁.1 b hb m_last hm_last).next_le_cap (hmem_last₁ hj_cap)⟩
      set s₂ := (Memory.spec 0).clientState s₁
        (Succinct.unlinkIfIndexedProg U V w N h_space (((0, b), m_last), j_last))
      obtain ⟨_, _, _, _, hgm_u2, L₂, hval₂, hmem₂⟩ :=
        Succinct.unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
          (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_last)
          (j_del := j_last) (s := s₁) hw hb hm_last hj_last_n hval₁ hmem_last₁
      refine .seq (T₁ := 287) (T₂ := 545 + T_pop)
        (unlinkIfIndexedRegCode_fixedCoupled (rB := 272) (rM := 279) (rJ := 277) (s_fix := s₁)
          (by decide) (by decide) (by decide) hw hN_pos hnU hU hy1_wf hy1_er hy1_cpl hy1_sz_meta
          hb hm_last hj_last_n hb_last₁ hy1_272 hy1_279 hy1_277)
        (fun y2 ⟨hy2_wf, hy2_er, hy2_sz, hy2_cpl, hy2_td, hy2_low, hy2_regs⟩ => ?_) (by omega)
      have hy2_gm : gmAtBit U w N y2.mem = gmAtBit U w N x.mem :=
        (hy2_cpl.gm_eq.trans (hgm_u2.trans hgm_u1)).trans hgm_x.symm
      have hy2_td_x : tdAtBit U w N y2.mem = tdAtBit U w N x.mem := hy2_td.trans hy1_td
      have hy2_low_x : ∀ a < offLM U w N, y2.mem a = x.mem a :=
        fun a ha => (hy2_low a ha).trans (hy1_low a ha)
      have hslot₂ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₂.mem) := by
        rw [hgm_u2, hgm_u1]; exact hb_inv.hslot
      have hj_del₂ : j_del < Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₂.mem) b := by
        rw [hgm_u2, hgm_u1]; exact hj_del
      have hphys_del₂ : phys_del =
          Succinct.slotOf N (Succinct.gmAt 0 U V w N h_space s₂.mem) b j_del := by
        rw [hgm_u2, hgm_u1]; exact hphys_del
      have hbc₂ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₂.mem) b := by
        rw [hgm_u2, hgm_u1]; exact hbc_pos
      set s₃ := (Memory.spec 0).clientState s₂
        (Succinct.copyLastPayloadProg U V w N h_space ((0, b), phys_del))
      obtain ⟨_, _, _, _, hlm_c, hgm_c⟩ :=
        Succinct.copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := N)
          (h_space := h_space) (base := 0) (b := b) (phys_del := phys_del) (s := s₂)
          hw hslot₂ hb hbc₂ hphys_del_lt
      refine .seq (T₁ := 195) (T₂ := 350 + T_pop)
        (copyDenseItemRegCode_fixedCoupled (rSrc := 278) (rDst := 276) (s_fix := s₂)
          (by decide) (by decide) hw hN_pos hU.le hV hy2_wf hy2_er hy2_cpl hslot₂ hb hj_del₂
          hphys_del₂
          (by rw [hy2_regs 278 (by decide), hy1_278, hy2_gm, hy2_td_x])
          (by rw [hy2_regs 276 (by decide), hy1_276, hy2_gm, hy2_td_x])
          (by rw [hy2_sz, hy1_sz, hy2_gm, hsz])
          (by rw [hy2_low_x 2 h2_lt, hm2])
          (by rw [hy2_low_x 3 h3_lt, hm3]))
        (fun y3 ⟨hy3_wf, hy3_er, hy3_sz, hy3_cpl, hy3_meta, hy3_regs⟩ => ?_) (by omega)
      have hy3_sz_x : y3.bitSize = x.bitSize := hy3_sz.trans (hy2_sz.trans hy1_sz)
      have hy3_low_x : ∀ a < offLM U w N, y3.mem a = x.mem a :=
        fun a ha => (hy3_meta a (by rw [← offDT_add_eq_epochMetaWords hN_pos]
                                    unfold offDT offTD offGM; omega)).trans (hy2_low_x a ha)
      have hval₃ : AllChainsValid N (Succinct.lmAt 0 U V w N h_space s₃.mem) L₂ :=
        hval₂.of_lm_eq hlm_c
      have hold₃ : Succinct.lmHead N (Succinct.lmAt 0 U V w N h_space s₃.mem) b m_last ≤
          effBucketCap N := (hval₃.1 b hb m_last hm_last).head_le_cap
      have hj_not₂ : ∀ m' < numMicroPerBucket N, j_del ∉ L₂ b m' := by
        intro m' hm' hj_in
        have hj_in₁ := ((hmem₂ b hb m' hm' j_del).mp hj_in).1
        exact ((hmem₁ b hb m' hm' j_del).mp hj_in₁).2 ⟨rfl, rfl⟩
      set s₄ := (Memory.spec 0).clientState s₃
        (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m_last), j_del))
      obtain ⟨_, _, _, _, hgm_pr, _⟩ :=
        Succinct.prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
          (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_last)
          (j_new := j_del) (s := s₃) hw hb hm_last hj_del_n hval₃ hj_not₂
      refine .seq (T₁ := 350) (T₂ := T_pop)
        (prependIfIndexedRegCode_fixedCoupled (rB := 272) (rM := 279) (rJ := 275) (s_fix := s₃)
          (by decide) (by decide) (by decide) hw hN_pos hnU hU hy3_wf hy3_er hy3_cpl
          (by rw [hy3_sz_x]; exact hsz_meta) hb hm_last hj_del_n hold₃
          (by rw [hy3_regs 272 (by decide), hy2_regs 272 (by decide), hy1_272])
          (by rw [hy3_regs 279 (by decide), hy2_regs 279 (by decide), hy1_279])
          (by rw [hy3_regs 275 (by decide), hy2_regs 275 (by decide), hy1_275]))
        (fun y4 ⟨hy4_wf, hy4_er, hy4_sz, hy4_cpl, _, hy4_low, hy4_regs⟩ => ?_) le_rfl
      have hy4_sz_x : y4.bitSize = x.bitSize := hy4_sz.trans hy3_sz_x
      have hy4_low_x : ∀ a < offLM U w N, y4.mem a = x.mem a :=
        fun a ha => (hy4_low a ha).trans (hy3_low_x a ha)
      have hgm₄_eq : Succinct.gmAt 0 U V w N h_space s₄.mem = gm_fix := by
        rw [hgm_pr, hgm_c, hgm_u2, hgm_u1]
      have hy4_gm : gmAtBit U w N y4.mem = gmAtBit U w N x.mem :=
        (hy4_cpl.gm_eq.trans hgm₄_eq).trans hgm_x.symm
      have hslot₄ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₄.mem) := by
        rw [hgm₄_eq]; exact hb_inv.hslot
      have hbc₄ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₄.mem) b := by
        rw [hgm₄_eq]; exact hbc_pos
      have hs'_pop : s_out = (Memory.spec 0).clientState s₄
          (Succinct.popBackSlotProg U V w N h_space (0, b)) := by
        rw [hs_out]; dsimp only [s']
        unfold Succinct.deleteFoundProg Succinct.deleteSwapProg
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          Succinct.clientState_readBucketCountProg,
          Succinct.clientResult_readBucketCountProg (0, b) s₁ hb, hgm_u1,
          ite_eq_left hlt]
        repeat rw [StateTransitionSpec.clientState_bind]
      obtain ⟨T_p, hexec_p, hpot_p⟩ :=
        popBackSlotRegCode_exec (rB := 272) (s_fix := s₄) (x := y4) (by decide)
          hw hN_pos hnU hU hV hy4_wf hy4_er
          (by rw [hy4_low_x 2 h2_lt, hm2]) (by rw [hy4_low_x 3 h3_lt, hm3])
          hy4_cpl hslot₄ hb hbc₄
          (by rw [hy4_sz_x, hy4_gm, hsz])
          (by rw [hy4_regs 272 (by decide), hy3_regs 272 (by decide),
                  hy2_regs 272 (by decide), hy1_272])
      have hT_p_le : T_p ≤ T_pop := by
        rw [hy4_gm, hgm_x] at hpot_p
        rw [hT_pop, hgm_out]
        dsimp only [gm']
        rw [← hs_out, hs'_pop]
        dsimp only [gm_fix, h_space] at hpot_p ⊢
        omega
      refine hexec_p.mono (fun y ⟨hy_wf, hy_er, hy_sz, hy_cpl, hy_low, _⟩ =>
        ⟨hy_wf, hy_er, hy_sz, by rw [hs'_pop]; exact hy_cpl,
         fun a ha => (hy_low a ha).trans (hy4_low_x a ha)⟩) hT_p_le
    · have hcond : ¬BitRAM.CondHolds (.lt 275 277) y1 := by
        change ¬(y1.regs 275 < y1.regs 277); rw [hy1_275, hy1_277]; exact hlt
      refine .branch_neg (T₀ := T_pop) hcond ?_ (by omega)
      have hslot₁ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₁.mem) := by
        rw [hgm_u1]; exact hb_inv.hslot
      have hbc₁ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₁.mem) b := by
        rw [hgm_u1]; exact hbc_pos
      have hs'_pop : s_out = (Memory.spec 0).clientState s₁
          (Succinct.popBackSlotProg U V w N h_space (0, b)) := by
        rw [hs_out]; dsimp only [s']
        unfold Succinct.deleteFoundProg
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          Succinct.clientState_readBucketCountProg,
          Succinct.clientResult_readBucketCountProg (0, b) s₁ hb, hgm_u1,
          ite_eq_right hlt]
      obtain ⟨T_p, hexec_p, hpot_p⟩ :=
        popBackSlotRegCode_exec (rB := 272) (s_fix := s₁) (x := y1) (by decide)
          hw hN_pos hnU hU hV hy1_wf hy1_er
          (by rw [hy1_low 2 h2_lt, hm2]) (by rw [hy1_low 3 h3_lt, hm3])
          hy1_cpl hslot₁ hb hbc₁
          (by rw [hy1_sz, hy1_gm, hsz]) hy1_272
      have hT_p_le : T_p ≤ T_pop := by
        rw [hy1_gm, hgm_x] at hpot_p
        rw [hT_pop, hgm_out]
        dsimp only [gm']
        rw [← hs_out, hs'_pop]
        dsimp only [gm_fix, h_space] at hpot_p ⊢
        omega
      refine hexec_p.mono (fun y ⟨hy_wf, hy_er, hy_sz, hy_cpl, hy_low, _⟩ =>
        ⟨hy_wf, hy_er, hy_sz, by rw [hs'_pop]; exact hy_cpl,
         fun a ha => (hy_low a ha).trans (hy1_low a ha)⟩) hT_p_le
  · have hpot_bound : 1967 * Succinct.slotPotential N gm_out ≤
        1967 * Succinct.slotPotential N gm_fix + 4802 := by
      by_cases hlt : j_del < j_last
      · have hmem_last₁ : j_last < effBucketCap N → j_last ∈ L₁ b m_last := fun hj_cap => by
          rw [hmem₁ b hb m_last hm_last j_last]
          exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
        set s₂ := (Memory.spec 0).clientState s₁
          (Succinct.unlinkIfIndexedProg U V w N h_space (((0, b), m_last), j_last))
        obtain ⟨_, _, _, _, hgm_u2, L₂, hval₂, hmem₂⟩ :=
          Succinct.unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
            (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_last)
            (j_del := j_last) (s := s₁) hw hb hm_last hj_last_n hval₁ hmem_last₁
        have hslot₂ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₂.mem) := by
          rw [hgm_u2, hgm_u1]; exact hb_inv.hslot
        have hbc₂ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₂.mem) b := by
          rw [hgm_u2, hgm_u1]; exact hbc_pos
        set s₃ := (Memory.spec 0).clientState s₂
          (Succinct.copyLastPayloadProg U V w N h_space ((0, b), phys_del))
        obtain ⟨_, _, _, _, hlm_c, hgm_c⟩ :=
          Succinct.copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := N)
            (h_space := h_space) (base := 0) (b := b) (phys_del := phys_del) (s := s₂)
            hw hslot₂ hb hbc₂ hphys_del_lt
        have hval₃ : AllChainsValid N (Succinct.lmAt 0 U V w N h_space s₃.mem) L₂ :=
          hval₂.of_lm_eq hlm_c
        have hj_not₂ : ∀ m' < numMicroPerBucket N, j_del ∉ L₂ b m' := by
          intro m' hm' hj_in
          have hj_in₁ := ((hmem₂ b hb m' hm' j_del).mp hj_in).1
          exact ((hmem₁ b hb m' hm' j_del).mp hj_in₁).2 ⟨rfl, rfl⟩
        set s₄ := (Memory.spec 0).clientState s₃
          (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m_last), j_del))
        obtain ⟨_, _, _, _, hgm_pr, _⟩ :=
          Succinct.prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
            (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_last)
            (j_new := j_del) (s := s₃) hw hb hm_last hj_del_n hval₃ hj_not₂
        have hgm₄_eq : Succinct.gmAt 0 U V w N h_space s₄.mem = gm_fix := by
          rw [hgm_pr, hgm_c, hgm_u2, hgm_u1]
        have hslot₄ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₄.mem) := by
          rw [hgm₄_eq]; exact hb_inv.hslot
        have hbc₄ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₄.mem) b := by
          rw [hgm₄_eq]; exact hbc_pos
        have hs'_pop : s_out = (Memory.spec 0).clientState s₄
            (Succinct.popBackSlotProg U V w N h_space (0, b)) := by
          rw [hs_out]; dsimp only [s']
          unfold Succinct.deleteFoundProg Succinct.deleteSwapProg
          simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            Succinct.clientState_readBucketCountProg,
            Succinct.clientResult_readBucketCountProg (0, b) s₁ hb, hgm_u1,
            ite_eq_left hlt]
          repeat rw [StateTransitionSpec.clientState_bind]
        have eff_pop := Succinct.popBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := N)
          (h_space := h_space) (base := 0) (b := b) hw s₄ hslot₄ hb hbc₄
        have hcost_pop := eff_pop.2.2.2.2.2.2.2.2
        change _ + 66 * Succinct.slotPotential N _ ≤
          66 * Succinct.slotPotential N (Succinct.gmAt 0 U V w N h_space s₄.mem) + 174 at hcost_pop
        rw [hgm₄_eq] at hcost_pop
        rw [hgm_out]; dsimp only [gm']
        rw [← hs_out, hs'_pop]
        dsimp only [gm_fix, h_space] at hcost_pop ⊢
        omega
      · have hslot₁ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₁.mem) := by
          rw [hgm_u1]; exact hb_inv.hslot
        have hbc₁ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₁.mem) b := by
          rw [hgm_u1]; exact hbc_pos
        have hs'_pop : s_out = (Memory.spec 0).clientState s₁
            (Succinct.popBackSlotProg U V w N h_space (0, b)) := by
          rw [hs_out]; dsimp only [s']
          unfold Succinct.deleteFoundProg
          simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            Succinct.clientState_readBucketCountProg,
            Succinct.clientResult_readBucketCountProg (0, b) s₁ hb, hgm_u1,
            ite_eq_right hlt]
        have eff_pop := Succinct.popBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := N)
          (h_space := h_space) (base := 0) (b := b) hw s₁ hslot₁ hb hbc₁
        have hcost_pop := eff_pop.2.2.2.2.2.2.2.2
        change _ + 66 * Succinct.slotPotential N _ ≤
          66 * Succinct.slotPotential N (Succinct.gmAt 0 U V w N h_space s₁.mem) + 174 at hcost_pop
        rw [hgm_u1] at hcost_pop
        rw [hgm_out]; dsimp only [gm']
        rw [← hs_out, hs'_pop]
        dsimp only [gm_fix, h_space] at hcost_pop ⊢
        omega
    rw [hT_pop]; omega


/-! ## Section 3: Uniform `BitRAM` program for in-epoch `delete` (`inEpochDeleteRegCode`) -/

/-- Uniform `BitRAM.Code .standard 280` program executing an in-epoch deletion (`r270 = u.val`):
splits `u.val` via `feistelSplitRegCode`, searches bucket `b` via `searchBucketRegCode`, and
if found (`r32 ≠ 0`), runs `deletePrepLastRegCode` followed by `deleteExecFinishRegCode`. -/
@[expose]
def inEpochDeleteRegCode : BitRAM.Code .standard 280 :=
  .seq feistelSplitRegCode
  (.seq searchBucketRegCode
  (.seq (.op (.const 36 0))
        (.branch (.eq 32 36)
          (.op (.copy 0 0))
          (.seq deletePrepLastRegCode deleteExecFinishRegCode))))

open Classical in
theorem inEpochDeleteRegCode_exec {U V w N : ℕ}
    (hwf : Succinct.DictParamsWf U V w N)
    (henv : Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0)
    (hN_pos : 0 < N)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    (hdict : Succinct.DictStateInv U V w N 0 θ s_abs s_fix)
    (u : Fin U)
    {x : BitRAM.Data 280}
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hfit_cap : Fits w (dictBitSize U V w N N))
    (hr270 : x.regs 270 = u.val) :
    let h1 := Succinct.hValOfSeed U N θ
    let mOf := Succinct.mOfSeed U N θ
    let q := keyQuotient (bucketBits N) u.val
    let b := feistelBucket (bucketBits N) h1 u.val
    let m := mOf q
    let h_space := Succinct.hashSpace U w N
    let gm_fix := Succinct.gmAt 0 U V w N h_space s_fix.mem
    let prep := (Memory.spec 0).clientResult s_fix
      (Succinct.deletePrepProg U V w N h_space (((0, b), q), m))
    let d_fin := (((((0, b), prep.1.1), prep.1.2), m), mOf prep.2)
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.deleteFinishProg U V w N h_space d_fin)
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w inEpochDeleteRegCode x
        (fun y =>
          y.WellFormed w ∧
          EpochRegs U V w N y ∧
          y.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y.mem)) ∧
          FixedCoupled U V w N s' y.toBitMemoryState ∧
          (∀ a < offLM U w N, y.mem a = x.mem a)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm_fix + 292583 +
          350 * probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
            (Dynamic.dom s_abs) u := by
  intro h1 mOf q b m h_space gm_fix prep d_fin s' gm'
  rcases hwf with ⟨hw, hnU, hU, hV⟩
  obtain ⟨L, hb_inv⟩ := hdict.hbucket
  set gm := gmAtBit U w N x.mem
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  have hm_lt : m < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
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
  have hprep := Succinct.deletePrepProg_bucket_spec hb_inv henv hb_lt rfl hm_lt (q_target := q)
  have hfin := Succinct.deleteFinishProg_bucket_spec hw hb_inv henv hb_lt rfl hm_lt (q_target := q)
    (fun q' _ => Succinct.mOfSeed_lt U N θ q')
  have hres := hprep.2.2.2
  have hrep_bit : BucketRepInv U V w N mOf L
      (Succinct.bucketMapOfState U N h1 s_abs) x.toBitMemoryState :=
    bucketRepInv_of_fixedCoupled hb_inv hcpl
  have hprobe := chain_and_overflow_le_probeExcess_rep θ hrep_bit u
  obtain ⟨s_out, hs_out⟩ : ∃ s_out, s_out = s' := ⟨s', rfl⟩
  obtain ⟨gm_out, hgm_out⟩ : ∃ gm_out, gm_out = gm' := ⟨gm', rfl⟩
  obtain ⟨T_search, hT_search⟩ :
      ∃ T_search, T_search =
        295 + 350 * (L b m).length + 287 * (Succinct.bCount N gm b - effBucketCap N) :=
    ⟨_, rfl⟩
  obtain ⟨T_del, hT_del⟩ :
      ∃ T_del, T_del =
        1967 * Succinct.slotPotential N gm_fix + 5923 - 1967 * Succinct.slotPotential N gm_out :=
    ⟨_, rfl⟩
  rw [← hs_out, ← hgm_out]
  refine ⟨142643 + T_search + (143019 + T_del + 2) + 1, ?_, ?_⟩
  · unfold inEpochDeleteRegCode
    refine .seq (T₁ := 142643) (T₂ := T_search + (143019 + T_del + 2) + 1)
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
    refine .seq (T₂ := (143019 + T_del + 2) + 1)
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
    refine DemonicExecWithin.step_const (T := 143019 + T_del + 2) (fits_zero w) ?_
    set s2 := y2.set 36 0
    have hs2_wf : s2.WellFormed w := wf_set 36 hy2_wf (fits_zero w)
    have hs2_er : EpochRegs U V w N s2 :=
      hy2_er.congr_regs (fun r hr1 _ => by
        dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs2_272 : s2.regs 272 = b := by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by decide), hy2_hi 272 (by decide), hy1_272]
    have hs2_273 : s2.regs 273 = m := by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by decide), hy2_hi 273 (by decide), hy1_273]
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
      rcases hres with ⟨hf1, hj_lt, hq_res, hphys_eq, hq_last_eq⟩
      change prep.1.1.1 = 1 at hf1
      change prep.1.1.2 < Succinct.bCount N gm_fix b at hj_lt
      change Succinct.quotAt 0 U w N h_space s_fix.mem
        (Succinct.slotOf N gm_fix b prep.1.1.2) = q at hq_res
      change prep.1.2 = Succinct.slotOf N gm_fix b prep.1.1.2 at hphys_eq
      change prep.2 = Succinct.quotAt 0 U w N h_space s_fix.mem
        (Succinct.slotOf N gm_fix b (Succinct.bCount N gm_fix b - 1)) at hq_last_eq
      obtain ⟨hy2_32, hy2_33_lt, _, hy2_q, _, hy2_35⟩ := hy2_res
      have hcond : ¬BitRAM.CondHolds (.eq 32 36) s2 := by
        change s2.regs 32 ≠ s2.regs 36
        simp +decide [s2, BitRAM.Data.set, hy2_32]
      have hj_eq : y2.regs 33 = prep.1.1.2 := by
        have hq33 : Succinct.quotAt 0 U w N h_space s_fix.mem
            (Succinct.slotOf N gm_fix b (y2.regs 33)) = q := by
          rw [← hgm_eq]
          exact (virtualQuotAt_slotOf_eq_quotAt hcpl hb_inv.hslot hb_lt hy2_33_lt).symm.trans hy2_q
        exact hb_inv.hnodup_q b hb_lt (y2.regs 33)
          (by change y2.regs 33 < Succinct.bCount N gm_fix b; rw [← hgm_eq]; exact hy2_33_lt)
          prep.1.1.2 hj_lt (hq33.trans hq_res.symm)
      have hs2_33 : s2.regs 33 = prep.1.1.2 := by
        dsimp only [s2, BitRAM.Data.set]; rw [Function.update_of_ne (by decide), hj_eq]
      have hs2_35 : s2.regs 35 =
          denseOfPhys N (gmAtBit U w N s2.mem) (tdAtBit U w N s2.mem) prep.1.2 := by
        dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by decide), hy2_mem, hy2_35, hj_eq, hphys_eq]
        change denseOfPhys N gm (tdAtBit U w N x.mem) (Succinct.slotOf N gm b prep.1.1.2) =
          denseOfPhys N gm (tdAtBit U w N x.mem) (Succinct.slotOf N gm_fix b prep.1.1.2)
        rw [hgm_eq]
      have hbc_pos : 1 ≤ Succinct.bCount N gm_fix b := by omega
      have hbc_pos_gm : 1 ≤ Succinct.bCount N gm b := hgm_eq.symm ▸ hbc_pos
      have hm_last_lt : mOf prep.2 < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ prep.2
      have hs'_df : s_out = (Memory.spec 0).clientState s_fix
          (Succinct.deleteFoundProg U V w N h_space
            ((((0, b), prep.1.1.2), prep.1.2), (m, mOf prep.2))) := by
        rw [hs_out]; dsimp only [s', d_fin]
        unfold Succinct.deleteFinishProg; simp only [pure_bind]
        change (Memory.spec 0).clientState s_fix
          (if prep.1.1.1 = 1 then
             Succinct.deleteFoundProg U V w N h_space
               ((((0, b), prep.1.1.2), prep.1.2), (m, mOf prep.2))
           else pure ()) = _
        rw [ite_eq_left hf1]
      have hmem_del : prep.1.1.2 < effBucketCap N → prep.1.1.2 ∈ L b m := fun hj_cap => by
        rw [hb_inv.hchain_mem b hb_lt m hm_lt prep.1.1.2]
        exact ⟨hj_lt, hj_cap, congrArg mOf hq_res⟩
      have hmem_last : Succinct.bCount N gm_fix b - 1 < effBucketCap N →
          Succinct.bCount N gm_fix b - 1 ∈ L b (mOf prep.2) := fun hj_cap => by
        rw [hb_inv.hchain_mem b hb_lt (mOf prep.2) hm_last_lt]
        exact ⟨by dsimp only [gm_fix, h_space] at hbc_pos ⊢; omega,
          hj_cap, congrArg mOf hq_last_eq.symm⟩
      refine .branch_neg (T₀ := 143019 + T_del) hcond ?_ (by omega)
      refine .seq (T₁ := 143019) (T₂ := T_del)
        (deletePrepLastRegCode_exec (b := b) (m := m) (j_del := prep.1.1.2)
          (d_del := denseOfPhys N gm (tdAtBit U w N x.mem) prep.1.2) (x := s2)
          hw hN_pos hnU hU hfit_meta θ hs2_wf hs2_er
          (by change FixedCoupled U V w N s_fix y2.toBitMemoryState; rw [hy2_st_x]; exact hcpl)
          hb_inv.hslot
          (by change ReducedKWise.Rep _ _ _ _ _ _ θ y2.mem; rw [hy2_mem]; exact hrep_hash)
          (by change y2.mem 1 = N; rw [hy2_mem, hm1])
          (by change y2.mem 2 = _; rw [hy2_mem, hm2])
          (by change y2.mem 3 = _; rw [hy2_mem, hm3])
          (by change y2.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y2.mem))
              rw [hy2_sz, hy2_mem, hsz])
          hb_lt (by change 1 ≤ Succinct.bCount N (gmAtBit U w N y2.mem) b
                    rw [hy2_mem]; exact hbc_pos_gm)
          hs2_272 hs2_273 hs2_33
          (by rw [hs2_35]
              change denseOfPhys N (gmAtBit U w N y2.mem) (tdAtBit U w N y2.mem) prep.1.2 = _
              rw [hy2_mem]))
        (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_272, hy3_273, hy3_275, hy3_276, hy3_277,
          hy3_278, hy3_279⟩ => ?_) le_rfl
      have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState :=
        hy3_st.trans hy2_st_x
      have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
      have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
      have hs2_mem : s2.mem = x.mem := hy2_mem
      rw [hs2_mem] at hy3_277 hy3_278 hy3_279
      obtain ⟨T_df, hexec_df, hpot_df⟩ :=
        deleteExecFinishRegCode_exec (b := b) (m := m) (j_del := prep.1.1.2)
          (phys_del := prep.1.2) (m_last := mOf prep.2) (x := y3)
          hw hN_pos hnU hU hV hy3_wf hy3_er (by rw [hy3_st_x]; exact hcpl)
          hb_inv hb_lt hm_lt hm_last_lt hj_lt hphys_eq hmem_del hmem_last
          (by rw [hy3_sz, hy3_mem, hsz])
          (by rw [hy3_mem, hm2]) (by rw [hy3_mem, hm3])
          hy3_272 hy3_273 hy3_275
          (by rw [hy3_mem]; exact hy3_276)
          (by rw [hy3_mem]; exact hy3_277)
          (by rw [hy3_mem]; exact hy3_278)
          (by rw [hy3_279]; change mOf (Succinct.quotAt 0 U w N h_space s_fix.mem
                (Succinct.slotOf N gm b (Succinct.bCount N gm b - 1))) = mOf prep.2
              rw [hgm_eq, ← hq_last_eq])
      have hT_df_le : T_df ≤ T_del := by
        rw [hT_del, hgm_out]
        dsimp only [gm']
        rw [← hs_out, hs'_df]
        dsimp only [gm_fix, h_space] at hpot_df ⊢
        omega
      refine hexec_df.mono (fun y ⟨hy_wf, hy_er, hy_sz, hy_cpl, hy_low⟩ =>
        ⟨hy_wf, hy_er, hy_sz, by rw [hs'_df]; exact hy_cpl,
         fun a ha => (hy_low a ha).trans (congrFun hy3_mem a)⟩) hT_df_le
    · rw [ite_eq_right hex] at hres
      rw [ite_eq_right (mt hiff_cond.mp hex)] at hy2_res
      have hcond : BitRAM.CondHolds (.eq 32 36) s2 := by
        change s2.regs 32 = s2.regs 36
        simp +decide [s2, BitRAM.Data.set, hy2_res]
      have h0 : prep.1.1.1 = 0 := hres.1
      have hne1 : prep.1.1.1 ≠ 1 := by omega
      have hs'_eq_fix : s_out = s_fix := by
        rw [hs_out]; dsimp only [s', d_fin]
        unfold Succinct.deleteFinishProg; simp only [pure_bind]
        change (Memory.spec 0).clientState s_fix
          (if prep.1.1.1 = 1 then _ else pure ()) = _
        rw [ite_eq_right hne1]; rfl
      refine .branch_pos (T₀ := 1) hcond ?_ (by omega)
      refine DemonicExecWithin.copy ?_
      have hs2_0 : (s2.set 0 (s2.regs 0)).toBitMemoryState = x.toBitMemoryState := hy2_st_x
      have hs2_0_mem : (s2.set 0 (s2.regs 0)).mem = x.mem := hy2_mem
      have hs2_0_sz : (s2.set 0 (s2.regs 0)).bitSize = x.bitSize := hy2_sz
      refine ⟨wf_set 0 hs2_wf (hs2_wf.regs_fits 0),
        hs2_er.congr_regs (fun r hr1 _ => by
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
        by rw [hs2_0_sz, hs2_0_mem, hsz],
        by rw [hs'_eq_fix, hs2_0]; exact hcpl,
        fun a _ => congrFun hs2_0_mem a⟩
  · have hpot_bound : 1967 * Succinct.slotPotential N gm_out ≤
        1967 * Succinct.slotPotential N gm_fix + 5923 := by
      have hcost_fin := hfin.2.2.2.2.2
      rw [hgm_out]
      dsimp only [gm', gm_fix, s', d_fin, prep, h_space, m, mOf]
      omega
    have hsum := hprobe.2.2.1
    rw [hT_search, hT_del]
    dsimp only [BitRAM.Data.toBitMemoryState, b, q, m, mOf, h1, gm] at hsum hpot_bound ⊢
    omega

end Cslib.DataStructure.Dictionary.BitResizable
