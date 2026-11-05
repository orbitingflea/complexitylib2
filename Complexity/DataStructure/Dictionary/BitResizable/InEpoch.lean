/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.SlotResolve
public import Complexity.DataStructure.Dictionary.BitResizable.PromoteOps
public import Complexity.DataStructure.Dictionary.BitResizable.DemoteOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps

/-!
# Uniform `BitRAM` Programs for In-Epoch Slot Store and Payload Operations

This module implements uniform `BitRAM.Code .standard 280` programs for the high-level slot-store
operations of the bit-resizable succinct dictionary:
* `pushBackSlotRegCode`: executes `Succinct.pushBackSlotProg` directly on `BitRAM`, preserving
  `FixedCoupled` with `O(1)` amortized instruction bound against `1967 * Succinct.slotPotential`;
* `popBackSlotRegCode`: executes `Succinct.popBackSlotProg` directly on `BitRAM`, preserving
  `FixedCoupled` with `O(1)` amortized instruction bound against `1967 * Succinct.slotPotential`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: `pushBackSlotRegCode` and `pushBackSlotRegCode_exec` -/

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.pushBackSlotProg`:
in the single-bucket regime (`bucketBits N = 0`), appends `(q_val, v_val)` to the dense item region
and increments `gm 0`; in the multi-bucket regime (`0 < bucketBits N`), runs
`pushBackTailWriteRegCode` and conditionally promotes `K = slabSize N` tail items into a full slab
via `promoteSlabRegCode` when `r_b + 1 = 2 * K` (`32 ≤ rB, rQ, rV`). -/
@[expose]
def pushBackSlotRegCode (rB rQ rV : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 14 0))
  (.branch (.eq 245 14)
    (.seq (appendDenseRegCode rQ rV)
    (.seq (readGMConstRegCode 0 28)
    (.seq (.op (.const 14 1))
    (.seq (.op (.bin .add 28 28 14))
          (writeGMConstRegCode 0 28)))))
    (.seq computeGMBasesRegCode
    (.seq (pushBackTailWriteRegCode rB rQ rV)
    (.seq (.op (.bin .add 28 250 250))
    (.branch (.eq 27 28)
      (promoteSlabRegCode rB)
      nopRegCode)))))

private theorem pushBackSlotRegCode_single_exec {U V w N b q_val v_val : ℕ}
    {rB rQ rV : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrQ_ge : 32 ≤ rQ.val) (hrV_ge : 32 ≤ rV.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb0 : bucketBits N = 0)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hb : b < numBuckets N)
    (htot : Succinct.totalSlots N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) < N)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hfits : Fits w (dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem) + 1)))
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V)
    (hrQ : x.regs rQ = q_val) (hrV : x.regs rV = v_val) :
    let d_arg := (((0, b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg)
    let gm₀ := gmAtBit U w N x.mem
    let gm' := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w (pushBackSlotRegCode rB rQ rV) x
        (fun z =>
          z.WellFormed w ∧
          EpochRegs U V w N z ∧
          z.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N z.mem)) ∧
          FixedCoupled U V w N s' z.toBitMemoryState ∧
          (∀ a < offLM U w N, z.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm₀ + 3300 := by
  intro d_arg s' gm₀ gm'
  have hb_eq : b = 0 := by
    have : numBuckets N = 1 := by simp [numBuckets, hb0]
    omega
  subst hb_eq
  have hgm0_eq : gm₀ = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
  have htot0 : gm₀ 0 < N := by
    rw [← hgm0_eq] at htot
    unfold Succinct.totalSlots at htot
    rwa [ite_eq_left hb0] at htot
  have htot_eq : Succinct.totalSlots N gm₀ = gm₀ 0 := by
    unfold Succinct.totalSlots; rw [ite_eq_left hb0]
  have hsz_off : x.bitSize = itemBitOff U V w N (gm₀ 0) := by
    rw [hsz, htot_eq]; rfl
  have hfits_off : Fits w (itemBitOff U V w N (gm₀ 0 + 1)) := by
    rw [← htot_eq] at *; exact hfits
  have hfit_0 : Fits w 0 := fits_zero w
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_c1 : Fits w (gm₀ 0 + 1) := fits_of_le_N hw hnU hU (by omega)
  have hc1_lt : gm₀ 0 + 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have h245 : x.regs 245 = 0 := by rw [(her.active hN_pos).1, hb0]
  refine ⟨203, ?_, ?_⟩
  · unfold pushBackSlotRegCode
    refine DemonicExecWithin.step_const (T := 202) hfit_0 ?_
    set s0 := x.set 14 0
    have hs0_wf : s0.WellFormed w := wf_set 14 hx hfit_0
    have hs0_er : EpochRegs U V w N s0 := her.set_of_outside (by decide) 0
    have hs0_st : s0.toBitMemoryState = x.toBitMemoryState := rfl
    have hs0_mem : s0.mem = x.mem := rfl
    have hc : BitRAM.CondHolds (.eq 245 14) s0 := by
      change s0.regs 245 = s0.regs 14
      simp +decide [s0, BitRAM.Data.set, h245]
    refine dExec_branch_pos (T := 201) hc ?_
    have hs0_rQ : s0.regs rQ = q_val := by
      dsimp only [s0, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; subst h; omega), hrQ]
    have hs0_rV : s0.regs rV = v_val := by
      dsimp only [s0, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; subst h; omega), hrV]
    refine .seq (T₁ := 96) (T₂ := 105)
      (appendDenseRegCode_frame (by omega) (by omega) hw hN_pos (le_of_lt hU) hV
        hs0_wf hs0_er hsz_off hs0_rQ hs0_rV hq_lt hv_lt hfits_off)
      (fun y1 ⟨hy1_wf, hy1_er, hy1_sz, hy1_qn, hy1_vn, hy1_items,
        hy1_lm, hy1_gm, hy1_td, hy1_dt, hy1_out, hy1_regs⟩ => ?_) (by omega)
    have hy1_sz_meta : epochMetaBits U w N ≤ y1.bitSize := by
      rw [hy1_sz]; exact Nat.le_add_right _ _
    refine .seq (T₁ := 46) (T₂ := 59)
      (readGMConstRegCode_exec (idx := 0) (rDst := 28) (by decide) (by decide) (by decide)
        hw hN_pos hnU hU hy1_wf hy1_er hy1_sz_meta)
      (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_28, hy2_regs⟩ => ?_) (by omega)
    have hy2_mem : y2.mem = y1.mem := congrArg BitMemory.State.mem hy2_st
    have hy2_sz : y2.bitSize = y1.bitSize := congrArg BitMemory.State.bitSize hy2_st
    have hy2_28_val : y2.regs 28 = gm₀ 0 := by rw [hy2_28, hy1_gm, hs0_mem]
    refine DemonicExecWithin.step_const (T := 58) hfit_1 ?_
    refine step_dExec_bin (v := gm₀ 0 + 1) (T := 57)
      (by simp +decide [BinOp.eval, BitRAM.Data.set, hy2_28_val]) hfit_c1 ?_
    set s3 := (y2.set 14 1).set 28 (gm₀ 0 + 1)
    have hs3_wf : s3.WellFormed w := wf_set 28 (wf_set 14 hy2_wf hfit_1) hfit_c1
    have hs3_er : EpochRegs U V w N s3 :=
      hy2_er.congr_regs (fun r hr1 _ => by
        dsimp only [s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    refine (writeGMConstRegCode_exec (idx := 0) (rVal := 28) (by decide) (by decide)
      hw hN_pos hnU hU hs3_wf hs3_er
      (by change epochMetaBits U w N ≤ y2.bitSize; rw [hy2_sz]; exact hy1_sz_meta)
      (by simp +decide [s3, BitRAM.Data.set]) hc1_lt).mono
      (fun z ⟨hz_sz, hz_wf, hz_er, hz_gm, hz_lm, hz_td, hz_dt, hz_out, hz_items, hz_regs⟩ => ?_)
      le_rfl
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    obtain ⟨_, _, hq1, hv1, hl1, hg1⟩ :=
      Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
        hw htot0 hq_lt s_fix
    set s_wq := (Memory.spec 0).clientState s_fix
      (Succinct.writeQuotProg U w N (Succinct.hashSpace U w N) ((0, gm₀ 0), q_val))
    obtain ⟨_, _, hq2, hv2, hl2, hg2⟩ :=
      Succinct.writeValProg_effect (base := 0) (h_space := Succinct.hashSpace U w N)
        hw htot0 hv_lt s_wq
    set s_wv := (Memory.spec 0).clientState s_wq
      (Succinct.writeValProg U V w N (Succinct.hashSpace U w N) ((0, gm₀ 0), v_val))
    obtain ⟨_, _, hq3, hv3, hl3, hg3⟩ :=
      Succinct.writeGMProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
        hw h0_lt hc1_lt s_wv
    set s_wg := (Memory.spec 0).clientState s_wv
      (Succinct.writeGMProg U V w N (Succinct.hashSpace U w N) ((0, 0), gm₀ 0 + 1))
    have hs'_eq : s' = s_wg := by
      change (Memory.spec 0).clientState s_fix
        (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = s_wg
      unfold Succinct.pushBackSlotProg
      simp only [hb0, ↓reduceIte, d_arg]
      rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg,
        Succinct.clientResult_readGMProg s_fix h0_lt, ← hgm0_eq]
      repeat rw [StateTransitionSpec.clientState_bind]
    have hgm_z : gmAtBit U w N z.mem = Function.update gm₀ 0 (gm₀ 0 + 1) := by
      rw [hz_gm]; change Function.update (gmAtBit U w N y2.mem) 0 (gm₀ 0 + 1) = _
      rw [hy2_mem, hy1_gm, hs0_mem]
    have hgm_s' : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s'.mem =
        Function.update gm₀ 0 (gm₀ 0 + 1) := by
      rw [hs'_eq, hg3, hg2, hg1, ← hgm0_eq]
    have htot_z : Succinct.totalSlots N (gmAtBit U w N z.mem) = gm₀ 0 + 1 := by
      unfold Succinct.totalSlots; simp [hb0, hgm_z]
    have hgm_z1 : gmAtBit U w N z.mem 1 = gm₀ 1 := by
      rw [hgm_z, Function.update_of_ne (by decide)]
    have hM0 : maxTailItems N = 0 := by simp [maxTailItems, tailCapPerBucket, hb0]
    have hgm0_1 : gm₀ 1 = 0 := by
      by_contra hpos
      have := hcpl.win_inv.td_lt 0 (Nat.pos_of_ne_zero hpos)
      omega
    have htd_z : tdAtBit U w N z.mem = tdAtBit U w N x.mem := by
      rw [hz_td]; exact (congrArg (tdAtBit U w N) hy2_mem).trans hy1_td
    have hdt_z : dtAtBit U w N z.mem = dtAtBit U w N x.mem := by
      rw [hz_dt]; exact (congrArg (dtAtBit U w N) hy2_mem).trans hy1_dt
    refine ⟨hz_wf, hz_er,
      by rw [hz_sz]; change y2.bitSize = _; rw [hy2_sz, hy1_sz, htot_z]; rfl,
      ⟨hgm_z.trans hgm_s'.symm,
       by dsimp only [BitRAM.Data.toBitMemoryState]
          rw [hz_lm]; change lmAtBit U w N y2.mem = _
          rw [hy2_mem, hy1_lm, hs'_eq, hl3, hl2, hl1]
          exact hcpl.lm_eq,
       by dsimp only [BitRAM.Data.toBitMemoryState]
          rw [hgm_z1, hgm0_1]
          exact ⟨fun _ h => by omega, fun _ h => by omega,
            fun _ h => by omega, fun _ _ _ => by omega⟩,
       fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_z]; exact hcpl.td_lt i,
       fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hdt_z]; exact hcpl.dt_lt i,
       fun d hd => ?_, fun d hd => ?_⟩,
      fun a ha => by
        rw [hz_out a (Or.inl (by unfold offGM; omega))]
        exact (congrFun hy2_mem a).trans (hy1_out a ha),
      fun r hr => by
        rw [hz_regs r (by omega)]
        dsimp only [s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy2_regs r (by omega) (by intro h; subst h; omega), hy1_regs r (by omega)]
        dsimp only [s0, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; subst h; omega)]⟩
    · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
      rw [htot_z] at hd
      change denseQuotAt U V w N z.toBitMemoryState d =
        Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s'.mem
          (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
      have hphys_d :
          physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d = d := by
        unfold physByBase; simp [hb0]
      have hphys_d0 : physByBase N (gm₀ 0 * slabSize N) (dtAtBit U w N x.mem) d = d := by
        unfold physByBase; simp [hb0]
      rw [(hz_items d).1]; change denseQuotAt U V w N y2.toBitMemoryState d = _
      rw [hy2_st, hs'_eq, hq3, hq2, hq1, hphys_d]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd_lt | rfl
      · rw [(hy1_items d hd_lt).1, hs0_st, Function.update_of_ne (by omega)]
        have hq := hcpl.quot_eq d
          (by change d < Succinct.totalSlots N gm₀; rw [htot_eq]; exact hd_lt)
        exact hq.trans (congrArg _ hphys_d0)
      · rw [hy1_qn, Function.update_self]
    · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
      rw [htot_z] at hd
      change denseValAt U V w N z.toBitMemoryState d =
        Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
          (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
      have hphys_d :
          physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d = d := by
        unfold physByBase; simp [hb0]
      have hphys_d0 : physByBase N (gm₀ 0 * slabSize N) (dtAtBit U w N x.mem) d = d := by
        unfold physByBase; simp [hb0]
      rw [(hz_items d).2]; change denseValAt U V w N y2.toBitMemoryState d = _
      rw [hy2_st, hs'_eq, hv3, hv2, hphys_d]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd_lt | rfl
      · rw [(hy1_items d hd_lt).2, hs0_st, Function.update_of_ne (by omega), hv1]
        have hv := hcpl.val_eq d
          (by change d < Succinct.totalSlots N gm₀; rw [htot_eq]; exact hd_lt)
        exact hv.trans (congrArg _ hphys_d0)
      · rw [hy1_vn, Function.update_self]
  · have hpot' : Succinct.slotPotential N gm' = 0 := by unfold Succinct.slotPotential; simp [hb0]
    have hpot0 : Succinct.slotPotential N gm₀ = 0 := by unfold Succinct.slotPotential; simp [hb0]
    omega

theorem pushBackSlotRegCode_exec {U V w N b q_val v_val : ℕ}
    {rB rQ rV : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 32 ≤ rB.val) (hrQ_ge : 32 ≤ rQ.val) (hrV_ge : 32 ≤ rV.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hinv : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hb : b < numBuckets N)
    (htot : Succinct.totalSlots N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) < N)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hfits : Fits w (dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem) + 1)))
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V)
    (hrB : x.regs rB = b) (hrQ : x.regs rQ = q_val) (hrV : x.regs rV = v_val) :
    let d_arg := (((0, b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg)
    let gm₀ := gmAtBit U w N x.mem
    let gm' := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w (pushBackSlotRegCode rB rQ rV) x
        (fun z =>
          z.WellFormed w ∧
          EpochRegs U V w N z ∧
          z.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N z.mem)) ∧
          FixedCoupled U V w N s' z.toBitMemoryState ∧
          (∀ a < offLM U w N, z.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm₀ + 3300 := by
  intro d_arg s' gm₀ gm'
  by_cases hb0 : bucketBits N = 0
  · exact pushBackSlotRegCode_single_exec hrQ_ge hrV_ge hw hN_pos hnU hU hV hb0
      hx her hcpl hb htot hsz hfits hq_lt hv_lt hrQ hrV
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hgm0_eq : gm₀ = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
    have hinv₀ : Succinct.SlotStoreInv N gm₀ := hgm0_eq ▸ hinv
    have hr0_lt : gm₀ (Succinct.gmRIdx b) < 2 * slabSize N := by
      have := (hinv₀.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this; rwa [ite_eq_right hb0] at this
    obtain ⟨hres1, _, _, _, hgm1_eq, htail1, hslab1, htot1, hqb1, hrb1, hother1, _⟩ :=
      Succinct.pushBackTailWriteProg_effect (U := U) (V := V) (h_space := Succinct.hashSpace U w N)
        hw hb_pos s_fix hinv hb htot hq_lt hv_lt
    set s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.pushBackTailWriteProg U V w N (Succinct.hashSpace U w N) d_arg)
    set gm₁ := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem
    have hfit_0 : Fits w 0 := fits_zero w
    have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
      rw [hsz]; exact Nat.le_add_right _ _
    have hfit_2K : Fits w (slabSize N + slabSize N) := by
      have h2K : slabSize N + slabSize N ≤ globalMetaLen N := by
        have := Succinct.tailCapPerBucket_le_globalMetaLen hb_pos
        unfold tailCapPerBucket at this; rw [ite_eq_right hb0] at this; omega
      exact fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz_meta h2K
    have h245 : x.regs 245 = bucketBits N := (her.active hN_pos).1
    set s0 := x.set 14 0
    have hs0_wf : s0.WellFormed w := wf_set 14 hx hfit_0
    have hs0_er : EpochRegs U V w N s0 := her.set_of_outside (by decide) 0
    have hc_not0 : ¬BitRAM.CondHolds (.eq 245 14) s0 := by
      change s0.regs 245 ≠ s0.regs 14
      simp +decide [s0, BitRAM.Data.set, h245, hb0]
    by_cases hprom : gm₀ (Succinct.gmRIdx b) + 1 = 2 * slabSize N
    · refine ⟨1967 * slabSize N + 1333, ?_, ?_⟩
      · unfold pushBackSlotRegCode
        refine DemonicExecWithin.step_const (T := 1967 * slabSize N + 1332) hfit_0 ?_
        refine dExec_branch_neg (T := 1967 * slabSize N + 1330) hc_not0 ?_
        refine .seq (T₁ := 11) (T₂ := 1967 * slabSize N + 1319)
          (computeGMBasesRegCode_gmBases hw hN_pos hb_pos hs0_wf hs0_er hsz_meta)
          (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_gb, hy1_regs⟩ => ?_) (by omega)
        have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
        have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
        have hy1_rB : y1.regs rB = b := by
          rw [hy1_regs rB (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrB]
        have hy1_rQ : y1.regs rQ = q_val := by
          rw [hy1_regs rQ (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrQ]
        have hy1_rV : y1.regs rV = v_val := by
          rw [hy1_regs rV (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrV]
        refine .seq (T₁ := 684) (T₂ := 1967 * slabSize N + 635)
          (pushBackTailWriteRegCode_exec (by omega) (by omega) (by omega)
            hw hN_pos hnU hU hV hb_pos hb hy1_wf hy1_er hy1_gb
            (by rw [hy1_st]; exact hcpl) hinv htot (by rw [hy1_sz, hy1_mem, hsz])
            (by rw [hy1_mem]; exact hfits) hq_lt hv_lt hy1_rB hy1_rQ hy1_rV)
          (fun y2 ⟨hy2_wf, hy2_er, hy2_gb, hy2_cpl, hy2_sz, hy2_27, hy2_low, hy2_regs⟩ => ?_)
          (by omega)
        have hy2_250 : y2.regs 250 = slabSize N := (hy2_er.active hN_pos).2.2.2.2.2.1
        refine step_dExec_bin (v := slabSize N + slabSize N) (T := 1967 * slabSize N + 634)
          (by simp +decide [BinOp.eval, hy2_250]) hfit_2K ?_
        set s2 := y2.set 28 (slabSize N + slabSize N)
        have hs2_wf : s2.WellFormed w := wf_set 28 hy2_wf hfit_2K
        have hs2_er : EpochRegs U V w N s2 :=
          hy2_er.congr_regs (fun r hr1 _ => by
            dsimp only [s2, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
        have hs2_gb : GMBasesLoaded N s2 :=
          hy2_gb.congr_regs (fun r hr1 hr2 => by
            dsimp only [s2, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
        have hc_prom : BitRAM.CondHolds (.eq 27 28) s2 := by
          change s2.regs 27 = s2.regs 28
          simp only [s2, BitRAM.Data.set, Function.update_self,
            Function.update_of_ne (by decide : (27 : Fin 280) ≠ 28), hy2_27, hres1, ← hgm0_eq]
          omega
        refine dExec_branch_pos (T := 1967 * slabSize N + 633) hc_prom ?_
        have htot0_lt : gm₀ 0 * slabSize N + gm₀ 1 < N := by
          rw [← hgm0_eq] at htot; unfold Succinct.totalSlots at htot; rwa [ite_eq_right hb0] at htot
        have hpre_prom : Succinct.PromoteSlabInv U V w N (Succinct.hashSpace U w N) 0 b s₁ := by
          refine ⟨hb, htail1, hslab1, ?_, fun b' hb' hne => ?_, ?_⟩
          · change gm₁ (Succinct.gmRIdx b) = 2 * slabSize N
            rw [hrb1, ← hgm0_eq, hprom]
          · change gm₁ (Succinct.gmRIdx b') < tailCapPerBucket N ∧
              (0 < gm₁ (Succinct.gmQIdx b') → 1 ≤ gm₁ (Succinct.gmRIdx b'))
            rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
            exact hinv.multi_r_bounds hb_pos b' hb'
          · change gm₁ 0 * slabSize N + gm₁ 1 ≤ N
            rw [htot1, ← hgm0_eq]; omega
        have hs2_low : ∀ a < offLM U w N, y2.mem a = x.mem a :=
          fun a ha => (hy2_low a ha).trans (congrFun hy1_mem a)
        have hs2_rB : s2.regs rB = b := by
          dsimp only [s2, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hy2_regs rB (by omega), hy1_rB]
        refine (promoteSlabRegCode_exec (rB := rB) (by omega) hw hN_pos hnU hU hV hb_pos
          hs2_wf hs2_er hs2_gb
          (by change y2.mem 2 = _; rw [hs2_low 2 (by unfold offLM offHash; omega), hm2])
          (by change y2.mem 3 = _; rw [hs2_low 3 (by unfold offLM offHash; omega), hm3])
          hpre_prom hy2_cpl
          (by change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y2.mem)) ≤ y2.bitSize
              rw [hy2_sz]) hs2_rB).mono
          (fun z ⟨hz_wf, hz_er, _, hz_sz, hz_cpl, hz_low, hz_regs⟩ => ?_) (by omega)
        have hs'_eq : s' = (Memory.spec 0).clientState s₁
            (Succinct.promoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b)) := by
          change (Memory.spec 0).clientState s_fix
            (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = _
          unfold Succinct.pushBackSlotProg
          simp only [hb0, ↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, hres1, ← hgm0_eq, ite_eq_left hprom]
        have htot_prom := Succinct.promoteSlabProg_tot_eq hw hb_pos s₁ hpre_prom
        have hz_gm : gmAtBit U w N z.mem =
            Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N)
              ((Memory.spec 0).clientState s₁
                (Succinct.promoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b))).mem :=
          hz_cpl.gm_eq
        have hy2_gm : gmAtBit U w N y2.mem =
            Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem :=
          hy2_cpl.gm_eq
        have htot_z : Succinct.totalSlots N (gmAtBit U w N z.mem) =
            Succinct.totalSlots N (gmAtBit U w N y2.mem) := by
          unfold Succinct.totalSlots
          rw [ite_eq_right hb0, ite_eq_right hb0, hz_gm, hy2_gm, htot_prom]
        refine ⟨hz_wf, hz_er, by rw [hz_sz, htot_z]; exact hy2_sz,
          by rw [hs'_eq]; exact hz_cpl,
          fun a ha => (hz_low a (by unfold offGM; omega)).trans (hs2_low a ha),
          fun r hr => (hz_regs r hr).trans (by
            dsimp only [s2, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; subst h; omega), hy2_regs r (by omega),
              hy1_regs r (Or.inr (by omega))]
            dsimp only [s0, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; subst h; omega)])⟩
      · have hs'_eq : s' = (Memory.spec 0).clientState s₁
            (Succinct.promoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b)) := by
          change (Memory.spec 0).clientState s_fix
            (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = _
          unfold Succinct.pushBackSlotProg
          simp only [hb0, ↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, hres1, ← hgm0_eq, ite_eq_left hprom]
        have htot0_lt : gm₀ 0 * slabSize N + gm₀ 1 < N := by
          rw [← hgm0_eq] at htot; unfold Succinct.totalSlots at htot; rwa [ite_eq_right hb0] at htot
        have hpre_prom : Succinct.PromoteSlabInv U V w N (Succinct.hashSpace U w N) 0 b s₁ := by
          refine ⟨hb, htail1, hslab1, ?_, fun b' hb' hne => ?_, ?_⟩
          · change gm₁ (Succinct.gmRIdx b) = 2 * slabSize N
            rw [hrb1, ← hgm0_eq, hprom]
          · change gm₁ (Succinct.gmRIdx b') < tailCapPerBucket N ∧
              (0 < gm₁ (Succinct.gmQIdx b') → 1 ≤ gm₁ (Succinct.gmRIdx b'))
            rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
            exact hinv.multi_r_bounds hb_pos b' hb'
          · change gm₁ 0 * slabSize N + gm₁ 1 ≤ N
            rw [htot1, ← hgm0_eq]; omega
        obtain ⟨_, _, _, _, hqb2, hrb2, hother2, _⟩ :=
          Succinct.promoteSlabProg_effect hw hb_pos s₁ hpre_prom
        rw [← hs'_eq] at hqb2 hrb2 hother2
        have hupd : gm' (Succinct.gmQIdx b) =
              (pushBackCounts (slabSize N) (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
            gm' (Succinct.gmRIdx b) =
              (pushBackCounts (slabSize N)
                (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
          unfold pushBackCounts; rw [ite_eq_left hprom]
          exact ⟨by dsimp only [gm', gm₁] at hqb2 hqb1 ⊢; rw [hqb2, hqb1, ← hgm0_eq], hrb2⟩
        have hother_all : ∀ b' < numBuckets N, b' ≠ b →
            gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
            gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
          fun b' hb' hne => ⟨(hother2 b' hb' hne).1.trans ((hother1 b' hb' hne).1.trans
              (congrFun hgm0_eq.symm _)),
            (hother2 b' hb' hne).2.trans ((hother1 b' hb' hne).2.trans
              (congrFun hgm0_eq.symm _))⟩
        have hpot := Succinct.slotPotential_pushBack_le hb_pos hb hr0_lt hupd hother_all
        have hwork : pushBackWork (slabSize N) (gm₀ (Succinct.gmRIdx b)) = slabSize N := by
          unfold pushBackWork; rw [ite_eq_left hprom]
        rw [hwork] at hpot
        omega
    · refine ⟨702, ?_, ?_⟩
      · unfold pushBackSlotRegCode
        refine DemonicExecWithin.step_const (T := 701) hfit_0 ?_
        refine dExec_branch_neg (T := 699) hc_not0 ?_
        refine .seq (T₁ := 11) (T₂ := 688)
          (computeGMBasesRegCode_gmBases hw hN_pos hb_pos hs0_wf hs0_er hsz_meta)
          (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_gb, hy1_regs⟩ => ?_) (by omega)
        have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
        have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
        have hy1_rB : y1.regs rB = b := by
          rw [hy1_regs rB (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrB]
        have hy1_rQ : y1.regs rQ = q_val := by
          rw [hy1_regs rQ (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrQ]
        have hy1_rV : y1.regs rV = v_val := by
          rw [hy1_regs rV (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrV]
        refine .seq (T₁ := 684) (T₂ := 4)
          (pushBackTailWriteRegCode_exec (by omega) (by omega) (by omega)
            hw hN_pos hnU hU hV hb_pos hb hy1_wf hy1_er hy1_gb
            (by rw [hy1_st]; exact hcpl) hinv htot (by rw [hy1_sz, hy1_mem, hsz])
            (by rw [hy1_mem]; exact hfits) hq_lt hv_lt hy1_rB hy1_rQ hy1_rV)
          (fun y2 ⟨hy2_wf, hy2_er, hy2_gb, hy2_cpl, hy2_sz, hy2_27, hy2_low, hy2_regs⟩ => ?_)
          (by omega)
        have hy2_250 : y2.regs 250 = slabSize N := (hy2_er.active hN_pos).2.2.2.2.2.1
        refine step_dExec_bin (v := slabSize N + slabSize N) (T := 3)
          (by simp +decide [BinOp.eval, hy2_250]) hfit_2K ?_
        set s2 := y2.set 28 (slabSize N + slabSize N)
        have hs2_wf : s2.WellFormed w := wf_set 28 hy2_wf hfit_2K
        have hs2_er : EpochRegs U V w N s2 :=
          hy2_er.congr_regs (fun r hr1 _ => by
            dsimp only [s2, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
        have hc_nprom : ¬BitRAM.CondHolds (.eq 27 28) s2 := by
          change s2.regs 27 ≠ s2.regs 28
          simp only [s2, BitRAM.Data.set, Function.update_self,
            Function.update_of_ne (by decide : (27 : Fin 280) ≠ 28), hy2_27, hres1, ← hgm0_eq]
          omega
        refine dExec_branch_neg (T := 1) hc_nprom (nopRegCode_exec ?_)
        have hs'_eq : s' = s₁ := by
          change (Memory.spec 0).clientState s_fix
            (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = s₁
          unfold Succinct.pushBackSlotProg
          simp only [hb0, ↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, hres1, ← hgm0_eq, ite_eq_right hprom]
          rfl
        refine ⟨hs2_wf, hs2_er, hy2_sz, by rw [hs'_eq]; exact hy2_cpl,
          fun a ha => (hy2_low a ha).trans (congrFun hy1_mem a),
          fun r hr => by
            dsimp only [s2, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; subst h; omega), hy2_regs r (by omega),
              hy1_regs r (Or.inr (by omega))]
            dsimp only [s0, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; subst h; omega)]⟩
      · have hs'_eq : s' = s₁ := by
          change (Memory.spec 0).clientState s_fix
            (Succinct.pushBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = s₁
          unfold Succinct.pushBackSlotProg
          simp only [hb0, ↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, hres1, ← hgm0_eq, ite_eq_right hprom]
          rfl
        have hgm'_eq : gm' = gm₁ := by dsimp only [gm', gm₁]; rw [hs'_eq]
        have hupd : gm' (Succinct.gmQIdx b) =
              (pushBackCounts (slabSize N) (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
            gm' (Succinct.gmRIdx b) =
              (pushBackCounts (slabSize N)
                (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
          unfold pushBackCounts; rw [ite_eq_right hprom, hgm'_eq]
          exact ⟨by rw [hqb1, ← hgm0_eq], by rw [hrb1, ← hgm0_eq]⟩
        have hother_all : ∀ b' < numBuckets N, b' ≠ b →
            gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
            gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
          fun b' hb' hne => ⟨by rw [hgm'_eq, (hother1 b' hb' hne).1, ← hgm0_eq],
            by rw [hgm'_eq, (hother1 b' hb' hne).2, ← hgm0_eq]⟩
        have hpot := Succinct.slotPotential_pushBack_le hb_pos hb hr0_lt hupd hother_all
        have hwork : pushBackWork (slabSize N) (gm₀ (Succinct.gmRIdx b)) = 0 := by
          unfold pushBackWork; rw [ite_eq_right hprom]
        rw [hwork] at hpot
        omega

/-! ## Section 2: `popBackSlotRegCode` and `popBackSlotRegCode_exec` -/

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.popBackSlotProg`:
in the single-bucket regime (`bucketBits N = 0`), decrements `gm 0` and pops the last dense item;
in the multi-bucket regime (`0 < bucketBits N`), runs `removeLastTailRightRegCode` and conditionally
demotes the top full slab via `demoteSlabRegCode` when `r_b - 1 = 0 ∧ 0 < q_b` (`32 ≤ rB`). -/
@[expose]
def popBackSlotRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 14 0))
  (.branch (.eq 245 14)
    (.seq (readGMConstRegCode 0 28)
    (.seq (.op (.const 14 1))
    (.seq (.op (.bin .sub 28 28 14))
    (.seq (writeGMConstRegCode 0 28)
          popDenseRegCode))))
    (.seq computeGMBasesRegCode
    (.seq (removeLastTailRightRegCode rB)
    (.seq (readGMBucketRegCode 1 rB 27)
    (.seq (readGMBucketRegCode 0 rB 28)
    (.seq (.op (.const 29 0))
    (.branch (.eq 27 29)
      (.branch (.lt 29 28)
        (demoteSlabRegCode rB)
        nopRegCode)
      nopRegCode)))))))

private theorem popBackSlotRegCode_single_exec {U V w N b : ℕ}
    {rB : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb0 : bucketBits N = 0)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hinv : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ Succinct.bCount N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem))) :
    let d_arg := (0, b)
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.popBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg)
    let gm₀ := gmAtBit U w N x.mem
    let gm' := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w (popBackSlotRegCode rB) x
        (fun z =>
          z.WellFormed w ∧
          EpochRegs U V w N z ∧
          z.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N z.mem)) ∧
          FixedCoupled U V w N s' z.toBitMemoryState ∧
          (∀ a < offLM U w N, z.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm₀ + 4802 := by
  intro d_arg s' gm₀ gm'
  have hb_eq : b = 0 := by
    have : numBuckets N = 1 := by simp [numBuckets, hb0]
    omega
  subst hb_eq
  have hgm0_eq : gm₀ = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
  have hbc0 : 1 ≤ gm₀ 0 := by
    rw [← hgm0_eq] at hbc; unfold Succinct.bCount at hbc; simpa [hb0] using hbc
  have hc_le : gm₀ 0 ≤ N := (hgm0_eq ▸ hinv).single_valid hb0
  have htot_eq : Succinct.totalSlots N gm₀ = gm₀ 0 := by
    unfold Succinct.totalSlots; rw [ite_eq_left hb0]
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
    rw [hsz]; exact Nat.le_add_right _ _
  have hfit_0 : Fits w 0 := fits_zero w
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_sub : Fits w (gm₀ 0 - 1) := fits_of_le_N hw hnU hU (by omega)
  have hc1_lt : gm₀ 0 - 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have h245 : x.regs 245 = 0 := by rw [(her.active hN_pos).1, hb0]
  refine ⟨132, ?_, ?_⟩
  · unfold popBackSlotRegCode
    refine DemonicExecWithin.step_const (T := 131) hfit_0 ?_
    set s0 := x.set 14 0
    have hs0_wf : s0.WellFormed w := wf_set 14 hx hfit_0
    have hs0_er : EpochRegs U V w N s0 := her.set_of_outside (by decide) 0
    have hc : BitRAM.CondHolds (.eq 245 14) s0 := by
      change s0.regs 245 = s0.regs 14
      simp +decide [s0, BitRAM.Data.set, h245]
    have hs0_mem : s0.mem = x.mem := rfl
    refine dExec_branch_pos (T := 130) hc ?_
    refine .seq (T₁ := 46) (T₂ := 84)
      (readGMConstRegCode_exec (idx := 0) (rDst := 28) (by decide) (by decide) (by decide)
        hw hN_pos hnU hU hs0_wf hs0_er hsz_meta)
      (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_28, hy1_regs⟩ => ?_) (by omega)
    have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
    have hy1_28_val : y1.regs 28 = gm₀ 0 := by rw [hy1_28, hs0_mem]
    refine DemonicExecWithin.step_const (T := 83) hfit_1 ?_
    refine step_dExec_bin (v := gm₀ 0 - 1) (T := 82)
      (by simp +decide [BinOp.eval, BitRAM.Data.set, hy1_28_val]) hfit_sub ?_
    set s2 := (y1.set 14 1).set 28 (gm₀ 0 - 1)
    have hs2_wf : s2.WellFormed w := wf_set 28 (wf_set 14 hy1_wf hfit_1) hfit_sub
    have hs2_er : EpochRegs U V w N s2 :=
      hy1_er.congr_regs (fun r hr1 _ => by
        dsimp only [s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    refine .seq (T₁ := 57) (T₂ := 25)
      (writeGMConstRegCode_exec (idx := 0) (rVal := 28) (by decide) (by decide)
        hw hN_pos hnU hU hs2_wf hs2_er
        (by change epochMetaBits U w N ≤ y1.bitSize; rw [hy1_sz]; exact hsz_meta)
        (by simp +decide [s2, BitRAM.Data.set]) hc1_lt)
      (fun y3 ⟨hy3_sz, hy3_wf, hy3_er, hy3_gm, hy3_lm, hy3_td, hy3_dt, hy3_out, hy3_items,
        hy3_regs⟩ => ?_)
      (by omega)
    have hy3_sz_x : y3.bitSize = itemBitOff U V w N (gm₀ 0 - 1 + 1) := by
      rw [hy3_sz]; change y1.bitSize = _; rw [hy1_sz, hsz, htot_eq, Nat.sub_add_cancel hbc0]; rfl
    refine (popDenseRegCode_exec (n_t := gm₀ 0 - 1) hw (le_of_lt hU) hV hy3_wf hy3_er hy3_sz_x).mono
      (fun z ⟨_, hz_wf, hz_er, hz_sz, hz_items, hz_meta, hz_regs⟩ => ?_) (by omega)
    have hz_low_y3 : ∀ a < epochMetaWords U w N, z.mem a = y3.mem a := hz_meta
    obtain ⟨hz_lm, hz_gm, hz_td, hz_dt, _⟩ := meta_eq_of_low_words_eq hw hN_pos hz_low_y3
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    obtain ⟨_, _, hq1, hv1, hl1, hg1⟩ :=
      Succinct.writeGMProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
        hw h0_lt hc1_lt s_fix
    set s_wg := (Memory.spec 0).clientState s_fix
      (Succinct.writeGMProg U V w N (Succinct.hashSpace U w N) ((0, 0), gm₀ 0 - 1))
    have hs'_eq : s' = s_wg := by
      change (Memory.spec 0).clientState s_fix
        (Succinct.popBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = s_wg
      unfold Succinct.popBackSlotProg
      simp only [hb0, ↓reduceIte, d_arg]
      rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg,
        Succinct.clientResult_readGMProg s_fix h0_lt, ← hgm0_eq]
    have hgm_z : gmAtBit U w N z.mem = Function.update gm₀ 0 (gm₀ 0 - 1) := by
      rw [hz_gm, hy3_gm]; change Function.update (gmAtBit U w N y1.mem) 0 (gm₀ 0 - 1) = _
      rw [hy1_mem]
    have hgm_s' : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s'.mem =
        Function.update gm₀ 0 (gm₀ 0 - 1) := by
      rw [hs'_eq, hg1, ← hgm0_eq]
    have htot_z : Succinct.totalSlots N (gmAtBit U w N z.mem) = gm₀ 0 - 1 := by
      unfold Succinct.totalSlots; simp [hb0, hgm_z]
    have hgm_z1 : gmAtBit U w N z.mem 1 = gm₀ 1 := by
      rw [hgm_z, Function.update_of_ne (by decide)]
    have hM0 : maxTailItems N = 0 := by simp [maxTailItems, tailCapPerBucket, hb0]
    have hgm0_1 : gm₀ 1 = 0 := by
      by_contra hpos
      have := hcpl.win_inv.td_lt 0 (Nat.pos_of_ne_zero hpos)
      omega
    have htd_z : tdAtBit U w N z.mem = tdAtBit U w N x.mem := by
      rw [hz_td, hy3_td]; exact congrArg (tdAtBit U w N) hy1_mem
    have hdt_z : dtAtBit U w N z.mem = dtAtBit U w N x.mem := by
      rw [hz_dt, hy3_dt]; exact congrArg (dtAtBit U w N) hy1_mem
    refine ⟨hz_wf, hz_er, by rw [hz_sz, htot_z]; rfl,
      ⟨hgm_z.trans hgm_s'.symm,
       by dsimp only [BitRAM.Data.toBitMemoryState]
          rw [hz_lm, hy3_lm]; change lmAtBit U w N y1.mem = _
          rw [hy1_mem, hs'_eq, hl1]
          exact hcpl.lm_eq,
       by dsimp only [BitRAM.Data.toBitMemoryState]
          rw [hgm_z1, hgm0_1]
          exact ⟨fun _ h => by omega, fun _ h => by omega,
            fun _ h => by omega, fun _ _ _ => by omega⟩,
       fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_z]; exact hcpl.td_lt i,
       fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hdt_z]; exact hcpl.dt_lt i,
       fun d hd => ?_, fun d hd => ?_⟩,
      fun a ha => by
        rw [hz_low_y3 a (by
              rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD offGM; omega),
          hy3_out a (Or.inl (by unfold offGM; omega))]
        exact congrFun hy1_mem a,
      fun r hr => by
        rw [hz_regs r (by omega), hy3_regs r (by omega)]
        dsimp only [s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy1_regs r (by omega) (by intro h; subst h; omega)]
        dsimp only [s0, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; subst h; omega)]⟩
    · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
      rw [htot_z] at hd
      change denseQuotAt U V w N z.toBitMemoryState d =
        Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s'.mem
          (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
      have hphys_d :
          physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d = d := by
        unfold physByBase; simp [hb0]
      have hphys_d0 : physByBase N (gm₀ 0 * slabSize N) (dtAtBit U w N x.mem) d = d := by
        unfold physByBase; simp [hb0]
      rw [(hz_items d hd).1, (hy3_items d).1]
      change denseQuotAt U V w N y1.toBitMemoryState d = _
      rw [hy1_st, hs'_eq, hq1, hphys_d]
      have hq := hcpl.quot_eq d (by change d < Succinct.totalSlots N gm₀; rw [htot_eq]; omega)
      exact hq.trans (congrArg _ hphys_d0)
    · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
      rw [htot_z] at hd
      change denseValAt U V w N z.toBitMemoryState d =
        Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
          (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
      have hphys_d :
          physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d = d := by
        unfold physByBase; simp [hb0]
      have hphys_d0 : physByBase N (gm₀ 0 * slabSize N) (dtAtBit U w N x.mem) d = d := by
        unfold physByBase; simp [hb0]
      rw [(hz_items d hd).2, (hy3_items d).2]
      change denseValAt U V w N y1.toBitMemoryState d = _
      rw [hy1_st, hs'_eq, hv1, hphys_d]
      have hv := hcpl.val_eq d (by change d < Succinct.totalSlots N gm₀; rw [htot_eq]; omega)
      exact hv.trans (congrArg _ hphys_d0)
  · have hpot' : Succinct.slotPotential N gm' = 0 := by unfold Succinct.slotPotential; simp [hb0]
    have hpot0 : Succinct.slotPotential N gm₀ = 0 := by unfold Succinct.slotPotential; simp [hb0]
    omega

theorem popBackSlotRegCode_exec {U V w N b : ℕ}
    {rB : Fin 280} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 32 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hinv : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ Succinct.bCount N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hrB : x.regs rB = b) :
    let d_arg := (0, b)
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.popBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg)
    let gm₀ := gmAtBit U w N x.mem
    let gm' := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
    ∃ T,
      BitRAM.DemonicExecWithin w (popBackSlotRegCode rB) x
        (fun z =>
          z.WellFormed w ∧
          EpochRegs U V w N z ∧
          z.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N z.mem)) ∧
          FixedCoupled U V w N s' z.toBitMemoryState ∧
          (∀ a < offLM U w N, z.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r)) T ∧
      T + 1967 * Succinct.slotPotential N gm' ≤
        1967 * Succinct.slotPotential N gm₀ + 4802 := by
  intro d_arg s' gm₀ gm'
  by_cases hb0 : bucketBits N = 0
  · exact popBackSlotRegCode_single_exec hw hN_pos hnU hU hV hb0 hx her hcpl hinv hb hbc hsz
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hgm0_eq : gm₀ = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
    have hinv₀ : Succinct.SlotStoreInv N gm₀ := hgm0_eq ▸ hinv
    have hbc₀ : 1 ≤ Succinct.bCount N gm₀ b := hgm0_eq ▸ hbc
    have hr0_pos : 1 ≤ gm₀ (Succinct.gmRIdx b) :=
      Succinct.pos_gmRIdx_of_pos_bCount hb_pos hinv₀ hb hbc₀
    have hr0_lt : gm₀ (Succinct.gmRIdx b) < 2 * slabSize N := by
      have := (hinv₀.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this; rwa [ite_eq_right hb0] at this
    have htail₀ := hinv₀.multi_tail hb_pos
    have hslab₀ := hinv₀.multi_slab hb_pos
    have htot₀ := hinv₀.multi_total_le hb_pos
    have htot_le : Succinct.totalSlots N gm₀ ≤ N := by
      unfold Succinct.totalSlots; rwa [ite_eq_right hb0]
    obtain ⟨_, _, _, _, _, hgm1_eq⟩ :=
      Succinct.removeLastTailItemProg_effect (U := U) (V := V)
        (h_space := Succinct.hashSpace U w N) hw hb_pos hb s_fix (hgm0_eq ▸ htail₀)
        (hgm0_eq ▸ hr0_pos)
    set s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.removeLastTailItemProg U V w N (Succinct.hashSpace U w N) d_arg)
    set gm₁ := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem
    have hgm1_rem : gm₁ = Succinct.gmRemoveTail N gm₀ b := by
      rw [hgm0_eq]; exact hgm1_eq
    have hpres1 := Succinct.gmRemoveTail_preserves_nonTail hb hr0_pos htail₀
    have htail1 : Succinct.TailBijection N gm₁ (fun b' => gm₁ (Succinct.gmRIdx b')) (gm₁ 1) := by
      rw [hgm1_rem]; exact Succinct.tailBijection_gmRemoveTail hb hr0_pos htail₀
    have hslab1 : Succinct.SlabBijection N gm₁ (fun b' => gm₁ (Succinct.gmQIdx b')) (gm₁ 0) := by
      rw [hgm1_rem]; exact (Succinct.slabBijection_gmRemoveTail hb hr0_pos htail₀ hslab₀).2
    have hqb1 : gm₁ (Succinct.gmQIdx b) = gm₀ (Succinct.gmQIdx b) := by
      rw [hgm1_rem, hpres1.2.2.2.2.1 b hb]
    have hrb1 : gm₁ (Succinct.gmRIdx b) = gm₀ (Succinct.gmRIdx b) - 1 := by
      rw [hgm1_rem, hpres1.2.2.1]
    have hother1 : ∀ b' < numBuckets N, b' ≠ b →
        gm₁ (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
        gm₁ (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
      fun b' hb' hne => ⟨by rw [hgm1_rem, hpres1.2.2.2.2.1 b' hb'],
        by rw [hgm1_rem, hpres1.2.2.2.1 b' hb' hne]⟩
    have hgm0_1_pos : 1 ≤ gm₀ 1 :=
      le_trans hr0_pos (Succinct.r_le_ntails_of_tailBijection htail₀ hb)
    have htot1 : gm₁ 0 * slabSize N + gm₁ 1 + 1 = gm₀ 0 * slabSize N + gm₀ 1 := by
      rw [hgm1_rem, hpres1.1, hpres1.2.1]; omega
    have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
    have hq_idx_lt : 4 + 3 * b < globalMetaLen N := Succinct.gmQIdx_lt hb_pos hb
    have hres_r : (Memory.spec 0).clientResult s₁
        (Succinct.readGMProg U V w N (Succinct.hashSpace U w N) (0, 4 + 3 * b + 1)) =
        gm₁ (Succinct.gmRIdx b) :=
      Succinct.clientResult_readGMProg s₁ hr_idx_lt
    have hres_q : (Memory.spec 0).clientResult s₁
        (Succinct.readGMProg U V w N (Succinct.hashSpace U w N) (0, 4 + 3 * b)) =
        gm₁ (Succinct.gmQIdx b) :=
      Succinct.clientResult_readGMProg s₁ hq_idx_lt
    have hfit_0 : Fits w 0 := fits_zero w
    have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
      rw [hsz]; exact Nat.le_add_right _ _
    have h245 : x.regs 245 = bucketBits N := (her.active hN_pos).1
    set s0 := x.set 14 0
    have hs0_wf : s0.WellFormed w := wf_set 14 hx hfit_0
    have hs0_er : EpochRegs U V w N s0 := her.set_of_outside (by decide) 0
    have hc_not0 : ¬BitRAM.CondHolds (.eq 245 14) s0 := by
      change s0.regs 245 ≠ s0.regs 14
      simp +decide [s0, BitRAM.Data.set, h245, hb0]
    by_cases hdem : gm₀ (Succinct.gmRIdx b) = 1 ∧ 0 < gm₀ (Succinct.gmQIdx b)
    · have hr1_eq0 : gm₁ (Succinct.gmRIdx b) = 0 := by rw [hrb1, hdem.1]
      have hq1_pos : 0 < gm₁ (Succinct.gmQIdx b) := by rw [hqb1]; exact hdem.2
      have hs'_eq : s' = (Memory.spec 0).clientState s₁
          (Succinct.demoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b)) := by
        change (Memory.spec 0).clientState s_fix
          (Succinct.popBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = _
        unfold Succinct.popBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_r,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_q,
          ite_eq_left hr1_eq0, ite_eq_left hq1_pos]
      have hpre_dem : Succinct.DemoteSlabInv U V w N (Succinct.hashSpace U w N) 0 b s₁ := by
        refine ⟨hb, htail1, hslab1, hr1_eq0, hq1_pos, fun b' hb' hne => ?_, ?_⟩
        · change gm₁ (Succinct.gmRIdx b') < tailCapPerBucket N ∧
            (0 < gm₁ (Succinct.gmQIdx b') → 1 ≤ gm₁ (Succinct.gmRIdx b'))
          rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
          exact hinv₀.multi_r_bounds hb_pos b' hb'
        · change gm₁ 0 * slabSize N + gm₁ 1 ≤ N
          omega
      refine ⟨988 * slabSize N + 2836, ?_, ?_⟩
      · unfold popBackSlotRegCode
        refine DemonicExecWithin.step_const (T := 988 * slabSize N + 2835) hfit_0 ?_
        refine dExec_branch_neg (T := 988 * slabSize N + 2833) hc_not0 ?_
        refine .seq (T₁ := 11) (T₂ := 988 * slabSize N + 2822)
          (computeGMBasesRegCode_gmBases hw hN_pos hb_pos hs0_wf hs0_er hsz_meta)
          (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_gb, hy1_regs⟩ => ?_) (by omega)
        have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
        have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
        have hy1_rB : y1.regs rB = b := by
          rw [hy1_regs rB (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrB]
        refine .seq (T₁ := 1400) (T₂ := 988 * slabSize N + 1422)
          (removeLastTailRightRegCode_exec (rB := rB) (s_fix := s_fix) (by omega)
            hw hN_pos hnU hU hV hb_pos hb hy1_wf hy1_er hy1_gb
            (by rw [hy1_st]; exact hcpl) (by rw [hy1_mem]; exact htail₀)
            (by rw [hy1_mem]; exact hr0_pos) (by rw [hy1_mem, hm2]) (by rw [hy1_mem, hm3])
            (by rw [hy1_sz, hy1_mem, hsz]) (by rw [hy1_mem]; exact htot_le) hy1_rB)
          (fun y2 ⟨hy2_wf, hy2_er, hy2_gb, hy2_sz, hy2_cpl, hy2_low, hy2_regs⟩ => ?_)
          (by omega)
        have hy2_sz_meta : epochMetaBits U w N ≤ y2.bitSize := by
          rw [hy2_sz]; exact Nat.le_add_right _ _
        have hy2_rB : y2.regs rB = b := by rw [hy2_regs rB (by omega), hy1_rB]
        have hy2_gm : gmAtBit U w N y2.mem = gm₁ := hy2_cpl.gm_eq
        refine .seq (T₁ := 49) (T₂ := 988 * slabSize N + 1373)
          (readGMBucketRegCode_exec (c := 1) (rB := rB) (rDst := 27)
            (by omega) (by decide) (by decide) hw hN_pos hnU hU hy2_wf hy2_er hy2_sz_meta
            hy2_rB hr_idx_lt)
          (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_27, hy3_regs⟩ => ?_) (by omega)
        have hy3_mem : y3.mem = y2.mem := congrArg BitMemory.State.mem hy3_st
        have hy3_sz : y3.bitSize = y2.bitSize := congrArg BitMemory.State.bitSize hy3_st
        have hy3_rB : y3.regs rB = b := by
          rw [hy3_regs rB (by omega) (by intro h; subst h; omega), hy2_rB]
        refine .seq (T₁ := 49) (T₂ := 988 * slabSize N + 1324)
          (readGMBucketRegCode_exec (c := 0) (rB := rB) (rDst := 28)
            (by omega) (by decide) (by decide) hw hN_pos hnU hU hy3_wf hy3_er
            (by rw [hy3_sz]; exact hy2_sz_meta) hy3_rB
            (by rw [Nat.add_zero]; exact hq_idx_lt))
          (fun y4 ⟨hy4_st, hy4_wf, hy4_er, hy4_28, hy4_regs⟩ => ?_) (by omega)
        have hy4_st_y2 : y4.toBitMemoryState = y2.toBitMemoryState := hy4_st.trans hy3_st
        have hy4_mem : y4.mem = y2.mem := congrArg BitMemory.State.mem hy4_st_y2
        have hy4_sz : y4.bitSize = y2.bitSize := congrArg BitMemory.State.bitSize hy4_st_y2
        refine DemonicExecWithin.step_const (T := 988 * slabSize N + 1323) hfit_0 ?_
        set s4 := y4.set 29 0
        have hs4_wf : s4.WellFormed w := wf_set 29 hy4_wf hfit_0
        have hs4_er : EpochRegs U V w N s4 :=
          hy4_er.congr_regs (fun r hr1 _ => by
            dsimp only [s4, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
        have hs4_gb : GMBasesLoaded N s4 :=
          hy2_gb.congr_regs (fun r hr1 hr2 => by
            dsimp only [s4, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
              hy4_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega),
              hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)])
        have hs4_27 : s4.regs 27 = 0 := by
          dsimp only [s4, BitRAM.Data.set]
          rw [Function.update_of_ne (by decide), hy4_regs 27 (by decide) (by decide),
            hy3_27, hy2_gm]
          exact hr1_eq0
        have hs4_28 : s4.regs 28 = gm₁ (Succinct.gmQIdx b) := by
          dsimp only [s4, BitRAM.Data.set]
          rw [Function.update_of_ne (by decide), hy4_28, hy3_mem, hy2_gm]
          rfl
        have hc1 : BitRAM.CondHolds (.eq 27 29) s4 := by
          change s4.regs 27 = s4.regs 29
          rw [hs4_27]; simp +decide [s4, BitRAM.Data.set]
        have hc2 : BitRAM.CondHolds (.lt 29 28) s4 := by
          change s4.regs 29 < s4.regs 28
          rw [hs4_28]; dsimp only [s4, BitRAM.Data.set]; rw [Function.update_self]; exact hq1_pos
        refine dExec_branch_pos (T := 988 * slabSize N + 1322) hc1 ?_
        refine dExec_branch_pos (T := 988 * slabSize N + 1321) hc2 ?_
        have hs4_low : ∀ a < offGM U w N, y4.mem a = x.mem a :=
          fun a ha => (congrFun hy4_mem a).trans
            ((hy2_low a ha).trans (congrFun hy1_mem a))
        have hs4_rB : s4.regs rB = b := by
          dsimp only [s4, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega),
            hy4_regs rB (by omega) (by intro h; subst h; omega), hy3_rB]
        refine (demoteSlabRegCode_exec (rB := rB) (by omega) hw hN_pos hnU hU hV hb_pos
          hs4_wf hs4_er hs4_gb
          (by change y4.mem 2 = _; rw [hs4_low 2 (by unfold offGM offLM offHash; omega), hm2])
          (by change y4.mem 3 = _; rw [hs4_low 3 (by unfold offGM offLM offHash; omega), hm3])
          hpre_dem
          (by change FixedCoupled _ _ _ _ _ y4.toBitMemoryState; rw [hy4_st_y2]; exact hy2_cpl)
          (by change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y4.mem)) ≤ y4.bitSize
              rw [hy4_mem, hy4_sz, hy2_sz, hy2_gm]) hs4_rB).mono
          (fun z ⟨hz_wf, hz_er, _, hz_sz, hz_cpl, hz_low, hz_regs⟩ => ?_) (by omega)
        have htot_dem := Succinct.demoteSlabProg_tot_eq hw hb_pos s₁ hpre_dem
        have hz_gm : gmAtBit U w N z.mem =
            Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N)
              ((Memory.spec 0).clientState s₁
                (Succinct.demoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b))).mem :=
          hz_cpl.gm_eq
        have htot_z : Succinct.totalSlots N (gmAtBit U w N z.mem) =
            Succinct.totalSlots N gm₁ := by
          unfold Succinct.totalSlots
          rw [ite_eq_right hb0, ite_eq_right hb0, hz_gm, htot_dem]
        refine ⟨hz_wf, hz_er,
          by rw [hz_sz]; change y4.bitSize = _; rw [hy4_sz, hy2_sz, htot_z],
          by rw [hs'_eq]; exact hz_cpl,
          fun a ha =>
            (hz_low a (by unfold offGM; omega)).trans (hs4_low a (by unfold offGM; omega)),
          fun r hr => (hz_regs r hr).trans (by
            dsimp only [s4, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; subst h; omega),
              hy4_regs r (by omega) (by intro h; subst h; omega),
              hy3_regs r (by omega) (by intro h; subst h; omega),
              hy2_regs r (by omega), hy1_regs r (Or.inr (by omega))]
            dsimp only [s0, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; subst h; omega)])⟩
      · obtain ⟨_, _, _, _, hqb2, hrb2, hother2, _⟩ :=
          Succinct.demoteSlabProg_effect hw hb_pos s₁ hpre_dem
        rw [← hs'_eq] at hqb2 hrb2 hother2
        have hupd : gm' (Succinct.gmQIdx b) =
              (popBackCounts (slabSize N) (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
            gm' (Succinct.gmRIdx b) =
              (popBackCounts (slabSize N)
                (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
          unfold popBackCounts; rw [ite_eq_left hdem]
          exact ⟨by dsimp only [gm', gm₁] at hqb2 hqb1 ⊢; rw [hqb2, hqb1], hrb2⟩
        have hother_all : ∀ b' < numBuckets N, b' ≠ b →
            gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
            gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
          fun b' hb' hne => ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
            (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
        have hpot := Succinct.slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt hupd hother_all
        have hwork : popBackWork (slabSize N) (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b)) =
            slabSize N := by
          unfold popBackWork; rw [ite_eq_left hdem]
        rw [hwork] at hpot
        omega
    · have hs'_eq : s' = s₁ := by
        change (Memory.spec 0).clientState s_fix
          (Succinct.popBackSlotProg U V w N (Succinct.hashSpace U w N) d_arg) = s₁
        unfold Succinct.popBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_r,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_q]
        by_cases hr1_eq0 : gm₁ (Succinct.gmRIdx b) = 0
        · have hnot_q : ¬(0 < gm₁ (Succinct.gmQIdx b)) := by
            intro hq_pos; apply hdem
            rw [hrb1] at hr1_eq0; rw [hqb1] at hq_pos
            exact ⟨by omega, hq_pos⟩
          rw [ite_eq_left hr1_eq0, ite_eq_right hnot_q]; rfl
        · rw [ite_eq_right hr1_eq0]; rfl
      refine ⟨1517, ?_, ?_⟩
      · unfold popBackSlotRegCode
        refine DemonicExecWithin.step_const (T := 1516) hfit_0 ?_
        refine dExec_branch_neg (T := 1514) hc_not0 ?_
        refine .seq (T₁ := 11) (T₂ := 1503)
          (computeGMBasesRegCode_gmBases hw hN_pos hb_pos hs0_wf hs0_er hsz_meta)
          (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_gb, hy1_regs⟩ => ?_) (by omega)
        have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
        have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
        have hy1_rB : y1.regs rB = b := by
          rw [hy1_regs rB (Or.inr (by omega))]
          dsimp only [s0, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; subst h; omega), hrB]
        refine .seq (T₁ := 1400) (T₂ := 103)
          (removeLastTailRightRegCode_exec (rB := rB) (s_fix := s_fix) (by omega)
            hw hN_pos hnU hU hV hb_pos hb hy1_wf hy1_er hy1_gb
            (by rw [hy1_st]; exact hcpl) (by rw [hy1_mem]; exact htail₀)
            (by rw [hy1_mem]; exact hr0_pos) (by rw [hy1_mem, hm2]) (by rw [hy1_mem, hm3])
            (by rw [hy1_sz, hy1_mem, hsz]) (by rw [hy1_mem]; exact htot_le) hy1_rB)
          (fun y2 ⟨hy2_wf, hy2_er, hy2_gb, hy2_sz, hy2_cpl, hy2_low, hy2_regs⟩ => ?_)
          (by omega)
        have hy2_sz_meta : epochMetaBits U w N ≤ y2.bitSize := by
          rw [hy2_sz]; exact Nat.le_add_right _ _
        have hy2_rB : y2.regs rB = b := by rw [hy2_regs rB (by omega), hy1_rB]
        have hy2_gm : gmAtBit U w N y2.mem = gm₁ := hy2_cpl.gm_eq
        refine .seq (T₁ := 49) (T₂ := 54)
          (readGMBucketRegCode_exec (c := 1) (rB := rB) (rDst := 27)
            (by omega) (by decide) (by decide) hw hN_pos hnU hU hy2_wf hy2_er hy2_sz_meta
            hy2_rB hr_idx_lt)
          (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_27, hy3_regs⟩ => ?_) (by omega)
        have hy3_mem : y3.mem = y2.mem := congrArg BitMemory.State.mem hy3_st
        have hy3_sz : y3.bitSize = y2.bitSize := congrArg BitMemory.State.bitSize hy3_st
        have hy3_rB : y3.regs rB = b := by
          rw [hy3_regs rB (by omega) (by intro h; subst h; omega), hy2_rB]
        refine .seq (T₁ := 49) (T₂ := 5)
          (readGMBucketRegCode_exec (c := 0) (rB := rB) (rDst := 28)
            (by omega) (by decide) (by decide) hw hN_pos hnU hU hy3_wf hy3_er
            (by rw [hy3_sz]; exact hy2_sz_meta) hy3_rB
            (by rw [Nat.add_zero]; exact hq_idx_lt))
          (fun y4 ⟨hy4_st, hy4_wf, hy4_er, hy4_28, hy4_regs⟩ => ?_) (by omega)
        have hy4_st_y2 : y4.toBitMemoryState = y2.toBitMemoryState := hy4_st.trans hy3_st
        have hy4_mem : y4.mem = y2.mem := congrArg BitMemory.State.mem hy4_st_y2
        have hy4_sz : y4.bitSize = y2.bitSize := congrArg BitMemory.State.bitSize hy4_st_y2
        refine DemonicExecWithin.step_const (T := 4) hfit_0 ?_
        set s4 := y4.set 29 0
        have hs4_wf : s4.WellFormed w := wf_set 29 hy4_wf hfit_0
        have hs4_er : EpochRegs U V w N s4 :=
          hy4_er.congr_regs (fun r hr1 _ => by
            dsimp only [s4, BitRAM.Data.set]
            rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
        have hs4_post :
            s4.WellFormed w ∧
            EpochRegs U V w N s4 ∧
            s4.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N s4.mem)) ∧
            FixedCoupled U V w N s' s4.toBitMemoryState ∧
            (∀ a < offLM U w N, s4.mem a = x.mem a) ∧
            (∀ r : Fin 280, 32 ≤ r.val → s4.regs r = x.regs r) := by
          refine ⟨hs4_wf, hs4_er,
            by change y4.bitSize =
                 dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y4.mem))
               rw [hy4_sz, hy4_mem, hy2_sz, hy2_gm],
            by change FixedCoupled U V w N s' y4.toBitMemoryState
               rw [hs'_eq, hy4_st_y2]; exact hy2_cpl,
            fun a ha => (congrFun hy4_mem a).trans
              ((hy2_low a (by unfold offGM; omega)).trans (congrFun hy1_mem a)),
            fun r hr => by
              dsimp only [s4, BitRAM.Data.set]
              rw [Function.update_of_ne (by intro h; subst h; omega),
                hy4_regs r (by omega) (by intro h; subst h; omega),
                hy3_regs r (by omega) (by intro h; subst h; omega),
                hy2_regs r (by omega), hy1_regs r (Or.inr (by omega))]
              dsimp only [s0, BitRAM.Data.set]
              rw [Function.update_of_ne (by intro h; subst h; omega)]⟩
        by_cases hc1 : BitRAM.CondHolds (.eq 27 29) s4
        · have hc1_eq : gm₁ (Succinct.gmRIdx b) = 0 := by
            change s4.regs 27 = s4.regs 29 at hc1
            dsimp only [s4, BitRAM.Data.set] at hc1
            rw [Function.update_of_ne (by decide), Function.update_self,
              hy4_regs 27 (by decide) (by decide), hy3_27, hy2_gm] at hc1
            exact hc1
          have hc2_neg : ¬BitRAM.CondHolds (.lt 29 28) s4 := by
            change ¬(s4.regs 29 < s4.regs 28)
            dsimp only [s4, BitRAM.Data.set]
            rw [Function.update_self, Function.update_of_ne (by decide), hy4_28,
              hy3_mem, hy2_gm]
            intro hq_pos
            apply hdem
            rw [Nat.add_zero] at hq_pos
            change 0 < gm₁ (Succinct.gmQIdx b) at hq_pos
            rw [hrb1] at hc1_eq; rw [hqb1] at hq_pos
            exact ⟨by omega, hq_pos⟩
          exact (dExec_branch_pos (T := 3) hc1
            (dExec_branch_neg (T := 1) hc2_neg (nopRegCode_exec hs4_post))).mono
            (fun _ h => h) (by omega)
        · exact (dExec_branch_neg (T := 1) hc1 (nopRegCode_exec hs4_post)).mono
            (fun _ h => h) (by omega)
      · have hgm'_eq : gm' = gm₁ := by dsimp only [gm', gm₁]; rw [hs'_eq]
        have hupd : gm' (Succinct.gmQIdx b) =
              (popBackCounts (slabSize N) (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
            gm' (Succinct.gmRIdx b) =
              (popBackCounts (slabSize N)
                (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
          unfold popBackCounts; rw [ite_eq_right hdem, hgm'_eq]
          exact ⟨hqb1, hrb1⟩
        have hother_all : ∀ b' < numBuckets N, b' ≠ b →
            gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
            gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
          fun b' hb' hne => by rw [hgm'_eq]; exact hother1 b' hb' hne
        have hpot := Succinct.slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt hupd hother_all
        have hwork :
            popBackWork (slabSize N) (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b)) = 0 := by
          unfold popBackWork; rw [ite_eq_right hdem]
        rw [hwork] at hpot
        omega


end Cslib.DataStructure.Dictionary.BitResizable
