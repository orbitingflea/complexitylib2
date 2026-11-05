/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.SlabPoolOps
public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps

/-!
# Uniform `BitRAM` Tail-Write, Tail-Remove, and Slab-Promotion Operations

This module implements uniform `BitRAM.Code .standard 280` programs that maintain lockstep
`WindowCoupled` / `FixedCoupled` coupling with the fixed-capacity reference `Memory.Prog`
operations:
* `pushBackTailWriteRegCode`: lockstep with `Succinct.pushBackTailWriteProg`;
* `removeLastTailCopyRegCode` and `removeLastTailRightRegCode`: lockstep with
  `Succinct.removeLastTailItemProg`;
* `promoteStepRegCode` and `promoteSlabRegCode`: lockstep with `Succinct.promoteStepProg` and
  `Succinct.promoteSlabProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Tail-to-Dense Physical Slot Bijection Lemmas -/

theorem physByBase_denseOfCirc_td {N b_win n_win t : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N)
    (hw_inv : WindowInv (maxTailItems N) b_win n_win td dt)
    (ht : t < n_win) :
    let d := denseOfCirc (maxTailItems N) b_win (td t)
    b_win ≤ d ∧ d < b_win + n_win ∧ physByBase N b_win dt d = N - 1 - t := by
  intro d
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM : 0 < maxTailItems N := by
    have := hw_inv.td_lt t ht
    omega
  have hlo : b_win ≤ d := denseOfCirc_ge (maxTailItems N) b_win (td t)
  have hhi : d < b_win + n_win := hw_inv.dense_lt t ht
  refine ⟨hlo, hhi, ?_⟩
  unfold physByBase
  rw [ite_eq_right hb0, ite_eq_right (by omega : ¬ d < b_win)]
  have hmod : d % maxTailItems N = td t := denseOfCirc_mod hM (hw_inv.td_lt t ht)
  rw [hmod, hw_inv.dt_td t ht]

theorem physByBase_eq_sub_iff_eq_denseOfCirc {N b_win n_win t d : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N)
    (hw_inv : WindowInv (maxTailItems N) b_win n_win td dt)
    (hwin_le : b_win + n_win ≤ N)
    (hn_le_M : n_win ≤ maxTailItems N)
    (ht : t < n_win) (hd : d < b_win + n_win) :
    physByBase N b_win dt d = N - 1 - t ↔
      d = denseOfCirc (maxTailItems N) b_win (td t) := by
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM : 0 < maxTailItems N := by omega
  constructor
  · intro hphys
    unfold physByBase at hphys
    rw [ite_eq_right hb0] at hphys
    split_ifs at hphys with hd_lt
    · omega
    · have hlo : b_win ≤ d := Nat.le_of_not_lt hd_lt
      have hown := hw_inv.owner_valid d hlo hd
      have hdt_lt : dt (d % maxTailItems N) < n_win := hown.1
      have hdt_eq : dt (d % maxTailItems N) = t := by omega
      have htd_eq : td t = d % maxTailItems N := by rw [← hdt_eq, hown.2]
      rw [htd_eq]
      exact (denseOfCirc_mod_self hM hlo (by omega)).symm
  · rintro rfl
    exact (physByBase_denseOfCirc_td hb_pos hw_inv ht).2.2

theorem physByBase_eq_self_iff_of_lt {N b_win n_win g d : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N)
    (hw_inv : WindowInv (maxTailItems N) b_win n_win td dt)
    (hwin_le : b_win + n_win ≤ N)
    (hg : g < b_win) (hd : d < b_win + n_win) :
    physByBase N b_win dt d = g ↔ d = g := by
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  constructor
  · intro hphys
    unfold physByBase at hphys
    rw [ite_eq_right hb0] at hphys
    split_ifs at hphys with hd_lt
    · exact hphys
    · have hlo : b_win ≤ d := Nat.le_of_not_lt hd_lt
      have hdt_lt : dt (d % maxTailItems N) < n_win := (hw_inv.owner_valid d hlo hd).1
      omega
  · rintro rfl
    unfold physByBase
    rw [ite_eq_right hb0, ite_eq_left hg]

theorem windowCoupled_read_tail {U V w N b_win n_win t : ℕ}
    {s_fix : Memory.State} {s_bit : BitMemory.State}
    (hb_pos : 0 < bucketBits N)
    (hc : WindowCoupled U V w N b_win n_win (b_win + n_win) s_fix s_bit)
    (ht : t < n_win) :
    let d := denseOfCirc (maxTailItems N) b_win (tdAtBit U w N s_bit.mem t)
    b_win ≤ d ∧ d < b_win + n_win ∧
    denseQuotAt U V w N s_bit d =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem (N - 1 - t) ∧
    denseValAt U V w N s_bit d =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem (N - 1 - t) := by
  intro d
  obtain ⟨hlo, hhi, hphys⟩ := physByBase_denseOfCirc_td hb_pos hc.win_inv ht
  refine ⟨hlo, hhi, ?_, ?_⟩
  · rw [hc.quot_eq d hhi, hphys]
  · rw [hc.val_eq d hhi, hphys]

/-! ## Section 2: `pushBackTailWriteRegCode` (lockstep with `Succinct.pushBackTailWriteProg`) -/

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.pushBackTailWriteProg` on
`((0, b), q_val, v_val)` when `0 < bucketBits N`:
1. Appends `(q_val, v_val)` to dense slot `m = gm 0 * K + gm 1` via `appendDenseRegCode rQ rV`.
2. Computes `b_win = gm 0 * K` in `r26` and `n_win = gm 1` in `r27`, then runs
   `winGrowRightRegCode 26 27`.
3. Runs `gmAppendTailRegCode rB`.
4. Reads the updated `gm' (gmRIdx b)` into `r27` (`28 ≤ rB, rQ, rV`, `T = 684`). -/
@[expose]
def pushBackTailWriteRegCode (rB rQ rV : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (appendDenseRegCode rQ rV)
  (.seq (readGMConstRegCode 0 26)
  (.seq (.op (.bin .mul 26 26 250))
  (.seq (readGMConstRegCode 1 27)
  (.seq (winGrowRightRegCode 26 27)
  (.seq (gmAppendTailRegCode rB)
        (readGMBucketRegCode 1 rB 27))))))

theorem pushBackTailWriteRegCode_exec {U V w N b q_val v_val : ℕ}
    {rB rQ rV : Fin 280} {x : BitRAM.Data 280} {s_fix : Memory.State}
    (hrB_ge : 28 ≤ rB.val) (hrQ_ge : 28 ≤ rQ.val) (hrV_ge : 28 ≤ rV.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hinv : Succinct.SlotStoreInv N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem))
    (htot : Succinct.totalSlots N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) < N)
    (hsz : x.bitSize = dictBitSize U V w N
      (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (hfits : Fits w (dictBitSize U V w N
      (Succinct.totalSlots N (gmAtBit U w N x.mem) + 1)))
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V)
    (hrB : x.regs rB = b) (hrQ : x.regs rQ = q_val) (hrV : x.regs rV = v_val) :
    let d_arg := (((0, b), q_val), v_val)
    let s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.pushBackTailWriteProg U V w N (Succinct.hashSpace U w N) d_arg)
    BitRAM.DemonicExecWithin w (pushBackTailWriteRegCode rB rQ rV) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        FixedCoupled U V w N s₁ z.toBitMemoryState ∧
        z.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N z.mem)) ∧
        z.regs 27 = (Memory.spec 0).clientResult s_fix
          (Succinct.pushBackTailWriteProg U V w N (Succinct.hashSpace U w N) d_arg) ∧
        (∀ a < offLM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 28 ≤ r.val → z.regs r = x.regs r)) 684 := by
  intro d_arg s₁
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  set gm₀ := gmAtBit U w N x.mem
  have hgm0_eq : gm₀ = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
  have hinv₀ : Succinct.SlotStoreInv N gm₀ := hgm0_eq ▸ hinv
  have htot₀ : Succinct.totalSlots N gm₀ < N := hgm0_eq ▸ htot
  set b_win := gm₀ 0 * slabSize N
  set n_win := gm₀ 1
  have htot_eq : Succinct.totalSlots N gm₀ = b_win + n_win := by
    unfold Succinct.totalSlots; rw [ite_eq_right hb0]
  have hbn_lt : b_win + n_win < N := htot_eq ▸ htot₀
  have htail₀ := hinv₀.multi_tail hb_pos
  have hr_lt : gm₀ (Succinct.gmRIdx b) < tailCapPerBucket N :=
    (hinv₀.multi_r_bounds hb_pos b hb).1
  have ht_lt : n_win < maxTailItems N :=
    Succinct.ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  have hsz_off : x.bitSize = itemBitOff U V w N (b_win + n_win) := by
    rw [hsz, htot_eq]; rfl
  have hfits_off : Fits w (itemBitOff U V w N (b_win + n_win + 1)) := by
    rw [← htot_eq] at *; exact hfits
  unfold pushBackTailWriteRegCode
  refine .seq (T₁ := 96) (T₂ := 588)
    (appendDenseRegCode_frame (by omega) (by omega) hw hN_pos (le_of_lt hU) hV
      hx her hsz_off hrQ hrV hq_lt hv_lt hfits_off)
    (fun y1 ⟨hy1_wf, hy1_er, hy1_sz, hy1_qn, hy1_vn, hy1_items,
      hy1_lm, hy1_gm, hy1_td, hy1_dt, hy1_out, hy1_regs⟩ => ?_) (by omega)
  have hy1_gb : GMBasesLoaded N y1 :=
    hgb.congr_regs (fun r hr1 _ => hy1_regs r (by omega))
  have hy1_sz_meta : epochMetaBits U w N ≤ y1.bitSize := by
    rw [hy1_sz]; exact Nat.le_add_right _ _
  refine .seq (T₁ := 46) (T₂ := 542)
    (readGMConstRegCode_exec (idx := 0) (rDst := 26) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy1_wf hy1_er hy1_sz_meta)
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_26, hy2_regs⟩ => ?_) (by omega)
  have hy2_mem : y2.mem = y1.mem := congrArg BitMemory.State.mem hy2_st
  have hy2_sz : y2.bitSize = y1.bitSize := congrArg BitMemory.State.bitSize hy2_st
  have hy2_250 : y2.regs 250 = slabSize N := (hy2_er.active hN_pos).2.2.2.2.2.1
  have hy2_26_val : y2.regs 26 = gm₀ 0 := by rw [hy2_26, hy1_gm]
  have hfit_bwin : Fits w b_win := fits_of_le_N hw hnU hU (by omega)
  refine step_dExec_bin (v := b_win) (T := 541)
    (by simp [BinOp.eval, hy2_26_val, hy2_250, b_win]) hfit_bwin ?_
  set s2 := y2.set 26 b_win
  have hs2_wf : s2.WellFormed w := wf_set 26 hy2_wf hfit_bwin
  have hs2_er : EpochRegs U V w N s2 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _)
  refine .seq (T₁ := 46) (T₂ := 495)
    (readGMConstRegCode_exec (idx := 1) (rDst := 27) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hs2_wf hs2_er
      (by change epochMetaBits U w N ≤ y2.bitSize; rw [hy2_sz]; exact hy1_sz_meta))
    (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_27, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_y1 : y3.toBitMemoryState = y1.toBitMemoryState := hy3_st.trans hy2_st
  have hy3_mem : y3.mem = y1.mem := congrArg BitMemory.State.mem hy3_st_y1
  have hy3_sz : y3.bitSize = y1.bitSize := congrArg BitMemory.State.bitSize hy3_st_y1
  have hy3_26 : y3.regs 26 = b_win := by
    rw [hy3_regs 26 (by decide) (by decide)]; simp +decide [s2, BitRAM.Data.set]
  have hy3_27_val : y3.regs 27 = n_win := by
    rw [hy3_27]; change gmAtBit U w N y2.mem 1 = n_win; rw [hy2_mem, hy1_gm]
  refine .seq (T₁ := 115) (T₂ := 380)
    (winGrowRightRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hb_pos
      hy3_wf hy3_er (by rw [hy3_sz]; exact hy1_sz_meta) (by omega) (by omega)
      hy3_26 hy3_27_val)
    (fun y4 ⟨hy4_sz, hy4_wf, hy4_er, hy4_td, hy4_dt, hy4_gm, hy4_lm, hy4_out, hy4_items,
      hy4_regs⟩ => ?_)
    (by omega)
  have hy4_gb : GMBasesLoaded N y4 :=
    hy1_gb.congr_regs (fun r hr1 hr2 => by
      rw [hy4_regs r (by omega), hy3_regs r (by omega) (by intro h; subst h; omega)]
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; subst h; omega),
        hy2_regs r (by omega) (by intro h; subst h; omega)])
  have hy4_rB : y4.regs rB = b := by
    rw [hy4_regs rB (by omega), hy3_regs rB (by omega) (by intro h; subst h; omega)]
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; subst h; omega),
      hy2_regs rB (by omega) (by intro h; subst h; omega),
      hy1_regs rB (by omega), hrB]
  have hy4_gm0 : gmAtBit U w N y4.mem = gm₀ := by rw [hy4_gm, hy3_mem, hy1_gm]
  refine .seq (T₁ := 331) (T₂ := 49)
    (gmAppendTailRegCode_exec (by omega) hw hN_pos hnU hU hb_pos hb hy4_wf hy4_er hy4_gb
      (by rw [hy4_sz, hy3_sz]; exact hy1_sz_meta) hy4_rB
      (by rw [hy4_gm0]; exact htail₀) (by rw [hy4_gm0]; exact hr_lt))
    (fun y5 ⟨hy5_sz, hy5_wf, hy5_er, hy5_gb, hy5_gm, hy5_lm, hy5_td, hy5_dt,
      hy5_out, hy5_items, hy5_regs⟩ => ?_) (by omega)
  have hy5_rB : y5.regs rB = b := by rw [hy5_regs rB (by omega), hy4_rB]
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
  refine (readGMBucketRegCode_exec (c := 1) (rB := rB) (rDst := 27)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hy5_wf hy5_er
    (by rw [hy5_sz, hy4_sz, hy3_sz]; exact hy1_sz_meta) hy5_rB hr_idx_lt).mono
    (fun z ⟨hz_st, hz_wf, hz_er, hz_27, hz_regs⟩ => ?_) le_rfl
  have hz_mem : z.mem = y5.mem := congrArg BitMemory.State.mem hz_st
  have hz_sz : z.bitSize = y5.bitSize := congrArg BitMemory.State.bitSize hz_st
  have hz_gb : GMBasesLoaded N z :=
    hy5_gb.congr_regs (fun r hr1 hr2 => hz_regs r (by omega) (by intro h; subst h; omega))
  obtain ⟨hres_app, _, _, hq_app, hv_app, hl_app, hgm_app⟩ :=
    Succinct.appendTailItemProg_effect (base := 0) (U := U) (V := V)
      (h_space := Succinct.hashSpace U w N) hw hb_pos hb s_fix (hgm0_eq ▸ htail₀) (hgm0_eq ▸ hr_lt)
  set s_app := (Memory.spec 0).clientState s_fix
    (Succinct.appendTailItemProg U V w N (Succinct.hashSpace U w N) (0, b))
  set g_new := (N - 1) - gm₀ 1
  have hg_new_lt : g_new < N := by omega
  obtain ⟨_, _, hq_wq, hv_wq, hl_wq, hgm_wq⟩ :=
    Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hg_new_lt hq_lt s_app
  set s_wq := (Memory.spec 0).clientState s_app
    (Succinct.writeQuotProg U w N (Succinct.hashSpace U w N) ((0, g_new), q_val))
  obtain ⟨_, _, hq_wv, hv_wv, hl_wv, hgm_wv⟩ :=
    Succinct.writeValProg_effect (base := 0) (h_space := Succinct.hashSpace U w N)
      hw hg_new_lt hv_lt s_wq
  set s_wv := (Memory.spec 0).clientState s_wq
    (Succinct.writeValProg U V w N (Succinct.hashSpace U w N) ((0, g_new), v_val))
  have hs1_eq : s₁ = s_wv := by
    change (Memory.spec 0).clientState s_fix
      (Succinct.pushBackTailWriteProg U V w N (Succinct.hashSpace U w N) d_arg) = s_wv
    unfold Succinct.pushBackTailWriteProg
    dsimp only [d_arg]
    rw [StateTransitionSpec.clientState_bind, hres_app, ← hgm0_eq,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      Succinct.clientState_readGMProg]
  have hgm_z : gmAtBit U w N z.mem = Succinct.gmAppendTail N gm₀ b := by
    rw [hz_mem, hy5_gm, hy4_gm0]
  have hgm_s1 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem =
      Succinct.gmAppendTail N gm₀ b := by
    rw [hs1_eq, hgm_wv, hgm_wq, hgm_app, ← hgm0_eq]
  have hpres := Succinct.gmAppendTail_preserves_nonTail gm₀ hb hr_lt ht_lt
  have hres_s1 : (Memory.spec 0).clientResult s_fix
      (Succinct.pushBackTailWriteProg U V w N (Succinct.hashSpace U w N) d_arg) =
      gmAtBit U w N z.mem (4 + 3 * b + 1) := by
    unfold Succinct.pushBackTailWriteProg
    dsimp only [d_arg]
    rw [StateTransitionSpec.clientResult_bind, hres_app, ← hgm0_eq,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      Succinct.clientResult_readGMProg s_wv hr_idx_lt, ← hs1_eq, hgm_s1, hgm_z]
  have htot_z : Succinct.totalSlots N (gmAtBit U w N z.mem) = b_win + n_win + 1 := by
    unfold Succinct.totalSlots
    rw [ite_eq_right hb0, hgm_z, hpres.1, hpres.2.1]
    dsimp only [b_win, n_win]; omega
  have hM_pos : 0 < maxTailItems N := Nat.zero_le n_win |>.trans_lt ht_lt
  have hmax_M : max (maxTailItems N) 1 = maxTailItems N := max_eq_left hM_pos
  have hwin_z := winGrowRight_spec hcpl.win_inv ht_lt
    (fun i => hmax_M ▸ hcpl.td_lt i) (fun i => hmax_M ▸ hcpl.dt_lt i)
  have htd_z : tdAtBit U w N z.mem =
      (winGrowRight (maxTailItems N) b_win n_win
        (tdAtBit U w N x.mem, dtAtBit U w N x.mem)).1 := by
    rw [hz_mem, hy5_td, hy4_td, hy3_mem, hy1_td, hy1_dt]
  have hdt_z : dtAtBit U w N z.mem =
      (winGrowRight (maxTailItems N) b_win n_win
        (tdAtBit U w N x.mem, dtAtBit U w N x.mem)).2 := by
    rw [hz_mem, hy5_dt, hy4_dt, hy3_mem, hy1_td, hy1_dt]
  obtain ⟨hphys_new, hphys_old⟩ :=
    physByBase_winGrowRight (td := tdAtBit U w N x.mem) (dt := dtAtBit U w N x.mem)
      hb_pos (by omega : n_win + 1 ≤ maxTailItems N)
  refine ⟨hz_wf, hz_er, hz_gb,
    ⟨hgm_z.trans hgm_s1.symm,
     by dsimp only [BitRAM.Data.toBitMemoryState]
        rw [hz_mem, hy5_lm, hy4_lm, hy3_mem, hy1_lm, hs1_eq, hl_wv, hl_wq, hl_app]
        exact hcpl.lm_eq,
     by dsimp only [BitRAM.Data.toBitMemoryState]
        rw [hgm_z, hpres.1, hpres.2.1, htd_z, hdt_z]; exact hwin_z.1,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_z, hmax_M]; exact hwin_z.2.1 i,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hdt_z, hmax_M]; exact hwin_z.2.2 i,
     fun d hd => ?_, fun d hd => ?_⟩,
    by rw [hz_sz, hy5_sz, hy4_sz, hy3_sz, hy1_sz, htot_z]; rfl,
    by rw [hz_27, ← hz_mem, hres_s1],
    fun a ha => by
      rw [hz_mem, hy5_out a (Or.inl (by unfold offGM; omega)),
        hy4_out a (by unfold offTD offGM; omega),
        hy3_mem, hy1_out a ha],
    fun r hr => by
      rw [hz_regs r (by omega) (by intro h; subst h; omega),
        hy5_regs r (by omega), hy4_regs r (by omega),
        hy3_regs r (by omega) (by intro h; subst h; omega)]
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; subst h; omega),
        hy2_regs r (by omega) (by intro h; subst h; omega),
        hy1_regs r (by omega)]⟩
  · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
    rw [htot_z] at hd
    change denseQuotAt U V w N z.toBitMemoryState d =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s₁.mem
        (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
    rw [hgm_z, hpres.1, hdt_z, hz_st, (hy5_items d).1, (hy4_items d).1, hy3_st_y1,
      hs1_eq, hq_wv, hq_wq, hq_app]
    change denseQuotAt U V w N y1.toBitMemoryState d =
      Function.update (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem) g_new q_val
        (physByBase N b_win
          (winGrowRight (maxTailItems N) b_win n_win
            (tdAtBit U w N x.mem, dtAtBit U w N x.mem)).2 d)
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd_lt | rfl
    · rw [(hy1_items d hd_lt).1, hphys_old d hd_lt]
      have hne_g : physByBase N b_win (dtAtBit U w N x.mem) d ≠ g_new := by
        unfold physByBase
        rw [ite_eq_right hb0]
        split_ifs with hlt
        · dsimp only [g_new, n_win]; omega
        · have hdt_lt : dtAtBit U w N x.mem (d % maxTailItems N) < n_win :=
            (hcpl.win_inv.owner_valid d (Nat.le_of_not_lt hlt) hd_lt).1
          dsimp only [g_new, n_win]; omega
      rw [Function.update_of_ne hne_g]
      exact hcpl.quot_eq d (by change d < Succinct.totalSlots N gm₀; rw [htot_eq]; exact hd_lt)
    · rw [hy1_qn, hphys_new, Function.update_self]
  · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
    rw [htot_z] at hd
    change denseValAt U V w N z.toBitMemoryState d =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem
        (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
    rw [hgm_z, hpres.1, hdt_z, hz_st, (hy5_items d).2, (hy4_items d).2, hy3_st_y1,
      hs1_eq, hv_wv]
    change denseValAt U V w N y1.toBitMemoryState d =
      Function.update (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_wq.mem) g_new v_val
        (physByBase N b_win
          (winGrowRight (maxTailItems N) b_win n_win
            (tdAtBit U w N x.mem, dtAtBit U w N x.mem)).2 d)
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd_lt | rfl
    · rw [(hy1_items d hd_lt).2, hphys_old d hd_lt]
      have hne_g : physByBase N b_win (dtAtBit U w N x.mem) d ≠ g_new := by
        unfold physByBase
        rw [ite_eq_right hb0]
        split_ifs with hlt
        · dsimp only [g_new, n_win]; omega
        · have hdt_lt : dtAtBit U w N x.mem (d % maxTailItems N) < n_win :=
            (hcpl.win_inv.owner_valid d (Nat.le_of_not_lt hlt) hd_lt).1
          dsimp only [g_new, n_win]; omega
      rw [Function.update_of_ne hne_g, hv_wq, hv_app]
      exact hcpl.val_eq d (by change d < Succinct.totalSlots N gm₀; rw [htot_eq]; exact hd_lt)
    · rw [hy1_vn, hphys_new, Function.update_self]

/-! ## Section 3: `removeLastTailCopyRegCode` and `removeLastTailRightRegCode` -/

/-- Uniform `BitRAM.Code .standard 280` program that copies the last tail item `t_last = gm 1 - 1`
into the deleted tail slot `t_del = gm (gmTailPtrIdx N b (gm (gmRIdx b) - 1))` within a circular
window at base `b_win = x.regs rBWin`, and then updates `GlobalMeta` via `gmRemoveTailRegCode rB`
(`28 ≤ rB, rBWin`, preserving `GMBasesLoaded` and all registers `28 ≤ r.val`, `T = 835`). -/
@[expose]
def removeLastTailCopyRegCode (rB rBWin : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMBucketRegCode 1 rB 26)
  (.seq (.op (.const 14 1))
  (.seq (.op (.bin .sub 26 26 14))
  (.seq (readGM2DRegCode 23 21 rB 26 26)
  (.seq (readTDRegCode 26 26)
  (.seq (denseOfTailRegCode rBWin 26 26)
  (.seq (readGMConstRegCode 1 27)
  (.seq (.op (.const 14 1))
  (.seq (.op (.bin .sub 27 27 14))
  (.seq (readTDRegCode 27 27)
  (.seq (denseOfTailRegCode rBWin 27 27)
  (.seq (copyDenseItemRegCode 27 26)
        (gmRemoveTailRegCode rB))))))))))))

theorem removeLastTailCopyRegCode_exec {U V w N b b_win : ℕ}
    {rB rBWin : Fin 280} {x : BitRAM.Data 280} {s_fix : Memory.State}
    (hrB_ge : 28 ≤ rB.val) (hrBWin_ge : 28 ≤ rBWin.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hcpl : WindowCoupled U V w N b_win (gmAtBit U w N x.mem 1)
      (b_win + gmAtBit U w N x.mem 1) s_fix x.toBitMemoryState)
    (htail : Succinct.TailBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmRIdx b'))
      (gmAtBit U w N x.mem 1))
    (hr_pos : 1 ≤ gmAtBit U w N x.mem (Succinct.gmRIdx b))
    (hm_le_N : b_win + gmAtBit U w N x.mem 1 ≤ N)
    (hsz : itemBitOff U V w N (b_win + gmAtBit U w N x.mem 1) ≤ x.bitSize)
    (hrB : x.regs rB = b) (hrBWin : x.regs rBWin = b_win) :
    let s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.removeLastTailItemProg U V w N (Succinct.hashSpace U w N) (0, b))
    BitRAM.DemonicExecWithin w (removeLastTailCopyRegCode rB rBWin) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        z.bitSize = x.bitSize ∧
        gmAtBit U w N z.mem = Succinct.gmRemoveTail N (gmAtBit U w N x.mem) b ∧
        WindowCoupled U V w N b_win (gmAtBit U w N x.mem 1)
          (b_win + gmAtBit U w N x.mem 1) s₁ z.toBitMemoryState ∧
        (∀ a < offGM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 28 ≤ r.val → z.regs r = x.regs r)) 866 := by
  intro s₁
  set gm₀ := gmAtBit U w N x.mem
  set n_win := gm₀ 1
  set m_items := b_win + n_win
  set r_del := gm₀ (Succinct.gmRIdx b) - 1
  set t_del := gm₀ (Succinct.gmTailPtrIdx N b r_del)
  set t_last := n_win - 1
  set M := maxTailItems N
  set td₀ := tdAtBit U w N x.mem
  set dt₀ := dtAtBit U w N x.mem
  set d_del := denseOfCirc M b_win (td₀ t_del)
  set d_last := denseOfCirc M b_win (td₀ t_last)
  have hr_del_lt : r_del < gm₀ (Succinct.gmRIdx b) := by omega
  have hr_del_cap : r_del < tailCapPerBucket N := lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have ht_del_lt : t_del < n_win := htail.ptr_lt b hb r_del hr_del_lt
  have ht_last_lt : t_last < n_win := by omega
  have hn_le_M : n_win ≤ M := htail.ntails_le
  have ht_del_M : t_del < M := lt_of_lt_of_le ht_del_lt hn_le_M
  have ht_last_M : t_last < M := lt_of_lt_of_le ht_last_lt hn_le_M
  have hc_del_M : td₀ t_del < M := hcpl.win_inv.td_lt t_del ht_del_lt
  have hc_last_M : td₀ t_last < M := hcpl.win_inv.td_lt t_last ht_last_lt
  obtain ⟨hd_del_lo, hd_del_hi, hphys_del⟩ :=
    physByBase_denseOfCirc_td hb_pos hcpl.win_inv ht_del_lt
  obtain ⟨hd_last_lo, hd_last_hi, hphys_last⟩ :=
    physByBase_denseOfCirc_td hb_pos hcpl.win_inv ht_last_lt
  have hd_del_m : d_del < m_items := hd_del_hi
  have hd_last_m : d_last < m_items := hd_last_hi
  have hd_del_N : d_del ≤ N := le_of_lt (lt_of_lt_of_le hd_del_m hm_le_N)
  have hd_last_N : d_last ≤ N := le_of_lt (lt_of_lt_of_le hd_last_m hm_le_N)
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
  have hptr_del_lt :
      Succinct.gmTailPtrBase N + b * tailCapPerBucket N + r_del < globalMetaLen N := by
    have h := Succinct.gmTailPtrIdx_lt hb_pos hb hr_del_cap
    unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx at h; omega
  have hptr_eq : Succinct.gmTailPtrBase N + b * tailCapPerBucket N + r_del =
      Succinct.gmTailPtrIdx N b r_del := by
    unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx; omega
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_rdel : Fits w r_del :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz_meta (by omega)
  have hfit_tlast : Fits w t_last := fits_of_le_N hw hnU hU (by omega)
  unfold removeLastTailCopyRegCode
  refine .seq (T₁ := 49) (T₂ := 817)
    (readGMBucketRegCode_exec (c := 1) (rB := rB) (rDst := 26)
      (by omega) (by decide) (by decide) hw hN_pos hnU hU hx her hsz_meta hrB hr_idx_lt)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_26, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_26_val : y1.regs 26 = gm₀ (Succinct.gmRIdx b) := hy1_26
  refine DemonicExecWithin.step_const (T := 816) hfit_1 ?_
  refine step_dExec_bin (v := r_del) (T := 815)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy1_26_val, r_del]) hfit_rdel ?_
  set s2 := (y1.set 14 1).set 26 r_del
  have hs2_wf : s2.WellFormed w := wf_set 26 (wf_set 14 hy1_wf hfit_1) hfit_rdel
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_23 : s2.regs 23 = Succinct.gmTailPtrBase N := by
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy1_regs 23 (by decide) (by decide)]
    exact hgb.2.2.2.1
  have hs2_21 : s2.regs 21 = tailCapPerBucket N := by
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy1_regs 21 (by decide) (by decide)]
    exact hgb.2.1
  have hs2_rB : s2.regs rB = b := by
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; subst h; omega)]
    rw [hy1_regs rB (by omega) (by intro h; subst h; omega), hrB]
  refine .seq (T₁ := 48) (T₂ := 766)
    (readGM2DRegCode_exec (rBase := 23) (rStride := 21) (rB := rB) (rK := 26) (rDst := 26)
      (by decide) (by decide) (by omega) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hs2_wf hs2_er
      (by change epochMetaBits U w N ≤ y1.bitSize; rw [hy1_sz]; exact hsz_meta)
      hs2_23 hs2_21 hs2_rB (by simp +decide [s2, BitRAM.Data.set]) hptr_del_lt)
    (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_26, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy1_st
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
  have hy3_26_val : y3.regs 26 = t_del := by
    rw [hy3_26, hptr_eq]
    exact congrArg (fun m => gmAtBit U w N m (Succinct.gmTailPtrIdx N b r_del)) hy1_mem
  refine .seq (T₁ := 45) (T₂ := 721)
    (readTDRegCode_exec (rIdx := 26) (rDst := 26) (by decide)
      hw hN_pos hnU hU hy3_wf hy3_er ht_del_M hy3_26_val (by rw [hy3_sz]; exact hsz_meta))
    (fun y4 ⟨hy4_st, hy4_wf, hy4_26, hy4_regs⟩ => ?_) (by omega)
  have hy4_st_x : y4.toBitMemoryState = x.toBitMemoryState := hy4_st.trans hy3_st_x
  have hy4_mem : y4.mem = x.mem := congrArg BitMemory.State.mem hy4_st_x
  have hy4_sz : y4.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy4_st_x
  have hy4_er : EpochRegs U V w N y4 :=
    hy3_er.congr_regs (fun r hr1 _ =>
      hy4_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy4_26_val : y4.regs 26 = td₀ t_del := by
    rw [hy4_26, hy3_mem]
  have hy4_rBWin : y4.regs rBWin = b_win := by
    rw [hy4_regs rBWin (by omega) (by intro h; subst h; omega),
      hy3_regs rBWin (by omega) (by intro h; subst h; omega)]
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; subst h; omega)]
    rw [hy1_regs rBWin (by omega) (by intro h; subst h; omega), hrBWin]
  refine .seq (T₁ := 5) (T₂ := 716)
    (denseOfTailRegCode_exec (rB := rBWin) (rC := 26) (rDst := 26)
      (by omega) (by decide) hw hN_pos hnU hU hb_pos hy4_wf hy4_er
      (by rw [hy4_sz]; exact hsz_meta) hd_del_N hc_del_M hy4_rBWin hy4_26_val)
    (fun y5 ⟨hy5_st, hy5_wf, hy5_26, hy5_regs⟩ => ?_) (by omega)
  have hy5_st_x : y5.toBitMemoryState = x.toBitMemoryState := hy5_st.trans hy4_st_x
  have hy5_mem : y5.mem = x.mem := congrArg BitMemory.State.mem hy5_st_x
  have hy5_sz : y5.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy5_st_x
  have hy5_er : EpochRegs U V w N y5 :=
    hy4_er.congr_regs (fun r hr1 _ =>
      hy5_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  refine .seq (T₁ := 46) (T₂ := 670)
    (readGMConstRegCode_exec (idx := 1) (rDst := 27) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy5_wf hy5_er (by rw [hy5_sz]; exact hsz_meta))
    (fun y6 ⟨hy6_st, hy6_wf, hy6_er, hy6_27, hy6_regs⟩ => ?_) (by omega)
  have hy6_st_x : y6.toBitMemoryState = x.toBitMemoryState := hy6_st.trans hy5_st_x
  have hy6_mem : y6.mem = x.mem := congrArg BitMemory.State.mem hy6_st_x
  have hy6_sz : y6.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy6_st_x
  have hy6_27_val : y6.regs 27 = n_win := by rw [hy6_27, hy5_mem]
  refine DemonicExecWithin.step_const (T := 669) hfit_1 ?_
  refine step_dExec_bin (v := t_last) (T := 668)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy6_27_val, t_last]) hfit_tlast ?_
  set s7 := (y6.set 14 1).set 27 t_last
  have hs7_wf : s7.WellFormed w := wf_set 27 (wf_set 14 hy6_wf hfit_1) hfit_tlast
  have hs7_er : EpochRegs U V w N s7 :=
    hy6_er.congr_regs (fun r hr1 _ => by
      dsimp only [s7, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 45) (T₂ := 623)
    (readTDRegCode_exec (rIdx := 27) (rDst := 27) (by decide)
      hw hN_pos hnU hU hs7_wf hs7_er ht_last_M (by simp +decide [s7, BitRAM.Data.set])
      (by change epochMetaBits U w N ≤ y6.bitSize; rw [hy6_sz]; exact hsz_meta))
    (fun y8 ⟨hy8_st, hy8_wf, hy8_27, hy8_regs⟩ => ?_) (by omega)
  have hy8_st_x : y8.toBitMemoryState = x.toBitMemoryState := hy8_st.trans hy6_st_x
  have hy8_mem : y8.mem = x.mem := congrArg BitMemory.State.mem hy8_st_x
  have hy8_sz : y8.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy8_st_x
  have hy8_er : EpochRegs U V w N y8 :=
    hs7_er.congr_regs (fun r hr1 _ =>
      hy8_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy8_27_val : y8.regs 27 = td₀ t_last := by
    rw [hy8_27]; exact congrArg (fun m => tdAtBit U w N m t_last) hy6_mem
  have hy8_rBWin : y8.regs rBWin = b_win := by
    rw [hy8_regs rBWin (by omega) (by intro h; subst h; omega)]
    dsimp only [s7, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; subst h; omega)]
    rw [hy6_regs rBWin (by omega) (by intro h; subst h; omega),
      hy5_regs rBWin (by omega) (by intro h; subst h; omega), hy4_rBWin]
  refine .seq (T₁ := 5) (T₂ := 618)
    (denseOfTailRegCode_exec (rB := rBWin) (rC := 27) (rDst := 27)
      (by omega) (by decide) hw hN_pos hnU hU hb_pos hy8_wf hy8_er
      (by rw [hy8_sz]; exact hsz_meta) hd_last_N hc_last_M hy8_rBWin hy8_27_val)
    (fun y9 ⟨hy9_st, hy9_wf, hy9_27, hy9_regs⟩ => ?_) (by omega)
  have hy9_st_x : y9.toBitMemoryState = x.toBitMemoryState := hy9_st.trans hy8_st_x
  have hy9_mem : y9.mem = x.mem := congrArg BitMemory.State.mem hy9_st_x
  have hy9_sz : y9.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy9_st_x
  have hy9_er : EpochRegs U V w N y9 :=
    hy8_er.congr_regs (fun r hr1 _ =>
      hy9_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy9_26 : y9.regs 26 = d_del := by
    rw [hy9_regs 26 (by decide) (by decide), hy8_regs 26 (by decide) (by decide)]
    dsimp only [s7, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy6_regs 26 (by decide) (by decide), hy5_26]
  have hy9_regs20 : ∀ r : Fin 280, 20 ≤ r.val → r ≠ 26 → r ≠ 27 → y9.regs r = x.regs r := by
    intro r hr h26 h27
    rw [hy9_regs r (by omega) h27, hy8_regs r (by omega) h27]
    dsimp only [s7, BitRAM.Data.set]
    rw [Function.update_of_ne h27,
      Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
      hy6_regs r (by omega) h27, hy5_regs r (by omega) h26,
      hy4_regs r (by omega) h26, hy3_regs r (by omega) h26]
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne h26,
      Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs r (by omega) h26]
  refine .seq (T₁ := 195) (T₂ := 423)
    (copyDenseItemRegCode_exec (rSrc := 27) (rDst := 26)
      (by decide) (by decide) hw (le_of_lt hU) hV hy9_wf hy9_er
      hd_last_m hd_del_m hy9_27 hy9_26 (by rw [hy9_sz]; exact hsz)
      (by rw [hy9_mem, hm2]) (by rw [hy9_mem, hm3]))
    (fun y10 ⟨hy10_wf, hy10_er, hy10_sz, hy10_q, hy10_v, hy10_other, hy10_meta, hy10_regs⟩ => ?_)
    (by omega)
  have hy10_sz_x : y10.bitSize = x.bitSize := hy10_sz.trans hy9_sz
  have hy10_low : ∀ a < epochMetaWords U w N, y10.mem a = x.mem a :=
    fun a ha => (hy10_meta a ha).trans (congrFun hy9_mem a)
  obtain ⟨hy10_lm, hy10_gm, hy10_td, hy10_dt, hy10_out⟩ :=
    meta_eq_of_low_words_eq hw hN_pos hy10_low
  have hy10_gb : GMBasesLoaded N y10 :=
    hgb.congr_regs (fun r hr1 hr2 =>
      (hy10_regs r hr1).trans
        (hy9_regs20 r hr1 (by intro h; subst h; omega) (by intro h; subst h; omega)))
  have hy10_rB : y10.regs rB = b := by
    rw [hy10_regs rB (by omega),
      hy9_regs20 rB (by omega) (by intro h; subst h; omega) (by intro h; subst h; omega), hrB]
  refine (gmRemoveTailRegCode_exec (rB := rB) (by omega) hw hN_pos hnU hU hb_pos hb
    hy10_wf hy10_er hy10_gb (by rw [hy10_sz_x]; exact hsz_meta) hy10_rB
    (by rw [hy10_gm]; exact htail) (by rw [hy10_gm]; exact hr_pos)).mono
    (fun z ⟨hz_sz, hz_wf, hz_er, hz_gb, hz_gm, hz_lm, hz_td, hz_dt, hz_out, hz_items,
      hz_regs⟩ => ?_) (by omega)
  have hgm_f : gm₀ = Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := hcpl.gm_eq
  have htail_f : Succinct.TailBijection N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem)
      (fun b' => Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
        (Succinct.gmRIdx b'))
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem 1) := hgm_f ▸ htail
  have hr_pos_f : 1 ≤ Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
      (Succinct.gmRIdx b) := by rw [← hgm_f]; exact hr_pos
  obtain ⟨_, _, hq_rem, hv_rem, hl_rem, hgm_rem⟩ :=
    Succinct.removeLastTailItemProg_effect (U := U) (V := V) (w := w) (n_max := N)
      (h_space := Succinct.hashSpace U w N) (base := 0) (b := b)
      hw hb_pos hb s_fix htail_f hr_pos_f
  set g_del := N - 1 - t_del
  set g_last := N - 1 - t_last
  have hq_s1 : Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s₁.mem =
      Function.update (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem) g_del
        (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_last) := by
    rw [hq_rem, ← hgm_f]
  have hv_s1 : Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem =
      Function.update (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) g_del
        (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_last) := by
    rw [hv_rem, ← hgm_f]
  have hgm_z : gmAtBit U w N z.mem = Succinct.gmRemoveTail N gm₀ b := by
    rw [hz_gm, hy10_gm]
  have hgm_s1 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem =
      Succinct.gmRemoveTail N gm₀ b := by
    rw [hgm_rem, ← hgm_f]
  have htd_z : tdAtBit U w N z.mem = td₀ := hz_td.trans hy10_td
  have hdt_z : dtAtBit U w N z.mem = dt₀ := hz_dt.trans hy10_dt
  refine ⟨hz_wf, hz_er, hz_gb, hz_sz.trans hy10_sz_x, hgm_z,
    ⟨hgm_z.trans hgm_s1.symm,
     by dsimp only [BitRAM.Data.toBitMemoryState]
        rw [hz_lm, hy10_lm, hl_rem]
        exact hcpl.lm_eq,
     by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_z, hdt_z]; exact hcpl.win_inv,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [htd_z]; exact hcpl.td_lt i,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hdt_z]; exact hcpl.dt_lt i,
     fun d hd => ?_, fun d hd => ?_⟩,
    fun a ha => (hz_out a (Or.inl ha)).trans (hy10_low a (by
      rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega)),
    fun r hr => (hz_regs r (by omega)).trans
      ((hy10_regs r (by omega)).trans
        (hy9_regs20 r (by omega) (by intro h; subst h; omega) (by intro h; subst h; omega)))⟩
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hdt_z]
    change denseQuotAt U V w N z.toBitMemoryState d =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s₁.mem (physByBase N b_win dt₀ d)
    rw [(hz_items d).1, hq_s1]
    change physByBase N b_win dt₀ d_del = g_del at hphys_del
    change physByBase N b_win dt₀ d_last = g_last at hphys_last
    by_cases heq : d = d_del
    · subst heq
      rw [hy10_q, hy9_st_x, hphys_del, Function.update_self, hcpl.quot_eq d_last hd_last_m]
      exact congrArg (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem) hphys_last
    · obtain ⟨hq_o, _⟩ := hy10_other d hd heq
      rw [hq_o, hy9_st_x]
      have hne_g : physByBase N b_win dt₀ d ≠ g_del := fun hphys =>
        heq ((physByBase_eq_sub_iff_eq_denseOfCirc hb_pos hcpl.win_inv
          hm_le_N hn_le_M ht_del_lt hd).mp hphys)
      rw [Function.update_of_ne hne_g]
      exact hcpl.quot_eq d hd
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hdt_z]
    change denseValAt U V w N z.toBitMemoryState d =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem (physByBase N b_win dt₀ d)
    rw [(hz_items d).2, hv_s1]
    change physByBase N b_win dt₀ d_del = g_del at hphys_del
    change physByBase N b_win dt₀ d_last = g_last at hphys_last
    by_cases heq : d = d_del
    · subst heq
      rw [hy10_v, hy9_st_x, hphys_del, Function.update_self, hcpl.val_eq d_last hd_last_m]
      exact congrArg (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) hphys_last
    · obtain ⟨_, hv_o⟩ := hy10_other d hd heq
      rw [hv_o, hy9_st_x]
      have hne_g : physByBase N b_win dt₀ d ≠ g_del := fun hphys =>
        heq ((physByBase_eq_sub_iff_eq_denseOfCirc hb_pos hcpl.win_inv
          hm_le_N hn_le_M ht_del_lt hd).mp hphys)
      rw [Function.update_of_ne hne_g]
      exact hcpl.val_eq d hd

theorem physByBase_winShrinkRight_ite {N b_win n_win : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N)
    (hw : WindowInv (maxTailItems N) b_win (n_win + 1) td dt)
    (hn_lt : n_win < maxTailItems N) :
    let M := maxTailItems N
    let p' := winShrinkRight M b_win n_win (td, dt)
    let d_last := denseOfCirc M b_win (td n_win)
    ∀ d < b_win + n_win,
      physByBase N b_win p'.2 d =
        physByBase N b_win dt (if d = d_last then b_win + n_win else d) := by
  intro M p' d_last d hd
  obtain ⟨_, hlast, hother⟩ := physByBase_winShrinkRight hb_pos hw hn_lt
  by_cases heq : d = d_last
  · subst heq; rw [ite_eq_left rfl]; exact hlast
  · rw [ite_eq_right heq]; exact hother d hd heq

theorem physByBase_winShrinkLeft_ite {N b_win n_win : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N)
    (hw : WindowInv (maxTailItems N) b_win (n_win + 1) td dt)
    (hn_lt : n_win < maxTailItems N) :
    let M := maxTailItems N
    let p' := winShrinkLeft M b_win n_win (td, dt)
    let d_last := denseOfCirc M b_win (td n_win)
    physByBase N (b_win + 1) p'.2 b_win = b_win ∧
    (∀ d < b_win + 1 + n_win, d ≠ b_win →
      physByBase N (b_win + 1) p'.2 d =
        physByBase N b_win dt (if d = d_last then b_win else d)) := by
  intro M p' d_last
  obtain ⟨hd_lo, _, hlast, hother⟩ := physByBase_winShrinkLeft hb_pos hw hn_lt
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  refine ⟨by unfold physByBase; rw [ite_eq_right hb0, ite_eq_left (by omega)],
    fun d hd hne_b => ?_⟩
  by_cases heq : d = d_last
  · have hd_gt : b_win < d_last := Nat.lt_of_le_of_ne hd_lo (heq ▸ hne_b).symm
    subst heq
    rw [ite_eq_left rfl, hlast hd_gt]
    unfold physByBase
    rw [ite_eq_right hb0, ite_eq_right (by omega)]
  · rw [ite_eq_right heq]
    exact hother d hd hne_b heq

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.removeLastTailItemProg` when
the circular window is at the standard base `b_win = gm 0 * slabSize N`, followed by
`winShrinkRightRegCode`, `computeGMBasesRegCode`, and `popDenseRegCode` (`29 ≤ rB.val`,
preserving `GMBasesLoaded` and all registers `29 ≤ r.val`, `T = 1369`). -/
@[expose]
def removeLastTailRightRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMConstRegCode 0 28)
  (.seq (.op (.bin .mul 28 28 250))
  (.seq (removeLastTailCopyRegCode rB 28)
  (.seq (readGMConstRegCode 1 27)
  (.seq (winShrinkRightRegCode 28 27)
  (.seq computeGMBasesRegCode
        popDenseRegCode)))))

theorem removeLastTailRightRegCode_exec {U V w N b : ℕ} {rB : Fin 280}
    {x : BitRAM.Data 280} {s_fix : Memory.State}
    (hrB_ge : 29 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (htail : Succinct.TailBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmRIdx b'))
      (gmAtBit U w N x.mem 1))
    (hr_pos : 1 ≤ gmAtBit U w N x.mem (Succinct.gmRIdx b))
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)))
    (htot_le : Succinct.totalSlots N (gmAtBit U w N x.mem) ≤ N)
    (hrB : x.regs rB = b) :
    let s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.removeLastTailItemProg U V w N (Succinct.hashSpace U w N) (0, b))
    let m₁ := Succinct.totalSlots N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem)
    BitRAM.DemonicExecWithin w (removeLastTailRightRegCode rB) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        z.bitSize = dictBitSize U V w N m₁ ∧
        FixedCoupled U V w N s₁ z.toBitMemoryState ∧
        (∀ a < offGM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 29 ≤ r.val → z.regs r = x.regs r)) 1400 := by
  intro s₁ m₁
  set gm₀ := gmAtBit U w N x.mem
  set K := slabSize N
  set b_win := gm₀ 0 * K
  set n_win := gm₀ 1
  set m₀ := Succinct.totalSlots N gm₀
  set n_win' := n_win - 1
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by
    unfold maxTailItems tailCapPerBucket
    rw [ite_eq_right hb0]
    exact Nat.mul_pos (Nat.two_pow_pos _) (by have := slabSize_pos N; omega)
  have hm0_eq : m₀ = b_win + n_win := by
    unfold m₀ Succinct.totalSlots; rw [ite_eq_right hb0]
  have hr_le_nt : gm₀ (Succinct.gmRIdx b) ≤ n_win :=
    Succinct.r_le_ntails_of_tailBijection htail hb
  have hn_pos : 1 ≤ n_win := le_trans hr_pos hr_le_nt
  have hn_eq : n_win' + 1 = n_win := by omega
  have hn_le_M : n_win ≤ maxTailItems N := htail.ntails_le
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize := by
    rw [hsz]; exact Nat.le_add_right _ _
  have h250 : x.regs 250 = K := (her.active hN_pos).2.2.2.2.2.1
  have hfit_bwin : Fits w b_win := fits_of_le_N hw hnU hU (by omega)
  unfold removeLastTailRightRegCode
  refine .seq (T₁ := 46) (T₂ := 1354)
    (readGMConstRegCode_exec (idx := 0) (rDst := 28) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hx her hsz_meta)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_28, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_250 : y1.regs 250 = K := by
    rw [hy1_regs 250 (by decide) (by decide), h250]
  refine step_dExec_bin (v := b_win) (T := 1353)
    (by simp [BinOp.eval, hy1_28, hy1_250, b_win, gm₀, K]) hfit_bwin ?_
  set s2 := y1.set 28 b_win
  have hs2_wf : s2.WellFormed w := wf_set 28 hy1_wf hfit_bwin
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_gb : GMBasesLoaded N s2 :=
    hgb.congr_regs (fun r hr1 hr2 => by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
        hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_st : s2.toBitMemoryState = x.toBitMemoryState := hy1_st
  have hs2_mem : s2.mem = x.mem := hy1_mem
  have hs2_sz : s2.bitSize = x.bitSize := hy1_sz
  have hs2_rB : s2.regs rB = b := by
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; subst h; omega),
      hy1_regs rB (by omega) (by intro h; subst h; omega), hrB]
  have hs2_cpl : WindowCoupled U V w N b_win (gmAtBit U w N s2.mem 1)
      (b_win + gmAtBit U w N s2.mem 1) s_fix s2.toBitMemoryState := by
    rw [hs2_mem, hs2_st]
    have hwc : WindowCoupled U V w N b_win (gmAtBit U w N x.mem 1) m₀ s_fix x.toBitMemoryState :=
      hcpl
    rwa [hm0_eq] at hwc
  refine .seq (T₁ := 866) (T₂ := 487)
    (removeLastTailCopyRegCode_exec (rB := rB) (rBWin := 28)
      (by omega) (by decide) hw hN_pos hnU hU hV hb_pos hb
      hs2_wf hs2_er hs2_gb (by rw [hs2_mem, hm2]) (by rw [hs2_mem, hm3]) hs2_cpl
      (by rw [hs2_mem]; exact htail) (by rw [hs2_mem]; exact hr_pos)
      (by rw [hs2_mem]; change b_win + n_win ≤ N; omega)
      (by rw [hs2_sz, hs2_mem, hsz, hm0_eq]; exact le_rfl)
      hs2_rB (by simp +decide [s2, BitRAM.Data.set]))
    (fun y3 ⟨hy3_wf, hy3_er, hy3_gb, hy3_sz, hy3_gm0, hy3_cpl, hy3_low, hy3_regs⟩ => ?_)
    (by omega)
  have hy3_sz_x : y3.bitSize = x.bitSize := hy3_sz.trans hs2_sz
  have hy3_low_x : ∀ a < offGM U w N, y3.mem a = x.mem a :=
    fun a ha => (hy3_low a ha).trans (congrFun hs2_mem a)
  have hy3_gm : gmAtBit U w N y3.mem = Succinct.gmRemoveTail N gm₀ b := by
    rw [hy3_gm0, hs2_mem]
  have hgm_s1 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem =
      Succinct.gmRemoveTail N gm₀ b :=
    hy3_cpl.gm_eq.symm.trans hy3_gm
  have hpres_rem := Succinct.gmRemoveTail_preserves_nonTail hb hr_pos htail
  have hy3_gm_0 : gmAtBit U w N y3.mem 0 = gm₀ 0 := by rw [hy3_gm, hpres_rem.1]
  have hy3_gm_1 : gmAtBit U w N y3.mem 1 = n_win' := by rw [hy3_gm, hpres_rem.2.1]
  have hm1_eq : m₁ = b_win + n_win' := by
    unfold m₁ Succinct.totalSlots
    rw [ite_eq_right hb0, hgm_s1, hpres_rem.1, hpres_rem.2.1]
  refine .seq (T₁ := 46) (T₂ := 441)
    (readGMConstRegCode_exec (idx := 1) (rDst := 27) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy3_wf hy3_er (by rw [hy3_sz_x]; exact hsz_meta))
    (fun y4 ⟨hy4_st, hy4_wf, hy4_er, hy4_27, hy4_regs⟩ => ?_) (by omega)
  have hy4_mem : y4.mem = y3.mem := congrArg BitMemory.State.mem hy4_st
  have hy4_sz : y4.bitSize = x.bitSize :=
    (congrArg BitMemory.State.bitSize hy4_st).trans hy3_sz_x
  have hy4_27_val : y4.regs 27 = n_win' := by rw [hy4_27, hy3_gm_1]
  have hy4_28_val : y4.regs 28 = b_win := by
    rw [hy4_regs 28 (by decide) (by decide), hy3_regs 28 (by decide)]
    simp +decide [s2, BitRAM.Data.set]
  have hy4_win : WindowInv (maxTailItems N) b_win (n_win' + 1)
      (tdAtBit U w N y4.mem) (dtAtBit U w N y4.mem) := by
    rw [hy4_mem, hn_eq]
    have h := hy3_cpl.win_inv
    rwa [hs2_mem] at h
  refine .seq (T₁ := 404) (T₂ := 37)
    (winShrinkRightRegCode_exec (n_t := m₀) (b_win := b_win) (n_win := n_win')
      (rB := 28) (rN := 27) (by decide) (by decide)
      hw hN_pos hnU hU hV hb_pos hy4_wf hy4_er
      (by rw [hy4_mem, hy3_low_x 2 (by unfold offGM offLM offHash; omega), hm2])
      (by rw [hy4_mem, hy3_low_x 3 (by unfold offGM offLM offHash; omega), hm3])
      (by rw [hy4_sz, hsz]; exact le_rfl)
      (by omega) (by omega) (by omega) hy4_win hy4_28_val hy4_27_val)
    (fun y5 ⟨hy5_sz, hy5_wf, hy5_er, hy5_td, hy5_dt, hy5_gm, hy5_lm, hy5_out, hy5_items,
      hy5_regs⟩ => ?_) (by omega)
  have hy5_sz_x : y5.bitSize = x.bitSize := hy5_sz.trans hy4_sz
  have hy5_low_x : ∀ a < offGM U w N, y5.mem a = x.mem a :=
    fun a ha => (hy5_out a (by unfold offTD; omega)).trans
      ((congrFun hy4_mem a).trans (hy3_low_x a ha))
  refine .seq (T₁ := 11) (T₂ := 26)
    (computeGMBasesRegCode_gmBases hw hN_pos hb_pos hy5_wf hy5_er
      (by rw [hy5_sz_x]; exact hsz_meta))
    (fun y6 ⟨hy6_st, hy6_wf, hy6_er, hy6_gb, hy6_regs⟩ => ?_) (by omega)
  have hy6_mem : y6.mem = y5.mem := congrArg BitMemory.State.mem hy6_st
  have hy6_sz_x : y6.bitSize = x.bitSize :=
    (congrArg BitMemory.State.bitSize hy6_st).trans hy5_sz_x
  have hm1_succ : m₁ + 1 = m₀ := by omega
  refine (popDenseRegCode_exec (n_t := m₁) hw (le_of_lt hU) hV hy6_wf hy6_er
    (by rw [hy6_sz_x, hsz, hm1_succ]; rfl)).mono
    (fun z ⟨_, hz_wf, hz_er, hz_sz, hz_items, hz_meta, hz_regs⟩ => ?_) (by omega)
  have hz_low_y5 : ∀ a < epochMetaWords U w N, z.mem a = y5.mem a :=
    fun a ha => (hz_meta a ha).trans (congrFun hy6_mem a)
  obtain ⟨hz_lm, hz_gm, hz_td, hz_dt, _⟩ :=
    meta_eq_of_low_words_eq hw hN_pos hz_low_y5
  have hz_gb : GMBasesLoaded N z :=
    hy6_gb.congr_regs (fun r hr1 hr2 => hz_regs r (by omega))
  refine ⟨hz_wf, hz_er, hz_gb, hz_sz, ?_,
    fun a ha => (hz_low_y5 a (by
      rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega)).trans (hy5_low_x a ha),
    fun r hr => (hz_regs r (by omega)).trans
      ((hy6_regs r (Or.inr (by omega))).trans
        ((hy5_regs r (by omega)).trans
          ((hy4_regs r (by omega) (by intro h; subst h; omega)).trans
            ((hy3_regs r (by omega)).trans
              (by dsimp only [s2, BitRAM.Data.set]
                  rw [Function.update_of_ne (by intro h; subst h; omega),
                    hy1_regs r (by omega) (by intro h; subst h; omega)])))))⟩
  unfold FixedCoupled
  have hz_gm_y3 : gmAtBit U w N z.mem = gmAtBit U w N y3.mem :=
    hz_gm.trans (hy5_gm.trans (by rw [hy4_mem]))
  have hz_gm0 : gmAtBit U w N z.mem 0 * K = b_win := by rw [hz_gm_y3, hy3_gm_0]
  have hz_gm1 : gmAtBit U w N z.mem 1 = n_win' := by rw [hz_gm_y3, hy3_gm_1]
  have hz_tot : Succinct.totalSlots N (gmAtBit U w N z.mem) = b_win + n_win' := by
    unfold Succinct.totalSlots; rw [ite_eq_right hb0, hz_gm0, hz_gm1]
  obtain ⟨hwin_s, htd_M, hdt_M⟩ := winShrinkRight_spec hy4_win (by omega)
    (fun i => by rw [hy4_mem]; have := hy3_cpl.td_lt i; rwa [max_eq_left hM_pos] at this)
    (fun i => by rw [hy4_mem]; have := hy3_cpl.dt_lt i; rwa [max_eq_left hM_pos] at this)
  refine ⟨by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_gm_y3]; exact hy3_cpl.gm_eq,
    by dsimp only [BitRAM.Data.toBitMemoryState]
       rw [hz_lm, hy5_lm, hy4_mem]; exact hy3_cpl.lm_eq,
    by dsimp only [BitRAM.Data.toBitMemoryState]
       rw [hz_gm0, hz_gm1, hz_td, hz_dt, hy5_td, hy5_dt]; exact hwin_s,
    fun i => by
      dsimp only [BitRAM.Data.toBitMemoryState]
      rw [hz_td, hy5_td, max_eq_left hM_pos]; exact htd_M i,
    fun i => by
      dsimp only [BitRAM.Data.toBitMemoryState]
      rw [hz_dt, hy5_dt, max_eq_left hM_pos]; exact hdt_M i,
    fun d hd => ?_, fun d hd => ?_⟩
  · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
    rw [hz_tot] at hd
    change denseQuotAt U V w N z.toBitMemoryState d =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s₁.mem
        (physByBase N (gmAtBit U w N z.mem 0 * K) (dtAtBit U w N z.mem) d)
    rw [hz_gm0, hz_dt, hy5_dt, (hz_items d (by rw [hm1_eq]; exact hd)).1]
    have hy6_q : denseQuotAt U V w N y6.toBitMemoryState d =
        denseQuotAt U V w N y5.toBitMemoryState d := by rw [hy6_st]
    rw [hy6_q, (hy5_items d hd).1]
    have hy4_q : ∀ idx, denseQuotAt U V w N y4.toBitMemoryState idx =
        denseQuotAt U V w N y3.toBitMemoryState idx := fun _ => by rw [hy4_st]
    rw [hy4_q, physByBase_winShrinkRight_ite hb_pos hy4_win (by omega) d hd, hy4_mem]
    set idx := if d = denseOfCirc (maxTailItems N) b_win (tdAtBit U w N y3.mem n_win')
      then b_win + n_win' else d
    have hidx_lt : idx < b_win + gmAtBit U w N s2.mem 1 := by
      rw [hs2_mem]
      change idx < b_win + n_win
      dsimp only [idx]
      split_ifs with heq <;> omega
    exact hy3_cpl.quot_eq idx hidx_lt
  · change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
    rw [hz_tot] at hd
    change denseValAt U V w N z.toBitMemoryState d =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s₁.mem
        (physByBase N (gmAtBit U w N z.mem 0 * K) (dtAtBit U w N z.mem) d)
    rw [hz_gm0, hz_dt, hy5_dt, (hz_items d (by rw [hm1_eq]; exact hd)).2]
    have hy6_v : denseValAt U V w N y6.toBitMemoryState d =
        denseValAt U V w N y5.toBitMemoryState d := by rw [hy6_st]
    rw [hy6_v, (hy5_items d hd).2]
    have hy4_v : ∀ idx, denseValAt U V w N y4.toBitMemoryState idx =
        denseValAt U V w N y3.toBitMemoryState idx := fun _ => by rw [hy4_st]
    rw [hy4_v, physByBase_winShrinkRight_ite hb_pos hy4_win (by omega) d hd, hy4_mem]
    set idx := if d = denseOfCirc (maxTailItems N) b_win (tdAtBit U w N y3.mem n_win')
      then b_win + n_win' else d
    have hidx_lt : idx < b_win + gmAtBit U w N s2.mem 1 := by
      rw [hs2_mem]
      change idx < b_win + n_win
      dsimp only [idx]
      split_ifs with heq <;> omega
    exact hy3_cpl.val_eq idx hidx_lt

end Cslib.DataStructure.Dictionary.BitResizable
