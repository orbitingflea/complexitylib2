/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.SlabMoveOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps

/-!
# Slab Promotion and `pushBackSlotRegCode` in `BitRAM`

This module implements the uniform `BitRAM.Code .standard 280` programs for:
1. One iteration of the slab promotion loop (`promotePrepRegCode`, `promoteStepRegCode`),
   synchronized with `Succinct.promoteStepProg` via `WindowCoupled` and `winShrinkLeft`.
2. Full slab promotion (`promoteSlabRegCode`), synchronized with `Succinct.promoteSlabProg`
   via `FixedCoupled`.
3. Amortized `O(1)` bucket slot append (`pushBackSlotRegCode`), synchronized with
   `Succinct.pushBackSlotProg` via `FixedCoupled` and `growDenseRegCode`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Window helpers and `promotePrepRegCode` -/

theorem physByBase_ne_of_ne_denseOfCirc_td {N b_win n_win t d' : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n_win ≤ maxTailItems N) (hbn_le : b_win + n_win ≤ N)
    (hwin : WindowInv (maxTailItems N) b_win n_win td dt) (ht : t < n_win)
    (hd' : d' < b_win + n_win) (hne : d' ≠ denseOfCirc (maxTailItems N) b_win (td t)) :
    physByBase N b_win dt d' ≠ N - 1 - t :=
  fun h => hne ((physByBase_eq_sub_iff_eq_denseOfCirc hb_pos hwin hbn_le hM ht hd').mp h)

/-- Uniform `BitRAM.Code .standard 280` prefix of `promoteStepRegCode`:
given `rB = b` and `rK = k` (`31 ≤ rB, rK`, `rB ≠ rK`), computes `b_win = gm 0 * K + k` in `r28`,
loads `(q_u, v_u)` into `(r29, r30)`, and copies dense item `d_top` into `d_u` (`T = 529`). -/
@[expose]
def promotePrepRegCode (rB rK : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 16 1))
  (.seq (.op (.bin .sub 16 250 16))
  (.seq (.op (.bin .sub 16 16 rK))
  (.seq (.op (.bin .add 17 250 16))
  (.seq (readGM2DRegCode 23 21 rB 16 26)
  (.seq (readGM2DRegCode 23 21 rB 17 27)
  (.seq (readGMConstRegCode 0 28)
  (.seq (.op (.bin .mul 28 28 250))
  (.seq (.op (.bin .add 28 28 rK))
  (.seq (readTDRegCode 26 16)
  (.seq (denseOfTailRegCode 28 16 26)
  (.seq (readTDRegCode 27 17)
  (.seq (denseOfTailRegCode 28 17 27)
  (.seq (readDenseQRegCode 26 29)
  (.seq (readDenseVRegCode 26 30)
        (copyDenseItemRegCode 27 26)))))))))))))))

theorem promotePrepRegCode_exec {U V w N b k : ℕ} {rB rK : Fin 280}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 31 ≤ rB.val) (hrK_ge : 31 ≤ rK.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hpre : Succinct.PromoteStepInv U V w N (Succinct.hashSpace U w N) 0 b k s_fix)
    (hcpl : WindowCoupled U V w N (gmAtBit U w N x.mem 0 * slabSize N + k)
      (gmAtBit U w N x.mem 1) (gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1)
      s_fix x.toBitMemoryState)
    (hsz : itemBitOff U V w N (gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1) ≤
      x.bitSize)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k) :
    let K := slabSize N
    let gm₀ := gmAtBit U w N x.mem
    let b_win := gm₀ 0 * K + k
    let n_win := gm₀ 1
    let m₀ := b_win + n_win
    let u := (K - 1) - k
    let r_top := K + u
    let g_u := (N - 1) - gm₀ (Succinct.gmTailPtrIdx N b u)
    let g_top := (N - 1) - gm₀ (Succinct.gmTailPtrIdx N b r_top)
    let q_u := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_u
    let v_u := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_u
    let q_top := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_top
    let v_top := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_top
    let s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.writeQuotProg U w N (Succinct.hashSpace U w N) ((0, g_u), q_top))
    let s₂ := (Memory.spec 0).clientState s₁
      (Succinct.writeValProg U V w N (Succinct.hashSpace U w N) ((0, g_u), v_top))
    BitRAM.DemonicExecWithin w (promotePrepRegCode rB rK) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        GMBasesLoaded N y ∧
        y.bitSize = x.bitSize ∧
        WindowCoupled U V w N b_win n_win m₀ s₂ y.toBitMemoryState ∧
        y.regs 28 = b_win ∧
        y.regs 29 = q_u ∧
        y.regs 30 = v_u ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 31 ≤ r.val → y.regs r = x.regs r)) 529 := by
  intro K gm₀ b_win n_win m₀ u r_top g_u g_top q_u v_u q_top v_top s₁ s₂
  change WindowCoupled U V w N b_win n_win m₀ s_fix x.toBitMemoryState at hcpl
  rcases hpre with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  have hgm_eq : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem = gm₀ :=
    hcpl.gm_eq.symm
  have htail : Succinct.TailBijection N gm₀ (fun b' => gm₀ (Succinct.gmRIdx b')) (gm₀ 1) := by
    rwa [hgm_eq] at htail_fix
  have hrb_eq : gm₀ (Succinct.gmRIdx b) = 2 * K - k := by
    rwa [hgm_eq] at hrb_fix
  have htot : b_win + n_win ≤ N := by
    change gmAtBit U w N x.mem 0 * K + k + gmAtBit U w N x.mem 1 ≤ N
    rwa [hgm_eq] at htot_fix
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hK_pos : 0 < K := slabSize_pos N
  have hM_le : n_win ≤ maxTailItems N := htail.ntails_le
  have hM_pos : 0 < maxTailItems N := by
    have := Succinct.r_le_ntails_of_tailBijection htail hb
    omega
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz_meta hv
  have hTcap : tailCapPerBucket N = 2 * K := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  have hu_lt_r : u < gm₀ (Succinct.gmRIdx b) := by dsimp only [u]; omega
  have hr_top_lt_r : r_top < gm₀ (Succinct.gmRIdx b) := by dsimp only [r_top, u]; omega
  have hu_cap : u < tailCapPerBucket N := by dsimp only [u]; omega
  have hr_top_cap : r_top < tailCapPerBucket N := by dsimp only [r_top, u]; omega
  have hptr_u_lt : Succinct.gmTailPtrBase N + b * tailCapPerBucket N + u < globalMetaLen N := by
    have h := Succinct.gmTailPtrIdx_lt hb_pos hb hu_cap
    unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx at h; omega
  have hptr_top_lt : Succinct.gmTailPtrBase N + b * tailCapPerBucket N + r_top <
      globalMetaLen N := by
    have h := Succinct.gmTailPtrIdx_lt hb_pos hb hr_top_cap
    unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx at h; omega
  set t_u := gm₀ (Succinct.gmTailPtrIdx N b u)
  set t_top := gm₀ (Succinct.gmTailPtrIdx N b r_top)
  have htu_lt : t_u < n_win := htail.ptr_lt b hb u hu_lt_r
  have httop_lt : t_top < n_win := htail.ptr_lt b hb r_top hr_top_lt_r
  have hwin : WindowInv (maxTailItems N) b_win n_win
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem) := hcpl.win_inv
  set c_u := tdAtBit U w N x.mem t_u
  set c_top := tdAtBit U w N x.mem t_top
  set d_u := denseOfCirc (maxTailItems N) b_win c_u
  set d_top := denseOfCirc (maxTailItems N) b_win c_top
  have hcu_lt : c_u < maxTailItems N := hwin.td_lt t_u htu_lt
  have hctop_lt : c_top < maxTailItems N := hwin.td_lt t_top httop_lt
  obtain ⟨_, hdu_lt, hphys_du⟩ := physByBase_denseOfCirc_td hb_pos hwin htu_lt
  obtain ⟨_, hdtop_lt, hphys_dtop⟩ := physByBase_denseOfCirc_td hb_pos hwin httop_lt
  have h250 : x.regs 250 = K := (her.active hN_pos).2.2.2.2.2.1
  have h21 : x.regs 21 = tailCapPerBucket N := hgb.2.1
  have h23 : x.regs 23 = Succinct.gmTailPtrBase N := hgb.2.2.2.1
  have hfit_1 : Fits w 1 := hfit_N 1 (by omega)
  have hfit_K1 : Fits w (K - 1) :=
    hfit_N (K - 1) ((Nat.sub_le _ _).trans (Succinct.slabSize_le_max_n_one N))
  have hfit_u : Fits w u :=
    hfit_N u ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Succinct.slabSize_le_max_n_one N)))
  have hfit_rtop : Fits w r_top :=
    hfit_gm r_top ((le_of_lt hr_top_cap).trans (Succinct.tailCapPerBucket_le_globalMetaLen hb_pos))
  have hfit_gm0K : Fits w (gm₀ 0 * K) := hfit_N _ (by omega)
  have hfit_bwin : Fits w b_win := hfit_N b_win (by omega)
  unfold promotePrepRegCode
  refine DemonicExecWithin.step_const (T := 528) hfit_1 ?_
  refine step_dExec_bin (v := K - 1) (T := 527)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, h250, K]) hfit_K1 ?_
  refine step_dExec_bin (v := u) (T := 526)
    (by
      have hrK_ne : rK ≠ 16 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hrK_ne, hrK, u]) hfit_u ?_
  refine step_dExec_bin (v := r_top) (T := 525)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, h250, r_top, K]) hfit_rtop ?_
  set a0 := (((x.set 16 1).set 16 (K - 1)).set 16 u).set 17 r_top
  have ha0_wf : a0.WellFormed w :=
    wf_set 17 (wf_set 16 (wf_set 16 (wf_set 16 hx hfit_1) hfit_K1) hfit_u) hfit_rtop
  have ha0_er : EpochRegs U V w N a0 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [a0, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have ha0_regs_ge18 : ∀ r : Fin 280, 18 ≤ r.val → a0.regs r = x.regs r := by
    intro r hr
    dsimp only [a0, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  refine .seq (T₁ := 48) (T₂ := 477)
    (readGM2DRegCode_exec (rBase := 23) (rStride := 21) (rB := rB) (rK := 16) (rDst := 26)
      (by decide) (by decide) (by omega) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU ha0_wf ha0_er hsz_meta
      (by rw [ha0_regs_ge18 23 (by decide), h23])
      (by rw [ha0_regs_ge18 21 (by decide), h21])
      (by rw [ha0_regs_ge18 rB (by omega), hrB])
      (by simp +decide [a0, BitRAM.Data.set])
      hptr_u_lt)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_26, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_26_val : y1.regs 26 = t_u := by
    rw [hy1_26]
    change gm₀ (Succinct.gmTailPtrBase N + b * tailCapPerBucket N + u) = t_u
    dsimp only [t_u, Succinct.gmTailPtrIdx, Succinct.gmTailPtrFlatIdx]
    rw [Nat.add_assoc]
  refine .seq (T₁ := 48) (T₂ := 429)
    (readGM2DRegCode_exec (rBase := 23) (rStride := 21) (rB := rB) (rK := 17) (rDst := 27)
      (by decide) (by decide) (by omega) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy1_wf hy1_er (by rw [hy1_sz]; exact hsz_meta)
      (by rw [hy1_regs 23 (by decide) (by decide), ha0_regs_ge18 23 (by decide), h23])
      (by rw [hy1_regs 21 (by decide) (by decide), ha0_regs_ge18 21 (by decide), h21])
      (by rw [hy1_regs rB (by omega) (by intro h; subst h; omega),
            ha0_regs_ge18 rB (by omega), hrB])
      (by rw [hy1_regs 17 (by decide) (by decide)]
          simp +decide [a0, BitRAM.Data.set])
      hptr_top_lt)
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_27, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  have hy2_27_val : y2.regs 27 = t_top := by
    rw [hy2_27, hy1_mem]
    change gm₀ (Succinct.gmTailPtrBase N + b * tailCapPerBucket N + r_top) = t_top
    dsimp only [t_top, Succinct.gmTailPtrIdx, Succinct.gmTailPtrFlatIdx]
    rw [Nat.add_assoc]
  refine .seq (T₁ := 46) (T₂ := 383)
    (readGMConstRegCode_exec (idx := 0) (rDst := 28) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy2_wf hy2_er (by rw [hy2_sz]; exact hsz_meta))
    (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_28, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
  have hy3_28_val : y3.regs 28 = gm₀ 0 := by rw [hy3_28, hy2_mem]
  have hy3_250 : y3.regs 250 = K := (hy3_er.active hN_pos).2.2.2.2.2.1
  have hy3_rK : y3.regs rK = k := by
    rw [hy3_regs rK (by omega) (by intro h; subst h; omega),
      hy2_regs rK (by omega) (by intro h; subst h; omega),
      hy1_regs rK (by omega) (by intro h; subst h; omega),
      ha0_regs_ge18 rK (by omega), hrK]
  refine step_dExec_bin (v := gm₀ 0 * K) (T := 382)
    (by simp [BinOp.eval, hy3_28_val, hy3_250]) hfit_gm0K ?_
  refine step_dExec_bin (v := b_win) (T := 381)
    (by
      have hrK_ne : rK ≠ 28 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hrK_ne, hy3_rK, b_win]) hfit_bwin ?_
  set a3 := (y3.set 28 (gm₀ 0 * K)).set 28 b_win
  have ha3_wf : a3.WellFormed w := wf_set 28 (wf_set 28 hy3_wf hfit_gm0K) hfit_bwin
  have ha3_er : EpochRegs U V w N a3 :=
    hy3_er.congr_regs (fun r hr1 _ => by
      dsimp only [a3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have ha3_26 : a3.regs 26 = t_u := by
    dsimp only [a3, BitRAM.Data.set]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hy3_regs 26 (by decide) (by decide), hy2_regs 26 (by decide) (by decide),
      hy1_26_val]
  have ha3_27 : a3.regs 27 = t_top := by
    dsimp only [a3, BitRAM.Data.set]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hy3_regs 27 (by decide) (by decide), hy2_27_val]
  refine .seq (T₁ := 45) (T₂ := 336)
    (readTDRegCode_exec (rIdx := 26) (rDst := 16) (by decide)
      hw hN_pos hnU hU ha3_wf ha3_er (lt_of_lt_of_le htu_lt hM_le) ha3_26
      (by rw [show a3.bitSize = x.bitSize from hy3_sz]; exact hsz_meta))
    (fun y4 ⟨hy4_st, hy4_wf, hy4_16, hy4_regs⟩ => ?_) (by omega)
  have hy4_st_x : y4.toBitMemoryState = x.toBitMemoryState := hy4_st.trans hy3_st_x
  have hy4_mem : y4.mem = x.mem := congrArg BitMemory.State.mem hy4_st_x
  have hy4_sz : y4.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy4_st_x
  have hy4_er : EpochRegs U V w N y4 :=
    ha3_er.congr_regs (fun r hr1 _ =>
      hy4_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy4_28 : y4.regs 28 = b_win := by
    rw [hy4_regs 28 (by decide) (by decide)]
    simp +decide [a3, BitRAM.Data.set]
  have hy4_16_val : y4.regs 16 = c_u := by
    rw [hy4_16]
    change tdAtBit U w N y3.mem t_u = c_u
    rw [hy3_mem]
  refine .seq (T₁ := 5) (T₂ := 331)
    (denseOfTailRegCode_exec (rB := 28) (rC := 16) (rDst := 26) (by decide) (by decide)
      hw hN_pos hnU hU hb_pos hy4_wf hy4_er (by rw [hy4_sz]; exact hsz_meta)
      (le_of_lt (lt_of_lt_of_le hdu_lt htot)) hcu_lt hy4_28 hy4_16_val)
    (fun y5 ⟨hy5_st, hy5_wf, hy5_26, hy5_regs⟩ => ?_) (by omega)
  have hy5_st_x : y5.toBitMemoryState = x.toBitMemoryState := hy5_st.trans hy4_st_x
  have hy5_mem : y5.mem = x.mem := congrArg BitMemory.State.mem hy5_st_x
  have hy5_sz : y5.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy5_st_x
  have hy5_er : EpochRegs U V w N y5 :=
    hy4_er.congr_regs (fun r hr1 _ =>
      hy5_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy5_27 : y5.regs 27 = t_top := by
    rw [hy5_regs 27 (by decide) (by decide), hy4_regs 27 (by decide) (by decide), ha3_27]
  refine .seq (T₁ := 45) (T₂ := 286)
    (readTDRegCode_exec (rIdx := 27) (rDst := 17) (by decide)
      hw hN_pos hnU hU hy5_wf hy5_er (lt_of_lt_of_le httop_lt hM_le) hy5_27
      (by rw [hy5_sz]; exact hsz_meta))
    (fun y6 ⟨hy6_st, hy6_wf, hy6_17, hy6_regs⟩ => ?_) (by omega)
  have hy6_st_x : y6.toBitMemoryState = x.toBitMemoryState := hy6_st.trans hy5_st_x
  have hy6_mem : y6.mem = x.mem := congrArg BitMemory.State.mem hy6_st_x
  have hy6_sz : y6.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy6_st_x
  have hy6_er : EpochRegs U V w N y6 :=
    hy5_er.congr_regs (fun r hr1 _ =>
      hy6_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy6_28 : y6.regs 28 = b_win := by
    rw [hy6_regs 28 (by decide) (by decide), hy5_regs 28 (by decide) (by decide), hy4_28]
  have hy6_17_val : y6.regs 17 = c_top := by
    rw [hy6_17, hy5_mem]
  refine .seq (T₁ := 5) (T₂ := 281)
    (denseOfTailRegCode_exec (rB := 28) (rC := 17) (rDst := 27) (by decide) (by decide)
      hw hN_pos hnU hU hb_pos hy6_wf hy6_er (by rw [hy6_sz]; exact hsz_meta)
      (le_of_lt (lt_of_lt_of_le hdtop_lt htot)) hctop_lt hy6_28 hy6_17_val)
    (fun y7 ⟨hy7_st, hy7_wf, hy7_27, hy7_regs⟩ => ?_) (by omega)
  have hy7_st_x : y7.toBitMemoryState = x.toBitMemoryState := hy7_st.trans hy6_st_x
  have hy7_mem : y7.mem = x.mem := congrArg BitMemory.State.mem hy7_st_x
  have hy7_sz : y7.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy7_st_x
  have hy7_er : EpochRegs U V w N y7 :=
    hy6_er.congr_regs (fun r hr1 _ =>
      hy7_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy7_26 : y7.regs 26 = d_u := by
    rw [hy7_regs 26 (by decide) (by decide), hy6_regs 26 (by decide) (by decide), hy5_26]
  refine .seq (T₁ := 42) (T₂ := 239)
    (readDenseQRegCode_exec (n_t := m₀) (d := d_u) (rD := 26) (rDst := 29) (by decide)
      hw (le_of_lt hU) hy7_wf hy7_er hdu_lt hy7_26 (by rw [hy7_sz]; exact hsz)
      (by rw [hy7_mem, hm2]) (by rw [hy7_mem, hm3]))
    (fun y8 ⟨hy8_st, hy8_wf, hy8_29, hy8_regs⟩ => ?_) (by omega)
  have hy8_st_x : y8.toBitMemoryState = x.toBitMemoryState := hy8_st.trans hy7_st_x
  have hy8_mem : y8.mem = x.mem := congrArg BitMemory.State.mem hy8_st_x
  have hy8_sz : y8.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy8_st_x
  have hy8_er : EpochRegs U V w N y8 :=
    hy7_er.congr_regs (fun r hr1 _ =>
      hy8_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy8_26 : y8.regs 26 = d_u := by
    rw [hy8_regs 26 (by decide) (by decide), hy7_26]
  refine .seq (T₁ := 44) (T₂ := 195)
    (readDenseVRegCode_exec (n_t := m₀) (d := d_u) (rD := 26) (rDst := 30) (by decide)
      hw hV hy8_wf hy8_er hdu_lt hy8_26 (by rw [hy8_sz]; exact hsz)
      (by rw [hy8_mem, hm2]) (by rw [hy8_mem, hm3]))
    (fun y9 ⟨hy9_st, hy9_wf, hy9_30, hy9_regs⟩ => ?_) (by omega)
  have hy9_st_x : y9.toBitMemoryState = x.toBitMemoryState := hy9_st.trans hy8_st_x
  have hy9_mem : y9.mem = x.mem := congrArg BitMemory.State.mem hy9_st_x
  have hy9_sz : y9.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy9_st_x
  have hy9_er : EpochRegs U V w N y9 :=
    hy8_er.congr_regs (fun r hr1 _ =>
      hy9_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy9_26 : y9.regs 26 = d_u := by
    rw [hy9_regs 26 (by decide) (by decide), hy8_26]
  have hy9_27 : y9.regs 27 = d_top := by
    rw [hy9_regs 27 (by decide) (by decide), hy8_regs 27 (by decide) (by decide), hy7_27]
  refine (copyDenseItemRegCode_exec (n_t := m₀) (rSrc := 27) (rDst := 26) (by decide) (by decide)
    hw (le_of_lt hU) hV hy9_wf hy9_er hdtop_lt hdu_lt hy9_27 hy9_26
    (by rw [hy9_sz]; exact hsz) (by rw [hy9_mem, hm2]) (by rw [hy9_mem, hm3])).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_q, hy_v, hy_other, hy_meta, hy_regs⟩ => ?_) le_rfl
  have hy_meta_x : ∀ a < epochMetaWords U w N, y.mem a = x.mem a :=
    fun a ha => (hy_meta a ha).trans (congrFun hy9_mem a)
  obtain ⟨hy_lm, hy_gm, hy_td, hy_dt, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy_meta_x
  have hy9_regs_20 : ∀ r : Fin 280, 20 ≤ r.val →
      r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → y9.regs r = x.regs r := by
    intro r hr h26 h27 h28 h29 h30
    rw [hy9_regs r (by omega) h30, hy8_regs r (by omega) h29, hy7_regs r (by omega) h27,
      hy6_regs r (by omega) (by intro h; subst h; omega),
      hy5_regs r (by omega) h26,
      hy4_regs r (by omega) (by intro h; subst h; omega)]
    dsimp only [a3, BitRAM.Data.set]
    rw [Function.update_of_ne h28, Function.update_of_ne h28,
      hy3_regs r (by omega) h28,
      hy2_regs r (by omega) h27,
      hy1_regs r (by omega) h26,
      ha0_regs_ge18 r (by omega)]
  have hy_gb : GMBasesLoaded N y :=
    hgb.congr_regs (fun r hr1 hr2 =>
      (hy_regs r hr1).trans
        (hy9_regs_20 r hr1 (by intro h; subst h; omega) (by intro h; subst h; omega)
          (by intro h; subst h; omega) (by intro h; subst h; omega)
          (by intro h; subst h; omega)))
  have hy_28 : y.regs 28 = b_win := by
    rw [hy_regs 28 (by decide), hy9_regs 28 (by decide) (by decide),
      hy8_regs 28 (by decide) (by decide), hy7_regs 28 (by decide) (by decide), hy6_28]
  have hy_29 : y.regs 29 = q_u := by
    have hq_eq := hcpl.quot_eq d_u hdu_lt
    change denseQuotAt U V w N x.toBitMemoryState d_u =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
        (physByBase N b_win (dtAtBit U w N x.mem) d_u) at hq_eq
    rw [hy_regs 29 (by decide), hy9_regs 29 (by decide) (by decide), hy8_29, hy7_st_x, hq_eq]
    exact congrArg (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem) hphys_du
  have hy_30 : y.regs 30 = v_u := by
    have hv_eq := hcpl.val_eq d_u hdu_lt
    change denseValAt U V w N x.toBitMemoryState d_u =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
        (physByBase N b_win (dtAtBit U w N x.mem) d_u) at hv_eq
    rw [hy_regs 30 (by decide), hy9_30, hy8_st_x, hv_eq]
    exact congrArg (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) hphys_du
  have hgu_lt_N : g_u < N := by dsimp only [g_u]; omega
  have hqtop_lt : q_top < 2 ^ quotientBits U N := Succinct.quotAt_lt _ _ _ _ _ _ _
  have hvtop_lt : v_top < 2 ^ valBits V := Succinct.valAt_lt _ _ _ _ _ _ _ _
  obtain ⟨_, _, hq1, hv1, hl1, hg1⟩ :=
    Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hgu_lt_N hqtop_lt s_fix
  obtain ⟨_, _, hq2, hv2, hl2, hg2⟩ :=
    Succinct.writeValProg_effect (base := 0) (h_space := Succinct.hashSpace U w N)
      hw hgu_lt_N hvtop_lt s₁
  refine ⟨hy_wf, hy_er, hy_gb, hy_sz.trans hy9_sz,
    ⟨?_, ?_, ?_, ?_, ?_, fun d hd => ?_, fun d hd => ?_⟩,
    hy_28, hy_29, hy_30, hy_meta_x,
    fun r hr => (hy_regs r (by omega)).trans
      (hy9_regs_20 r (by omega) (by intro h; subst h; omega) (by intro h; subst h; omega)
        (by intro h; subst h; omega) (by intro h; subst h; omega)
        (by intro h; subst h; omega))⟩
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hy_gm, hg2, hg1]; exact hcpl.gm_eq
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hy_lm, hl2, hl1]; exact hcpl.lm_eq
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hy_td, hy_dt]; exact hcpl.win_inv
  · intro i; dsimp only [BitRAM.Data.toBitMemoryState]; rw [hy_td]; exact hcpl.td_lt i
  · intro i; dsimp only [BitRAM.Data.toBitMemoryState]; rw [hy_dt]; exact hcpl.dt_lt i
  · have hy_dt' : dtAtBit U w N y.toBitMemoryState.mem = dtAtBit U w N x.mem := hy_dt
    have hx_dt' : dtAtBit U w N x.toBitMemoryState.mem = dtAtBit U w N x.mem := rfl
    rw [hy_dt', hq2, hq1]
    by_cases heq : d = d_u
    · subst heq
      have hq_top := hcpl.quot_eq d_top hdtop_lt
      rw [hx_dt'] at hq_top
      change denseQuotAt U V w N y.toBitMemoryState d_u =
        denseQuotAt U V w N y9.toBitMemoryState d_top at hy_q
      change physByBase N b_win (dtAtBit U w N x.mem) d_u = g_u at hphys_du
      change physByBase N b_win (dtAtBit U w N x.mem) d_top = g_top at hphys_dtop
      rw [hy_q, hy9_st_x, hq_top, hphys_dtop, hphys_du, Function.update_self]
    · obtain ⟨hq_d, _⟩ := hy_other d hd heq
      have hq_x := hcpl.quot_eq d hd
      rw [hx_dt'] at hq_x
      rw [hq_d, hy9_st_x, hq_x,
        Function.update_of_ne
          (physByBase_ne_of_ne_denseOfCirc_td hb_pos hM_le htot hwin htu_lt hd heq)]
  · have hy_dt' : dtAtBit U w N y.toBitMemoryState.mem = dtAtBit U w N x.mem := hy_dt
    have hx_dt' : dtAtBit U w N x.toBitMemoryState.mem = dtAtBit U w N x.mem := rfl
    rw [hy_dt', hv2, hv1]
    by_cases heq : d = d_u
    · subst heq
      have hv_top := hcpl.val_eq d_top hdtop_lt
      rw [hx_dt'] at hv_top
      change denseValAt U V w N y.toBitMemoryState d_u =
        denseValAt U V w N y9.toBitMemoryState d_top at hy_v
      change physByBase N b_win (dtAtBit U w N x.mem) d_u = g_u at hphys_du
      change physByBase N b_win (dtAtBit U w N x.mem) d_top = g_top at hphys_dtop
      rw [hy_v, hy9_st_x, hv_top, hphys_dtop, hphys_du, Function.update_self]
    · obtain ⟨_, hv_d⟩ := hy_other d hd heq
      have hv_x := hcpl.val_eq d hd
      rw [hx_dt'] at hv_x
      rw [hv_d, hy9_st_x, hv_x,
        Function.update_of_ne
          (physByBase_ne_of_ne_denseOfCirc_td hb_pos hM_le htot hwin htu_lt hd heq)]

/-! ## Section 2: `promoteStepRegCode` and `promoteSlabRegCode` -/

/-- Uniform `BitRAM.Code .standard 280` program executing one iteration of the slab promotion loop:
synchronizes with `Succinct.promoteStepProg` while advancing the circular window left from
`b_win = gm 0 * K + k` to `b_win + 1 = gm' 0 * K + (k + 1)` (`31 ≤ rB, rK`, `rB ≠ rK`,
`T = 1965`). -/
@[expose]
def promoteStepRegCode (rB rK : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (promotePrepRegCode rB rK)
  (.seq (removeLastTailCopyRegCode rB 28)
  (.seq (readGMConstRegCode 1 27)
  (.seq (winShrinkLeftRegCode 28 27)
  (.seq computeGMBasesRegCode
  (.seq (writeDenseQVRegCode 28 29 30)
  (.seq (.op (.const 16 1))
        (.op (.bin .add rK rK 16))))))))

theorem promoteStepRegCode_exec {U V w N b k : ℕ} {rB rK : Fin 280}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 31 ≤ rB.val) (hrK_ge : 31 ≤ rK.val) (hrK_lt : rK.val < 240) (hne_BK : rB ≠ rK)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hpre : Succinct.PromoteStepInv U V w N (Succinct.hashSpace U w N) 0 b k s_fix)
    (hcpl : WindowCoupled U V w N (gmAtBit U w N x.mem 0 * slabSize N + k)
      (gmAtBit U w N x.mem 1) (gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1)
      s_fix x.toBitMemoryState)
    (hsz : itemBitOff U V w N (gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1) ≤
      x.bitSize)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k) :
    let K := slabSize N
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.promoteStepProg U V w N (Succinct.hashSpace U w N) ((0, b), k))
    BitRAM.DemonicExecWithin w (promoteStepRegCode rB rK) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        z.bitSize = x.bitSize ∧
        WindowCoupled U V w N (gmAtBit U w N z.mem 0 * K + (k + 1))
          (gmAtBit U w N z.mem 1) (gmAtBit U w N z.mem 0 * K + (k + 1) + gmAtBit U w N z.mem 1)
          s' z.toBitMemoryState ∧
        z.regs rK = k + 1 ∧
        (∀ a < offGM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 31 ≤ r.val → r ≠ rK → z.regs r = x.regs r)) 1965 := by
  intro K s'
  set gm₀ := gmAtBit U w N x.mem
  set b_win := gm₀ 0 * K + k
  set n_win := gm₀ 1
  set m₀ := b_win + n_win
  set u := (K - 1) - k
  set r_top := K + u
  set g_u := (N - 1) - gm₀ (Succinct.gmTailPtrIdx N b u)
  set g_top := (N - 1) - gm₀ (Succinct.gmTailPtrIdx N b r_top)
  set q_u := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_u
  set v_u := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_u
  set q_top := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_top
  set v_top := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_top
  set s₁ := (Memory.spec 0).clientState s_fix
    (Succinct.writeQuotProg U w N (Succinct.hashSpace U w N) ((0, g_u), q_top))
  set s₂ := (Memory.spec 0).clientState s₁
    (Succinct.writeValProg U V w N (Succinct.hashSpace U w N) ((0, g_u), v_top))
  set s₃ := (Memory.spec 0).clientState s₂
    (Succinct.removeLastTailItemProg U V w N (Succinct.hashSpace U w N) (0, b))
  rcases hpre with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  have hgm_eq : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem = gm₀ :=
    hcpl.gm_eq.symm
  have htail : Succinct.TailBijection N gm₀ (fun b' => gm₀ (Succinct.gmRIdx b')) (gm₀ 1) := by
    rwa [hgm_eq] at htail_fix
  have hrb_eq : gm₀ (Succinct.gmRIdx b) = 2 * K - k := by rwa [hgm_eq] at hrb_fix
  have htot : b_win + n_win ≤ N := by
    change gmAtBit U w N x.mem 0 * K + k + gmAtBit U w N x.mem 1 ≤ N
    rwa [hgm_eq] at htot_fix
  have hK_pos : 0 < K := slabSize_pos N
  have hr_pos : 1 ≤ gm₀ (Succinct.gmRIdx b) := by omega
  have hn_win_pos : 1 ≤ n_win := by
    have := Succinct.r_le_ntails_of_tailBijection htail hb
    omega
  set n_win' := n_win - 1
  have hn_eq : n_win = n_win' + 1 := by omega
  have hM_le : n_win ≤ maxTailItems N := htail.ntails_le
  have hM_pos : 0 < maxTailItems N := by omega
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_k1 : Fits w (k + 1) :=
    fits_of_le_N hw hnU hU (le_trans (by omega : k + 1 ≤ K) (Succinct.slabSize_le_max_n_one N))
  unfold promoteStepRegCode
  refine .seq (T₁ := 529) (T₂ := 1436)
    (promotePrepRegCode_exec hrB_ge hrK_ge hw hN_pos hnU hU hV hb_pos hx her hgb hm2 hm3
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩ hcpl hsz hrB hrK)
    (fun y1 ⟨hy1_wf, hy1_er, hy1_gb, hy1_sz, hy1_cpl, hy1_28, hy1_29, hy1_30, hy1_meta,
      hy1_regs⟩ => ?_) (by omega)
  obtain ⟨_, hy1_gm, _, _, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy1_meta
  refine .seq (T₁ := 866) (T₂ := 570)
    (removeLastTailCopyRegCode_exec (rB := rB) (rBWin := 28) (s_fix := s₂)
      (by omega) (by decide) hw hN_pos hnU hU hV hb_pos hb
      hy1_wf hy1_er hy1_gb
      (by rw [hy1_meta 2 (by unfold epochMetaWords; split_ifs <;> omega), hm2])
      (by rw [hy1_meta 3 (by unfold epochMetaWords; split_ifs <;> omega), hm3])
      (by rw [hy1_gm]; exact hy1_cpl)
      (by rw [hy1_gm]; exact htail)
      (by rw [hy1_gm]; exact hr_pos)
      (by rw [hy1_gm]; exact htot)
      (by rw [hy1_gm, hy1_sz]; exact hsz)
      (by rw [hy1_regs rB hrB_ge, hrB]) hy1_28)
    (fun y2 ⟨hy2_wf, hy2_er, hy2_gb, hy2_sz, hy2_gm0, hy2_cpl, hy2_low, hy2_regs⟩ => ?_)
    (by omega)
  have hy2_sz_x : y2.bitSize = x.bitSize := hy2_sz.trans hy1_sz
  have hy2_low_x : ∀ a < offGM U w N, y2.mem a = x.mem a :=
    fun a ha => (hy2_low a ha).trans
      (hy1_meta a (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega))
  have hy2_gm : gmAtBit U w N y2.mem = Succinct.gmRemoveTail N gm₀ b := by
    rw [hy2_gm0, hy1_gm]
  have hpres_rem := Succinct.gmRemoveTail_preserves_nonTail hb hr_pos htail
  have hy2_gm_0 : gmAtBit U w N y2.mem 0 = gm₀ 0 := by rw [hy2_gm, hpres_rem.1]
  have hy2_gm_1 : gmAtBit U w N y2.mem 1 = n_win' := by rw [hy2_gm, hpres_rem.2.1]
  refine .seq (T₁ := 46) (T₂ := 524)
    (readGMConstRegCode_exec (idx := 1) (rDst := 27) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy2_wf hy2_er (by rw [hy2_sz_x]; exact hsz_meta))
    (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_27, hy3_regs⟩ => ?_) (by omega)
  have hy3_mem : y3.mem = y2.mem := congrArg BitMemory.State.mem hy3_st
  have hy3_sz : y3.bitSize = x.bitSize :=
    (congrArg BitMemory.State.bitSize hy3_st).trans hy2_sz_x
  have hy3_27_val : y3.regs 27 = n_win' := by rw [hy3_27, hy2_gm_1]
  have hy3_28_val : y3.regs 28 = b_win := by
    rw [hy3_regs 28 (by decide) (by decide), hy2_regs 28 (by decide), hy1_28]
  have hy3_win : WindowInv (maxTailItems N) b_win (n_win' + 1)
      (tdAtBit U w N y3.mem) (dtAtBit U w N y3.mem) := by
    rw [hy3_mem, ← hn_eq]
    have h := hy2_cpl.win_inv
    rwa [hy1_gm] at h
  refine .seq (T₁ := 403) (T₂ := 121)
    (winShrinkLeftRegCode_exec (n_t := m₀) (b_win := b_win) (n_win := n_win')
      (rB := 28) (rN := 27) (by decide) (by decide)
      hw hN_pos hnU hU hV hb_pos hy3_wf hy3_er
      (by rw [hy3_mem, hy2_low_x 2 (by unfold offGM offLM offHash; omega), hm2])
      (by rw [hy3_mem, hy2_low_x 3 (by unfold offGM offLM offHash; omega), hm3])
      (by rw [hy3_sz]; exact hsz)
      (by omega) (by omega) (by omega) hy3_win hy3_28_val hy3_27_val)
    (fun y4 ⟨hy4_sz, hy4_wf, hy4_er, hy4_td, hy4_dt, hy4_gm, hy4_lm, hy4_out, hy4_items,
      hy4_regs⟩ => ?_) (by omega)
  have hy4_sz_x : y4.bitSize = x.bitSize := hy4_sz.trans hy3_sz
  have hy4_low_x : ∀ a < offGM U w N, y4.mem a = x.mem a :=
    fun a ha => (hy4_out a (by unfold offTD; omega)).trans
      ((congrFun hy3_mem a).trans (hy2_low_x a ha))
  refine .seq (T₁ := 11) (T₂ := 110)
    (computeGMBasesRegCode_gmBases hw hN_pos hb_pos hy4_wf hy4_er
      (by rw [hy4_sz_x]; exact hsz_meta))
    (fun y5 ⟨hy5_st, hy5_wf, hy5_er, hy5_gb, hy5_regs⟩ => ?_) (by omega)
  have hy5_mem : y5.mem = y4.mem := congrArg BitMemory.State.mem hy5_st
  have hy5_sz_x : y5.bitSize = x.bitSize :=
    (congrArg BitMemory.State.bitSize hy5_st).trans hy4_sz_x
  have hy5_28 : y5.regs 28 = b_win := by
    rw [hy5_regs 28 (Or.inr (by decide)), hy4_regs 28 (by decide), hy3_28_val]
  have hy5_29 : y5.regs 29 = q_u := by
    rw [hy5_regs 29 (Or.inr (by decide)), hy4_regs 29 (by decide),
      hy3_regs 29 (by decide) (by decide), hy2_regs 29 (by decide), hy1_29]
  have hy5_30 : y5.regs 30 = v_u := by
    rw [hy5_regs 30 (Or.inr (by decide)), hy4_regs 30 (by decide),
      hy3_regs 30 (by decide) (by decide), hy2_regs 30 (by decide), hy1_30]
  refine .seq (T₁ := 108) (T₂ := 2)
    (writeDenseQVRegCode_exec (n_t := m₀) (rD := 28) (rQ := 29) (rV := 30)
      (by decide) (by decide) (by decide) hw (le_of_lt hU) hV hy5_wf hy5_er
      (by omega : b_win < m₀) hy5_28 hy5_29 hy5_30
      (Succinct.quotAt_lt _ _ _ _ _ _ _) (Succinct.valAt_lt _ _ _ _ _ _ _ _)
      (by rw [hy5_sz_x]; exact hsz)
      (by rw [hy5_mem, hy4_low_x 2 (by unfold offGM offLM offHash; omega), hm2])
      (by rw [hy5_mem, hy4_low_x 3 (by unfold offGM offLM offHash; omega), hm3]))
    (fun y6 ⟨hy6_wf, hy6_er, hy6_sz, hy6_q, hy6_v, hy6_other, hy6_meta, hy6_regs⟩ => ?_)
    (by omega)
  have hy6_sz_x : y6.bitSize = x.bitSize := hy6_sz.trans hy5_sz_x
  have hy6_low_y4 : ∀ a < epochMetaWords U w N, y6.mem a = y4.mem a :=
    fun a ha => (hy6_meta a ha).trans (congrFun hy5_mem a)
  obtain ⟨hy6_lm, hy6_gm, hy6_td, hy6_dt, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy6_low_y4
  have hy6_gb : GMBasesLoaded N y6 :=
    hy5_gb.congr_regs (fun r hr1 _ => hy6_regs r (by omega))
  have hy6_regs_ge31 : ∀ r : Fin 280, 31 ≤ r.val → y6.regs r = x.regs r := by
    intro r hr
    rw [hy6_regs r (by omega), hy5_regs r (Or.inr (by omega)), hy4_regs r (by omega),
      hy3_regs r (by omega) (by intro h; subst h; omega),
      hy2_regs r (by omega), hy1_regs r hr]
  refine DemonicExecWithin.step_const (T := 1) hfit_1 ?_
  have heval_k1 : BinOp.eval .add ((y6.set 16 1).regs rK) ((y6.set 16 1).regs 16) = k + 1 := by
    have hrK_ne16 : rK ≠ 16 := by intro h; subst h; omega
    simp [BinOp.eval, BitRAM.Data.set, hrK_ne16, hy6_regs_ge31 rK hrK_ge, hrK]
  refine DemonicExecWithin.bin (by rw [heval_k1]; exact hfit_k1) ?_
  rw [heval_k1]
  set z := (y6.set 16 1).set rK (k + 1)
  have hz_wf : z.WellFormed w := wf_set rK (wf_set 16 hy6_wf hfit_1) hfit_k1
  have hz_er : EpochRegs U V w N z :=
    hy6_er.congr_regs (fun r hr1 _ => by
      dsimp only [z, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; subst h; omega),
        Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hz_gb : GMBasesLoaded N z :=
    hy6_gb.congr_regs (fun r hr1 hr2 => by
      dsimp only [z, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; subst h; omega),
        Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hz_st : z.toBitMemoryState = y6.toBitMemoryState := rfl
  have hz_mem : z.mem = y6.mem := rfl
  obtain ⟨_, _, _, hq_s', hv_s', hl_s', hgm_s'⟩ :=
    Succinct.promoteStepProg_effect (U := U) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hb_pos s_fix ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  have hgu_lt_N : g_u < N := by dsimp only [g_u]; omega
  have hqtop_lt : q_top < 2 ^ quotientBits U N := Succinct.quotAt_lt _ _ _ _ _ _ _
  have hvtop_lt : v_top < 2 ^ valBits V := Succinct.valAt_lt _ _ _ _ _ _ _ _
  obtain ⟨_, _, hq1, hv1, _, hg1⟩ :=
    Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hgu_lt_N hqtop_lt s_fix
  obtain ⟨_, _, hq2, hv2, _, hg2⟩ :=
    Succinct.writeValProg_effect (base := 0) (h_space := Succinct.hashSpace U w N)
      hw hgu_lt_N hvtop_lt s₁
  have hgm_s2 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₂.mem = gm₀ := by
    rw [hg2, hg1, hgm_eq]
  have htail_s2 : Succinct.TailBijection N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₂.mem)
      (fun b' => Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₂.mem (Succinct.gmRIdx b'))
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₂.mem 1) := by
    rw [hgm_s2]; exact htail
  have hr_s2 : 1 ≤ Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s₂.mem
      (Succinct.gmRIdx b) := by
    rw [hgm_s2]; exact hr_pos
  obtain ⟨_, _, hq3, hv3, hl3, hg3⟩ :=
    Succinct.removeLastTailItemProg_effect (U := U) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hb_pos hb s₂ htail_s2 hr_s2
  have hq_s'_s3 : Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s'.mem =
      Function.update (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s₃.mem) b_win q_u := by
    rw [hq_s', hq3, hgm_s2, hq2, hq1, hgm_eq]
  have hv_s'_s3 : Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s'.mem =
      Function.update (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s₃.mem) b_win v_u := by
    rw [hv_s', hv3, hgm_s2, hv2, hv1, hgm_eq]
  have hz_gm_y2 : gmAtBit U w N z.mem = gmAtBit U w N y2.mem := by
    rw [hz_mem, hy6_gm, hy4_gm, hy3_mem]
  have hz_gm0 : gmAtBit U w N z.mem 0 = gm₀ 0 := by rw [hz_gm_y2, hy2_gm_0]
  have hz_gm1 : gmAtBit U w N z.mem 1 = n_win' := by rw [hz_gm_y2, hy2_gm_1]
  have hz_bwin : gmAtBit U w N z.mem 0 * K + (k + 1) = b_win + 1 := by
    rw [hz_gm0]; dsimp only [b_win]; omega
  have hz_m0 : b_win + 1 + n_win' = m₀ := by dsimp only [m₀]; omega
  obtain ⟨hwin_s, htd_M, hdt_M⟩ := winShrinkLeft_spec hy3_win (by omega)
    (fun i => by rw [hy3_mem]; have := hy2_cpl.td_lt i; rwa [max_eq_left hM_pos] at this)
    (fun i => by rw [hy3_mem]; have := hy2_cpl.dt_lt i; rwa [max_eq_left hM_pos] at this)
  refine ⟨hz_wf, hz_er, hz_gb, hy6_sz_x, ?_,
    by simp +decide [z, BitRAM.Data.set],
    fun a ha => (hy6_low_y4 a (by
      rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega)).trans (hy4_low_x a ha),
    fun r hr hne => by
      dsimp only [z, BitRAM.Data.set]
      rw [Function.update_of_ne hne,
        Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
        hy6_regs_ge31 r hr]⟩
  refine ⟨?_, ?_, ?_, fun i => ?_, fun i => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hz_gm_y2, hy2_gm, hgm_s', hgm_eq]
  · dsimp only [BitRAM.Data.toBitMemoryState]
    have hy2_lm := hy2_cpl.lm_eq
    change lmAtBit U w N y2.mem = _ at hy2_lm
    rw [hz_mem, hy6_lm, hy4_lm, hy3_mem, hy2_lm, hl3, hl_s']
    exact (Succinct.writeValProg_effect hw hgu_lt_N hvtop_lt s₁).2.2.2.2.1.trans
      (Succinct.writeQuotProg_effect hw hgu_lt_N hqtop_lt s_fix).2.2.2.2.1
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hz_bwin, hz_gm1, hz_mem, hy6_td, hy6_dt, hy4_td, hy4_dt]
    exact hwin_s
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hz_mem, hy6_td, hy4_td, max_eq_left hM_pos]; exact htd_M i
  · dsimp only [BitRAM.Data.toBitMemoryState]
    rw [hz_mem, hy6_dt, hy4_dt, max_eq_left hM_pos]; exact hdt_M i
  · rw [hz_bwin, hz_gm1] at hd
    rw [hz_bwin]
    have hz_st : z.toBitMemoryState = y6.toBitMemoryState := rfl
    have hz_dt : dtAtBit U w N z.toBitMemoryState.mem =
        (winShrinkLeft (maxTailItems N) b_win n_win'
          (tdAtBit U w N y3.mem, dtAtBit U w N y3.mem)).2 := by
      dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_mem, hy6_dt, hy4_dt]
    rw [hz_dt, hz_st, hq_s'_s3]
    by_cases heq : d = b_win
    · subst heq
      have hphys_b : physByBase N (b_win + 1)
          (winShrinkLeft (maxTailItems N) b_win n_win'
            (tdAtBit U w N y3.mem, dtAtBit U w N y3.mem)).2 b_win = b_win := by
        unfold physByBase
        rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_left (Nat.lt_succ_self b_win)]
      rw [hy6_q, hphys_b, Function.update_self]
    · obtain ⟨hq_o, _⟩ := hy6_other d (by rw [← hz_m0]; exact hd) heq
      have hy5_q : denseQuotAt U V w N y5.toBitMemoryState d =
          denseQuotAt U V w N y4.toBitMemoryState d := by rw [hy5_st]
      rw [hq_o, hy5_q, (hy4_items d hd heq).1]
      have hy3_q : ∀ idx, denseQuotAt U V w N y3.toBitMemoryState idx =
          denseQuotAt U V w N y2.toBitMemoryState idx := fun _ => by rw [hy3_st]
      have hphys_ne : physByBase N (b_win + 1)
          (winShrinkLeft (maxTailItems N) b_win n_win'
            (tdAtBit U w N y3.mem, dtAtBit U w N y3.mem)).2 d ≠ b_win := by
        unfold physByBase
        rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
        split_ifs with hlt
        · omega
        · have hown := hwin_s.owner_valid d (by omega) hd
          have := hown.1
          omega
      rw [hy3_q, Function.update_of_ne hphys_ne,
        (physByBase_winShrinkLeft_ite hb_pos hy3_win (by omega)).2 d hd heq, hy3_mem]
      set idx := if d = denseOfCirc (maxTailItems N) b_win (tdAtBit U w N y2.mem n_win')
        then b_win else d
      have hidx_lt : idx < b_win + gmAtBit U w N y1.mem 1 := by
        rw [hy1_gm]
        change idx < b_win + n_win
        dsimp only [idx]; split_ifs <;> omega
      exact hy2_cpl.quot_eq idx hidx_lt
  · rw [hz_bwin, hz_gm1] at hd
    rw [hz_bwin]
    have hz_st : z.toBitMemoryState = y6.toBitMemoryState := rfl
    have hz_dt : dtAtBit U w N z.toBitMemoryState.mem =
        (winShrinkLeft (maxTailItems N) b_win n_win'
          (tdAtBit U w N y3.mem, dtAtBit U w N y3.mem)).2 := by
      dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_mem, hy6_dt, hy4_dt]
    rw [hz_dt, hz_st, hv_s'_s3]
    by_cases heq : d = b_win
    · subst heq
      have hphys_b : physByBase N (b_win + 1)
          (winShrinkLeft (maxTailItems N) b_win n_win'
            (tdAtBit U w N y3.mem, dtAtBit U w N y3.mem)).2 b_win = b_win := by
        unfold physByBase
        rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_left (Nat.lt_succ_self b_win)]
      rw [hy6_v, hphys_b, Function.update_self]
    · obtain ⟨_, hv_o⟩ := hy6_other d (by rw [← hz_m0]; exact hd) heq
      have hy5_v : denseValAt U V w N y5.toBitMemoryState d =
          denseValAt U V w N y4.toBitMemoryState d := by rw [hy5_st]
      rw [hv_o, hy5_v, (hy4_items d hd heq).2]
      have hy3_v : ∀ idx, denseValAt U V w N y3.toBitMemoryState idx =
          denseValAt U V w N y2.toBitMemoryState idx := fun _ => by rw [hy3_st]
      have hphys_ne : physByBase N (b_win + 1)
          (winShrinkLeft (maxTailItems N) b_win n_win'
            (tdAtBit U w N y3.mem, dtAtBit U w N y3.mem)).2 d ≠ b_win := by
        unfold physByBase
        rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
        split_ifs with hlt
        · omega
        · have hown := hwin_s.owner_valid d (by omega) hd
          have := hown.1
          omega
      rw [hy3_v, Function.update_of_ne hphys_ne,
        (physByBase_winShrinkLeft_ite hb_pos hy3_win (by omega)).2 d hd heq, hy3_mem]
      set idx := if d = denseOfCirc (maxTailItems N) b_win (tdAtBit U w N y2.mem n_win')
        then b_win else d
      have hidx_lt : idx < b_win + gmAtBit U w N y1.mem 1 := by
        rw [hy1_gm]
        change idx < b_win + n_win
        dsimp only [idx]; split_ifs <;> omega
      exact hy2_cpl.val_eq idx hidx_lt

/-- Uniform `BitRAM.Code .standard 280` loop executing `promoteStepRegCode rB 31` while
`r31 < r250` (`k < slabSize N`). -/
@[expose]
def promoteLoopRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .loop (.lt 31 250) (promoteStepRegCode rB 31)

theorem promoteLoopRegCode_exec {U V w N b : ℕ} {rB : Fin 280}
    {s₀ : Memory.State}
    (hrB_ge : 32 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N) :
    ∀ m k (s_fix : Memory.State) (x : BitRAM.Data 280),
      k + m = slabSize N →
      x.WellFormed w →
      EpochRegs U V w N x →
      GMBasesLoaded N x →
      x.mem 2 = itemBits U V N →
      x.mem 3 = epochMetaBits U w N →
      Succinct.PromoteLoopInv U V w N (Succinct.hashSpace U w N) 0 b s₀ k s_fix →
      WindowCoupled U V w N (gmAtBit U w N x.mem 0 * slabSize N + k)
        (gmAtBit U w N x.mem 1) (gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1)
        s_fix x.toBitMemoryState →
      itemBitOff U V w N (gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1) ≤
        x.bitSize →
      x.regs rB = b →
      x.regs 31 = k →
      let s_end := (Memory.spec 0).clientState s_fix
        (iterate (Succinct.promoteStepProg U V w N (Succinct.hashSpace U w N))
          (0, b) m k)
      BitRAM.DemonicExecWithin w (promoteLoopRegCode rB) x
        (fun z =>
          z.WellFormed w ∧
          EpochRegs U V w N z ∧
          GMBasesLoaded N z ∧
          z.bitSize = x.bitSize ∧
          Succinct.PromoteLoopInv U V w N (Succinct.hashSpace U w N) 0 b s₀ (k + m) s_end ∧
          WindowCoupled U V w N (gmAtBit U w N z.mem 0 * slabSize N + (k + m))
            (gmAtBit U w N z.mem 1)
            (gmAtBit U w N z.mem 0 * slabSize N + (k + m) + gmAtBit U w N z.mem 1)
            s_end z.toBitMemoryState ∧
          (∀ a < offGM U w N, z.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r))
        (2 + 1967 * m) := by
  intro m
  induction m with
  | zero =>
    intro k s_fix x hkm hx her hgb _ _ hinv hcpl _ _ hr31 s_end
    have hk_ge : ¬BitRAM.CondHolds (.lt 31 250) x := by
      change ¬(x.regs 31 < x.regs 250)
      rw [hr31, (her.active hN_pos).2.2.2.2.2.1]; omega
    have hs_end : s_end = s_fix := rfl
    exact .loop_exit hk_ge
      ⟨hx, her, hgb, rfl, by simpa [hs_end] using hinv,
        by simpa [hs_end] using hcpl,
        fun _ _ => rfl, fun _ _ => rfl⟩ (by omega)
  | succ m ih =>
    intro k s_fix x hkm hx her hgb hm2 hm3 hinv hcpl hsz hrB hr31 s_end
    have hk_lt : k < slabSize N := by omega
    have hcond : BitRAM.CondHolds (.lt 31 250) x := by
      change x.regs 31 < x.regs 250
      rw [hr31, (her.active hN_pos).2.2.2.2.2.1]; exact hk_lt
    have hstep_inv := Succinct.promoteStepInv_of_loopInv hinv hk_lt
    obtain ⟨hres_step, hinv_next⟩ := Succinct.promoteLoopInv_step hw hb_pos hinv hk_lt
    set s_next := (Memory.spec 0).clientState s_fix
      (Succinct.promoteStepProg U V w N (Succinct.hashSpace U w N) ((0, b), k))
    have hne_B31 : rB ≠ 31 := by intro h; subst h; omega
    refine .loop_iter (T₁ := 1965) (T₂ := 2 + 1967 * m) hcond
      (promoteStepRegCode_exec (by omega) (by decide) (by decide) hne_B31
        hw hN_pos hnU hU hV hb_pos hx her hgb hm2 hm3 hstep_inv hcpl hsz hrB hr31)
      (fun y ⟨hy_wf, hy_er, hy_gb, hy_sz, hy_cpl, hy_31, hy_low, hy_regs⟩ => ?_)
      (by omega)
    have hm_eq : gmAtBit U w N y.mem 0 * slabSize N + (k + 1) + gmAtBit U w N y.mem 1 =
        gmAtBit U w N x.mem 0 * slabSize N + k + gmAtBit U w N x.mem 1 := by
      have hy_gm := hy_cpl.gm_eq
      have hx_gm := hcpl.gm_eq
      change gmAtBit U w N y.mem =
        Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_next.mem at hy_gm
      change gmAtBit U w N x.mem =
        Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem at hx_gm
      rw [hy_gm, hx_gm]
      have h0 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_next.mem 0 =
          Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem 0 :=
        hinv_next.gm0_eq.trans hinv.gm0_eq.symm
      have h1 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_next.mem 1 + (k + 1) =
          Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem 1 + k :=
        hinv_next.gm1_eq.trans hinv.gm1_eq.symm
      rw [h0]
      omega
    have hsend_eq : s_end = (Memory.spec 0).clientState s_next
        (iterate (Succinct.promoteStepProg U V w N (Succinct.hashSpace U w N))
          (0, b) m (k + 1)) := by
      dsimp only [s_end, iterate]
      rw [StateTransitionSpec.clientState_bind, hres_step]
    refine (ih (k + 1) s_next y (by omega) hy_wf hy_er hy_gb
      (by rw [hy_low 2 (by unfold offGM offLM offHash; omega), hm2])
      (by rw [hy_low 3 (by unfold offGM offLM offHash; omega), hm3])
      hinv_next hy_cpl (by rw [hm_eq, hy_sz]; exact hsz)
      (by rw [hy_regs rB (by omega) hne_B31, hrB]) hy_31).mono
      (fun z ⟨hz_wf, hz_er, hz_gb, hz_sz, hz_inv, hz_cpl, hz_low, hz_regs⟩ => ?_) le_rfl
    rw [hsend_eq, show k + (m + 1) = (k + 1) + m by omega]
    exact ⟨hz_wf, hz_er, hz_gb, hz_sz.trans hy_sz, hz_inv, hz_cpl,
      fun a ha => (hz_low a ha).trans (hy_low a ha),
      fun r hr => (hz_regs r hr).trans (hy_regs r (by omega) (by intro h; subst h; omega))⟩

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.promoteSlabProg`:
initializes `r31 = 0`, runs `promoteLoopRegCode rB`, and pushes the new slab via
`gmPushSlabRegCode rB` (`32 ≤ rB`, `T = 633 + 1967 * slabSize N`). -/
@[expose]
def promoteSlabRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 31 0))
  (.seq (promoteLoopRegCode rB)
        (gmPushSlabRegCode rB))

theorem promoteSlabRegCode_exec {U V w N b : ℕ} {rB : Fin 280}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 32 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hpre : Succinct.PromoteSlabInv U V w N (Succinct.hashSpace U w N) 0 b s_fix)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hsz : itemBitOff U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hrB : x.regs rB = b) :
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.promoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b))
    BitRAM.DemonicExecWithin w (promoteSlabRegCode rB) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        z.bitSize = x.bitSize ∧
        FixedCoupled U V w N s' z.toBitMemoryState ∧
        (∀ a < offGM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r))
      (633 + 1967 * slabSize N) := by
  intro s'
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hfit_0 : Fits w 0 := fits_of_le_N hw hnU hU (by omega)
  have hloop0 := Succinct.promoteLoopInv_zero hpre
  have htot_eq : Succinct.totalSlots N (gmAtBit U w N x.mem) =
      gmAtBit U w N x.mem 0 * slabSize N + 0 + gmAtBit U w N x.mem 1 := by
    unfold Succinct.totalSlots; rw [ite_eq_right hb0]; omega
  unfold promoteSlabRegCode
  refine (DemonicExecWithin.step_const (T := 632 + 1967 * slabSize N) hfit_0 ?_).mono
    (fun z hz => hz) (by omega)
  set s0 := x.set 31 0
  have hs0_wf : s0.WellFormed w := wf_set 31 hx hfit_0
  have hs0_er : EpochRegs U V w N s0 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s0, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs0_gb : GMBasesLoaded N s0 :=
    hgb.congr_regs (fun r hr1 hr2 => by
      dsimp only [s0, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs0_rB : s0.regs rB = b := by
    dsimp only [s0, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; subst h; omega), hrB]
  have hs0_cpl : WindowCoupled U V w N (gmAtBit U w N s0.mem 0 * slabSize N + 0)
      (gmAtBit U w N s0.mem 1)
      (gmAtBit U w N s0.mem 0 * slabSize N + 0 + gmAtBit U w N s0.mem 1)
      s_fix s0.toBitMemoryState := by
    change WindowCoupled U V w N (gmAtBit U w N x.mem 0 * slabSize N + 0)
      (gmAtBit U w N x.mem 1)
      (gmAtBit U w N x.mem 0 * slabSize N + 0 + gmAtBit U w N x.mem 1)
      s_fix x.toBitMemoryState
    rw [← htot_eq, Nat.add_zero]
    exact hcpl
  refine .seq (T₁ := 2 + 1967 * slabSize N) (T₂ := 630)
    (promoteLoopRegCode_exec hrB_ge hw hN_pos hnU hU hV hb_pos (slabSize N) 0 s_fix s0
      (by omega) hs0_wf hs0_er hs0_gb hm2 hm3 hloop0 hs0_cpl
      (by
        change itemBitOff U V w N (gmAtBit U w N x.mem 0 * slabSize N + 0 + gmAtBit U w N x.mem 1) ≤
          x.bitSize
        rwa [← htot_eq])
      hs0_rB (by simp +decide [s0, BitRAM.Data.set]))
    (fun y1 ⟨hy1_wf, hy1_er, hy1_gb, hy1_sz, hy1_inv, hy1_cpl, hy1_low, hy1_regs⟩ => ?_)
    (by omega)
  rw [Nat.zero_add] at hy1_inv hy1_cpl
  set s_loop := (Memory.spec 0).clientState s_fix
    (iterate (Succinct.promoteStepProg U V w N (Succinct.hashSpace U w N))
      (0, b) (slabSize N) 0)
  have hgm_y1 : gmAtBit U w N y1.mem =
      Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_loop.mem := hy1_cpl.gm_eq
  have hslab_y1 : Succinct.SlabBijection N (gmAtBit U w N y1.mem)
      (fun b' => gmAtBit U w N y1.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N y1.mem 0) := by
    rw [hgm_y1]; exact hy1_inv.slab_bij
  have hp_lt_y1 : gmAtBit U w N y1.mem 0 < maxFullSlabs N := by
    rw [hgm_y1]
    have htot_loop := hy1_inv.tot_le
    exact Succinct.nslabs_lt_maxFullSlabs_of_mul_le hb_pos (by rw [Nat.add_one_mul]; omega)
  have hsz_meta : epochMetaBits U w N ≤ y1.bitSize := by
    rw [hy1_sz]; exact (Nat.le_add_right _ _).trans hsz
  refine (gmPushSlabRegCode_exec (by omega) hw hN_pos hnU hU hb_pos hpre.1
    hy1_wf hy1_er hy1_gb hsz_meta (by rw [hy1_regs rB hrB_ge, hs0_rB])
    hslab_y1 hp_lt_y1).mono
    (fun z ⟨hz_sz, hz_wf, hz_er, hz_gb, hz_gm, hz_lm, hz_td, hz_dt, hz_out, hz_items,
      hz_regs⟩ => ?_) le_rfl
  have hs'_eq : s' = (Memory.spec 0).clientState s_loop
      (Succinct.gmPushSlabProg U V w N (Succinct.hashSpace U w N) (0, b)) := by
    dsimp only [s', s_loop, Succinct.promoteSlabProg, Succinct.promoteLoopProg]
    rw [StateTransitionSpec.clientState_bind]
  obtain ⟨_, _, hq_push, hv_push, hl_push, hgm_push⟩ :=
    Succinct.gmPushSlabProg_effect (base := 0) (U := U) (V := V)
      (h_space := Succinct.hashSpace U w N) hw hb_pos hpre.1 s_loop hy1_inv.slab_bij
      (hgm_y1 ▸ hp_lt_y1)
  have hfields := Succinct.gmPushSlab_fields (gmAtBit U w N y1.mem) hpre.1
  have hz_gm0 : gmAtBit U w N z.mem 0 * slabSize N =
      gmAtBit U w N y1.mem 0 * slabSize N + slabSize N := by
    rw [hz_gm, hfields.1, Nat.add_one_mul]
  have hz_gm1 : gmAtBit U w N z.mem 1 = gmAtBit U w N y1.mem 1 := by
    rw [hz_gm, hfields.2.1]
  have hz_tot : Succinct.totalSlots N (gmAtBit U w N z.mem) =
      gmAtBit U w N y1.mem 0 * slabSize N + slabSize N + gmAtBit U w N y1.mem 1 := by
    unfold Succinct.totalSlots; rw [ite_eq_right hb0, hz_gm0, hz_gm1]
  refine ⟨hz_wf, hz_er, hz_gb, hz_sz.trans hy1_sz,
    ⟨by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_gm, hs'_eq, hgm_push, hgm_y1],
     by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_lm, hs'_eq, hl_push]; exact hy1_cpl.lm_eq,
     by dsimp only [BitRAM.Data.toBitMemoryState]
        rw [hz_gm0, hz_gm1, hz_td, hz_dt]; exact hy1_cpl.win_inv,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_td]; exact hy1_cpl.td_lt i,
     fun i => by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_dt]; exact hy1_cpl.dt_lt i,
     fun d hd => by
       change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
       rw [hz_tot] at hd
       change denseQuotAt U V w N z.toBitMemoryState d =
         Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s'.mem
           (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
       rw [(hz_items d).1, hs'_eq, hq_push, hz_gm0, hz_dt]
       exact hy1_cpl.quot_eq d hd,
     fun d hd => by
       change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
       rw [hz_tot] at hd
       change denseValAt U V w N z.toBitMemoryState d =
         Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
           (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
       rw [(hz_items d).2, hs'_eq, hv_push, hz_gm0, hz_dt]
       exact hy1_cpl.val_eq d hd⟩,
    fun a ha => (hz_out a (Or.inl ha)).trans (hy1_low a ha),
    fun r hr => (hz_regs r (by omega)).trans
      ((hy1_regs r hr).trans (by
        dsimp only [s0, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]))⟩

end Cslib.DataStructure.Dictionary.BitResizable
