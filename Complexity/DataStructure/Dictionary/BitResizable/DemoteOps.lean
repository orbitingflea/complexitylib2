/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.PromoteOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps

/-!
# Slab Demotion in `BitRAM` (`demotePrepRegCode`, `demoteStepRegCode`, `demoteSlabRegCode`)

This module implements the uniform `BitRAM.Code .standard 280` programs for:
1. One iteration of the slab demotion loop (`demotePrepRegCode`, `demoteStepRegCode`),
   synchronized with `Succinct.demoteStepProg` via `WindowCoupled` and `winGrowLeft`.
2. The `K = slabSize N`-step slab demotion loop (`demoteLoopRegCode`) and full slab demotion
   (`demoteSlabRegCode`), synchronized with `Succinct.demoteSlabProg` via `FixedCoupled`.
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

/-! ## Section 1: `demotePrepRegCode` -/

theorem physByBase_lt_base {N b_win d : ℕ} {dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hd : d < b_win) :
    physByBase N b_win dt d = d := by
  unfold physByBase
  rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_left hd]

theorem physByBase_ne_of_lt_base {N b_win n_win g d : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hwin : WindowInv (maxTailItems N) b_win n_win td dt)
    (htot : b_win + n_win ≤ N) (hg : g < b_win) (hd : d < b_win + n_win) (hne : d ≠ g) :
    physByBase N b_win dt d ≠ g := by
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  unfold physByBase
  rw [ite_eq_right hb0]
  split_ifs with hlt
  · exact hne
  · have hown := hwin.owner_valid d (by omega) hd
    have := hown.1
    omega

/-- Uniform `BitRAM.Code .standard 280` prefix of `demoteStepRegCode`:
given `rB = b` and `rK = k` (`31 ≤ rB, rK`), computes `g_del = p_del * K + u` in `r26` and
`g_last = (gm 0 - 1) * K + u` in `r27`, loads `n_win = gm 1` into `r28` and `(q_del, v_del)`
into `(r29, r30)`, and copies dense item `g_last` into `g_del` (`T = 431`). -/
@[expose]
def demotePrepRegCode (rB rK : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 16 1))
  (.seq (.op (.bin .sub 16 250 16))
  (.seq (.op (.bin .sub 16 16 rK))
  (.seq (readGMBucketRegCode 2 rB 26)
  (.seq (readGMConstRegCode 0 27)
  (.seq (readGMConstRegCode 1 28)
  (.seq (.op (.const 17 1))
  (.seq (.op (.bin .sub 27 27 17))
  (.seq (.op (.bin .mul 26 26 250))
  (.seq (.op (.bin .add 26 26 16))
  (.seq (.op (.bin .mul 27 27 250))
  (.seq (.op (.bin .add 27 27 16))
  (.seq (readDenseQRegCode 26 29)
  (.seq (readDenseVRegCode 26 30)
        (copyDenseItemRegCode 27 26))))))))))))))

theorem demotePrepRegCode_exec {U V w N b k : ℕ} {rB rK : Fin 280}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 31 ≤ rB.val) (hrK_ge : 31 ≤ rK.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hpre : Succinct.DemoteStepInv U V w N (Succinct.hashSpace U w N) 0 b k s_fix)
    (hcpl : WindowCoupled U V w N
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k))
      (gmAtBit U w N x.mem 1)
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) + gmAtBit U w N x.mem 1)
      s_fix x.toBitMemoryState)
    (hsz : itemBitOff U V w N
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) + gmAtBit U w N x.mem 1) ≤
      x.bitSize)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k) :
    let K := slabSize N
    let gm₀ := gmAtBit U w N x.mem
    let b_win := (gm₀ 0 - 1) * K + (K - k)
    let n_win := gm₀ 1
    let m₀ := b_win + n_win
    let u := (K - 1) - k
    let p_del := gm₀ (Succinct.gmSlabTopIdx b)
    let p_last := gm₀ 0 - 1
    let g_del := p_del * K + u
    let g_last := p_last * K + u
    let q_del := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_del
    let v_del := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_del
    let q_last := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_last
    let v_last := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_last
    let s₁ := (Memory.spec 0).clientState s_fix
      (Succinct.writeQuotProg U w N (Succinct.hashSpace U w N) ((0, g_del), q_last))
    let s₂ := (Memory.spec 0).clientState s₁
      (Succinct.writeValProg U V w N (Succinct.hashSpace U w N) ((0, g_del), v_last))
    BitRAM.DemonicExecWithin w (demotePrepRegCode rB rK) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        GMBasesLoaded N y ∧
        y.bitSize = x.bitSize ∧
        WindowCoupled U V w N b_win n_win m₀ s₂ y.toBitMemoryState ∧
        y.regs 27 = g_last ∧
        y.regs 28 = n_win ∧
        y.regs 29 = q_del ∧
        y.regs 30 = v_del ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 31 ≤ r.val → y.regs r = x.regs r)) 431 := by
  intro K gm₀ b_win n_win m₀ u p_del p_last g_del g_last q_del v_del q_last v_last s₁ s₂
  change WindowCoupled U V w N b_win n_win m₀ s_fix x.toBitMemoryState at hcpl
  rcases hpre with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  have hgm_eq : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem = gm₀ :=
    hcpl.gm_eq.symm
  have htail : Succinct.TailBijection N gm₀ (fun b' => gm₀ (Succinct.gmRIdx b')) (gm₀ 1) := by
    rwa [hgm_eq] at htail_fix
  have hslab : Succinct.SlabBijection N gm₀ (fun b' => gm₀ (Succinct.gmQIdx b')) (gm₀ 0) := by
    rwa [hgm_eq] at hslab_fix
  have hqb_pos : 1 ≤ gm₀ (Succinct.gmQIdx b) := by
    rwa [hgm_eq] at hqb_fix
  have htot : b_win + n_win ≤ N := by
    dsimp only [b_win, n_win, K, gm₀]
    rwa [hgm_eq] at htot_fix
  have htop_eq := hslab.top_eq b hb (gm₀ (Succinct.gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : p_del < gm₀ 0 := by
    dsimp only [p_del]; rw [htop_eq]
    exact hslab.ptr_lt b hb (gm₀ (Succinct.gmQIdx b) - 1) (by omega)
  have hglast_eq : g_last + 1 = b_win := by
    dsimp only [g_last, p_last, u, b_win]; omega
  have hgdel_le_glast : g_del ≤ g_last := by
    have hmul : p_del * K ≤ p_last * K := Nat.mul_le_mul_right K (by dsimp only [p_last]; omega)
    dsimp only [g_del, g_last]; omega
  have hglast_lt_bwin : g_last < b_win := by omega
  have hgdel_lt_bwin : g_del < b_win := lt_of_le_of_lt hgdel_le_glast hglast_lt_bwin
  have hglast_lt_m0 : g_last < m₀ := by dsimp only [m₀]; omega
  have hgdel_lt_m0 : g_del < m₀ := by dsimp only [m₀]; omega
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen N := Succinct.gmSlabTopIdx_lt hb_pos hb
  have h250 : x.regs 250 = K := (her.active hN_pos).2.2.2.2.2.1
  have hfit_1 : Fits w 1 := hfit_N 1 (by omega)
  have hfit_K1 : Fits w (K - 1) :=
    hfit_N (K - 1) ((Nat.sub_le _ _).trans (Succinct.slabSize_le_max_n_one N))
  have hfit_u : Fits w u :=
    hfit_N u ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Succinct.slabSize_le_max_n_one N)))
  have hK_pos : 0 < K := Nat.zero_lt_of_lt hk_lt
  have hplast_le : p_last ≤ p_last * K := Nat.le_mul_of_pos_right p_last hK_pos
  have hpdel_le : p_del ≤ p_del * K := Nat.le_mul_of_pos_right p_del hK_pos
  have hfit_plast : Fits w p_last :=
    hfit_N p_last (by dsimp only [g_last] at hglast_lt_bwin; omega)
  have hfit_pdelK : Fits w (p_del * K) :=
    hfit_N _ (by dsimp only [g_del] at hgdel_lt_bwin; omega)
  have hfit_gdel : Fits w g_del := hfit_N g_del (by omega)
  have hfit_plastK : Fits w (p_last * K) :=
    hfit_N _ (by dsimp only [g_last] at hglast_lt_bwin; omega)
  have hfit_glast : Fits w g_last := hfit_N g_last (by omega)
  unfold demotePrepRegCode
  refine DemonicExecWithin.step_const (T := 430) hfit_1 ?_
  refine step_dExec_bin (v := K - 1) (T := 429)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, h250, K]) hfit_K1 ?_
  refine step_dExec_bin (v := u) (T := 428)
    (by
      have hrK_ne : rK ≠ 16 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hrK_ne, hrK, u]) hfit_u ?_
  set a0 := ((x.set 16 1).set 16 (K - 1)).set 16 u
  have ha0_wf : a0.WellFormed w :=
    wf_set 16 (wf_set 16 (wf_set 16 hx hfit_1) hfit_K1) hfit_u
  have ha0_er : EpochRegs U V w N a0 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [a0, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have ha0_regs_ge17 : ∀ r : Fin 280, 17 ≤ r.val → a0.regs r = x.regs r := by
    intro r hr
    dsimp only [a0, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  refine .seq (T₁ := 49) (T₂ := 379)
    (readGMBucketRegCode_exec (c := 2) (rB := rB) (rDst := 26)
      (by omega) (by decide) (by decide) hw hN_pos hnU hU ha0_wf ha0_er hsz_meta
      (by rw [ha0_regs_ge17 rB (by omega), hrB]) htop_idx_lt)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_26, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  refine .seq (T₁ := 46) (T₂ := 333)
    (readGMConstRegCode_exec (idx := 0) (rDst := 27) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy1_wf hy1_er (by rw [hy1_sz]; exact hsz_meta))
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_27, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  refine .seq (T₁ := 46) (T₂ := 287)
    (readGMConstRegCode_exec (idx := 1) (rDst := 28) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hy2_wf hy2_er (by rw [hy2_sz]; exact hsz_meta))
    (fun y3 ⟨hy3_st, hy3_wf, hy3_er, hy3_28, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
  have hy3_16 : y3.regs 16 = u := by
    rw [hy3_regs 16 (by decide) (by decide), hy2_regs 16 (by decide) (by decide),
      hy1_regs 16 (by decide) (by decide)]
    simp +decide [a0, BitRAM.Data.set]
  have hy3_26 : y3.regs 26 = p_del := by
    rw [hy3_regs 26 (by decide) (by decide), hy2_regs 26 (by decide) (by decide), hy1_26]
    rfl
  have hy3_27 : y3.regs 27 = gm₀ 0 := by
    rw [hy3_regs 27 (by decide) (by decide), hy2_27, hy1_mem]
  have hy3_28_val : y3.regs 28 = n_win := by
    rw [hy3_28, hy2_mem]
  have hy3_250 : y3.regs 250 = K := (hy3_er.active hN_pos).2.2.2.2.2.1
  refine DemonicExecWithin.step_const (T := 286) hfit_1 ?_
  refine step_dExec_bin (v := p_last) (T := 285)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hy3_27, p_last]) hfit_plast ?_
  refine step_dExec_bin (v := p_del * K) (T := 284)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hy3_26, hy3_250]) hfit_pdelK ?_
  refine step_dExec_bin (v := g_del) (T := 283)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hy3_16, g_del]) hfit_gdel ?_
  refine step_dExec_bin (v := p_last * K) (T := 282)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hy3_250]) hfit_plastK ?_
  refine step_dExec_bin (v := g_last) (T := 281)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hy3_16, g_last]) hfit_glast ?_
  set a3 :=
    (((((y3.set 17 1).set 27 p_last).set 26 (p_del * K)).set 26 g_del).set 27
      (p_last * K)).set 27 g_last
  have ha3_wf : a3.WellFormed w :=
    wf_set 27 (wf_set 27 (wf_set 26 (wf_set 26 (wf_set 27 (wf_set 17 hy3_wf hfit_1) hfit_plast)
      hfit_pdelK) hfit_gdel) hfit_plastK) hfit_glast
  have ha3_er : EpochRegs U V w N a3 :=
    hy3_er.congr_regs (fun r hr1 _ => by
      dsimp only [a3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have ha3_26 : a3.regs 26 = g_del := by simp +decide [a3, BitRAM.Data.set]
  have ha3_27 : a3.regs 27 = g_last := by simp +decide [a3, BitRAM.Data.set]
  refine .seq (T₁ := 42) (T₂ := 239)
    (readDenseQRegCode_exec (n_t := m₀) (d := g_del) (rD := 26) (rDst := 29) (by decide)
      hw (le_of_lt hU) ha3_wf ha3_er hgdel_lt_m0 ha3_26
      (by rw [show a3.bitSize = x.bitSize from hy3_sz]; exact hsz)
      (by rw [show a3.mem = x.mem from hy3_mem, hm2])
      (by rw [show a3.mem = x.mem from hy3_mem, hm3]))
    (fun y4 ⟨hy4_st, hy4_wf, hy4_29, hy4_regs⟩ => ?_) (by omega)
  have hy4_st_x : y4.toBitMemoryState = x.toBitMemoryState := hy4_st.trans hy3_st_x
  have hy4_mem : y4.mem = x.mem := congrArg BitMemory.State.mem hy4_st_x
  have hy4_sz : y4.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy4_st_x
  have hy4_er : EpochRegs U V w N y4 :=
    ha3_er.congr_regs (fun r hr1 _ =>
      hy4_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy4_26 : y4.regs 26 = g_del := by
    rw [hy4_regs 26 (by decide) (by decide), ha3_26]
  refine .seq (T₁ := 44) (T₂ := 195)
    (readDenseVRegCode_exec (n_t := m₀) (d := g_del) (rD := 26) (rDst := 30) (by decide)
      hw hV hy4_wf hy4_er hgdel_lt_m0 hy4_26 (by rw [hy4_sz]; exact hsz)
      (by rw [hy4_mem, hm2]) (by rw [hy4_mem, hm3]))
    (fun y5 ⟨hy5_st, hy5_wf, hy5_30, hy5_regs⟩ => ?_) (by omega)
  have hy5_st_x : y5.toBitMemoryState = x.toBitMemoryState := hy5_st.trans hy4_st_x
  have hy5_mem : y5.mem = x.mem := congrArg BitMemory.State.mem hy5_st_x
  have hy5_sz : y5.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy5_st_x
  have hy5_er : EpochRegs U V w N y5 :=
    hy4_er.congr_regs (fun r hr1 _ =>
      hy5_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy5_26 : y5.regs 26 = g_del := by
    rw [hy5_regs 26 (by decide) (by decide), hy4_26]
  have hy5_27 : y5.regs 27 = g_last := by
    rw [hy5_regs 27 (by decide) (by decide), hy4_regs 27 (by decide) (by decide), ha3_27]
  refine (copyDenseItemRegCode_exec (n_t := m₀) (rSrc := 27) (rDst := 26) (by decide) (by decide)
    hw (le_of_lt hU) hV hy5_wf hy5_er hglast_lt_m0 hgdel_lt_m0 hy5_27 hy5_26
    (by rw [hy5_sz]; exact hsz) (by rw [hy5_mem, hm2]) (by rw [hy5_mem, hm3])).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_q, hy_v, hy_other, hy_meta, hy_regs⟩ => ?_) le_rfl
  have hy_meta_x : ∀ a < epochMetaWords U w N, y.mem a = x.mem a :=
    fun a ha => (hy_meta a ha).trans (congrFun hy5_mem a)
  obtain ⟨hy_lm, hy_gm, hy_td, hy_dt, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy_meta_x
  have hy5_regs_20 : ∀ r : Fin 280, 20 ≤ r.val →
      r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → y5.regs r = x.regs r := by
    intro r hr h26 h27 h28 h29 h30
    rw [hy5_regs r (by omega) h30, hy4_regs r (by omega) h29]
    dsimp only [a3, BitRAM.Data.set]
    rw [Function.update_of_ne h27, Function.update_of_ne h27,
      Function.update_of_ne h26, Function.update_of_ne h26,
      Function.update_of_ne h27,
      Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
      hy3_regs r (by omega) h28,
      hy2_regs r (by omega) h27,
      hy1_regs r (by omega) h26,
      ha0_regs_ge17 r (by omega)]
  have hy_gb : GMBasesLoaded N y :=
    hgb.congr_regs (fun r hr1 hr2 =>
      (hy_regs r hr1).trans
        (hy5_regs_20 r hr1 (by intro h; subst h; omega) (by intro h; subst h; omega)
          (by intro h; subst h; omega) (by intro h; subst h; omega)
          (by intro h; subst h; omega)))
  have hy_27 : y.regs 27 = g_last := by
    rw [hy_regs 27 (by decide), hy5_27]
  have hy_28 : y.regs 28 = n_win := by
    rw [hy_regs 28 (by decide), hy5_regs 28 (by decide) (by decide),
      hy4_regs 28 (by decide) (by decide)]
    dsimp only [a3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    exact hy3_28_val
  have hphys_del : physByBase N b_win (dtAtBit U w N x.mem) g_del = g_del :=
    physByBase_lt_base hb_pos hgdel_lt_bwin
  have hphys_last : physByBase N b_win (dtAtBit U w N x.mem) g_last = g_last :=
    physByBase_lt_base hb_pos hglast_lt_bwin
  have hy_29 : y.regs 29 = q_del := by
    have hq_eq := hcpl.quot_eq g_del hgdel_lt_m0
    change denseQuotAt U V w N x.toBitMemoryState g_del =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
        (physByBase N b_win (dtAtBit U w N x.mem) g_del) at hq_eq
    change y4.regs 29 = denseQuotAt U V w N y3.toBitMemoryState g_del at hy4_29
    rw [hy_regs 29 (by decide), hy5_regs 29 (by decide) (by decide), hy4_29, hy3_st_x, hq_eq]
    exact congrArg (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem) hphys_del
  have hy_30 : y.regs 30 = v_del := by
    have hv_eq := hcpl.val_eq g_del hgdel_lt_m0
    change denseValAt U V w N x.toBitMemoryState g_del =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
        (physByBase N b_win (dtAtBit U w N x.mem) g_del) at hv_eq
    change y5.regs 30 = denseValAt U V w N y4.toBitMemoryState g_del at hy5_30
    rw [hy_regs 30 (by decide), hy5_30, hy4_st_x, hv_eq]
    exact congrArg (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) hphys_del
  have hgdel_lt_N : g_del < N := lt_of_lt_of_le hgdel_lt_m0 htot
  have hqlast_lt : q_last < 2 ^ quotientBits U N := Succinct.quotAt_lt _ _ _ _ _ _ _
  have hvlast_lt : v_last < 2 ^ valBits V := Succinct.valAt_lt _ _ _ _ _ _ _ _
  obtain ⟨_, _, hq1, hv1, hl1, hg1⟩ :=
    Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hgdel_lt_N hqlast_lt s_fix
  obtain ⟨_, _, hq2, hv2, hl2, hg2⟩ :=
    Succinct.writeValProg_effect (base := 0) (U := U) (h_space := Succinct.hashSpace U w N)
      hw hgdel_lt_N hvlast_lt s₁
  have hwin_x0 : WindowInv (maxTailItems N) b_win n_win
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem) := hcpl.win_inv
  refine ⟨hy_wf, hy_er, hy_gb, hy_sz.trans hy5_sz,
    ⟨?_, ?_, ?_, ?_, ?_, fun d hd => ?_, fun d hd => ?_⟩,
    hy_27, hy_28, hy_29, hy_30, hy_meta_x,
    fun r hr => (hy_regs r (by omega)).trans
      (hy5_regs_20 r (by omega) (by intro h; subst h; omega) (by intro h; subst h; omega)
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
    by_cases heq : d = g_del
    · subst heq
      have hq_last := hcpl.quot_eq g_last hglast_lt_m0
      rw [hx_dt'] at hq_last
      change denseQuotAt U V w N y.toBitMemoryState g_del =
        denseQuotAt U V w N y5.toBitMemoryState g_last at hy_q
      rw [hy_q, hy5_st_x, hq_last, hphys_last, hphys_del, Function.update_self]
    · obtain ⟨hq_d, _⟩ := hy_other d hd heq
      have hq_x := hcpl.quot_eq d hd
      rw [hx_dt'] at hq_x
      rw [hq_d, hy5_st_x, hq_x,
        Function.update_of_ne
          (physByBase_ne_of_lt_base hb_pos hwin_x0 htot hgdel_lt_bwin hd heq)]
  · have hy_dt' : dtAtBit U w N y.toBitMemoryState.mem = dtAtBit U w N x.mem := hy_dt
    have hx_dt' : dtAtBit U w N x.toBitMemoryState.mem = dtAtBit U w N x.mem := rfl
    rw [hy_dt', hv2, hv1]
    by_cases heq : d = g_del
    · subst heq
      have hv_last := hcpl.val_eq g_last hglast_lt_m0
      rw [hx_dt'] at hv_last
      change denseValAt U V w N y.toBitMemoryState g_del =
        denseValAt U V w N y5.toBitMemoryState g_last at hy_v
      rw [hy_v, hy5_st_x, hv_last, hphys_last, hphys_del, Function.update_self]
    · obtain ⟨_, hv_d⟩ := hy_other d hd heq
      have hv_x := hcpl.val_eq d hd
      rw [hx_dt'] at hv_x
      rw [hv_d, hy5_st_x, hv_x,
        Function.update_of_ne
          (physByBase_ne_of_lt_base hb_pos hwin_x0 htot hgdel_lt_bwin hd heq)]

/-! ## Section 2: `demoteStepRegCode`, `demoteLoopRegCode`, and `demoteSlabRegCode` -/

/-- Uniform `BitRAM.Code .standard 280` program executing one iteration of the slab demotion loop:
synchronizes with `Succinct.demoteStepProg` while expanding the circular window left from
`b_win = (gm 0 - 1) * K + (K - k)` to `b_win - 1 = (gm' 0 - 1) * K + (K - (k + 1))`
(`31 ≤ rB, rK`, `rB ≠ rK`, `T = 986`). -/
@[expose]
def demoteStepRegCode (rB rK : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (demotePrepRegCode rB rK)
  (.seq (writeDenseQVRegCode 27 29 30)
  (.seq (winGrowLeftRegCode 27 28)
  (.seq (gmAppendTailRegCode rB)
  (.seq (.op (.const 16 1))
        (.op (.bin .add rK rK 16))))))

theorem demoteStepRegCode_exec {U V w N b k : ℕ} {rB rK : Fin 280}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 31 ≤ rB.val) (hrK_ge : 31 ≤ rK.val) (hrK_lt : rK.val < 240) (hne_BK : rB ≠ rK)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hpre : Succinct.DemoteStepInv U V w N (Succinct.hashSpace U w N) 0 b k s_fix)
    (hcpl : WindowCoupled U V w N
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k))
      (gmAtBit U w N x.mem 1)
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) + gmAtBit U w N x.mem 1)
      s_fix x.toBitMemoryState)
    (hsz : itemBitOff U V w N
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) + gmAtBit U w N x.mem 1) ≤
      x.bitSize)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k) :
    let K := slabSize N
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.demoteStepProg U V w N (Succinct.hashSpace U w N) ((0, b), k))
    BitRAM.DemonicExecWithin w (demoteStepRegCode rB rK) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        z.bitSize = x.bitSize ∧
        WindowCoupled U V w N
          ((gmAtBit U w N z.mem 0 - 1) * K + (K - (k + 1)))
          (gmAtBit U w N z.mem 1)
          ((gmAtBit U w N z.mem 0 - 1) * K + (K - (k + 1)) + gmAtBit U w N z.mem 1)
          s' z.toBitMemoryState ∧
        z.regs rK = k + 1 ∧
        (∀ a < offGM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 31 ≤ r.val → r ≠ rK → z.regs r = x.regs r)) 986 := by
  intro K s'
  set gm₀ := gmAtBit U w N x.mem
  set b_win := (gm₀ 0 - 1) * K + (K - k)
  set n_win := gm₀ 1
  set m₀ := b_win + n_win
  set u := (K - 1) - k
  set p_del := gm₀ (Succinct.gmSlabTopIdx b)
  set p_last := gm₀ 0 - 1
  set g_del := p_del * K + u
  set g_last := p_last * K + u
  set q_del := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_del
  set v_del := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_del
  set q_last := Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem g_last
  set v_last := Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem g_last
  set s₁ := (Memory.spec 0).clientState s_fix
    (Succinct.writeQuotProg U w N (Succinct.hashSpace U w N) ((0, g_del), q_last))
  set s₂ := (Memory.spec 0).clientState s₁
    (Succinct.writeValProg U V w N (Succinct.hashSpace U w N) ((0, g_del), v_last))
  rcases hpre with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  have hgm_eq : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem = gm₀ :=
    hcpl.gm_eq.symm
  have htail : Succinct.TailBijection N gm₀ (fun b' => gm₀ (Succinct.gmRIdx b')) (gm₀ 1) := by
    rwa [hgm_eq] at htail_fix
  have hslab : Succinct.SlabBijection N gm₀ (fun b' => gm₀ (Succinct.gmQIdx b')) (gm₀ 0) := by
    rwa [hgm_eq] at hslab_fix
  have hrb_eq : gm₀ (Succinct.gmRIdx b) = k := by
    rwa [hgm_eq] at hrb_fix
  have hqb_pos : 1 ≤ gm₀ (Succinct.gmQIdx b) := by
    rwa [hgm_eq] at hqb_fix
  have htot : b_win + n_win ≤ N := by
    dsimp only [b_win, n_win, K, gm₀]
    rwa [hgm_eq] at htot_fix
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have htop_eq := hslab.top_eq b hb (gm₀ (Succinct.gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : p_del < gm₀ 0 := by
    dsimp only [p_del]; rw [htop_eq]
    exact hslab.ptr_lt b hb (gm₀ (Succinct.gmQIdx b) - 1) (by omega)
  have hglast_eq : g_last + 1 = b_win := by
    dsimp only [g_last, p_last, u, b_win]; omega
  have hgdel_le_glast : g_del ≤ g_last := by
    have hmul : p_del * K ≤ p_last * K := Nat.mul_le_mul_right K (by dsimp only [p_last]; omega)
    dsimp only [g_del, g_last]; omega
  have hglast_lt_m0 : g_last < m₀ := by dsimp only [m₀]; omega
  have hr_cap : gm₀ (Succinct.gmRIdx b) < tailCapPerBucket N := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb_eq]; omega
  have ht_cap : n_win < maxTailItems N :=
    Succinct.ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_k1 : Fits w (k + 1) :=
    fits_of_le_N hw hnU hU (hk_lt.trans_le (Succinct.slabSize_le_max_n_one N))
  have hqdel_lt : q_del < 2 ^ quotientBits U N := Succinct.quotAt_lt _ _ _ _ _ _ _
  have hvdel_lt : v_del < 2 ^ valBits V := Succinct.valAt_lt _ _ _ _ _ _ _ _
  have hglast_lt_N : g_last < N := lt_of_lt_of_le hglast_lt_m0 htot
  have hgdel_lt_N : g_del < N := lt_of_le_of_lt hgdel_le_glast hglast_lt_N
  have hqlast_lt : q_last < 2 ^ quotientBits U N := Succinct.quotAt_lt _ _ _ _ _ _ _
  have hvlast_lt : v_last < 2 ^ valBits V := Succinct.valAt_lt _ _ _ _ _ _ _ _
  obtain ⟨_, _, hq1, hv1, hl1, hg1⟩ :=
    Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := Succinct.hashSpace U w N)
      hw hgdel_lt_N hqlast_lt s_fix
  obtain ⟨_, _, hq2, hv2, hl2, hg2⟩ :=
    Succinct.writeValProg_effect (base := 0) (U := U) (h_space := Succinct.hashSpace U w N)
      hw hgdel_lt_N hvlast_lt s₁
  obtain ⟨_, _, _, hq_step, hv_step, hl_step, hgm_step⟩ :=
    Succinct.demoteStepProg_effect (base := 0) (U := U) (V := V)
      (h_space := Succinct.hashSpace U w N) hw hb_pos s_fix
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  unfold demoteStepRegCode
  refine .seq (T₁ := 431) (T₂ := 555)
    (demotePrepRegCode_exec hrB_ge hrK_ge hw hN_pos hnU hU hV hb_pos hx her hgb hm2 hm3
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩ hcpl hsz hrB hrK)
    (fun y1 ⟨hy1_wf, hy1_er, hy1_gb, hy1_sz, hy1_cpl, hy1_27, hy1_28, hy1_29, hy1_30,
      hy1_meta, hy1_regs⟩ => ?_) (by omega)
  have h2_lt : 2 < epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
  have h3_lt : 3 < epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
  refine .seq (T₁ := 108) (T₂ := 447)
    (writeDenseQVRegCode_exec (n_t := m₀) (d := g_last) (q := q_del) (v := v_del)
      (rD := 27) (rQ := 29) (rV := 30) (by decide) (by decide) (by decide)
      hw (le_of_lt hU) hV hy1_wf hy1_er hglast_lt_m0 hy1_27 hy1_29 hy1_30 hqdel_lt hvdel_lt
      (by rw [hy1_sz]; exact hsz) (by rw [hy1_meta 2 h2_lt, hm2]) (by rw [hy1_meta 3 h3_lt, hm3]))
    (fun y2 ⟨hy2_wf, hy2_er, hy2_sz, hy2_q, hy2_v, hy2_other, hy2_meta, hy2_regs⟩ => ?_)
    (by omega)
  have hy2_sz_x : y2.bitSize = x.bitSize := hy2_sz.trans hy1_sz
  have hy2_meta_x : ∀ a < epochMetaWords U w N, y2.mem a = x.mem a :=
    fun a ha => (hy2_meta a ha).trans (hy1_meta a ha)
  obtain ⟨hy2_lm, hy2_gm, hy2_td, hy2_dt, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy2_meta_x
  have hy2_gb : GMBasesLoaded N y2 :=
    hy1_gb.congr_regs (fun r hr1 _ => hy2_regs r (by omega))
  have hy2_27 : y2.regs 27 = g_last := (hy2_regs 27 (by decide)).trans hy1_27
  have hy2_28 : y2.regs 28 = n_win := (hy2_regs 28 (by decide)).trans hy1_28
  refine .seq (T₁ := 114) (T₂ := 333)
    (winGrowLeftRegCode_exec (b_win := g_last) (n_win := n_win) (rB := 27) (rN := 28)
      (by decide) (by decide) hw hN_pos hnU hU hb_pos hy2_wf hy2_er
      (by rw [hy2_sz_x]; exact hsz_meta) (le_of_lt hglast_lt_N) ht_cap hy2_27 hy2_28)
    (fun y3 ⟨hy3_sz, hy3_wf, hy3_er, hy3_td, hy3_dt, hy3_gm, hy3_lm, hy3_out, hy3_items,
      hy3_regs⟩ => ?_) (by omega)
  have hy3_sz_x : y3.bitSize = x.bitSize := hy3_sz.trans hy2_sz_x
  have hy3_gb : GMBasesLoaded N y3 :=
    hy2_gb.congr_regs (fun r hr1 _ => hy3_regs r (by omega))
  have hy3_gm_x : gmAtBit U w N y3.mem = gm₀ := hy3_gm.trans hy2_gm
  have hy3_rB : y3.regs rB = b := by
    rw [hy3_regs rB (by omega), hy2_regs rB (by omega), hy1_regs rB hrB_ge, hrB]
  refine .seq (T₁ := 331) (T₂ := 2)
    (gmAppendTailRegCode_exec (rB := rB) (by omega) hw hN_pos hnU hU hb_pos hb
      hy3_wf hy3_er hy3_gb (by rw [hy3_sz_x]; exact hsz_meta) hy3_rB
      (by rw [hy3_gm_x]; exact htail) (by rw [hy3_gm_x]; exact hr_cap))
    (fun y4 ⟨hy4_sz, hy4_wf, hy4_er, hy4_gb, hy4_gm, hy4_lm, hy4_td, hy4_dt, hy4_out,
      hy4_items, hy4_regs⟩ => ?_) (by omega)
  have hy4_sz_x : y4.bitSize = x.bitSize := hy4_sz.trans hy3_sz_x
  have hy4_rK : y4.regs rK = k := by
    rw [hy4_regs rK (by omega), hy3_regs rK (by omega), hy2_regs rK (by omega),
      hy1_regs rK hrK_ge, hrK]
  have hne_K16 : rK ≠ 16 := by intro h; subst h; omega
  refine DemonicExecWithin.step_const (T := 1) hfit_1 ?_
  refine dExec_bin (v := k + 1)
    (by simp [BinOp.eval, BitRAM.Data.set, hne_K16, hy4_rK]) hfit_k1 ?_
  set z := (y4.set 16 1).set rK (k + 1)
  have hz_wf : z.WellFormed w := wf_set rK (wf_set 16 hy4_wf hfit_1) hfit_k1
  have hz_er : EpochRegs U V w N z :=
    hy4_er.congr_regs (fun r hr1 _ => by
      dsimp only [z, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hz_gb : GMBasesLoaded N z :=
    hy4_gb.congr_regs (fun r hr1 hr2 => by
      dsimp only [z, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hpres := Succinct.gmAppendTail_preserves_nonTail gm₀ hb hr_cap ht_cap
  have hz_gm_eq : gmAtBit U w N z.mem = Succinct.gmAppendTail N gm₀ b := by
    change gmAtBit U w N y4.mem = _
    rw [hy4_gm, hy3_gm_x]
  have hz_bwin : (gmAtBit U w N z.mem 0 - 1) * K + (K - (k + 1)) = g_last := by
    rw [hz_gm_eq, hpres.1]
    dsimp only [g_last, p_last, u]
    omega
  have hz_nwin : gmAtBit U w N z.mem 1 = n_win + 1 := by
    rw [hz_gm_eq, hpres.2.1]
  have hm0_eq : g_last + (n_win + 1) = m₀ := by
    dsimp only [m₀]; omega
  have hwin_x : WindowInv (maxTailItems N) (g_last + 1) n_win
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem) := by
    rw [hglast_eq]; exact hcpl.win_inv
  have hmax_M : max (maxTailItems N) 1 = maxTailItems N := max_eq_left (by omega)
  obtain ⟨hwin_z, htd_z, hdt_z⟩ :=
    winGrowLeft_spec hwin_x ht_cap
      (fun i => by have := hcpl.td_lt i; rwa [hmax_M] at this)
      (fun i => by have := hcpl.dt_lt i; rwa [hmax_M] at this)
  obtain ⟨hphys_glast, hphys_other⟩ :=
    physByBase_winGrowLeft (N := N) (b := g_last) (n := n_win)
      (td := tdAtBit U w N x.mem) (dt := dtAtBit U w N x.mem) hb_pos ht_cap
  set g_tail := (N - 1) - n_win
  have h_sum_le : g_last + 1 + n_win ≤ N := by rw [hglast_eq]; exact htot
  have hgtail_le : g_last ≤ g_tail := by
    dsimp only [g_tail]
    rw [Nat.sub_sub]
    exact Nat.le_sub_of_add_le (by rw [← Nat.add_assoc, hglast_eq]; exact htot)
  have hnwin_lt_N : n_win < N :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.succ_pos g_last)) h_sum_le
  have hnwin_le_N1 : n_win ≤ N - 1 := Nat.le_sub_one_of_lt hnwin_lt_N
  refine ⟨hz_wf, hz_er, hz_gb, hy4_sz_x, ?_,
    by simp +decide [z, BitRAM.Data.set],
    fun a ha => (hy4_out a (Or.inl ha)).trans
      ((hy3_out a (by unfold offTD; omega)).trans
        (hy2_meta_x a (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega))),
    fun r hr hne => ?_⟩
  · rw [hz_bwin, hz_nwin, hm0_eq]
    refine ⟨?_, ?_, ?_, fun i => ?_, fun i => ?_, fun d hd => ?_, fun d hd => ?_⟩
    · dsimp only [BitRAM.Data.toBitMemoryState, z, BitRAM.Data.set]
      rw [hy4_gm, hy3_gm_x, hgm_step, hgm_eq]
    · dsimp only [BitRAM.Data.toBitMemoryState, z, BitRAM.Data.set]
      rw [hy4_lm, hy3_lm, hy2_lm, hl_step]; exact hcpl.lm_eq
    · dsimp only [BitRAM.Data.toBitMemoryState, z, BitRAM.Data.set]
      rw [hy4_td, hy4_dt, hy3_td, hy3_dt, hy2_td, hy2_dt]
      exact hwin_z
    · dsimp only [BitRAM.Data.toBitMemoryState, z, BitRAM.Data.set]
      rw [hy4_td, hy3_td, hy2_td, hmax_M]; exact htd_z i
    · dsimp only [BitRAM.Data.toBitMemoryState, z, BitRAM.Data.set]
      rw [hy4_dt, hy3_dt, hy2_dt, hmax_M]; exact hdt_z i
    · change denseQuotAt U V w N y4.toBitMemoryState d =
        Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s'.mem
          (physByBase N g_last (dtAtBit U w N y4.mem) d)
      rw [(hy4_items d).1, (hy3_items d).1, hy4_dt, hy3_dt, hy2_td, hy2_dt, hq_step, hgm_eq]
      by_cases heq : d = g_last
      · subst heq
        rw [hy2_q, hphys_glast]
        dsimp only [q_del, g_del, p_del, u, K, g_tail, n_win]
        rw [Function.update_self]
      · obtain ⟨hq_d, _⟩ := hy2_other d hd heq
        have hphys_eq : physByBase N g_last
            (winGrowLeft (maxTailItems N) g_last n_win
              (tdAtBit U w N x.mem, dtAtBit U w N x.mem)).2 d =
            physByBase N b_win (dtAtBit U w N x.mem) d := by
          rw [← hglast_eq]
          exact hphys_other d (by omega) heq
        have hphys_ne_tail : physByBase N b_win (dtAtBit U w N x.mem) d ≠ g_tail := by
          unfold physByBase
          rw [ite_eq_right hb0]
          split_ifs with hlt
          · have hd_le : d < g_last + 1 := by rwa [hglast_eq]
            have hd_lt : d < g_last := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hd_le) heq
            exact Nat.ne_of_lt (lt_of_lt_of_le hd_lt hgtail_le)
          · have hown : dtAtBit U w N x.mem (d % maxTailItems N) < n_win :=
              (hcpl.win_inv.owner_valid d (by omega) hd).1
            exact Nat.ne_of_gt (Nat.sub_lt_sub_left (lt_of_lt_of_le hown hnwin_le_N1) hown)
        have hy1_dt' : dtAtBit U w N y1.toBitMemoryState.mem = dtAtBit U w N x.mem := by
          obtain ⟨_, _, _, hdt1, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy1_meta
          exact hdt1
        have hq_y1 := hy1_cpl.quot_eq d hd
        change denseQuotAt U V w N y1.toBitMemoryState d =
          Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s₂.mem
            (physByBase N b_win (dtAtBit U w N y1.toBitMemoryState.mem) d) at hq_y1
        rw [hy1_dt', hq2, hq1] at hq_y1
        rw [hq_d, hq_y1, hphys_eq]
        dsimp only [q_del, g_del, p_del, u, K, q_last, g_last, p_last, g_tail, n_win]
        rw [Function.update_of_ne hphys_ne_tail]
    · change denseValAt U V w N y4.toBitMemoryState d =
        Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
          (physByBase N g_last (dtAtBit U w N y4.mem) d)
      rw [(hy4_items d).2, (hy3_items d).2, hy4_dt, hy3_dt, hy2_td, hy2_dt, hv_step, hgm_eq]
      by_cases heq : d = g_last
      · subst heq
        rw [hy2_v, hphys_glast]
        dsimp only [v_del, g_del, p_del, u, K, g_tail, n_win]
        rw [Function.update_self]
      · obtain ⟨_, hv_d⟩ := hy2_other d hd heq
        have hphys_eq : physByBase N g_last
            (winGrowLeft (maxTailItems N) g_last n_win
              (tdAtBit U w N x.mem, dtAtBit U w N x.mem)).2 d =
            physByBase N b_win (dtAtBit U w N x.mem) d := by
          rw [← hglast_eq]
          exact hphys_other d (by omega) heq
        have hphys_ne_tail : physByBase N b_win (dtAtBit U w N x.mem) d ≠ g_tail := by
          unfold physByBase
          rw [ite_eq_right hb0]
          split_ifs with hlt
          · have hd_le : d < g_last + 1 := by rwa [hglast_eq]
            have hd_lt : d < g_last := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hd_le) heq
            exact Nat.ne_of_lt (lt_of_lt_of_le hd_lt hgtail_le)
          · have hown : dtAtBit U w N x.mem (d % maxTailItems N) < n_win :=
              (hcpl.win_inv.owner_valid d (by omega) hd).1
            exact Nat.ne_of_gt (Nat.sub_lt_sub_left (lt_of_lt_of_le hown hnwin_le_N1) hown)
        have hy1_dt' : dtAtBit U w N y1.toBitMemoryState.mem = dtAtBit U w N x.mem := by
          obtain ⟨_, _, _, hdt1, _⟩ := meta_eq_of_low_words_eq hw hN_pos hy1_meta
          exact hdt1
        have hv_y1 := hy1_cpl.val_eq d hd
        change denseValAt U V w N y1.toBitMemoryState d =
          Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s₂.mem
            (physByBase N b_win (dtAtBit U w N y1.toBitMemoryState.mem) d) at hv_y1
        rw [hy1_dt', hv2, hv1] at hv_y1
        rw [hv_d, hv_y1, hphys_eq]
        dsimp only [v_del, g_del, p_del, u, K, v_last, g_last, p_last, g_tail, n_win]
        rw [Function.update_of_ne hphys_ne_tail]
  · dsimp only [z, BitRAM.Data.set]
    rw [Function.update_of_ne hne,
      Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
      hy4_regs r (by omega), hy3_regs r (by omega), hy2_regs r (by omega),
      hy1_regs r hr]

/-- Uniform `BitRAM.Code .standard 280` loop executing `demoteStepRegCode rB 31` while
`r31 < r250` (`k < slabSize N`). -/
@[expose]
def demoteLoopRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .loop (.lt 31 250) (demoteStepRegCode rB 31)

theorem demoteLoopRegCode_exec {U V w N b : ℕ} {rB : Fin 280}
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
      Succinct.DemoteLoopInv U V w N (Succinct.hashSpace U w N) 0 b s₀ k s_fix →
      WindowCoupled U V w N
        ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k))
        (gmAtBit U w N x.mem 1)
        ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) + gmAtBit U w N x.mem 1)
        s_fix x.toBitMemoryState →
      itemBitOff U V w N
        ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) + gmAtBit U w N x.mem 1) ≤
        x.bitSize →
      x.regs rB = b →
      x.regs 31 = k →
      let s_end := (Memory.spec 0).clientState s_fix
        (iterate (Succinct.demoteStepProg U V w N (Succinct.hashSpace U w N))
          (0, b) m k)
      BitRAM.DemonicExecWithin w (demoteLoopRegCode rB) x
        (fun z =>
          z.WellFormed w ∧
          EpochRegs U V w N z ∧
          GMBasesLoaded N z ∧
          z.bitSize = x.bitSize ∧
          Succinct.DemoteLoopInv U V w N (Succinct.hashSpace U w N) 0 b s₀ (k + m) s_end ∧
          WindowCoupled U V w N
            ((gmAtBit U w N z.mem 0 - 1) * slabSize N + (slabSize N - (k + m)))
            (gmAtBit U w N z.mem 1)
            ((gmAtBit U w N z.mem 0 - 1) * slabSize N + (slabSize N - (k + m)) +
              gmAtBit U w N z.mem 1)
            s_end z.toBitMemoryState ∧
          (∀ a < offGM U w N, z.mem a = x.mem a) ∧
          (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r))
        (2 + 988 * m) := by
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
    have hstep_inv := Succinct.demoteLoopInv_to_stepInv hinv hk_lt
    obtain ⟨hres_step, hinv_next⟩ := Succinct.demoteLoopInv_step hw hb_pos hinv hk_lt
    set s_next := (Memory.spec 0).clientState s_fix
      (Succinct.demoteStepProg U V w N (Succinct.hashSpace U w N) ((0, b), k))
    have hne_B31 : rB ≠ 31 := by intro h; subst h; omega
    refine .loop_iter (T₁ := 986) (T₂ := 2 + 988 * m) hcond
      (demoteStepRegCode_exec (by omega) (by decide) (by decide) hne_B31
        hw hN_pos hnU hU hV hb_pos hx her hgb hm2 hm3 hstep_inv hcpl hsz hrB hr31)
      (fun y ⟨hy_wf, hy_er, hy_gb, hy_sz, hy_cpl, hy_31, hy_low, hy_regs⟩ => ?_)
      (by omega)
    have hm_eq : (gmAtBit U w N y.mem 0 - 1) * slabSize N + (slabSize N - (k + 1)) +
          gmAtBit U w N y.mem 1 =
        (gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - k) +
          gmAtBit U w N x.mem 1 := by
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
      have h1 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_next.mem 1 =
          Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem 1 + 1 := by
        rw [hinv_next.gm1_eq, hinv.gm1_eq]
        omega
      rw [h0, h1]
      omega
    have hsend_eq : s_end = (Memory.spec 0).clientState s_next
        (iterate (Succinct.demoteStepProg U V w N (Succinct.hashSpace U w N))
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

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.demoteSlabProg`:
initializes `r31 = 0`, runs `demoteLoopRegCode rB`, and pops the top slab via
`gmPopSlabRegCode rB` (`32 ≤ rB`, `T = 1321 + 988 * slabSize N`). -/
@[expose]
def demoteSlabRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 31 0))
  (.seq (demoteLoopRegCode rB)
        (gmPopSlabRegCode rB))

theorem demoteSlabRegCode_exec {U V w N b : ℕ} {rB : Fin 280}
    {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hrB_ge : 32 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hpre : Succinct.DemoteSlabInv U V w N (Succinct.hashSpace U w N) 0 b s_fix)
    (hcpl : FixedCoupled U V w N s_fix x.toBitMemoryState)
    (hsz : itemBitOff U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hrB : x.regs rB = b) :
    let s' := (Memory.spec 0).clientState s_fix
      (Succinct.demoteSlabProg U V w N (Succinct.hashSpace U w N) (0, b))
    BitRAM.DemonicExecWithin w (demoteSlabRegCode rB) x
      (fun z =>
        z.WellFormed w ∧
        EpochRegs U V w N z ∧
        GMBasesLoaded N z ∧
        z.bitSize = x.bitSize ∧
        FixedCoupled U V w N s' z.toBitMemoryState ∧
        (∀ a < offGM U w N, z.mem a = x.mem a) ∧
        (∀ r : Fin 280, 32 ≤ r.val → z.regs r = x.regs r))
      (1321 + 988 * slabSize N) := by
  intro s'
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hfit_0 : Fits w 0 := fits_of_le_N hw hnU hU (by omega)
  have hloop0 := Succinct.demoteLoopInv_zero hpre
  rcases hpre with ⟨hb, _, hslab_fix, _, hqb_fix, _, _⟩
  have hgm_eq : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem =
      gmAtBit U w N x.mem := hcpl.gm_eq.symm
  have hslab_x : Succinct.SlabBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N x.mem 0) := by rwa [hgm_eq] at hslab_fix
  have hqb_x : 1 ≤ gmAtBit U w N x.mem (Succinct.gmQIdx b) := by rwa [hgm_eq] at hqb_fix
  have hgm0_pos : 1 ≤ gmAtBit U w N x.mem 0 :=
    hqb_x.trans (Succinct.q_le_nslabs_of_slabBijection hslab_x hb)
  have hbwin0_eq : (gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - 0) =
      gmAtBit U w N x.mem 0 * slabSize N := by
    rw [Nat.sub_zero, ← Nat.add_one_mul, Nat.sub_add_cancel hgm0_pos]
  have htot_eq : Succinct.totalSlots N (gmAtBit U w N x.mem) =
      (gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - 0) + gmAtBit U w N x.mem 1 := by
    unfold Succinct.totalSlots; rw [ite_eq_right hb0, hbwin0_eq]
  unfold demoteSlabRegCode
  refine (DemonicExecWithin.step_const (T := 1320 + 988 * slabSize N) hfit_0 ?_).mono
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
  have hs0_cpl : WindowCoupled U V w N
      ((gmAtBit U w N s0.mem 0 - 1) * slabSize N + (slabSize N - 0))
      (gmAtBit U w N s0.mem 1)
      ((gmAtBit U w N s0.mem 0 - 1) * slabSize N + (slabSize N - 0) + gmAtBit U w N s0.mem 1)
      s_fix s0.toBitMemoryState := by
    change WindowCoupled U V w N
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - 0))
      (gmAtBit U w N x.mem 1)
      ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - 0) + gmAtBit U w N x.mem 1)
      s_fix x.toBitMemoryState
    rw [← htot_eq, hbwin0_eq]
    exact hcpl
  refine .seq (T₁ := 2 + 988 * slabSize N) (T₂ := 1318)
    (demoteLoopRegCode_exec hrB_ge hw hN_pos hnU hU hV hb_pos (slabSize N) 0 s_fix s0
      (by omega) hs0_wf hs0_er hs0_gb hm2 hm3 hloop0 hs0_cpl
      (by
        change itemBitOff U V w N
          ((gmAtBit U w N x.mem 0 - 1) * slabSize N + (slabSize N - 0) + gmAtBit U w N x.mem 1) ≤
          x.bitSize
        rwa [← htot_eq])
      hs0_rB (by simp +decide [s0, BitRAM.Data.set]))
    (fun y1 ⟨hy1_wf, hy1_er, hy1_gb, hy1_sz, hy1_inv, hy1_cpl, hy1_low, hy1_regs⟩ => ?_)
    (by omega)
  rw [Nat.zero_add] at hy1_inv
  rw [Nat.zero_add, Nat.sub_self, Nat.add_zero] at hy1_cpl
  set s_loop := (Memory.spec 0).clientState s_fix
    (iterate (Succinct.demoteStepProg U V w N (Succinct.hashSpace U w N))
      (0, b) (slabSize N) 0)
  have hgm_y1 : gmAtBit U w N y1.mem =
      Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_loop.mem := hy1_cpl.gm_eq
  have hslab_y1 : Succinct.SlabBijection N (gmAtBit U w N y1.mem)
      (fun b' => gmAtBit U w N y1.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N y1.mem 0) := by
    rw [hgm_y1]; exact hy1_inv.slab_bij
  have hqb_y1 : 1 ≤ gmAtBit U w N y1.mem (Succinct.gmQIdx b) := by
    rw [hgm_y1]; exact hy1_inv.qb_pos
  have hsz_meta : epochMetaBits U w N ≤ y1.bitSize := by
    rw [hy1_sz]; exact (Nat.le_add_right _ _).trans hsz
  refine (gmPopSlabRegCode_exec (by omega) hw hN_pos hnU hU hb_pos hb
    hy1_wf hy1_er hy1_gb hsz_meta (by rw [hy1_regs rB hrB_ge, hs0_rB])
    hslab_y1 hqb_y1).mono
    (fun z ⟨hz_sz, hz_wf, hz_er, hz_gb, hz_gm, hz_lm, hz_td, hz_dt, hz_out, hz_items,
      hz_regs⟩ => ?_) le_rfl
  have hs'_eq : s' = (Memory.spec 0).clientState s_loop
      (Succinct.gmPopSlabProg U V w N (Succinct.hashSpace U w N) (0, b)) := by
    dsimp only [s', s_loop, Succinct.demoteSlabProg, Succinct.demoteLoopProg]
    rw [StateTransitionSpec.clientState_bind]
  obtain ⟨_, _, hq_pop, hv_pop, hl_pop, hgm_pop⟩ :=
    Succinct.gmPopSlabProg_effect (base := 0) (U := U) (V := V)
      (h_space := Succinct.hashSpace U w N) hw hb_pos hb s_loop hy1_inv.slab_bij hy1_inv.qb_pos
  have hfields := Succinct.gmPopSlab_preserves_tail hb hslab_y1
  have hz_gm0 : gmAtBit U w N z.mem 0 * slabSize N =
      (gmAtBit U w N y1.mem 0 - 1) * slabSize N := by
    rw [hz_gm, hfields.1]
  have hz_gm1 : gmAtBit U w N z.mem 1 = gmAtBit U w N y1.mem 1 := by
    rw [hz_gm, hfields.2.1]
  have hz_tot : Succinct.totalSlots N (gmAtBit U w N z.mem) =
      (gmAtBit U w N y1.mem 0 - 1) * slabSize N + gmAtBit U w N y1.mem 1 := by
    unfold Succinct.totalSlots; rw [ite_eq_right hb0, hz_gm0, hz_gm1]
  refine ⟨hz_wf, hz_er, hz_gb, hz_sz.trans hy1_sz,
    ⟨by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_gm, hs'_eq, hgm_pop, hgm_y1],
     by dsimp only [BitRAM.Data.toBitMemoryState]; rw [hz_lm, hs'_eq, hl_pop]; exact hy1_cpl.lm_eq,
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
       rw [(hz_items d).1, hs'_eq, hq_pop, hz_gm0, hz_dt]
       exact hy1_cpl.quot_eq d hd,
     fun d hd => by
       change d < Succinct.totalSlots N (gmAtBit U w N z.mem) at hd
       rw [hz_tot] at hd
       change denseValAt U V w N z.toBitMemoryState d =
         Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s'.mem
           (physByBase N (gmAtBit U w N z.mem 0 * slabSize N) (dtAtBit U w N z.mem) d)
       rw [(hz_items d).2, hs'_eq, hv_pop, hz_gm0, hz_dt]
       exact hy1_cpl.val_eq d hd⟩,
    fun a ha => (hz_out a (Or.inl ha)).trans (hy1_low a ha),
    fun r hr => (hz_regs r (by omega)).trans
      ((hy1_regs r hr).trans (by
        dsimp only [s0, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]))⟩

end Cslib.DataStructure.Dictionary.BitResizable
