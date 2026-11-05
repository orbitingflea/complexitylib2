/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Sync

/-!
# Companion Window-Shrink, `LocalMeta` Chain, and Tail Pool Programs in `BitRAM`

This module continues `Sync.lean` with uniform `BitRAM.Code .standard 280` programs for:
1. Left circular window shrink (`winShrinkLeftRegCode`), used during slab demotion.
2. Doubly-linked `LocalMeta` chain updates (`lmPrependRegCode`, `prependIfIndexedRegCode`,
   `lmUnlinkRegCode`, `unlinkIfIndexedRegCode`) and their exact functional equivalence with
   `Succinct.lmPrependProg`, `Succinct.prependIfIndexedProg`, `Succinct.lmUnlinkProg`, and
   `Succinct.unlinkIfIndexedProg`.
3. Tail pool allocation and payload write (`appendTailItemRegCode`, `pushBackTailWriteRegCode`),
   synchronized in lockstep with `Succinct.appendTailItemProg` and `Succinct.pushBackTailWriteProg`
   together with `winGrowRight`.
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

/-! ## Section 1: Left circular window shrink (`winShrinkLeftRegCode`) -/

/-- Uniform `BitRAM.Code .standard 280` program executing
`winShrinkLeft (maxTailItems N) b_win n_win` on `(tdAtBit, dtAtBit)` and copying dense item
`b_win` into `denseOfCirc (maxTailItems N) b_win (tdAtBit n_win)`, given `rB = b_win` and
`rN = n_win` (`24 ≤ rB, rN`). -/
@[expose]
def winShrinkLeftRegCode (rB rN : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mod 21 rB 253))
  (.seq (readDTRegCode 21 22)
  (.seq (readTDRegCode rN 21)
  (.seq (denseOfTailRegCode rB 21 23)
  (.seq (copyDenseItemRegCode rB 23)
  (.seq (writeTDRegCode 22 21)
        (writeDTRegCode 21 22))))))

theorem winShrinkLeftRegCode_exec {U V w N n_t b_win n_win : ℕ} {rB rN : Fin 280}
    {x : BitRAM.Data 280}
    (hrB_ge : 24 ≤ rB.val) (hrN_ge : 24 ≤ rN.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hbn_le : b_win + n_win ≤ N) (hM : n_win + 1 ≤ maxTailItems N)
    (hnt : b_win + n_win + 1 ≤ n_t)
    (hwin : WindowInv (maxTailItems N) b_win (n_win + 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hrB : x.regs rB = b_win) (hrN : x.regs rN = n_win) :
    let M := maxTailItems N
    let td := tdAtBit U w N x.mem
    let dt := dtAtBit U w N x.mem
    let p' := winShrinkLeft M b_win n_win (td, dt)
    BitRAM.DemonicExecWithin w (winShrinkLeftRegCode rB rN) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        tdAtBit U w N y.mem = p'.1 ∧
        dtAtBit U w N y.mem = p'.2 ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        (∀ a < offTD U w N, y.mem a = x.mem a) ∧
        (∀ d < b_win + 1 + n_win, d ≠ b_win →
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState
              (if d = denseOfCirc M b_win (td n_win) then b_win else d) ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState
              (if d = denseOfCirc M b_win (td n_win) then b_win else d)) ∧
        (∀ r : Fin 280, 24 ≤ r.val → y.regs r = x.regs r)) 403 := by
  intro M td dt p'
  have h253 : x.regs 253 = maxTailItems N := (her.active hN_pos).2.2.2.2.2.2.2.2.1
  have hM_pos : 0 < M := by omega
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz_meta hv
  have h2M_le : 2 * M ≤ globalMetaLen N := two_mul_maxTailItems_le_globalMetaLen hb_pos
  set c_rem := b_win % M
  set t_rem := dt c_rem
  set c_last := td n_win
  set d_last := denseOfCirc M b_win c_last
  have hc_rem_lt : c_rem < M := Nat.mod_lt _ hM_pos
  have hn_lt : n_win < M := by omega
  have ht_rem_lt : t_rem < M := lt_of_lt_of_le (hwin.owner_valid b_win le_rfl (by omega)).1 hM
  have hc_last_lt : c_last < M := hwin.td_lt n_win (Nat.lt_succ_self n_win)
  have hd_last_lt_win : d_last < b_win + (n_win + 1) :=
    hwin.dense_lt n_win (Nat.lt_succ_self n_win)
  have hd_last_lt : d_last < n_t := lt_of_lt_of_le hd_last_lt_win (by omega)
  have hd_last_le_N : d_last ≤ N := by omega
  have hfit_crem : Fits w c_rem := hfit_gm _ (by omega)
  have hclast_val : c_last < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le hc_last_lt (maxTailItems_le N)))
  have htrem_val : t_rem < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le ht_rem_lt (maxTailItems_le N)))
  unfold winShrinkLeftRegCode
  refine step_dExec_bin (v := c_rem) (T := 402)
    (by simp [BinOp.eval, hrB, h253, c_rem, M]) hfit_crem ?_
  set s1 := x.set 21 c_rem
  have hs1_wf : s1.WellFormed w := wf_set 21 hx hfit_crem
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 45) (T₂ := 357)
    (readDTRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hc_rem_lt
      (by simp +decide [s1, BitRAM.Data.set]) hsz_meta)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_22, hy1_regs⟩ => ?_) (by omega)
  have hy1_er : EpochRegs U V w N y1 :=
    hs1_er.congr_regs (fun r hr1 _ =>
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy1_rN : y1.regs rN = n_win := by
    rw [hy1_regs rN (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s1, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega), hrN]
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  refine .seq (T₁ := 45) (T₂ := 312)
    (readTDRegCode_exec (by omega) hw hN_pos hnU hU hy1_wf hy1_er hn_lt hy1_rN
      (by rw [hy1_sz]; exact hsz_meta))
    (fun y2 ⟨hy2_st, hy2_wf, hy2_21, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  have hy2_er : EpochRegs U V w N y2 :=
    hy1_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy2_rB : y2.regs rB = b_win := by
    rw [hy2_regs rB (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs rB (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s1, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega), hrB]
  have hy2_21_eq : y2.regs 21 = c_last := by
    rw [hy2_21, hy1_mem]
  refine .seq (T₁ := 5) (T₂ := 307)
    (denseOfTailRegCode_exec (by omega) (by decide) hw hN_pos hnU hU hb_pos hy2_wf hy2_er
      (by rw [hy2_sz]; exact hsz_meta)
      hd_last_le_N hc_last_lt hy2_rB hy2_21_eq)
    (fun y3 ⟨hy3_st, hy3_wf, hy3_23, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
  have hy3_er : EpochRegs U V w N y3 :=
    hy2_er.congr_regs (fun r hr1 _ =>
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy3_rB : y3.regs rB = b_win := by
    rw [hy3_regs rB (by omega) (by intro h; have := congrArg Fin.val h; omega), hy2_rB]
  have hy3_21 : y3.regs 21 = c_last := by
    rw [hy3_regs 21 (by decide) (by decide), hy2_21_eq]
  have hy3_22 : y3.regs 22 = t_rem := by
    rw [hy3_regs 22 (by decide) (by decide), hy2_regs 22 (by decide) (by decide), hy1_22]
    rfl
  refine .seq (T₁ := 195) (T₂ := 112)
    (copyDenseItemRegCode_exec (by omega) (by decide) hw (le_of_lt hU) hV hy3_wf hy3_er
      (by omega) hd_last_lt hy3_rB hy3_23 (by rw [hy3_sz]; exact hsz)
      (by rw [hy3_mem, hm2]) (by rw [hy3_mem, hm3]))
    (fun y4 ⟨hy4_wf, hy4_er, hy4_sz, hy4_q, hy4_v, hy4_other, hy4_meta, hy4_regs⟩ => ?_)
    (by omega)
  have hy4_sz_x : y4.bitSize = x.bitSize := hy4_sz.trans hy3_sz
  have hy4_td : tdAtBit U w N y4.mem = td := by
    funext i; unfold td tdAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT; omega)).trans
          (congrFun hy3_mem addr)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hy4_dt : dtAtBit U w N y4.mem = dt := by
    funext i; unfold dt dtAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr (by rw [← offDT_add_eq_epochMetaWords hN_pos]; omega)).trans
          (congrFun hy3_mem addr)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hy4_gm : gmAtBit U w N y4.mem = gmAtBit U w N x.mem := by
    funext i; unfold gmAtBit
    by_cases hi : i < globalMetaLen N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr (by
          rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega)).trans
          (congrFun hy3_mem addr)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hy4_lm : lmAtBit U w N y4.mem = lmAtBit U w N x.mem := by
    funext ⟨c, j⟩; unfold lmAtBit; dsimp only
    by_cases hcj : c < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj, ite_eq_left hcj]
      apply readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr ?_).trans (congrFun hy3_mem addr)) hcj.2
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hcj.1
      have haddr_hi := haddr.2
      unfold offLMSub at haddr_hi
      rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD offGM
      rw [lmSubWords_eq] at hmul haddr_hi ⊢
      rw [Nat.add_one_mul] at hmul
      omega
    · rw [ite_eq_right hcj, ite_eq_right hcj]
  refine .seq (T₁ := 56) (T₂ := 56)
    (writeTDRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hy4_wf hy4_er
      ht_rem_lt hclast_val (by rw [hy4_regs 22 (by decide), hy3_22])
      (by rw [hy4_regs 21 (by decide), hy3_21]) (by rw [hy4_sz_x]; exact hsz_meta))
    (fun y5 ⟨hy5_sz, hy5_wf, hy5_er, hy5_td, hy5_gm, hy5_lm, hy5_dt, hy5_out, hy5_items,
      hy5_regs⟩ => ?_) (by omega)
  refine (writeDTRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hy5_wf hy5_er
    hc_last_lt htrem_val
    (by rw [hy5_regs 21 (by decide), hy4_regs 21 (by decide), hy3_21])
    (by rw [hy5_regs 22 (by decide), hy4_regs 22 (by decide), hy3_22])
    (by rw [hy5_sz, hy4_sz_x]; exact hsz_meta)).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_dt, hy_gm, hy_lm, hy_td, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz.trans (hy5_sz.trans hy4_sz_x), hy_wf, hy_er,
    hy_td.trans (hy5_td.trans (by rw [hy4_td]; rfl)),
    hy_dt.trans (by rw [hy5_dt, hy4_dt]; rfl),
    hy_gm.trans (hy5_gm.trans hy4_gm),
    hy_lm.trans (hy5_lm.trans hy4_lm),
    fun a ha => (hy_out a (Or.inl (by unfold offDT; omega))).trans
      ((hy5_out a (Or.inl ha)).trans
        ((hy4_meta a (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT; omega)).trans
          (congrFun hy3_mem a))),
    fun d hd _ => ?_,
    fun r hr => ?_⟩
  · rw [(hy_items d).1, (hy_items d).2, (hy5_items d).1, (hy5_items d).2]
    by_cases heq : d = d_last
    · subst heq
      rw [ite_eq_left rfl, hy4_q, hy4_v, hy3_st_x]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right heq]
      obtain ⟨hq_o, hv_o⟩ := hy4_other d (by omega) heq
      rw [hy3_st_x] at hq_o hv_o
      exact ⟨hq_o, hv_o⟩
  · rw [hy_regs r (by omega), hy5_regs r (by omega), hy4_regs r (by omega),
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s1, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-! ## Section 2: Uniform `BitRAM` programs for `LocalMeta` doubly-linked chain updates -/

theorem lmAtBit_lt (U w N : ℕ) (mem : ℕ → ℕ) (p : ℕ × ℕ) :
    lmAtBit U w N mem p < 2 ^ effBucketPosBits N := by
  unfold lmAtBit; split_ifs
  · exact readPacked_lt (offLMSub U w N p.1) (effBucketPosBits N) w mem p.2
  · exact Nat.two_pow_pos _

/-- Pure functional effect of `lmPrependProg` on `lm : ℕ × ℕ → ℕ`. -/
@[expose]
def lmPrependFn (N b m j_new : ℕ) (lm : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  let old_h := lm (0, b * numMicroPerBucket N + m)
  let lm₁ := Function.update lm (1 + j_new % 4, b * numMicroPerBucket N + j_new / 4) 0
  let lm₂ := Function.update lm₁ (5 + j_new % 4, b * numMicroPerBucket N + j_new / 4) old_h
  let lm₃ := if 0 < old_h then
      Function.update lm₂ (1 + (old_h - 1) % 4, b * numMicroPerBucket N + (old_h - 1) / 4)
        (j_new + 1)
    else lm₂
  Function.update lm₃ (0, b * numMicroPerBucket N + m) (j_new + 1)

theorem lmPrependProg_lmAt {U V w N h_space base b m j_new : ℕ}
    (hw : 0 < w) (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hj : j_new < effBucketCap N) (hj_n : j_new < N)
    {s : Memory.State}
    (hold : Succinct.lmHead N (Succinct.lmAt base U V w N h_space s.mem) b m ≤ effBucketCap N) :
    let s' := (Memory.spec 0).clientState s
      (Succinct.lmPrependProg U V w N h_space (((base, b), m), j_new))
    Succinct.lmAt base U V w N h_space s'.mem =
      lmPrependFn N b m j_new (Succinct.lmAt base U V w N h_space s.mem) ∧
    Succinct.gmAt base U V w N h_space s'.mem =
      Succinct.gmAt base U V w N h_space s.mem ∧
    Succinct.quotAt base U w N h_space s'.mem =
      Succinct.quotAt base U w N h_space s.mem ∧
    Succinct.valAt base U V w N h_space s'.mem =
      Succinct.valAt base U V w N h_space s.mem := by
  intro s'
  set lm := Succinct.lmAt base U V w N h_space s.mem
  set old_h := Succinct.lmHead N lm b m
  have hval_lt : j_new + 1 < 2 ^ effBucketPosBits N :=
    (Nat.succ_le_of_lt (lt_min hj_n hj)).trans_lt
      (min_effBucketCap_lt_two_pow_effBucketPosBits N)
  have h0_lt : 0 < 2 ^ effBucketPosBits N := Nat.two_pow_pos _
  have hold_lt : old_h < 2 ^ effBucketPosBits N :=
    Succinct.lmAt_lt base U V w N h_space s.mem (0, b * numMicroPerBucket N + m)
  set s₁ := (Memory.spec 0).clientState s
    (Succinct.writeLMMod4Prog U V w N h_space 1 (((base, b), j_new), 0))
  obtain ⟨_, _, hq₁, hv₁, hlm₁, hgm₁⟩ :=
    Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
      (c_base := 1) (base := base) (b := b) (j := j_new) (val := 0) hw (by decide) hb hj h0_lt s
  set s₂ := (Memory.spec 0).clientState s₁
    (Succinct.writeLMMod4Prog U V w N h_space 5 (((base, b), j_new), old_h))
  obtain ⟨_, _, hq₂, hv₂, hlm₂, hgm₂⟩ :=
    Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
      (c_base := 5) (base := base) (b := b) (j := j_new) (val := old_h)
      hw (by decide) hb hj hold_lt s₁
  have hs'_def : s' = (if 0 < old_h then
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s₂
          (Succinct.writeLMMod4Prog U V w N h_space 1 (((base, b), old_h - 1), j_new + 1)))
        (Succinct.writeLMProg U V w N h_space 0 (((base, b * numMicroPerBucket N + m)), j_new + 1))
    else
      (Memory.spec 0).clientState s₂
        (Succinct.writeLMProg U V w N h_space 0
          (((base, b * numMicroPerBucket N + m)), j_new + 1))) := by
    dsimp only [s', s₂, s₁, old_h, lm]
    unfold Succinct.lmPrependProg Succinct.writeLMPrevProg Succinct.writeLMNextProg
      Succinct.writeLMHeadProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readLMHeadProg,
      Succinct.clientResult_readLMHeadProg _ hb hm,
      StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind]
    split_ifs
    · rw [StateTransitionSpec.clientState_bind]
    · rfl
  rw [hs'_def]
  unfold lmPrependFn
  change _ = Function.update (if 0 < old_h then _ else _) _ _ ∧ _
  split_ifs with hpos
  · have hold_idx : old_h - 1 < effBucketCap N := by omega
    set s₃ := (Memory.spec 0).clientState s₂
      (Succinct.writeLMMod4Prog U V w N h_space 1 (((base, b), old_h - 1), j_new + 1))
    obtain ⟨_, _, hq₃, hv₃, hlm₃, hgm₃⟩ :=
      Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c_base := 1) (base := base) (b := b) (j := old_h - 1) (val := j_new + 1)
        hw (by decide) hb hold_idx hval_lt s₂
    obtain ⟨_, _, hq₄, hv₄, hlm₄, hgm₄⟩ :=
      Succinct.writeLMProg_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c := 0) (base := base) (idx := b * numMicroPerBucket N + m) (val := j_new + 1)
        hw (by decide) (Succinct.lmHeadIdx_lt hb hm) hval_lt s₃
    exact ⟨by rw [hlm₄, hlm₃, hlm₂, hlm₁]; rfl,
      by rw [hgm₄, hgm₃, hgm₂, hgm₁],
      by rw [hq₄, hq₃, hq₂, hq₁],
      by rw [hv₄, hv₃, hv₂, hv₁]⟩
  · obtain ⟨_, _, hq₄, hv₄, hlm₄, hgm₄⟩ :=
      Succinct.writeLMProg_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c := 0) (base := base) (idx := b * numMicroPerBucket N + m) (val := j_new + 1)
        hw (by decide) (Succinct.lmHeadIdx_lt hb hm) hval_lt s₂
    exact ⟨by rw [hlm₄, hlm₂, hlm₁]; rfl,
      by rw [hgm₄, hgm₂, hgm₁],
      by rw [hq₄, hq₂, hq₁],
      by rw [hv₄, hv₂, hv₁]⟩

/-- Uniform `BitRAM.Code .standard 280` program executing `lmPrependFn N b m j_new` on `lmAtBit`:
given `rB = b`, `rM = m`, `rJ = j_new` (`23 ≤ rB, rM, rJ`), uses `r19..r22` and `r13..r18` as
temporaries and preserves `r ≥ 23`. -/
@[expose]
def lmPrependRegCode (rB rM rJ : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 13 rB))
  (.seq (.op (.copy 14 rM))
  (.seq readLMHeadRegCode
  (.seq (.op (.copy 19 0))
  (.seq (.op (.const 20 0))
  (.seq (.op (.const 21 1))
  (.seq (.op (.bin .add 22 rJ 21))
  (.seq (.op (.copy 13 rB))
  (.seq (.op (.copy 14 rJ))
  (.seq (.op (.copy 15 20))
  (.seq writeLMPrevRegCode
  (.seq (.op (.copy 13 rB))
  (.seq (.op (.copy 14 rJ))
  (.seq (.op (.copy 15 19))
  (.seq writeLMNextRegCode
  (.seq (.branch (.lt 20 19)
          (.seq (.op (.bin .sub 14 19 21))
          (.seq (.op (.copy 13 rB))
          (.seq (.op (.copy 15 22))
                writeLMPrevRegCode)))
          nopRegCode)
  (.seq (.op (.copy 13 rB))
  (.seq (.op (.copy 14 rM))
  (.seq (.op (.copy 15 22))
        writeLMHeadRegCode))))))))))))))))))

theorem lmPrependRegCode_exec {U V w N b m j_new : ℕ} {rB rM rJ : Fin 280}
    {x : BitRAM.Data 280}
    (hrB_ge : 23 ≤ rB.val) (hrM_ge : 23 ≤ rM.val) (hrJ_ge : 23 ≤ rJ.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hj : j_new < effBucketCap N) (hj_n : j_new < N)
    (hold : Succinct.lmHead N (lmAtBit U w N x.mem) b m ≤ effBucketCap N)
    (hrB : x.regs rB = b) (hrM : x.regs rM = m) (hrJ : x.regs rJ = j_new) :
    BitRAM.DemonicExecWithin w (lmPrependRegCode rB rM rJ) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem = lmPrependFn N b m j_new (lmAtBit U w N x.mem) ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 23 ≤ r.val → y.regs r = x.regs r)) 349 := by
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hfit_1 : Fits w 1 := hfit_N 1 (by omega)
  have hfit_j1 : Fits w (j_new + 1) := hfit_N (j_new + 1) (by omega)
  have hval_lt : j_new + 1 < 2 ^ effBucketPosBits N :=
    (Nat.succ_le_of_lt (lt_min hj_n hj)).trans_lt
      (min_effBucketCap_lt_two_pow_effBucketPosBits N)
  have h0_lt : 0 < 2 ^ effBucketPosBits N := Nat.two_pow_pos _
  set lm₀ := lmAtBit U w N x.mem
  set old_h := Succinct.lmHead N lm₀ b m
  have hold_lt : old_h < 2 ^ effBucketPosBits N :=
    lmAtBit_lt U w N x.mem (0, b * numMicroPerBucket N + m)
  unfold lmPrependRegCode
  refine step_dExec_copy (v := b) (T := 348) hrB ?_
  refine step_dExec_copy (v := m) (T := 347)
    (by
      have hne : rM ≠ 13 := by intro h; subst h; omega
      simp [BitRAM.Data.set, hne, hrM]) ?_
  set s1 := (x.set 13 b).set 14 m
  have hs1_wf : s1.WellFormed w :=
    wf_set 14 (wf_set 13 hx (hrB ▸ hx.regs_fits rB)) (hrM ▸ hx.regs_fits rM)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 50) (T₂ := 297)
    (readLMHeadRegCode_exec hw hN_pos hnU hU hs1_wf hs1_er hsz hb hm
      (by simp +decide [s1, BitRAM.Data.set]) (by simp +decide [s1, BitRAM.Data.set]))
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_0, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_0_eq : y1.regs 0 = old_h := hy1_0
  have hy1_hi : ∀ r : Fin 280, 23 ≤ r.val → y1.regs r = x.regs r := by
    intro r hr
    rw [hy1_regs r (by omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  refine step_dExec_copy (v := old_h) (T := 296) hy1_0_eq ?_
  refine DemonicExecWithin.step_const (T := 295) (fits_zero w) ?_
  refine DemonicExecWithin.step_const (T := 294) hfit_1 ?_
  refine step_dExec_bin (v := j_new + 1) (T := 293)
    (by
      have h19 : rJ ≠ 19 := by intro h; subst h; omega
      have h20 : rJ ≠ 20 := by intro h; subst h; omega
      have h21 : rJ ≠ 21 := by intro h; subst h; omega
      simp [BitRAM.Data.set, h19, h20, h21, BinOp.eval, hy1_hi rJ hrJ_ge, hrJ])
    hfit_j1 ?_
  refine step_dExec_copy (v := b) (T := 292)
    (by
      have h19 : rB ≠ 19 := by intro h; subst h; omega
      have h20 : rB ≠ 20 := by intro h; subst h; omega
      have h21 : rB ≠ 21 := by intro h; subst h; omega
      have h22 : rB ≠ 22 := by intro h; subst h; omega
      simp [BitRAM.Data.set, h19, h20, h21, h22, hy1_hi rB hrB_ge, hrB]) ?_
  refine step_dExec_copy (v := j_new) (T := 291)
    (by
      have h13 : rJ ≠ 13 := by intro h; subst h; omega
      have h19 : rJ ≠ 19 := by intro h; subst h; omega
      have h20 : rJ ≠ 20 := by intro h; subst h; omega
      have h21 : rJ ≠ 21 := by intro h; subst h; omega
      have h22 : rJ ≠ 22 := by intro h; subst h; omega
      simp [BitRAM.Data.set, h13, h19, h20, h21, h22, hy1_hi rJ hrJ_ge, hrJ]) ?_
  refine step_dExec_copy (v := 0) (T := 290)
    (by simp +decide [BitRAM.Data.set]) ?_
  set s2 :=
    ((((((y1.set 19 old_h).set 20 0).set 21 1).set 22 (j_new + 1)).set 13 b).set 14 j_new).set 15 0
  have hs2_wf : s2.WellFormed w :=
    wf_set 15 (wf_set 14 (wf_set 13 (wf_set 22 (wf_set 21 (wf_set 20
      (wf_set 19 hy1_wf (hy1_0_eq ▸ hy1_wf.regs_fits 0)) (fits_zero w)) hfit_1) hfit_j1)
      (hrB ▸ hx.regs_fits rB)) (hrJ ▸ hx.regs_fits rJ)) (fits_zero w)
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_sz : epochMetaBits U w N ≤ s2.bitSize := by
    change epochMetaBits U w N ≤ y1.bitSize; rw [hy1_sz]; exact hsz
  refine .seq (T₁ := 73) (T₂ := 217)
    (writeLMMod4RegCode_exec hw hN_pos hnU hU hs2_wf hs2_er hs2_sz
      (c_base := 1) (by decide) hb hj h0_lt
      (by simp +decide [s2, BitRAM.Data.set])
      (by simp +decide [s2, BitRAM.Data.set])
      (by simp +decide [s2, BitRAM.Data.set]))
    (fun y2 ⟨hy2_sz, hy2_wf, hy2_er, hy2_lm, hy2_gm, hy2_td, hy2_dt, hy2_out, hy2_items,
      hy2_regs⟩ => ?_) (by omega)
  have hy2_sz_x : y2.bitSize = x.bitSize := hy2_sz.trans hy1_sz
  have hy2_hi : ∀ r : Fin 280, 19 ≤ r.val → y2.regs r = s2.regs r := hy2_regs
  refine step_dExec_copy (v := b) (T := 216)
    (by
      rw [hy2_hi rB (by omega)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact (hy1_hi rB hrB_ge).trans hrB) ?_
  refine step_dExec_copy (v := j_new) (T := 215)
    (by
      have h13 : rJ ≠ 13 := by intro h; subst h; omega
      simp only [BitRAM.Data.set_regs, Function.update_of_ne h13]
      rw [hy2_hi rJ (by omega)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact (hy1_hi rJ hrJ_ge).trans hrJ) ?_
  refine step_dExec_copy (v := old_h) (T := 214)
    (by
      simp only [BitRAM.Data.set_regs,
        Function.update_of_ne (by decide : (19 : Fin 280) ≠ 14),
        Function.update_of_ne (by decide : (19 : Fin 280) ≠ 13)]
      rw [hy2_hi 19 (by decide)]
      simp +decide [s2, BitRAM.Data.set]) ?_
  set s3 := ((y2.set 13 b).set 14 j_new).set 15 old_h
  have hs3_wf : s3.WellFormed w :=
    wf_set 15 (wf_set 14 (wf_set 13 hy2_wf (hrB ▸ hx.regs_fits rB)) (hrJ ▸ hx.regs_fits rJ))
      (hy1_0_eq ▸ hy1_wf.regs_fits 0)
  have hs3_er : EpochRegs U V w N s3 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs3_sz : epochMetaBits U w N ≤ s3.bitSize := by
    change epochMetaBits U w N ≤ y2.bitSize; rw [hy2_sz_x]; exact hsz
  refine .seq (T₁ := 73) (T₂ := 141)
    (writeLMMod4RegCode_exec hw hN_pos hnU hU hs3_wf hs3_er
      hs3_sz (c_base := 5) (by decide) hb hj hold_lt
      (by simp +decide [s3, BitRAM.Data.set])
      (by simp +decide [s3, BitRAM.Data.set])
      (by simp +decide [s3, BitRAM.Data.set]))
    (fun y3 ⟨hy3_sz, hy3_wf, hy3_er, hy3_lm, hy3_gm, hy3_td, hy3_dt, hy3_out, hy3_items,
      hy3_regs⟩ => ?_) (by omega)
  have hy3_sz_x : y3.bitSize = x.bitSize := hy3_sz.trans hy2_sz_x
  have hy3_hi : ∀ r : Fin 280, 19 ≤ r.val → y3.regs r = s2.regs r := by
    intro r hr
    rw [hy3_regs r hr]
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hy2_hi r hr
  have hy3_19 : y3.regs 19 = old_h := by
    rw [hy3_hi 19 (by decide)]; simp +decide [s2, BitRAM.Data.set]
  have hy3_20 : y3.regs 20 = 0 := by
    rw [hy3_hi 20 (by decide)]; simp +decide [s2, BitRAM.Data.set]
  have hy3_21 : y3.regs 21 = 1 := by
    rw [hy3_hi 21 (by decide)]; simp +decide [s2, BitRAM.Data.set]
  have hy3_22 : y3.regs 22 = j_new + 1 := by
    rw [hy3_hi 22 (by decide)]; simp +decide [s2, BitRAM.Data.set]
  have hbranch : BitRAM.DemonicExecWithin w
      (.branch (.lt 20 19)
        (.seq (.op (.bin .sub 14 19 21))
        (.seq (.op (.copy 13 rB))
        (.seq (.op (.copy 15 22))
              writeLMPrevRegCode)))
        nopRegCode) y3
      (fun y4 =>
        y4.bitSize = x.bitSize ∧
        y4.WellFormed w ∧
        EpochRegs U V w N y4 ∧
        lmAtBit U w N y4.mem =
          (if 0 < old_h then
            Function.update (lmAtBit U w N y3.mem)
              (1 + (old_h - 1) % 4, b * numMicroPerBucket N + (old_h - 1) / 4) (j_new + 1)
          else lmAtBit U w N y3.mem) ∧
        gmAtBit U w N y4.mem = gmAtBit U w N y3.mem ∧
        tdAtBit U w N y4.mem = tdAtBit U w N y3.mem ∧
        dtAtBit U w N y4.mem = dtAtBit U w N y3.mem ∧
        (∀ a < offLM U w N, y4.mem a = y3.mem a) ∧
        (∀ d, denseQuotAt U V w N y4.toBitMemoryState d =
            denseQuotAt U V w N y3.toBitMemoryState d ∧
          denseValAt U V w N y4.toBitMemoryState d =
            denseValAt U V w N y3.toBitMemoryState d) ∧
        (∀ r : Fin 280, 19 ≤ r.val → y4.regs r = s2.regs r)) 77 := by
    by_cases hpos : 0 < old_h
    · have hcond : BitRAM.CondHolds (.lt 20 19) y3 := by
        change y3.regs 20 < y3.regs 19; rw [hy3_20, hy3_19]; exact hpos
      refine (dExec_branch_pos (T := 76) hcond ?_).mono (fun z hz => hz) (by omega)
      have hold_idx : old_h - 1 < effBucketCap N := by omega
      have hfit_sub : Fits w (old_h - 1) :=
        Nat.lt_of_le_of_lt (Nat.sub_le old_h 1) (hy1_0_eq ▸ hy1_wf.regs_fits 0)
      refine step_dExec_bin (v := old_h - 1) (T := 75)
        (by simp [BinOp.eval, hy3_19, hy3_21]) hfit_sub ?_
      refine step_dExec_copy (v := b) (T := 74)
        (by
          have h14 : rB ≠ 14 := by intro h; subst h; omega
          simp only [BitRAM.Data.set_regs, Function.update_of_ne h14]
          rw [hy3_hi rB (by omega)]
          dsimp only [s2, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
          exact (hy1_hi rB hrB_ge).trans hrB) ?_
      refine step_dExec_copy (v := j_new + 1) (T := 73)
        (by
          simp only [BitRAM.Data.set_regs,
            Function.update_of_ne (by decide : (22 : Fin 280) ≠ 13),
            Function.update_of_ne (by decide : (22 : Fin 280) ≠ 14), hy3_22]) ?_
      set s4 := ((y3.set 14 (old_h - 1)).set 13 b).set 15 (j_new + 1)
      have hs4_wf : s4.WellFormed w :=
        wf_set 15 (wf_set 13 (wf_set 14 hy3_wf hfit_sub) (hrB ▸ hx.regs_fits rB)) hfit_j1
      have hs4_er : EpochRegs U V w N s4 :=
        hy3_er.congr_regs (fun r hr1 _ => by
          dsimp only [s4, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      have hs4_sz : epochMetaBits U w N ≤ s4.bitSize := by
        change epochMetaBits U w N ≤ y3.bitSize; rw [hy3_sz_x]; exact hsz
      refine (writeLMMod4RegCode_exec hw hN_pos hnU hU hs4_wf hs4_er
        hs4_sz (c_base := 1) (by decide) hb hold_idx hval_lt
        (by simp +decide [s4, BitRAM.Data.set])
        (by simp +decide [s4, BitRAM.Data.set])
        (by simp +decide [s4, BitRAM.Data.set])).mono
        (fun y4 ⟨hy4_sz, hy4_wf, hy4_er, hy4_lm, hy4_gm, hy4_td, hy4_dt, hy4_out, hy4_items,
          hy4_regs⟩ => ?_) le_rfl
      rw [ite_eq_left hpos]
      refine ⟨hy4_sz.trans hy3_sz_x, hy4_wf, hy4_er, hy4_lm,
        hy4_gm, hy4_td, hy4_dt, fun a ha => hy4_out a (Or.inl ha), hy4_items,
        fun r hr => ?_⟩
      rw [hy4_regs r hr]
      dsimp only [s4, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hy3_hi r hr
    · have hcond : ¬BitRAM.CondHolds (.lt 20 19) y3 := by
        change ¬(y3.regs 20 < y3.regs 19); rw [hy3_20, hy3_19]; exact hpos
      refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
      rw [ite_eq_right hpos]
      exact ⟨hy3_sz_x, hy3_wf, hy3_er, rfl, rfl, rfl, rfl,
        fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, hy3_hi⟩
  refine .seq (T₁ := 77) (T₂ := 64) hbranch
    (fun y4 ⟨hy4_sz, hy4_wf, hy4_er, hy4_lm, hy4_gm, hy4_td, hy4_dt, hy4_out, hy4_items,
      hy4_regs⟩ => ?_) (by omega)
  refine step_dExec_copy (v := b) (T := 63)
    (by
      rw [hy4_regs rB (by omega)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact (hy1_hi rB hrB_ge).trans hrB) ?_
  refine step_dExec_copy (v := m) (T := 62)
    (by
      have h13 : rM ≠ 13 := by intro h; subst h; omega
      simp only [BitRAM.Data.set_regs, Function.update_of_ne h13]
      rw [hy4_regs rM (by omega)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact (hy1_hi rM hrM_ge).trans hrM) ?_
  refine step_dExec_copy (v := j_new + 1) (T := 61)
    (by
      simp only [BitRAM.Data.set_regs,
        Function.update_of_ne (by decide : (22 : Fin 280) ≠ 14),
        Function.update_of_ne (by decide : (22 : Fin 280) ≠ 13)]
      rw [hy4_regs 22 (by decide)]
      simp +decide [s2, BitRAM.Data.set]) ?_
  set s5 := ((y4.set 13 b).set 14 m).set 15 (j_new + 1)
  have hs5_wf : s5.WellFormed w :=
    wf_set 15 (wf_set 14 (wf_set 13 hy4_wf (hrB ▸ hx.regs_fits rB)) (hrM ▸ hx.regs_fits rM)) hfit_j1
  have hs5_er : EpochRegs U V w N s5 :=
    hy4_er.congr_regs (fun r hr1 _ => by
      dsimp only [s5, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs5_sz : epochMetaBits U w N ≤ s5.bitSize := by
    change epochMetaBits U w N ≤ y4.bitSize; rw [hy4_sz]; exact hsz
  refine (writeLMHeadRegCode_exec hw hN_pos hnU hU hs5_wf hs5_er
    hs5_sz hb hm hval_lt
    (by simp +decide [s5, BitRAM.Data.set])
    (by simp +decide [s5, BitRAM.Data.set])
    (by simp +decide [s5, BitRAM.Data.set])).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  change lmAtBit U w N y.mem = Function.update (lmAtBit U w N y4.mem) _ _ at hy_lm
  change lmAtBit U w N y3.mem = Function.update (lmAtBit U w N y2.mem) _ _ at hy3_lm
  change lmAtBit U w N y2.mem = Function.update (lmAtBit U w N y1.mem) _ _ at hy2_lm
  change gmAtBit U w N y2.mem = gmAtBit U w N y1.mem at hy2_gm
  change tdAtBit U w N y2.mem = tdAtBit U w N y1.mem at hy2_td
  change dtAtBit U w N y2.mem = dtAtBit U w N y1.mem at hy2_dt
  refine ⟨hy_sz.trans hy4_sz, hy_wf, hy_er,
    by
      rw [hy_lm, hy4_lm, hy3_lm, hy2_lm, hy1_mem]
      rfl,
    hy_gm.trans (hy4_gm.trans (hy3_gm.trans (hy2_gm.trans (by rw [hy1_mem])))),
    hy_td.trans (hy4_td.trans (hy3_td.trans (hy2_td.trans (by rw [hy1_mem])))),
    hy_dt.trans (hy4_dt.trans (hy3_dt.trans (hy2_dt.trans (by rw [hy1_mem])))),
    fun a ha => (hy_out a (Or.inl (by unfold offLMSub; omega))).trans
      ((hy4_out a ha).trans ((hy3_out a (Or.inl ha)).trans
        ((hy2_out a (Or.inl ha)).trans (congrFun hy1_mem a)))),
    fun d =>
      ⟨(hy_items d).1.trans ((hy4_items d).1.trans ((hy3_items d).1.trans
        ((hy2_items d).1.trans (congrArg (fun st => denseQuotAt U V w N st d) hy1_st)))),
       (hy_items d).2.trans ((hy4_items d).2.trans ((hy3_items d).2.trans
        ((hy2_items d).2.trans (congrArg (fun st => denseValAt U V w N st d) hy1_st))))⟩,
    fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s5, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  rw [hy4_regs r (by omega)]
  dsimp only [s2, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  exact hy1_hi r hr

/-- Uniform `BitRAM.Code .standard 280` program executing `prependIfIndexedProg`:
if `rJ < r251` (`effBucketCap N`), runs `lmPrependRegCode rB rM rJ`, else `nopRegCode`. -/
@[expose]
def prependIfIndexedRegCode (rB rM rJ : Fin 280) : BitRAM.Code .standard 280 :=
  .branch (.lt rJ 251) (lmPrependRegCode rB rM rJ) nopRegCode

theorem prependIfIndexedRegCode_exec {U V w N h_space base b m j_new : ℕ}
    {rB rM rJ : Fin 280} {x : BitRAM.Data 280} {s : Memory.State}
    (hrB_ge : 23 ≤ rB.val) (hrM_ge : 23 ≤ rM.val) (hrJ_ge : 23 ≤ rJ.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (hj_n : j_new < N)
    (hlm_eq : lmAtBit U w N x.mem = Succinct.lmAt base U V w N h_space s.mem)
    (hold : Succinct.lmHead N (Succinct.lmAt base U V w N h_space s.mem) b m ≤ effBucketCap N)
    (hrB : x.regs rB = b) (hrM : x.regs rM = m) (hrJ : x.regs rJ = j_new) :
    let s' := (Memory.spec 0).clientState s
      (Succinct.prependIfIndexedProg U V w N h_space (((base, b), m), j_new))
    BitRAM.DemonicExecWithin w (prependIfIndexedRegCode rB rM rJ) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem = Succinct.lmAt base U V w N h_space s'.mem ∧
        Succinct.gmAt base U V w N h_space s'.mem =
          Succinct.gmAt base U V w N h_space s.mem ∧
        Succinct.quotAt base U w N h_space s'.mem =
          Succinct.quotAt base U w N h_space s.mem ∧
        Succinct.valAt base U V w N h_space s'.mem =
          Succinct.valAt base U V w N h_space s.mem ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 23 ≤ r.val → y.regs r = x.regs r)) 350 := by
  intro s'
  have h251 : x.regs 251 = effBucketCap N := (her.active hN_pos).2.2.2.2.2.2.1
  unfold prependIfIndexedRegCode
  by_cases hj : j_new < effBucketCap N
  · have hj_min : j_new < min N (effBucketCap N) := lt_min hj_n hj
    have hs' : s' = (Memory.spec 0).clientState s
        (Succinct.lmPrependProg U V w N h_space (((base, b), m), j_new)) := by
      dsimp only [s']
      unfold Succinct.prependIfIndexedProg
      simp only [pure_bind]
      rw [ite_eq_left hj_min]
    have hcond : BitRAM.CondHolds (.lt rJ 251) x := by
      change x.regs rJ < x.regs 251; rw [hrJ, h251]; exact hj
    obtain ⟨hlm_s', hgm_s', hq_s', hv_s'⟩ :=
      lmPrependProg_lmAt (U := U) (V := V) (w := w) (N := N) (h_space := h_space)
        (base := base) (b := b) (m := m) (j_new := j_new) hw hb hm hj hj_n hold
    refine dExec_branch_pos (T := 349) hcond
      ((lmPrependRegCode_exec hrB_ge hrM_ge hrJ_ge hw hN_pos hnU hU hx her hsz
        hb hm hj hj_n (hlm_eq.symm ▸ hold) hrB hrM hrJ).mono
        (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
          ⟨hy_sz, hy_wf, hy_er, by rw [hy_lm, hlm_eq, hs', hlm_s'],
            by rw [hs', hgm_s'], by rw [hs', hq_s'], by rw [hs', hv_s'],
            hy_gm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩) le_rfl)
  · have hj_min : ¬(j_new < min N (effBucketCap N)) := fun h => hj (lt_min_iff.mp h).2
    have hs' : s' = s := by
      dsimp only [s']
      unfold Succinct.prependIfIndexedProg
      simp only [pure_bind]
      rw [ite_eq_right hj_min]
      rfl
    have hcond : ¬BitRAM.CondHolds (.lt rJ 251) x := by
      change ¬(x.regs rJ < x.regs 251); rw [hrJ, h251]; exact hj
    refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
    rw [hs']
    exact ⟨rfl, hx, her, hlm_eq, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

/-- Pure functional effect of `lmUnlinkProg` on `lm : ℕ × ℕ → ℕ`. -/
@[expose]
def lmUnlinkFn (N b m j_del : ℕ) (lm : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  let p := lm (1 + j_del % 4, b * numMicroPerBucket N + j_del / 4)
  let n := lm (5 + j_del % 4, b * numMicroPerBucket N + j_del / 4)
  let lm₁ := if 0 < p then
      Function.update lm (5 + (p - 1) % 4, b * numMicroPerBucket N + (p - 1) / 4) n
    else
      Function.update lm (0, b * numMicroPerBucket N + m) n
  if 0 < n then
    Function.update lm₁ (1 + (n - 1) % 4, b * numMicroPerBucket N + (n - 1) / 4) p
  else
    lm₁

theorem lmUnlinkProg_lmAt {U V w N h_space base b m j_del : ℕ}
    (hw : 0 < w) (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hj : j_del < effBucketCap N)
    {s : Memory.State}
    (hp_le : Succinct.lmPrev N (Succinct.lmAt base U V w N h_space s.mem) b j_del ≤
      effBucketCap N)
    (hn_le : Succinct.lmNext N (Succinct.lmAt base U V w N h_space s.mem) b j_del ≤
      effBucketCap N) :
    let s' := (Memory.spec 0).clientState s
      (Succinct.lmUnlinkProg U V w N h_space (((base, b), m), j_del))
    Succinct.lmAt base U V w N h_space s'.mem =
      lmUnlinkFn N b m j_del (Succinct.lmAt base U V w N h_space s.mem) ∧
    Succinct.gmAt base U V w N h_space s'.mem =
      Succinct.gmAt base U V w N h_space s.mem ∧
    Succinct.quotAt base U w N h_space s'.mem =
      Succinct.quotAt base U w N h_space s.mem ∧
    Succinct.valAt base U V w N h_space s'.mem =
      Succinct.valAt base U V w N h_space s.mem := by
  intro s'
  set lm := Succinct.lmAt base U V w N h_space s.mem
  set p := Succinct.lmPrev N lm b j_del
  set n := Succinct.lmNext N lm b j_del
  have hp_lt : p < 2 ^ effBucketPosBits N :=
    Succinct.lmAt_lt base U V w N h_space s.mem (1 + j_del % 4, b * numMicroPerBucket N + j_del / 4)
  have hn_lt : n < 2 ^ effBucketPosBits N :=
    Succinct.lmAt_lt base U V w N h_space s.mem (5 + j_del % 4, b * numMicroPerBucket N + j_del / 4)
  have hs'_def : s' =
      (if 0 < p then
         if 0 < n then
           (Memory.spec 0).clientState
             ((Memory.spec 0).clientState s
               (Succinct.writeLMMod4Prog U V w N h_space 5 (((base, b), p - 1), n)))
             (Succinct.writeLMMod4Prog U V w N h_space 1 (((base, b), n - 1), p))
         else
           (Memory.spec 0).clientState s
             (Succinct.writeLMMod4Prog U V w N h_space 5 (((base, b), p - 1), n))
       else
         if 0 < n then
           (Memory.spec 0).clientState
             ((Memory.spec 0).clientState s
               (Succinct.writeLMProg U V w N h_space 0
                 ((base, b * numMicroPerBucket N + m), n)))
             (Succinct.writeLMMod4Prog U V w N h_space 1 (((base, b), n - 1), p))
         else
           (Memory.spec 0).clientState s
             (Succinct.writeLMProg U V w N h_space 0
               ((base, b * numMicroPerBucket N + m), n))) := by
    dsimp only [s', p, n, lm]
    unfold Succinct.lmUnlinkProg Succinct.writeLMNextProg Succinct.writeLMPrevProg
      Succinct.writeLMHeadProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readLMPrevProg,
      Succinct.clientResult_readLMPrevProg _ hb hj,
      StateTransitionSpec.clientState_bind, Succinct.clientState_readLMNextProg,
      Succinct.clientResult_readLMNextProg _ hb hj]
    split_ifs <;>
      rw [StateTransitionSpec.clientState_bind] <;>
      rfl
  rw [hs'_def]
  unfold lmUnlinkFn
  change _ = (if 0 < n then Function.update (if 0 < p then _ else _) _ _
    else (if 0 < p then _ else _)) ∧ _
  split_ifs with hp_pos hn_pos hn_pos
  · have hp_idx : p - 1 < effBucketCap N := by omega
    have hn_idx : n - 1 < effBucketCap N := by omega
    set s₁ := (Memory.spec 0).clientState s
      (Succinct.writeLMMod4Prog U V w N h_space 5 (((base, b), p - 1), n))
    obtain ⟨_, _, hq₁, hv₁, hlm₁, hgm₁⟩ :=
      Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c_base := 5) (base := base) (b := b) (j := p - 1) (val := n)
        hw (by decide) hb hp_idx hn_lt s
    obtain ⟨_, _, hq₂, hv₂, hlm₂, hgm₂⟩ :=
      Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c_base := 1) (base := base) (b := b) (j := n - 1) (val := p)
        hw (by decide) hb hn_idx hp_lt s₁
    exact ⟨by rw [hlm₂, hlm₁]; rfl,
      by rw [hgm₂, hgm₁],
      by rw [hq₂, hq₁],
      by rw [hv₂, hv₁]⟩
  · have hp_idx : p - 1 < effBucketCap N := by omega
    obtain ⟨_, _, hq₁, hv₁, hlm₁, hgm₁⟩ :=
      Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c_base := 5) (base := base) (b := b) (j := p - 1) (val := n)
        hw (by decide) hb hp_idx hn_lt s
    exact ⟨by rw [hlm₁]; rfl, hgm₁, hq₁, hv₁⟩
  · have hn_idx : n - 1 < effBucketCap N := by omega
    set s₁ := (Memory.spec 0).clientState s
      (Succinct.writeLMProg U V w N h_space 0 ((base, b * numMicroPerBucket N + m), n))
    obtain ⟨_, _, hq₁, hv₁, hlm₁, hgm₁⟩ :=
      Succinct.writeLMProg_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c := 0) (base := base) (idx := b * numMicroPerBucket N + m) (val := n)
        hw (by decide) (Succinct.lmHeadIdx_lt hb hm) hn_lt s
    obtain ⟨_, _, hq₂, hv₂, hlm₂, hgm₂⟩ :=
      Succinct.writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c_base := 1) (base := base) (b := b) (j := n - 1) (val := p)
        hw (by decide) hb hn_idx hp_lt s₁
    exact ⟨by rw [hlm₂, hlm₁]; rfl,
      by rw [hgm₂, hgm₁],
      by rw [hq₂, hq₁],
      by rw [hv₂, hv₁]⟩
  · obtain ⟨_, _, hq₁, hv₁, hlm₁, hgm₁⟩ :=
      Succinct.writeLMProg_effect (U := U) (V := V) (w := w) (n_max := N) (h_space := h_space)
        (c := 0) (base := base) (idx := b * numMicroPerBucket N + m) (val := n)
        hw (by decide) (Succinct.lmHeadIdx_lt hb hm) hn_lt s
    exact ⟨by rw [hlm₁]; rfl, hgm₁, hq₁, hv₁⟩

/-- Uniform `BitRAM.Code .standard 280` program executing `lmUnlinkFn N b m j_del` on `lmAtBit`:
given `rB = b`, `rM = m`, `rJ = j_del` (`23 ≤ rB, rM, rJ`), uses `r19..r22` and `r13..r18` as
temporaries and preserves `r ≥ 23`. -/
@[expose]
def lmUnlinkRegCode (rB rM rJ : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 13 rB))
  (.seq (.op (.copy 14 rJ))
  (.seq readLMPrevRegCode
  (.seq (.op (.copy 19 0))
  (.seq (.op (.copy 13 rB))
  (.seq (.op (.copy 14 rJ))
  (.seq readLMNextRegCode
  (.seq (.op (.copy 20 0))
  (.seq (.op (.const 21 0))
  (.seq (.op (.const 22 1))
  (.seq (.branch (.lt 21 19)
          (.seq (.op (.bin .sub 14 19 22))
          (.seq (.op (.copy 13 rB))
          (.seq (.op (.copy 15 20))
                writeLMNextRegCode)))
          (.seq (.op (.copy 13 rB))
          (.seq (.op (.copy 14 rM))
          (.seq (.op (.copy 15 20))
                writeLMHeadRegCode))))
        (.branch (.lt 21 20)
          (.seq (.op (.bin .sub 14 20 22))
          (.seq (.op (.copy 13 rB))
          (.seq (.op (.copy 15 19))
                writeLMPrevRegCode)))
          nopRegCode)))))))))))

theorem lmUnlinkRegCode_exec {U V w N b m j_del : ℕ} {rB rM rJ : Fin 280}
    {x : BitRAM.Data 280}
    (hrB_ge : 23 ≤ rB.val) (hrM_ge : 23 ≤ rM.val) (hrJ_ge : 23 ≤ rJ.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (hj : j_del < effBucketCap N)
    (hp_le : Succinct.lmPrev N (lmAtBit U w N x.mem) b j_del ≤ effBucketCap N)
    (hn_le : Succinct.lmNext N (lmAtBit U w N x.mem) b j_del ≤ effBucketCap N)
    (hrB : x.regs rB = b) (hrM : x.regs rM = m) (hrJ : x.regs rJ = j_del) :
    BitRAM.DemonicExecWithin w (lmUnlinkRegCode rB rM rJ) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem = lmUnlinkFn N b m j_del (lmAtBit U w N x.mem) ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 23 ≤ r.val → y.regs r = x.regs r)) 286 := by
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hfit_1 : Fits w 1 := hfit_N 1 (by omega)
  set lm₀ := lmAtBit U w N x.mem
  set p := Succinct.lmPrev N lm₀ b j_del
  set n := Succinct.lmNext N lm₀ b j_del
  have hp_lt : p < 2 ^ effBucketPosBits N :=
    lmAtBit_lt U w N x.mem (1 + j_del % 4, b * numMicroPerBucket N + j_del / 4)
  have hn_lt : n < 2 ^ effBucketPosBits N :=
    lmAtBit_lt U w N x.mem (5 + j_del % 4, b * numMicroPerBucket N + j_del / 4)
  unfold lmUnlinkRegCode
  refine step_dExec_copy (v := b) (T := 285) hrB ?_
  refine step_dExec_copy (v := j_del) (T := 284)
    (by
      have hne : rJ ≠ 13 := by intro h; subst h; omega
      simp [BitRAM.Data.set, hne, hrJ]) ?_
  set s1 := (x.set 13 b).set 14 j_del
  have hs1_wf : s1.WellFormed w :=
    wf_set 14 (wf_set 13 hx (hrB ▸ hx.regs_fits rB)) (hrJ ▸ hx.regs_fits rJ)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 62) (T₂ := 222)
    (readLMMod4RegCode_exec hw hN_pos hnU hU hs1_wf hs1_er hsz (c_base := 1) (by decide) hb hj
      (by simp +decide [s1, BitRAM.Data.set]) (by simp +decide [s1, BitRAM.Data.set]))
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_0, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_0_eq : y1.regs 0 = p := hy1_0
  have hy1_hi : ∀ r : Fin 280, 19 ≤ r.val → y1.regs r = x.regs r := by
    intro r hr
    rw [hy1_regs r (by omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  refine step_dExec_copy (v := p) (T := 221) hy1_0_eq ?_
  refine step_dExec_copy (v := b) (T := 220)
    (by
      have h19 : rB ≠ 19 := by intro h; subst h; omega
      simp [BitRAM.Data.set, h19, hy1_hi rB (by omega), hrB]) ?_
  refine step_dExec_copy (v := j_del) (T := 219)
    (by
      have h13 : rJ ≠ 13 := by intro h; subst h; omega
      have h19 : rJ ≠ 19 := by intro h; subst h; omega
      simp [BitRAM.Data.set, h13, h19, hy1_hi rJ (by omega), hrJ]) ?_
  set s2 := ((y1.set 19 p).set 13 b).set 14 j_del
  have hs2_wf : s2.WellFormed w :=
    wf_set 14 (wf_set 13 (wf_set 19 hy1_wf (hy1_0_eq ▸ hy1_wf.regs_fits 0))
      (hrB ▸ hx.regs_fits rB)) (hrJ ▸ hx.regs_fits rJ)
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_sz : epochMetaBits U w N ≤ s2.bitSize := by
    change epochMetaBits U w N ≤ y1.bitSize; rw [hy1_sz]; exact hsz
  refine .seq (T₁ := 62) (T₂ := 157)
    (readLMMod4RegCode_exec hw hN_pos hnU hU hs2_wf hs2_er hs2_sz
      (c_base := 5) (by decide) hb hj
      (by simp +decide [s2, BitRAM.Data.set]) (by simp +decide [s2, BitRAM.Data.set]))
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_0, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  have hy2_0_eq : y2.regs 0 = n := by
    change y2.regs 0 = lmAtBit U w N y1.mem _ at hy2_0
    rw [hy2_0, hy1_mem]; rfl
  refine step_dExec_copy (v := n) (T := 156) hy2_0_eq ?_
  refine DemonicExecWithin.step_const (T := 155) (fits_zero w) ?_
  refine DemonicExecWithin.step_const (T := 154) hfit_1 ?_
  set s3 := ((y2.set 20 n).set 21 0).set 22 1
  have hs3_wf : s3.WellFormed w :=
    wf_set 22 (wf_set 21 (wf_set 20 hy2_wf (hy2_0_eq ▸ hy2_wf.regs_fits 0)) (fits_zero w)) hfit_1
  have hs3_er : EpochRegs U V w N s3 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs3_19 : s3.regs 19 = p := by
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy2_regs 19 (by decide)]
    simp +decide [s2, BitRAM.Data.set]
  have hs3_20 : s3.regs 20 = n := by simp +decide [s3, BitRAM.Data.set]
  have hs3_21 : s3.regs 21 = 0 := by simp +decide [s3, BitRAM.Data.set]
  have hs3_22 : s3.regs 22 = 1 := by simp +decide [s3, BitRAM.Data.set]
  have hs3_hi : ∀ r : Fin 280, 23 ≤ r.val → s3.regs r = x.regs r := by
    intro r hr
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    rw [hy2_regs r (by omega)]
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hy1_hi r (by omega)
  have hbranch1 : BitRAM.DemonicExecWithin w
      (.branch (.lt 21 19)
        (.seq (.op (.bin .sub 14 19 22))
        (.seq (.op (.copy 13 rB))
        (.seq (.op (.copy 15 20))
              writeLMNextRegCode)))
        (.seq (.op (.copy 13 rB))
        (.seq (.op (.copy 14 rM))
        (.seq (.op (.copy 15 20))
              writeLMHeadRegCode)))) s3
      (fun y3 =>
        y3.bitSize = x.bitSize ∧
        y3.WellFormed w ∧
        EpochRegs U V w N y3 ∧
        lmAtBit U w N y3.mem =
          (if 0 < p then
            Function.update lm₀ (5 + (p - 1) % 4, b * numMicroPerBucket N + (p - 1) / 4) n
          else
            Function.update lm₀ (0, b * numMicroPerBucket N + m) n) ∧
        gmAtBit U w N y3.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y3.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y3.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y3.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y3.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y3.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 19 ≤ r.val → y3.regs r = s3.regs r)) 77 := by
    by_cases hp_pos : 0 < p
    · have hcond : BitRAM.CondHolds (.lt 21 19) s3 := by
        change s3.regs 21 < s3.regs 19; rw [hs3_21, hs3_19]; exact hp_pos
      refine (dExec_branch_pos (T := 76) hcond ?_).mono (fun z hz => hz) (by omega)
      have hp_idx : p - 1 < effBucketCap N := by omega
      have hfit_sub : Fits w (p - 1) :=
        Nat.lt_of_le_of_lt (Nat.sub_le p 1) (hy1_0_eq ▸ hy1_wf.regs_fits 0)
      refine step_dExec_bin (v := p - 1) (T := 75)
        (by simp [BinOp.eval, hs3_19, hs3_22]) hfit_sub ?_
      refine step_dExec_copy (v := b) (T := 74)
        (by
          have h14 : rB ≠ 14 := by intro h; subst h; omega
          simp [BitRAM.Data.set, h14, hs3_hi rB hrB_ge, hrB]) ?_
      refine step_dExec_copy (v := n) (T := 73)
        (by
          simp only [BitRAM.Data.set_regs,
            Function.update_of_ne (by decide : (20 : Fin 280) ≠ 13),
            Function.update_of_ne (by decide : (20 : Fin 280) ≠ 14), hs3_20]) ?_
      set s4 := ((s3.set 14 (p - 1)).set 13 b).set 15 n
      have hs4_wf : s4.WellFormed w :=
        wf_set 15 (wf_set 13 (wf_set 14 hs3_wf hfit_sub) (hrB ▸ hx.regs_fits rB))
          (hy2_0_eq ▸ hy2_wf.regs_fits 0)
      have hs4_er : EpochRegs U V w N s4 :=
        hs3_er.congr_regs (fun r hr1 _ => by
          dsimp only [s4, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      have hs4_sz : epochMetaBits U w N ≤ s4.bitSize := by
        change epochMetaBits U w N ≤ y2.bitSize; rw [hy2_sz]; exact hsz
      refine (writeLMMod4RegCode_exec hw hN_pos hnU hU hs4_wf hs4_er
        hs4_sz (c_base := 5) (by decide) hb hp_idx hn_lt
        (by simp +decide [s4, BitRAM.Data.set])
        (by simp +decide [s4, BitRAM.Data.set])
        (by simp +decide [s4, BitRAM.Data.set])).mono
        (fun y3 ⟨hy3_sz, hy3_wf, hy3_er, hy3_lm, hy3_gm, hy3_td, hy3_dt, hy3_out, hy3_items,
          hy3_regs⟩ => ?_) le_rfl
      rw [ite_eq_left hp_pos]
      change lmAtBit U w N y3.mem = Function.update (lmAtBit U w N y2.mem) _ _ at hy3_lm
      change gmAtBit U w N y3.mem = gmAtBit U w N y2.mem at hy3_gm
      change tdAtBit U w N y3.mem = tdAtBit U w N y2.mem at hy3_td
      change dtAtBit U w N y3.mem = dtAtBit U w N y2.mem at hy3_dt
      refine ⟨hy3_sz.trans hy2_sz, hy3_wf, hy3_er,
        by rw [hy3_lm, hy2_mem],
        hy3_gm.trans (by rw [hy2_mem]), hy3_td.trans (by rw [hy2_mem]),
        hy3_dt.trans (by rw [hy2_mem]),
        fun a ha => (hy3_out a (Or.inl ha)).trans (congrFun hy2_mem a),
        fun d => ⟨(hy3_items d).1.trans (congrArg (fun st => denseQuotAt U V w N st d) hy2_st_x),
          (hy3_items d).2.trans (congrArg (fun st => denseValAt U V w N st d) hy2_st_x)⟩,
        fun r hr => ?_⟩
      rw [hy3_regs r hr]
      dsimp only [s4, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    · have hcond : ¬BitRAM.CondHolds (.lt 21 19) s3 := by
        change ¬(s3.regs 21 < s3.regs 19); rw [hs3_21, hs3_19]; exact hp_pos
      refine (dExec_branch_neg (T := 64) hcond ?_).mono (fun z hz => hz) (by omega)
      refine step_dExec_copy (v := b) (T := 63)
        (by rw [hs3_hi rB hrB_ge, hrB]) ?_
      refine step_dExec_copy (v := m) (T := 62)
        (by
          have h13 : rM ≠ 13 := by intro h; subst h; omega
          simp [BitRAM.Data.set, h13, hs3_hi rM hrM_ge, hrM]) ?_
      refine step_dExec_copy (v := n) (T := 61)
        (by
          simp only [BitRAM.Data.set_regs,
            Function.update_of_ne (by decide : (20 : Fin 280) ≠ 14),
            Function.update_of_ne (by decide : (20 : Fin 280) ≠ 13), hs3_20]) ?_
      set s4 := ((s3.set 13 b).set 14 m).set 15 n
      have hs4_wf : s4.WellFormed w :=
        wf_set 15 (wf_set 14 (wf_set 13 hs3_wf (hrB ▸ hx.regs_fits rB)) (hrM ▸ hx.regs_fits rM))
          (hy2_0_eq ▸ hy2_wf.regs_fits 0)
      have hs4_er : EpochRegs U V w N s4 :=
        hs3_er.congr_regs (fun r hr1 _ => by
          dsimp only [s4, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      have hs4_sz : epochMetaBits U w N ≤ s4.bitSize := by
        change epochMetaBits U w N ≤ y2.bitSize; rw [hy2_sz]; exact hsz
      refine (writeLMHeadRegCode_exec hw hN_pos hnU hU hs4_wf hs4_er
        hs4_sz hb hm hn_lt
        (by simp +decide [s4, BitRAM.Data.set])
        (by simp +decide [s4, BitRAM.Data.set])
        (by simp +decide [s4, BitRAM.Data.set])).mono
        (fun y3 ⟨hy3_sz, hy3_wf, hy3_er, hy3_lm, hy3_gm, hy3_td, hy3_dt, hy3_out, hy3_items,
          hy3_regs⟩ => ?_) le_rfl
      rw [ite_eq_right hp_pos]
      change lmAtBit U w N y3.mem = Function.update (lmAtBit U w N y2.mem) _ _ at hy3_lm
      change gmAtBit U w N y3.mem = gmAtBit U w N y2.mem at hy3_gm
      change tdAtBit U w N y3.mem = tdAtBit U w N y2.mem at hy3_td
      change dtAtBit U w N y3.mem = dtAtBit U w N y2.mem at hy3_dt
      refine ⟨hy3_sz.trans hy2_sz, hy3_wf, hy3_er,
        by rw [hy3_lm, hy2_mem],
        hy3_gm.trans (by rw [hy2_mem]), hy3_td.trans (by rw [hy2_mem]),
        hy3_dt.trans (by rw [hy2_mem]),
        fun a ha => (hy3_out a (Or.inl (by unfold offLMSub; omega))).trans (congrFun hy2_mem a),
        fun d => ⟨(hy3_items d).1.trans (congrArg (fun st => denseQuotAt U V w N st d) hy2_st_x),
          (hy3_items d).2.trans (congrArg (fun st => denseValAt U V w N st d) hy2_st_x)⟩,
        fun r hr => ?_⟩
      rw [hy3_regs r (by omega)]
      dsimp only [s4, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  refine .seq (T₁ := 77) (T₂ := 77) hbranch1
    (fun y3 ⟨hy3_sz, hy3_wf, hy3_er, hy3_lm, hy3_gm, hy3_td, hy3_dt, hy3_out, hy3_items,
      hy3_regs⟩ => ?_) (by omega)
  have hy3_19 : y3.regs 19 = p := by rw [hy3_regs 19 (by decide), hs3_19]
  have hy3_20 : y3.regs 20 = n := by rw [hy3_regs 20 (by decide), hs3_20]
  have hy3_21 : y3.regs 21 = 0 := by rw [hy3_regs 21 (by decide), hs3_21]
  have hy3_22 : y3.regs 22 = 1 := by rw [hy3_regs 22 (by decide), hs3_22]
  by_cases hn_pos : 0 < n
  · have hcond : BitRAM.CondHolds (.lt 21 20) y3 := by
      change y3.regs 21 < y3.regs 20; rw [hy3_21, hy3_20]; exact hn_pos
    refine (dExec_branch_pos (T := 76) hcond ?_).mono (fun z hz => hz) (by omega)
    have hn_idx : n - 1 < effBucketCap N := by omega
    have hfit_sub : Fits w (n - 1) :=
      Nat.lt_of_le_of_lt (Nat.sub_le n 1) (hy2_0_eq ▸ hy2_wf.regs_fits 0)
    refine step_dExec_bin (v := n - 1) (T := 75)
      (by simp [BinOp.eval, hy3_20, hy3_22]) hfit_sub ?_
    refine step_dExec_copy (v := b) (T := 74)
      (by
        have h14 : rB ≠ 14 := by intro h; subst h; omega
        simp [BitRAM.Data.set, h14, hy3_regs rB (by omega), hs3_hi rB hrB_ge, hrB]) ?_
    refine step_dExec_copy (v := p) (T := 73)
      (by
        simp only [BitRAM.Data.set_regs,
          Function.update_of_ne (by decide : (19 : Fin 280) ≠ 13),
          Function.update_of_ne (by decide : (19 : Fin 280) ≠ 14), hy3_19]) ?_
    set s5 := ((y3.set 14 (n - 1)).set 13 b).set 15 p
    have hs5_wf : s5.WellFormed w :=
      wf_set 15 (wf_set 13 (wf_set 14 hy3_wf hfit_sub) (hrB ▸ hx.regs_fits rB))
        (hy1_0_eq ▸ hy1_wf.regs_fits 0)
    have hs5_er : EpochRegs U V w N s5 :=
      hy3_er.congr_regs (fun r hr1 _ => by
        dsimp only [s5, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs5_sz : epochMetaBits U w N ≤ s5.bitSize := by
      change epochMetaBits U w N ≤ y3.bitSize; rw [hy3_sz]; exact hsz
    refine (writeLMMod4RegCode_exec hw hN_pos hnU hU hs5_wf hs5_er
      hs5_sz (c_base := 1) (by decide) hb hn_idx hp_lt
      (by simp +decide [s5, BitRAM.Data.set])
      (by simp +decide [s5, BitRAM.Data.set])
      (by simp +decide [s5, BitRAM.Data.set])).mono
      (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
      le_rfl
    change lmAtBit U w N y.mem = Function.update (lmAtBit U w N y3.mem) _ _ at hy_lm
    refine ⟨hy_sz.trans hy3_sz, hy_wf, hy_er,
      by
        unfold lmUnlinkFn
        change _ = if 0 < n then Function.update (if 0 < p then _ else _) _ _
          else (if 0 < p then _ else _)
        rw [ite_eq_left hn_pos, hy_lm, hy3_lm]
        rfl,
      hy_gm.trans hy3_gm, hy_td.trans hy3_td, hy_dt.trans hy3_dt,
      fun a ha => (hy_out a (Or.inl ha)).trans (hy3_out a ha),
      fun d => ⟨(hy_items d).1.trans (hy3_items d).1, (hy_items d).2.trans (hy3_items d).2⟩,
      fun r hr => ?_⟩
    rw [hy_regs r (by omega)]
    dsimp only [s5, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact (hy3_regs r (by omega)).trans (hs3_hi r hr)
  · have hcond : ¬BitRAM.CondHolds (.lt 21 20) y3 := by
      change ¬(y3.regs 21 < y3.regs 20); rw [hy3_21, hy3_20]; exact hn_pos
    refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
    refine ⟨hy3_sz, hy3_wf, hy3_er,
      by
        unfold lmUnlinkFn
        change _ = if 0 < n then Function.update (if 0 < p then _ else _) _ _
          else (if 0 < p then _ else _)
        rw [ite_eq_right hn_pos, hy3_lm]
        rfl,
      hy3_gm, hy3_td, hy3_dt, hy3_out, hy3_items,
      fun r hr => (hy3_regs r (by omega)).trans (hs3_hi r hr)⟩

/-- Uniform `BitRAM.Code .standard 280` program executing `unlinkIfIndexedProg`:
if `rJ < r251` (`effBucketCap N`), runs `lmUnlinkRegCode rB rM rJ`, else `nopRegCode`. -/
@[expose]
def unlinkIfIndexedRegCode (rB rM rJ : Fin 280) : BitRAM.Code .standard 280 :=
  .branch (.lt rJ 251) (lmUnlinkRegCode rB rM rJ) nopRegCode

theorem unlinkIfIndexedRegCode_exec {U V w N h_space base b m j_del : ℕ}
    {rB rM rJ : Fin 280} {x : BitRAM.Data 280} {s : Memory.State}
    (hrB_ge : 23 ≤ rB.val) (hrM_ge : 23 ≤ rM.val) (hrJ_ge : 23 ≤ rJ.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (hj_n : j_del < N)
    (hlm_eq : lmAtBit U w N x.mem = Succinct.lmAt base U V w N h_space s.mem)
    (hbounds : j_del < effBucketCap N →
      Succinct.lmPrev N (Succinct.lmAt base U V w N h_space s.mem) b j_del ≤ effBucketCap N ∧
      Succinct.lmNext N (Succinct.lmAt base U V w N h_space s.mem) b j_del ≤ effBucketCap N)
    (hrB : x.regs rB = b) (hrM : x.regs rM = m) (hrJ : x.regs rJ = j_del) :
    let s' := (Memory.spec 0).clientState s
      (Succinct.unlinkIfIndexedProg U V w N h_space (((base, b), m), j_del))
    BitRAM.DemonicExecWithin w (unlinkIfIndexedRegCode rB rM rJ) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem = Succinct.lmAt base U V w N h_space s'.mem ∧
        Succinct.gmAt base U V w N h_space s'.mem =
          Succinct.gmAt base U V w N h_space s.mem ∧
        Succinct.quotAt base U w N h_space s'.mem =
          Succinct.quotAt base U w N h_space s.mem ∧
        Succinct.valAt base U V w N h_space s'.mem =
          Succinct.valAt base U V w N h_space s.mem ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 23 ≤ r.val → y.regs r = x.regs r)) 287 := by
  intro s'
  have h251 : x.regs 251 = effBucketCap N := (her.active hN_pos).2.2.2.2.2.2.1
  unfold unlinkIfIndexedRegCode
  by_cases hj : j_del < effBucketCap N
  · have hj_min : j_del < min N (effBucketCap N) := lt_min hj_n hj
    have hs' : s' = (Memory.spec 0).clientState s
        (Succinct.lmUnlinkProg U V w N h_space (((base, b), m), j_del)) := by
      dsimp only [s']
      unfold Succinct.unlinkIfIndexedProg
      simp only [pure_bind]
      rw [ite_eq_left hj_min]
    have hcond : BitRAM.CondHolds (.lt rJ 251) x := by
      change x.regs rJ < x.regs 251; rw [hrJ, h251]; exact hj
    obtain ⟨hp_le, hn_le⟩ := hbounds hj
    obtain ⟨hlm_s', hgm_s', hq_s', hv_s'⟩ :=
      lmUnlinkProg_lmAt (U := U) (V := V) (w := w) (N := N) (h_space := h_space)
        (base := base) (b := b) (m := m) (j_del := j_del) hw hb hm hj hp_le hn_le
    refine dExec_branch_pos (T := 286) hcond
      ((lmUnlinkRegCode_exec hrB_ge hrM_ge hrJ_ge hw hN_pos hnU hU hx her hsz
        hb hm hj (hlm_eq.symm ▸ hp_le) (hlm_eq.symm ▸ hn_le) hrB hrM hrJ).mono
        (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
          ⟨hy_sz, hy_wf, hy_er, by rw [hy_lm, hlm_eq, hs', hlm_s'],
            by rw [hs', hgm_s'], by rw [hs', hq_s'], by rw [hs', hv_s'],
            hy_gm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩) le_rfl)
  · have hj_min : ¬(j_del < min N (effBucketCap N)) := fun h => hj (lt_min_iff.mp h).2
    have hs' : s' = s := by
      dsimp only [s']
      unfold Succinct.unlinkIfIndexedProg
      simp only [pure_bind]
      rw [ite_eq_right hj_min]
      rfl
    have hcond : ¬BitRAM.CondHolds (.lt rJ 251) x := by
      change ¬(x.regs rJ < x.regs 251); rw [hrJ, h251]; exact hj
    refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
    rw [hs']
    exact ⟨rfl, hx, her, hlm_eq, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

/-! ## Section 3: Metadata preservation under dense-item operations -/

/-- Any modification preserving all words `< epochMetaWords U w N` preserves `lmAtBit`, `gmAtBit`,
`tdAtBit`, `dtAtBit`, and all header/hash words `< offLM U w N`. -/
theorem meta_eq_of_low_words_eq {U w N : ℕ} (hw : 0 < w) (hN_pos : 0 < N)
    {m₁ m₂ : ℕ → ℕ} (hlow : ∀ a < epochMetaWords U w N, m₁ a = m₂ a) :
    lmAtBit U w N m₁ = lmAtBit U w N m₂ ∧
    gmAtBit U w N m₁ = gmAtBit U w N m₂ ∧
    tdAtBit U w N m₁ = tdAtBit U w N m₂ ∧
    dtAtBit U w N m₁ = dtAtBit U w N m₂ ∧
    (∀ a < offLM U w N, m₁ a = m₂ a) := by
  have hdt_meta : offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w =
      epochMetaWords U w N := offDT_add_eq_epochMetaWords hN_pos
  have htd_dt : offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w = offDT U w N := rfl
  have hgm_td : offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w = offTD U w N := rfl
  have hlm_gm : offLM U w N + 9 * Succinct.lmSubWords N w = offGM U w N := rfl
  refine ⟨?_, ?_, ?_, ?_, fun a ha => hlow a (by omega)⟩
  · funext ⟨c, j⟩
    unfold lmAtBit
    by_cases hcj : c < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj, ite_eq_left hcj]
      apply readPacked_congr hw (fun addr haddr => hlow addr ?_) hcj.2
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hcj.1
      have hhi : addr < offLM U w N + c * packedWords (totalMicroBuckets N) (effBucketPosBits N) w +
          packedWords (totalMicroBuckets N) (effBucketPosBits N) w := haddr.2
      rw [lmSubWords_eq] at hmul hlm_gm
      rw [Nat.add_one_mul] at hmul
      omega
    · rw [ite_eq_right hcj, ite_eq_right hcj]
  · funext i
    unfold gmAtBit
    by_cases hi : i < globalMetaLen N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hlow addr (by have := haddr.2; omega)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · funext i
    unfold tdAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hlow addr (by have := haddr.2; omega)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · funext i
    unfold dtAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hlow addr (by have := haddr.2; omega)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]

/-- Frame theorem for `appendDenseRegCode`: appends `(q, v)` at dense index `n_t` (when
`x.bitSize = itemBitOff U V w N n_t`), grows `bitSize` to `itemBitOff U V w N (n_t + 1)`, and
preserves all earlier dense items `d < n_t` and all metadata arrays. -/
theorem appendDenseRegCode_frame {U V w N n_t q v : ℕ} {rQ rV : Fin 280} {x : BitRAM.Data 280}
    (hrQ_ge : 16 ≤ rQ.val) (hrV_ge : 16 ≤ rV.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : x.bitSize = itemBitOff U V w N n_t)
    (hrQ : x.regs rQ = q) (hrV : x.regs rV = v)
    (hq : Fits (quotientBits U N) q) (hv : Fits (valBits V) v)
    (hfits : Fits w (itemBitOff U V w N (n_t + 1))) :
    BitRAM.DemonicExecWithin w (appendDenseRegCode rQ rV) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = itemBitOff U V w N (n_t + 1) ∧
        denseQuotAt U V w N y.toBitMemoryState n_t = q ∧
        denseValAt U V w N y.toBitMemoryState n_t = v ∧
        (∀ d < n_t,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 96 := by
  have hfits' : Fits w (x.bitSize + itemBits U V N) := by
    rwa [hsz, ← itemBitOff_succ]
  refine (appendDenseRegCode_exec hrQ_ge hrV_ge hw hU hV hx her hrQ hrV hq hv hfits').mono
    (fun y ⟨hy_st, hy_wf, hy_er, hy_sz, hy_regs⟩ => ?_) le_rfl
  obtain ⟨hq_n, hv_n, hitems, hlow⟩ :=
    denseQuotAt_ValAt_appendDenseItemState hw hU hV hx.mem_wf hsz hq hv hfits'
  have hlow' : ∀ a < epochMetaWords U w N, y.mem a = x.mem a := by
    intro a ha
    exact (congrFun (congrArg BitMemory.State.mem hy_st) a).trans (hlow a ha)
  obtain ⟨hlm, hgm, htd, hdt, hout⟩ := meta_eq_of_low_words_eq hw hN_pos hlow'
  refine ⟨hy_wf, hy_er, by rw [hy_sz, hsz, itemBitOff_succ],
    by rw [hy_st, hq_n], by rw [hy_st, hv_n],
    fun d hd => by rw [hy_st]; exact hitems d hd,
    hlm, hgm, htd, hdt, hout, hy_regs⟩

/-- Frame theorem for `popDenseRegCode`: shrinks `bitSize` from `itemBitOff U V w N (n_t + 1)` to
`itemBitOff U V w N n_t`, preserving all dense items `d < n_t` and all metadata arrays. -/
theorem popDenseRegCode_frame {U V w N n_t : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : x.bitSize = itemBitOff U V w N (n_t + 1)) :
    BitRAM.DemonicExecWithin w popDenseRegCode x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = itemBitOff U V w N n_t ∧
        (∀ d < n_t,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a < offLM U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 6 := by
  refine (popDenseRegCode_exec hw hU hV hx her hsz).mono
    (fun y ⟨_, hy_wf, hy_er, hy_sz, hitems, hlow, hy_regs⟩ => ?_) le_rfl
  obtain ⟨hlm, hgm, htd, hdt, hout⟩ := meta_eq_of_low_words_eq hw hN_pos hlow
  exact ⟨hy_wf, hy_er, hy_sz, hitems, hlm, hgm, htd, hdt, hout, hy_regs⟩

end Cslib.DataStructure.Dictionary.BitResizable
