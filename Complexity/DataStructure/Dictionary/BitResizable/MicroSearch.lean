/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.SlotResolve

/-!
# LocalMeta Doubly-Linked List Accessors and Phase 1 Micro-Chain Search on `BitRAM`

This module defines parameter-free `LocalMeta` doubly-linked list accessors (`readLMHeadRegCode`,
`writeLMHeadRegCode`, `readLMPrevRegCode`, `writeLMPrevRegCode`, `readLMNextRegCode`,
`writeLMNextRegCode`) and Phase 1 micro-chain search (`microStepRegCode`,
`searchMicroChainRegCode`) on `BitRAM.Data 280`.
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

/-! ## Section 1: Parameter-free `LocalMeta` doubly-linked list accessors (`readLMHeadRegCode`,
`writeLMHeadRegCode`, `readLMPrevRegCode`, `writeLMPrevRegCode`, `readLMNextRegCode`,
`writeLMNextRegCode`) -/

/-- 1-step idempotent no-op (`BitRAM.Code .standard 280`). -/
@[expose]
def nopRegCode : BitRAM.Code .standard 280 :=
  .op (.copy 0 0)

theorem nopRegCode_exec {w : ℕ} {x : BitRAM.Data 280} {P : BitRAM.Data 280 → Prop} (hP : P x) :
    BitRAM.DemonicExecWithin w nopRegCode x P 1 := by
  have heq : x.set 0 (x.regs 0) = x := by
    cases x
    simp [BitRAM.Data.set]
  exact DemonicExecWithin.copy (by rwa [heq])

theorem fits_of_le_totalMicroBuckets_of_le_N {U w N v : ℕ}
    (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w) (hv : v ≤ totalMicroBuckets N) :
    Fits w v :=
  fits_of_le_N hw hnU hU (hv.trans (totalMicroBuckets_le N))

/-- Read `Succinct.lmHead N (lmAtBit U w N x.mem) b m` into `r0` (`BitRAM.Code .standard 280`):
given `r13 = b` (`b < numBuckets N`) and `r14 = m` (`m < numMicroPerBucket N`), computes
`r13 := r13 * r248 + r14` and calls `readLMRegCode 0 13 0`. Preserves `r ≥ 15`. -/
@[expose]
def readLMHeadRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mul 13 13 248))
  (.seq (.op (.bin .add 13 13 14))
        (readLMRegCode 0 13 0))

theorem readLMHeadRegCode_exec {U V w N b m : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hr13 : x.regs 13 = b) (hr14 : x.regs 14 = m) :
    BitRAM.DemonicExecWithin w readLMHeadRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 0 = Succinct.lmHead N (lmAtBit U w N x.mem) b m ∧
        (∀ r : Fin 280, 15 ≤ r.val → y.regs r = x.regs r)) 50 := by
  obtain ⟨_, _, _, h248, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := her.active hN_pos
  have hidx_lt : b * numMicroPerBucket N + m < totalMicroBuckets N := Succinct.lmHeadIdx_lt hb hm
  have hfit_bm : Fits w (b * numMicroPerBucket N) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (by omega)
  have hfit_idx : Fits w (b * numMicroPerBucket N + m) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (le_of_lt hidx_lt)
  unfold readLMHeadRegCode
  refine step_dExec_bin (v := b * numMicroPerBucket N) (T := 49)
    (by simp [BinOp.eval, hr13, h248]) hfit_bm ?_
  refine step_dExec_bin (v := b * numMicroPerBucket N + m) (T := 48)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr14]) hfit_idx ?_
  set s1 := (x.set 13 (b * numMicroPerBucket N)).set 13 (b * numMicroPerBucket N + m)
  have hs1_wf : s1.WellFormed w := wf_set 13 (wf_set 13 hx hfit_bm) hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (readLMRegCode_exec (c := 0) (rIdx := 13) (rDst := 0) (by decide) hw hN_pos hnU hU
    hs1_wf hs1_er (by decide) hidx_lt (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
    (fun y ⟨hy_st, hy_wf, hy_0, hy_regs⟩ => ?_) le_rfl
  refine ⟨hy_st, hy_wf,
    hs1_er.congr_regs (fun r hr1 _ =>
      hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)),
    hy_0, fun r hr => ?_⟩
  rw [hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Write `val` in `r15` to `Succinct.lmHead N lm b m` (`BitRAM.Code .standard 280`):
given `r13 = b` (`b < numBuckets N`), `r14 = m` (`m < numMicroPerBucket N`), and `r15 = val`,
computes `r13 := r13 * r248 + r14` and calls `writeLMRegCode 0 13 15`. Preserves `r ≥ 15`. -/
@[expose]
def writeLMHeadRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mul 13 13 248))
  (.seq (.op (.bin .add 13 13 14))
        (writeLMRegCode 0 13 15))

theorem writeLMHeadRegCode_exec {U V w N b m val : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hval : val < 2 ^ effBucketPosBits N)
    (hr13 : x.regs 13 = b) (hr14 : x.regs 14 = m) (hr15 : x.regs 15 = val) :
    BitRAM.DemonicExecWithin w writeLMHeadRegCode x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem =
          Function.update (lmAtBit U w N x.mem) (0, b * numMicroPerBucket N + m) val ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offLMSub U w N 0 ∨ offLMSub U w N 1 ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N x.toBitMemoryState d ∧
              denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 15 ≤ r.val → y.regs r = x.regs r)) 61 := by
  obtain ⟨_, _, _, h248, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := her.active hN_pos
  have hidx_lt : b * numMicroPerBucket N + m < totalMicroBuckets N := Succinct.lmHeadIdx_lt hb hm
  have hfit_bm : Fits w (b * numMicroPerBucket N) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (by omega)
  have hfit_idx : Fits w (b * numMicroPerBucket N + m) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (le_of_lt hidx_lt)
  unfold writeLMHeadRegCode
  refine step_dExec_bin (v := b * numMicroPerBucket N) (T := 60)
    (by simp [BinOp.eval, hr13, h248]) hfit_bm ?_
  refine step_dExec_bin (v := b * numMicroPerBucket N + m) (T := 59)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr14]) hfit_idx ?_
  set s1 := (x.set 13 (b * numMicroPerBucket N)).set 13 (b * numMicroPerBucket N + m)
  have hs1_wf : s1.WellFormed w := wf_set 13 (wf_set 13 hx hfit_bm) hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (writeLMRegCode_exec (c := 0) (rIdx := 13) (rVal := 15) (by decide) (by decide)
    hw hN_pos hnU hU hs1_wf hs1_er (by decide) hidx_lt hval
    (by simp +decide [s1, BitRAM.Data.set])
    (by simp +decide [s1, BitRAM.Data.set, hr15]) hsz).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_dense, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_dense, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Read `lmAtBit U w N x.mem (c_base + j % 4, b * numMicroPerBucket N + j / 4)` into `r0`
(`BitRAM.Code .standard 280`): given `r13 = b` (`b < numBuckets N`) and `r14 = j`
(`j < effBucketCap N`), computes `r13 := r13 * r248 + r14 / 4` and `r16 := r14 % 4`, then branches
on `r16 = 0, 1, 2` calling `readLMRegCode (c_base + r) 13 0`. Preserves `r ≥ 18`. -/
@[expose]
def readLMMod4RegCode (c_base : ℕ) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 15 4))
  (.seq (.op (.bin .div 16 14 15))
  (.seq (.op (.bin .mod 17 14 15))
  (.seq (.op (.bin .mul 13 13 248))
  (.seq (.op (.bin .add 13 13 16))
  (.seq (.op (.const 15 0))
        (.branch (.eq 17 15)
          (readLMRegCode c_base 13 0)
          (.seq (.op (.const 15 1))
                (.branch (.eq 17 15)
                  (readLMRegCode (c_base + 1) 13 0)
                  (.seq (.op (.const 15 2))
                        (.branch (.eq 17 15)
                          (readLMRegCode (c_base + 2) 13 0)
                          (readLMRegCode (c_base + 3) 13 0)))))))))))

theorem readLMMod4RegCode_exec {U V w N c_base b j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hc : c_base + 3 < 9) (hb : b < numBuckets N) (hj : j < effBucketCap N)
    (hr13 : x.regs 13 = b) (hr14 : x.regs 14 = j) :
    BitRAM.DemonicExecWithin w (readLMMod4RegCode c_base) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 0 = lmAtBit U w N x.mem (c_base + j % 4, b * numMicroPerBucket N + j / 4) ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 62 := by
  obtain ⟨_, _, _, h248, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := her.active hN_pos
  have hidx_lt : b * numMicroPerBucket N + j / 4 < totalMicroBuckets N :=
    Succinct.lmSlotIdx_lt hb hj
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have h4_le_bs : 4 ≤ x.bitSize := by
    have h4 : 4 ≤ epochMetaWords U w N := by
      unfold epochMetaWords; rw [ite_eq_right (Nat.ne_of_gt hN_pos)]; omega
    calc 4 ≤ epochMetaWords U w N := h4
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  have hfit_const : ∀ v ≤ 4, Fits w v := fun v hv => Fits.of_le hfit_bs (by omega)
  have hfit_div : Fits w (j / 4) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (by omega)
  have hfit_mod : Fits w (j % 4) := hfit_const (j % 4) (by omega)
  have hfit_bm : Fits w (b * numMicroPerBucket N) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (by omega)
  have hfit_idx : Fits w (b * numMicroPerBucket N + j / 4) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (le_of_lt hidx_lt)
  unfold readLMMod4RegCode
  refine DemonicExecWithin.step_const (T := 61) (hfit_const 4 le_rfl) ?_
  refine step_dExec_bin (v := j / 4) (T := 60)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr14]) hfit_div ?_
  refine step_dExec_bin (v := j % 4) (T := 59)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr14]) hfit_mod ?_
  refine step_dExec_bin (v := b * numMicroPerBucket N) (T := 58)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr13, h248]) hfit_bm ?_
  refine step_dExec_bin (v := b * numMicroPerBucket N + j / 4) (T := 57)
    (by simp +decide [BitRAM.Data.set, BinOp.eval]) hfit_idx ?_
  refine DemonicExecWithin.step_const (T := 56) (fits_zero w) ?_
  set s1 := (((((x.set 15 4).set 16 (j / 4)).set 17 (j % 4)).set 13
    (b * numMicroPerBucket N)).set 13 (b * numMicroPerBucket N + j / 4)).set 15 0
  have hs1_wf : s1.WellFormed w :=
    wf_set 15 (wf_set 13 (wf_set 13 (wf_set 17 (wf_set 16
      (wf_set 15 hx (hfit_const 4 le_rfl)) hfit_div) hfit_mod) hfit_bm) hfit_idx) (fits_zero w)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_regs : ∀ r : Fin 280, 18 ≤ r.val → s1.regs r = x.regs r := by
    intro r hr
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  by_cases h0 : j % 4 = 0
  · have hcond0 : BitRAM.CondHolds (.eq 17 15) s1 := by
      change s1.regs 17 = s1.regs 15; simp +decide [s1, BitRAM.Data.set, h0]
    refine (dExec_branch_pos (T := 48) hcond0 ?_).mono (fun z hz => hz) (by omega)
    refine (readLMRegCode_exec (c := c_base) (rIdx := 13) (rDst := 0) (by decide) hw hN_pos hnU hU
      hs1_wf hs1_er (by omega) hidx_lt (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
      (fun y ⟨hy_st, hy_wf, hy_0, hy_regs⟩ => ?_) le_rfl
    refine ⟨hy_st, hy_wf,
      hs1_er.congr_regs (fun r hr1 _ =>
        hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)),
      by rw [h0, Nat.add_zero]; exact hy_0,
      fun r hr => (hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)).trans
        (hs1_regs r hr)⟩
  · have hcond0 : ¬BitRAM.CondHolds (.eq 17 15) s1 := by
      change s1.regs 17 ≠ s1.regs 15; simp +decide [s1, BitRAM.Data.set, h0]
    refine (dExec_branch_neg (T := 54) hcond0 ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 53) (hfit_const 1 (by omega)) ?_
    set s2 := s1.set 15 1
    have hs2_wf : s2.WellFormed w := wf_set 15 hs1_wf (hfit_const 1 (by omega))
    have hs2_er : EpochRegs U V w N s2 :=
      hs1_er.congr_regs (fun r hr1 _ => by
        dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    by_cases h1 : j % 4 = 1
    · have hcond1 : BitRAM.CondHolds (.eq 17 15) s2 := by
        change s2.regs 17 = s2.regs 15; simp +decide [s2, s1, BitRAM.Data.set, h1]
      refine (dExec_branch_pos (T := 48) hcond1 ?_).mono (fun z hz => hz) (by omega)
      refine (readLMRegCode_exec (c := c_base + 1) (rIdx := 13) (rDst := 0) (by decide)
        hw hN_pos hnU hU hs2_wf hs2_er (by omega) hidx_lt
        (by simp +decide [s2, s1, BitRAM.Data.set]) hsz).mono
        (fun y ⟨hy_st, hy_wf, hy_0, hy_regs⟩ => ?_) le_rfl
      refine ⟨hy_st, hy_wf,
        hs2_er.congr_regs (fun r hr1 _ =>
          hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)),
        by rw [h1]; exact hy_0,
        fun r hr => ?_⟩
      rw [hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hs1_regs r hr
    · have hcond1 : ¬BitRAM.CondHolds (.eq 17 15) s2 := by
        change s2.regs 17 ≠ s2.regs 15; simp +decide [s2, s1, BitRAM.Data.set, h1]
      refine (dExec_branch_neg (T := 51) hcond1 ?_).mono (fun z hz => hz) (by omega)
      refine DemonicExecWithin.step_const (T := 50) (hfit_const 2 (by omega)) ?_
      set s3 := s2.set 15 2
      have hs3_wf : s3.WellFormed w := wf_set 15 hs2_wf (hfit_const 2 (by omega))
      have hs3_er : EpochRegs U V w N s3 :=
        hs2_er.congr_regs (fun r hr1 _ => by
          dsimp only [s3, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      by_cases h2 : j % 4 = 2
      · have hcond2 : BitRAM.CondHolds (.eq 17 15) s3 := by
          change s3.regs 17 = s3.regs 15; simp +decide [s3, s2, s1, BitRAM.Data.set, h2]
        refine (dExec_branch_pos (T := 48) hcond2 ?_).mono (fun z hz => hz) (by omega)
        refine (readLMRegCode_exec (c := c_base + 2) (rIdx := 13) (rDst := 0) (by decide)
          hw hN_pos hnU hU hs3_wf hs3_er (by omega) hidx_lt
          (by simp +decide [s3, s2, s1, BitRAM.Data.set]) hsz).mono
          (fun y ⟨hy_st, hy_wf, hy_0, hy_regs⟩ => ?_) le_rfl
        refine ⟨hy_st, hy_wf,
          hs3_er.congr_regs (fun r hr1 _ =>
            hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)),
          by rw [h2]; exact hy_0,
          fun r hr => ?_⟩
        rw [hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s3, s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        exact hs1_regs r hr
      · have hcond2 : ¬BitRAM.CondHolds (.eq 17 15) s3 := by
          change s3.regs 17 ≠ s3.regs 15; simp +decide [s3, s2, s1, BitRAM.Data.set, h2]
        have h3 : j % 4 = 3 := by omega
        refine (dExec_branch_neg (T := 48) hcond2 ?_).mono (fun z hz => hz) (by omega)
        refine (readLMRegCode_exec (c := c_base + 3) (rIdx := 13) (rDst := 0) (by decide)
          hw hN_pos hnU hU hs3_wf hs3_er (by omega) hidx_lt
          (by simp +decide [s3, s2, s1, BitRAM.Data.set]) hsz).mono
          (fun y ⟨hy_st, hy_wf, hy_0, hy_regs⟩ => ?_) le_rfl
        refine ⟨hy_st, hy_wf,
          hs3_er.congr_regs (fun r hr1 _ =>
            hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)),
          by rw [h3]; exact hy_0,
          fun r hr => ?_⟩
        rw [hy_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s3, s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        exact hs1_regs r hr

/-- Read `Succinct.lmPrev N (lmAtBit U w N x.mem) b j` (`(r13, r14) = (b, j)`) into register `0`. -/
@[expose]
def readLMPrevRegCode : BitRAM.Code .standard 280 :=
  readLMMod4RegCode 1

theorem readLMPrevRegCode_exec {U V w N b j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hj : j < effBucketCap N)
    (hr13 : x.regs 13 = b) (hr14 : x.regs 14 = j) :
    BitRAM.DemonicExecWithin w readLMPrevRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 0 = Succinct.lmPrev N (lmAtBit U w N x.mem) b j ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 62 :=
  readLMMod4RegCode_exec hw hN_pos hnU hU hx her hsz (by decide) hb hj hr13 hr14

/-- Read `Succinct.lmNext N (lmAtBit U w N x.mem) b j` (`(r13, r14) = (b, j)`) into register `0`. -/
@[expose]
def readLMNextRegCode : BitRAM.Code .standard 280 :=
  readLMMod4RegCode 5

theorem readLMNextRegCode_exec {U V w N b j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hb : b < numBuckets N) (hj : j < effBucketCap N)
    (hr13 : x.regs 13 = b) (hr14 : x.regs 14 = j) :
    BitRAM.DemonicExecWithin w readLMNextRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 0 = Succinct.lmNext N (lmAtBit U w N x.mem) b j ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 62 :=
  readLMMod4RegCode_exec hw hN_pos hnU hU hx her hsz (by decide) hb hj hr13 hr14

/-- Write `val` in `r15` to `lmAtBit U w N x.mem (c_base + j % 4, b * numMicroPerBucket N + j / 4)`
(`BitRAM.Code .standard 280`): given `r13 = b` (`b < numBuckets N`), `r14 = j`
(`j < effBucketCap N`), and `r15 = val`, computes `r13 := r13 * r248 + r14 / 4` and
`r18 := r14 % 4`, then branches on `r18 = 0, 1, 2` calling `writeLMRegCode (c_base + r) 13 15`.
Preserves `r ≥ 19`. -/
@[expose]
def writeLMMod4RegCode (c_base : ℕ) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 16 4))
  (.seq (.op (.bin .div 17 14 16))
  (.seq (.op (.bin .mod 18 14 16))
  (.seq (.op (.bin .mul 13 13 248))
  (.seq (.op (.bin .add 13 13 17))
  (.seq (.op (.const 16 0))
        (.branch (.eq 18 16)
          (writeLMRegCode c_base 13 15)
          (.seq (.op (.const 16 1))
                (.branch (.eq 18 16)
                  (writeLMRegCode (c_base + 1) 13 15)
                  (.seq (.op (.const 16 2))
                        (.branch (.eq 18 16)
                          (writeLMRegCode (c_base + 2) 13 15)
                          (writeLMRegCode (c_base + 3) 13 15)))))))))))

theorem writeLMMod4RegCode_exec {U V w N c_base b j val : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hc : c_base + 3 < 9) (hb : b < numBuckets N) (hj : j < effBucketCap N)
    (hval : val < 2 ^ effBucketPosBits N)
    (hr13 : x.regs 13 = b) (hr14 : x.regs 14 = j) (hr15 : x.regs 15 = val) :
    BitRAM.DemonicExecWithin w (writeLMMod4RegCode c_base) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem =
          Function.update (lmAtBit U w N x.mem)
            (c_base + j % 4, b * numMicroPerBucket N + j / 4) val ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offLM U w N ∨ offGM U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N x.toBitMemoryState d ∧
              denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 19 ≤ r.val → y.regs r = x.regs r)) 73 := by
  obtain ⟨_, _, _, h248, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := her.active hN_pos
  have hidx_lt : b * numMicroPerBucket N + j / 4 < totalMicroBuckets N :=
    Succinct.lmSlotIdx_lt hb hj
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have h4_le_bs : 4 ≤ x.bitSize := by
    have h4 : 4 ≤ epochMetaWords U w N := by
      unfold epochMetaWords; rw [ite_eq_right (Nat.ne_of_gt hN_pos)]; omega
    calc 4 ≤ epochMetaWords U w N := h4
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  have hfit_const : ∀ v ≤ 4, Fits w v := fun v hv => Fits.of_le hfit_bs (by omega)
  have hfit_div : Fits w (j / 4) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (by omega)
  have hfit_mod : Fits w (j % 4) := hfit_const (j % 4) (by omega)
  have hfit_bm : Fits w (b * numMicroPerBucket N) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (by omega)
  have hfit_idx : Fits w (b * numMicroPerBucket N + j / 4) :=
    fits_of_le_totalMicroBuckets_of_le_N hw hnU hU (le_of_lt hidx_lt)
  have hout_of_sub : ∀ c < 9, ∀ a,
      (a < offLM U w N ∨ offGM U w N ≤ a) →
      (a < offLMSub U w N c ∨ offLMSub U w N (c + 1) ≤ a) := by
    intro c hc_lt a ha
    rcases ha with ha | ha
    · left; unfold offLMSub; omega
    · right
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hc_lt
      unfold offLMSub
      unfold offGM at ha
      omega
  unfold writeLMMod4RegCode
  refine DemonicExecWithin.step_const (T := 72) (hfit_const 4 le_rfl) ?_
  refine step_dExec_bin (v := j / 4) (T := 71)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr14]) hfit_div ?_
  refine step_dExec_bin (v := j % 4) (T := 70)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr14]) hfit_mod ?_
  refine step_dExec_bin (v := b * numMicroPerBucket N) (T := 69)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr13, h248]) hfit_bm ?_
  refine step_dExec_bin (v := b * numMicroPerBucket N + j / 4) (T := 68)
    (by simp +decide [BitRAM.Data.set, BinOp.eval]) hfit_idx ?_
  refine DemonicExecWithin.step_const (T := 67) (fits_zero w) ?_
  set s1 := (((((x.set 16 4).set 17 (j / 4)).set 18 (j % 4)).set 13
    (b * numMicroPerBucket N)).set 13 (b * numMicroPerBucket N + j / 4)).set 16 0
  have hs1_wf : s1.WellFormed w :=
    wf_set 16 (wf_set 13 (wf_set 13 (wf_set 18 (wf_set 17
      (wf_set 16 hx (hfit_const 4 le_rfl)) hfit_div) hfit_mod) hfit_bm) hfit_idx) (fits_zero w)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_regs : ∀ r : Fin 280, 19 ≤ r.val → s1.regs r = x.regs r := by
    intro r hr
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  by_cases h0 : j % 4 = 0
  · have hcond0 : BitRAM.CondHolds (.eq 18 16) s1 := by
      change s1.regs 18 = s1.regs 16; simp +decide [s1, BitRAM.Data.set, h0]
    refine (dExec_branch_pos (T := 59) hcond0 ?_).mono (fun z hz => hz) (by omega)
    refine (writeLMRegCode_exec (c := c_base) (rIdx := 13) (rVal := 15) (by decide) (by decide)
      hw hN_pos hnU hU hs1_wf hs1_er (by omega) hidx_lt hval
      (by simp +decide [s1, BitRAM.Data.set])
      (by simp +decide [s1, BitRAM.Data.set, hr15]) hsz).mono
      (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_dense, hy_regs⟩ => ?_)
      le_rfl
    refine ⟨hy_sz, hy_wf, hy_er, by rw [h0, Nat.add_zero]; exact hy_lm, hy_gm, hy_td, hy_dt,
      fun a ha => hy_out a (hout_of_sub c_base (by omega) a ha),
      hy_dense, fun r hr => (hy_regs r (by omega)).trans (hs1_regs r hr)⟩
  · have hcond0 : ¬BitRAM.CondHolds (.eq 18 16) s1 := by
      change s1.regs 18 ≠ s1.regs 16; simp +decide [s1, BitRAM.Data.set, h0]
    refine (dExec_branch_neg (T := 65) hcond0 ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 64) (hfit_const 1 (by omega)) ?_
    set s2 := s1.set 16 1
    have hs2_wf : s2.WellFormed w := wf_set 16 hs1_wf (hfit_const 1 (by omega))
    have hs2_er : EpochRegs U V w N s2 :=
      hs1_er.congr_regs (fun r hr1 _ => by
        dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    by_cases h1 : j % 4 = 1
    · have hcond1 : BitRAM.CondHolds (.eq 18 16) s2 := by
        change s2.regs 18 = s2.regs 16; simp +decide [s2, s1, BitRAM.Data.set, h1]
      refine (dExec_branch_pos (T := 59) hcond1 ?_).mono (fun z hz => hz) (by omega)
      refine (writeLMRegCode_exec (c := c_base + 1) (rIdx := 13) (rVal := 15)
        (by decide) (by decide) hw hN_pos hnU hU hs2_wf hs2_er (by omega)
        hidx_lt hval (by simp +decide [s2, s1, BitRAM.Data.set])
        (by simp +decide [s2, s1, BitRAM.Data.set, hr15]) hsz).mono
        (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_dense, hy_regs⟩ => ?_)
        le_rfl
      refine ⟨hy_sz, hy_wf, hy_er, by rw [h1]; exact hy_lm, hy_gm, hy_td, hy_dt,
        fun a ha => hy_out a (hout_of_sub (c_base + 1) (by omega) a ha),
        hy_dense, fun r hr => ?_⟩
      rw [hy_regs r (by omega)]
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hs1_regs r hr
    · have hcond1 : ¬BitRAM.CondHolds (.eq 18 16) s2 := by
        change s2.regs 18 ≠ s2.regs 16; simp +decide [s2, s1, BitRAM.Data.set, h1]
      refine (dExec_branch_neg (T := 62) hcond1 ?_).mono (fun z hz => hz) (by omega)
      refine DemonicExecWithin.step_const (T := 61) (hfit_const 2 (by omega)) ?_
      set s3 := s2.set 16 2
      have hs3_wf : s3.WellFormed w := wf_set 16 hs2_wf (hfit_const 2 (by omega))
      have hs3_er : EpochRegs U V w N s3 :=
        hs2_er.congr_regs (fun r hr1 _ => by
          dsimp only [s3, BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      by_cases h2 : j % 4 = 2
      · have hcond2 : BitRAM.CondHolds (.eq 18 16) s3 := by
          change s3.regs 18 = s3.regs 16; simp +decide [s3, s2, s1, BitRAM.Data.set, h2]
        refine (dExec_branch_pos (T := 59) hcond2 ?_).mono (fun z hz => hz) (by omega)
        refine (writeLMRegCode_exec (c := c_base + 2) (rIdx := 13) (rVal := 15)
          (by decide) (by decide) hw hN_pos hnU hU hs3_wf hs3_er
          (by omega) hidx_lt hval (by simp +decide [s3, s2, s1, BitRAM.Data.set])
          (by simp +decide [s3, s2, s1, BitRAM.Data.set, hr15]) hsz).mono
          (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_dense, hy_regs⟩ => ?_)
          le_rfl
        refine ⟨hy_sz, hy_wf, hy_er, by rw [h2]; exact hy_lm, hy_gm, hy_td, hy_dt,
          fun a ha => hy_out a (hout_of_sub (c_base + 2) (by omega) a ha),
          hy_dense, fun r hr => ?_⟩
        rw [hy_regs r (by omega)]
        dsimp only [s3, s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        exact hs1_regs r hr
      · have hcond2 : ¬BitRAM.CondHolds (.eq 18 16) s3 := by
          change s3.regs 18 ≠ s3.regs 16; simp +decide [s3, s2, s1, BitRAM.Data.set, h2]
        have h3 : j % 4 = 3 := by omega
        refine (dExec_branch_neg (T := 59) hcond2 ?_).mono (fun z hz => hz) (by omega)
        refine (writeLMRegCode_exec (c := c_base + 3) (rIdx := 13) (rVal := 15)
          (by decide) (by decide) hw hN_pos hnU hU hs3_wf hs3_er
          (by omega) hidx_lt hval (by simp +decide [s3, s2, s1, BitRAM.Data.set])
          (by simp +decide [s3, s2, s1, BitRAM.Data.set, hr15]) hsz).mono
          (fun y ⟨hy_sz, hy_wf, hy_er, hy_lm, hy_gm, hy_td, hy_dt, hy_out, hy_dense, hy_regs⟩ => ?_)
          le_rfl
        refine ⟨hy_sz, hy_wf, hy_er, by rw [h3]; exact hy_lm, hy_gm, hy_td, hy_dt,
          fun a ha => hy_out a (hout_of_sub (c_base + 3) (by omega) a ha),
          hy_dense, fun r hr => ?_⟩
        rw [hy_regs r (by omega)]
        dsimp only [s3, s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        exact hs1_regs r hr

/-- Write register `15` into the `lmPrev` slot of `(b, j) = (r13, r14)` in `LocalMeta`. -/
@[expose]
def writeLMPrevRegCode : BitRAM.Code .standard 280 :=
  writeLMMod4RegCode 1

/-- Write register `15` into the `lmNext` slot of `(b, j) = (r13, r14)` in `LocalMeta`. -/
@[expose]
def writeLMNextRegCode : BitRAM.Code .standard 280 :=
  writeLMMod4RegCode 5

/-! ## Section 4: Phase 1 micro-chain search (`microStepRegCode`, `searchMicroChainRegCode`) -/

theorem virtualQuotAt_slotOf_eq_denseQuotAt {U V w N b j : ℕ} {s_bit : BitMemory.State}
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N s_bit.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b) :
    virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) =
      denseQuotAt U V w N s_bit
        (denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)
          (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j)) := by
  have hphys_lt : Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j < N :=
    (Succinct.slotOf_lt_and_injective hslot).1 b hb j hj_bc
  unfold virtualQuotAt
  change (if Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j < N then
    denseQuotAt U V w N s_bit
      (denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)
        (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j))
    else 0) = _
  rw [ite_eq_left hphys_lt]

/-- Single step of Phase 1 micro-chain search (`BitRAM.Code .standard 280`):
given `r271 = q_target`, `r272 = b`, `r31 = ptr` (`0 < ptr`), and `r32 = 0`:
sets `r30 = ptr - 1`, reads `next_ptr = lmNext N lm b r30` into `r31`, resolves
`r17 = slotOf N gm b r30` and `r16 = denseOfPhys N gm td r17`, reads `q_val` at dense index `r16`,
and on match (`q_val = q_target`) sets `r31 = 0`, `r32 = 1`, `r33 = r30`, `r34 = r17`, `r35 = r16`.
Preserves all registers `r ≥ 36`. -/
@[expose]
def microStepRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 1))
  (.seq (.op (.bin .sub 30 31 12))
  (.seq (.op (.copy 13 272))
  (.seq (.op (.copy 14 30))
  (.seq readLMNextRegCode
  (.seq (.op (.copy 31 0))
  (.seq resolveIndexedSlotRegCode
  (.seq (.op (.copy 16 15))
  (.seq (.op (.copy 17 14))
  (.seq (readDenseQRegCode 16 0)
        (.branch (.eq 0 271)
          (.seq (.op (.const 31 0))
          (.seq (.op (.const 32 1))
          (.seq (.op (.copy 33 30))
          (.seq (.op (.copy 34 17))
                (.op (.copy 35 16))))))
          nopRegCode))))))))))

theorem microStepRegCode_exec {U V w N b q_target j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hj_cap : j < effBucketCap N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr271 : x.regs 271 = q_target)
    (hr272 : x.regs 272 = b)
    (hr31 : x.regs 31 = j + 1)
    (hr32 : x.regs 32 = 0) :
    let gm := gmAtBit U w N x.mem
    let lm := lmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    let phys := Succinct.slotOf N gm b j
    let dense := denseOfPhys N gm td phys
    let q_val := virtualQuotAt U V w N x.toBitMemoryState phys
    let next_ptr := Succinct.lmNext N lm b j
    BitRAM.DemonicExecWithin w microStepRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (if q_val = q_target then
          y.regs 31 = 0 ∧ y.regs 32 = 1 ∧ y.regs 33 = j ∧
          y.regs 34 = phys ∧ y.regs 35 = dense
        else
          y.regs 31 = next_ptr ∧ y.regs 32 = 0) ∧
        (∀ r : Fin 280, 36 ≤ r.val → y.regs r = x.regs r)) 348 := by
  intro gm lm td phys dense q_val next_ptr
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hbc_le : Succinct.bCount N (gmAtBit U w N x.mem) b ≤ N := Succinct.bCount_le_n_max hslot b
  have hj_le_N : j ≤ N := le_of_lt (lt_of_lt_of_le hj_bc hbc_le)
  have hfit_j : Fits w j := hfit_N j (by omega)
  unfold microStepRegCode
  refine DemonicExecWithin.step_const (T := 347) (hfit_N 1 (by omega)) ?_
  refine step_dExec_bin (v := j) (T := 346)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr31]) hfit_j ?_
  refine step_dExec_copy (v := b) (T := 345)
    (by simp +decide [BitRAM.Data.set, hr272]) ?_
  refine step_dExec_copy (v := j) (T := 344)
    (by simp +decide [BitRAM.Data.set]) ?_
  set s1 := (((x.set 12 1).set 30 j).set 13 b).set 14 j
  have hs1_wf : s1.WellFormed w :=
    wf_set 14 (wf_set 13 (wf_set 30 (wf_set 12 hx (hfit_N 1 (by omega))) hfit_j)
      (by rw [← hr272]; exact hx.regs_fits 272)) hfit_j
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₂ := 282)
    (readLMNextRegCode_exec hw hN_pos hnU hU hs1_wf hs1_er hsz_meta hb hj_cap
      (by simp +decide [s1, BitRAM.Data.set]) (by simp +decide [s1, BitRAM.Data.set]))
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_0, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  refine step_dExec_copy (v := y1.regs 0) (T := 281) rfl ?_
  set s2 := y1.set 31 (y1.regs 0)
  have hs2_wf : s2.WellFormed w := wf_set 31 hy1_wf (hy1_wf.regs_fits 0)
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_mem : s2.mem = x.mem := hy1_mem
  have hs2_sz : epochMetaBits U w N ≤ s2.bitSize := by
    change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz_meta
  have hs2_272 : s2.regs 272 = b := by
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne (by decide), hy1_regs 272 (by decide)]
    simp +decide [s1, BitRAM.Data.set, hr272]
  have hs2_30 : s2.regs 30 = j := by
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne (by decide), hy1_regs 30 (by decide)]
    simp +decide [s1, BitRAM.Data.set]
  refine .seq (T₂ := 51)
    (resolveIndexedSlotRegCode_exec hw hN_pos hnU hU hs2_wf hs2_er
      (by rw [hs2_mem, hm1]) hs2_sz (by rwa [hs2_mem]) (by rwa [hs2_mem])
      hb (by rwa [hs2_mem]) (Or.inl hj_cap) hs2_272 hs2_30)
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_14, hy2_15, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  rw [hs2_mem] at hy2_14 hy2_15
  refine step_dExec_copy (v := y2.regs 15) (T := 50) rfl ?_
  refine step_dExec_copy (v := y2.regs 14) (T := 49)
    (by simp +decide [BitRAM.Data.set]) ?_
  set s3 := (y2.set 16 (y2.regs 15)).set 17 (y2.regs 14)
  have hs3_wf : s3.WellFormed w :=
    wf_set 17 (wf_set 16 hy2_wf (hy2_wf.regs_fits 15)) (hy2_wf.regs_fits 14)
  have hs3_er : EpochRegs U V w N s3 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hd_lt : dense < Succinct.totalSlots N gm :=
    (denseOfPhys_slotOf_lt_and_injective hslot htd).1 b hb j hj_bc
  have hs3_sz : itemBitOff U V w N (Succinct.totalSlots N gm) ≤ s3.bitSize := by
    change dictBitSize U V w N (Succinct.totalSlots N gm) ≤ y2.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy2_st_x]; exact hsz
  refine .seq (T₂ := 7)
    (readDenseQRegCode_exec (rD := 16) (rDst := 0) (by decide) hw (le_of_lt hU) hs3_wf hs3_er hd_lt
      (by simp +decide [s3, BitRAM.Data.set, hy2_15, dense, phys, gm, td]) hs3_sz
      (by rw [show s3.mem = x.mem from hy2_mem, hm2])
      (by rw [show s3.mem = x.mem from hy2_mem, hm3]))
    (fun y3 ⟨hy3_st, hy3_wf, hy3_0, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_er : EpochRegs U V w N y3 :=
    hs3_er.congr_regs (fun r hr1 _ =>
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy3_0_eq : y3.regs 0 = q_val := by
    have h1 : y3.regs 0 = denseQuotAt U V w N x.toBitMemoryState dense := by
      rw [hy3_0]
      change denseQuotAt U V w N y2.toBitMemoryState dense = _
      rw [hy2_st_x]
    exact h1.trans (virtualQuotAt_slotOf_eq_denseQuotAt
      (s_bit := x.toBitMemoryState) hslot hb hj_bc).symm
  have hy3_16 : y3.regs 16 = dense := by
    rw [hy3_regs 16 (by decide) (by decide)]
    simp +decide [s3, BitRAM.Data.set, hy2_15, dense, phys, gm, td]
  have hy3_17 : y3.regs 17 = phys := by
    rw [hy3_regs 17 (by decide) (by decide)]
    simp +decide [s3, BitRAM.Data.set, hy2_14, phys, gm]
  have hy3_30 : y3.regs 30 = j := by
    rw [hy3_regs 30 (by decide) (by decide)]
    simp +decide [s3, BitRAM.Data.set, hy2_regs 30 (by decide), hs2_30]
  have hy3_31 : y3.regs 31 = next_ptr := by
    rw [hy3_regs 31 (by decide) (by decide)]
    dsimp only [s3, BitRAM.Data.set]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hy2_regs 31 (by decide)]
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_self, hy1_0]
    rfl
  have hy3_32 : y3.regs 32 = 0 := by
    rw [hy3_regs 32 (by decide) (by decide)]
    simp +decide [s3, s2, s1, BitRAM.Data.set, hy2_regs 32 (by decide),
      hy1_regs 32 (by decide), hr32]
  have hy3_271 : y3.regs 271 = q_target := by
    rw [hy3_regs 271 (by decide) (by decide)]
    simp +decide [s3, s2, s1, BitRAM.Data.set, hy2_regs 271 (by decide),
      hy1_regs 271 (by decide), hr271]
  have hy3_hi : ∀ r : Fin 280, 36 ≤ r.val → y3.regs r = x.regs r := by
    intro r hr
    rw [hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    rw [hy2_regs r (by omega)]
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs r (by omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  by_cases hmatch : q_val = q_target
  · have hcond : BitRAM.CondHolds (.eq 0 271) y3 := by
      change y3.regs 0 = y3.regs 271
      rw [hy3_0_eq, hy3_271, hmatch]
    refine (dExec_branch_pos (T := 5) hcond ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 4) (fits_zero w) ?_
    refine DemonicExecWithin.step_const (T := 3) (hfit_N 1 (by omega)) ?_
    refine step_dExec_copy (v := j) (T := 2)
      (by simp +decide [BitRAM.Data.set, hy3_30]) ?_
    refine step_dExec_copy (v := phys) (T := 1)
      (by simp +decide [BitRAM.Data.set, hy3_17]) ?_
    refine DemonicExecWithin.copy ?_
    refine ⟨hy3_st_x,
      wf_set 35 (wf_set 34 (wf_set 33 (wf_set 32 (wf_set 31 hy3_wf (fits_zero w))
        (hfit_N 1 (by omega))) hfit_j) (by rw [← hy3_17]; exact hy3_wf.regs_fits 17))
        (by
          dsimp only [BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by decide)]
          exact hy3_wf.regs_fits 16),
      hy3_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      ?_, fun r hr => ?_⟩
    · rw [ite_eq_left hmatch]
      simp +decide [BitRAM.Data.set, hy3_16]
    · dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hy3_hi r hr
  · have hcond : ¬BitRAM.CondHolds (.eq 0 271) y3 := by
      change y3.regs 0 ≠ y3.regs 271
      rw [hy3_0_eq, hy3_271]; exact hmatch
    refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
    refine ⟨hy3_st_x, hy3_wf, hy3_er, ?_, hy3_hi⟩
    rw [ite_eq_right hmatch]
    exact ⟨hy3_31, hy3_32⟩

open Classical in
theorem microLoop_exec {U V w N b q_target prev_ptr : ℕ} {L : List ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hchain : Succinct.IsDLChainAux N prev_ptr
      (Succinct.lmPrev N (lmAtBit U w N x.mem) b)
      (Succinct.lmNext N (lmAtBit U w N x.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr271 : x.regs 271 = q_target)
    (hr272 : x.regs 272 = b)
    (hr31 : x.regs 31 = (L.head?.map (· + 1)).getD 0)
    (hr32 : x.regs 32 = 0)
    (hr36 : x.regs 36 = 0) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    BitRAM.DemonicExecWithin w (.loop (.lt 36 31) microStepRegCode) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (if ∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
            (Succinct.slotOf N gm b j) = q_target then
          y.regs 32 = 1 ∧
          y.regs 33 ∈ L ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) =
            q_target ∧
          y.regs 34 = Succinct.slotOf N gm b (y.regs 33) ∧
          y.regs 35 = denseOfPhys N gm td (Succinct.slotOf N gm b (y.regs 33))
        else
          y.regs 32 = 0) ∧
        (∀ r : Fin 280, 36 ≤ r.val → y.regs r = x.regs r))
      (2 + 350 * L.length) := by
  intro gm td
  induction L generalizing prev_ptr x with
  | nil =>
    simp only [List.head?_nil, Option.map_none, Option.getD_none] at hr31
    have hcond : ¬BitRAM.CondHolds (.lt 36 31) x := by
      change ¬(x.regs 36 < x.regs 31)
      rw [hr36, hr31]; omega
    refine .loop_exit hcond ?_ (by omega)
    refine ⟨rfl, hx, her, ?_, fun _ _ => rfl⟩
    have hno : ¬∃ j ∈ ([] : List ℕ), virtualQuotAt U V w N x.toBitMemoryState
        (Succinct.slotOf N gm b j) = q_target := by simp
    rw [ite_eq_right hno]
    exact hr32
  | cons j rest ih =>
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at hr31
    rcases hchain with ⟨hj_cap, _, _, hnj, hrest⟩
    have hj_bc : j < Succinct.bCount N gm b := hc_lt j List.mem_cons_self
    have hrest_bc : ∀ k ∈ rest, k < Succinct.bCount N gm b :=
      fun k hk => hc_lt k (List.mem_cons_of_mem j hk)
    have hcond : BitRAM.CondHolds (.lt 36 31) x := by
      change x.regs 36 < x.regs 31
      rw [hr36, hr31]; omega
    refine .loop_iter (T₁ := 348) (T₂ := 2 + 350 * rest.length) hcond
      (microStepRegCode_exec hw hN_pos hnU hU hx her hm1 hm2 hm3 hsz hslot htd hb hj_cap hj_bc
        hr271 hr272 hr31 hr32)
      (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_step, hy1_hi⟩ => ?_)
      (by simp only [List.length_cons]; omega)
    have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy1_36 : y1.regs 36 = 0 := (hy1_hi 36 (by decide)).trans hr36
    have hy1_271 : y1.regs 271 = q_target := (hy1_hi 271 (by decide)).trans hr271
    have hy1_272 : y1.regs 272 = b := (hy1_hi 272 (by decide)).trans hr272
    by_cases hmatch : virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) =
        q_target
    · rw [ite_eq_left hmatch] at hy1_step
      obtain ⟨hy1_31, hy1_32, hy1_33, hy1_34, hy1_35⟩ := hy1_step
      have hcond_exit : ¬BitRAM.CondHolds (.lt 36 31) y1 := by
        change ¬(y1.regs 36 < y1.regs 31)
        rw [hy1_36, hy1_31]; omega
      refine .loop_exit hcond_exit ?_ (by omega)
      have hex : ∃ k ∈ j :: rest, virtualQuotAt U V w N x.toBitMemoryState
          (Succinct.slotOf N gm b k) = q_target := ⟨j, List.mem_cons_self, hmatch⟩
      refine ⟨hy1_st, hy1_wf, hy1_er, ?_, hy1_hi⟩
      rw [ite_eq_left hex, hy1_33]
      exact ⟨hy1_32, List.mem_cons_self, hmatch, hy1_34, hy1_35⟩
    · rw [ite_eq_right hmatch] at hy1_step
      obtain ⟨hy1_31, hy1_32⟩ := hy1_step
      have hy1_sz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
          y1.bitSize := by
        change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
          y1.toBitMemoryState.bitSize
        rw [hy1_mem, congrArg BitMemory.State.bitSize hy1_st]; exact hsz
      refine (ih hy1_wf hy1_er (by rw [hy1_mem, hm1]) (by rw [hy1_mem, hm2])
        (by rw [hy1_mem, hm3]) hy1_sz (by rwa [hy1_mem])
        (by rwa [hy1_mem]) (by rwa [hy1_mem]) (by rwa [hy1_mem])
        hy1_271 hy1_272 (by rw [hy1_31, ← hnj]) hy1_32 hy1_36).mono
        (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_) le_rfl
      have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
      rw [hy1_st, hy1_mem] at hy2_res
      refine ⟨hy2_st_x, hy2_wf, hy2_er, ?_,
        fun r hr => (hy2_hi r hr).trans (hy1_hi r hr)⟩
      by_cases hex_rest : ∃ k ∈ rest, virtualQuotAt U V w N x.toBitMemoryState
          (Succinct.slotOf N gm b k) = q_target
      · rw [ite_eq_left hex_rest] at hy2_res
        obtain ⟨hy2_32, hy2_in, hy2_q, hy2_34, hy2_35⟩ := hy2_res
        have hex : ∃ k ∈ j :: rest, virtualQuotAt U V w N x.toBitMemoryState
            (Succinct.slotOf N gm b k) = q_target := by
          obtain ⟨k, hk, hqk⟩ := hex_rest
          exact ⟨k, List.mem_cons_of_mem j hk, hqk⟩
        rw [ite_eq_left hex]
        exact ⟨hy2_32, List.mem_cons_of_mem j hy2_in, hy2_q, hy2_34, hy2_35⟩
      · rw [ite_eq_right hex_rest] at hy2_res
        have hno : ¬∃ k ∈ j :: rest, virtualQuotAt U V w N x.toBitMemoryState
            (Succinct.slotOf N gm b k) = q_target := by
          rintro ⟨k, hk, hqk⟩
          rcases List.mem_cons.mp hk with rfl | hk_rest
          · exact hmatch hqk
          · exact hex_rest ⟨k, hk_rest, hqk⟩
        rw [ite_eq_right hno]
        exact hy2_res

/-- Phase 1 micro-chain search (`BitRAM.Code .standard 280`):
given `r271 = q_target`, `r272 = b`, `r273 = m`, reads `head = lmHead N lm b m` and traverses the
micro-bucket chain, setting `r32 = 1`, `r33 = j_found`, `r34 = phys_found`, `r35 = dense_found` on
hit or `r32 = 0` on miss, and leaving `r36 = 0`. Preserves all registers `r ≥ 37`. -/
@[expose]
def searchMicroChainRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 13 272))
  (.seq (.op (.copy 14 273))
  (.seq readLMHeadRegCode
  (.seq (.op (.copy 31 0))
  (.seq (.op (.const 32 0))
  (.seq (.op (.const 33 0))
  (.seq (.op (.const 34 0))
  (.seq (.op (.const 35 0))
  (.seq (.op (.const 36 0))
        (.loop (.lt 36 31) microStepRegCode)))))))))

open Classical in
theorem searchMicroChainRegCode_exec {U V w N b m q_target : ℕ} {L : List ℕ}
    {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hchain : Succinct.IsDLChain N (Succinct.lmHead N (lmAtBit U w N x.mem) b m)
      (Succinct.lmPrev N (lmAtBit U w N x.mem) b)
      (Succinct.lmNext N (lmAtBit U w N x.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr271 : x.regs 271 = q_target)
    (hr272 : x.regs 272 = b)
    (hr273 : x.regs 273 = m) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    BitRAM.DemonicExecWithin w searchMicroChainRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 36 = 0 ∧
        (if ∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
            (Succinct.slotOf N gm b j) = q_target then
          y.regs 32 = 1 ∧
          y.regs 33 ∈ L ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) =
            q_target ∧
          y.regs 34 = Succinct.slotOf N gm b (y.regs 33) ∧
          y.regs 35 = denseOfPhys N gm td (Succinct.slotOf N gm b (y.regs 33))
        else
          y.regs 32 = 0) ∧
        (∀ r : Fin 280, 37 ≤ r.val → y.regs r = x.regs r))
      (60 + 350 * L.length) := by
  intro gm td
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  unfold searchMicroChainRegCode
  refine (step_dExec_copy (v := b) (T := 59 + 350 * L.length) hr272 ?_).mono
    (fun z hz => hz) (by omega)
  refine (step_dExec_copy (v := m) (T := 58 + 350 * L.length)
    (by simp +decide [BitRAM.Data.set, hr273]) ?_).mono (fun z hz => hz) (by omega)
  set s1 := (x.set 13 b).set 14 m
  have hs1_wf : s1.WellFormed w :=
    wf_set 14 (wf_set 13 hx (by rw [← hr272]; exact hx.regs_fits 272))
      (by rw [← hr273]; exact hx.regs_fits 273)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₂ := 8 + 350 * L.length)
    (readLMHeadRegCode_exec hw hN_pos hnU hU hs1_wf hs1_er hsz_meta hb hm
      (by simp +decide [s1, BitRAM.Data.set]) (by simp +decide [s1, BitRAM.Data.set]))
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_0, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  refine (step_dExec_copy (v := y1.regs 0) (T := 7 + 350 * L.length) rfl ?_).mono
    (fun z hz => hz) (by omega)
  refine (DemonicExecWithin.step_const (T := 6 + 350 * L.length) (fits_zero w) ?_).mono
    (fun z hz => hz) (by omega)
  refine (DemonicExecWithin.step_const (T := 5 + 350 * L.length) (fits_zero w) ?_).mono
    (fun z hz => hz) (by omega)
  refine (DemonicExecWithin.step_const (T := 4 + 350 * L.length) (fits_zero w) ?_).mono
    (fun z hz => hz) (by omega)
  refine (DemonicExecWithin.step_const (T := 3 + 350 * L.length) (fits_zero w) ?_).mono
    (fun z hz => hz) (by omega)
  refine (DemonicExecWithin.step_const (T := 2 + 350 * L.length) (fits_zero w) ?_).mono
    (fun z hz => hz) (by omega)
  set s2 := (((((y1.set 31 (y1.regs 0)).set 32 0).set 33 0).set 34 0).set 35 0).set 36 0
  have hs2_wf : s2.WellFormed w :=
    wf_set 36 (wf_set 35 (wf_set 34 (wf_set 33 (wf_set 32
      (wf_set 31 hy1_wf (hy1_wf.regs_fits 0)) (fits_zero w)) (fits_zero w))
      (fits_zero w)) (fits_zero w)) (fits_zero w)
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_mem : s2.mem = x.mem := hy1_mem
  have hs2_sz :
      dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N s2.mem)) ≤ s2.bitSize := by
    change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N s2.mem)) ≤
      y1.toBitMemoryState.bitSize
    rw [hs2_mem, congrArg BitMemory.State.bitSize hy1_st]; exact hsz
  have hs2_271 : s2.regs 271 = q_target := by
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy1_regs 271 (by decide)]; simp +decide [s1, BitRAM.Data.set, hr271]
  have hs2_272 : s2.regs 272 = b := by
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy1_regs 272 (by decide)]; simp +decide [s1, BitRAM.Data.set, hr272]
  have hs2_31 : s2.regs 31 = (L.head?.map (· + 1)).getD 0 := by
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [Function.update_self, hy1_0, ← hchain.1]
    rfl
  refine (microLoop_exec hw hN_pos hnU hU hs2_wf hs2_er
    (by rw [hs2_mem, hm1]) (by rw [hs2_mem, hm2]) (by rw [hs2_mem, hm3]) hs2_sz
    (by rwa [hs2_mem]) (by rwa [hs2_mem]) hb (by rw [hs2_mem]; exact hchain.2)
    (by rwa [hs2_mem]) hs2_271 hs2_272 hs2_31
    (by simp +decide [s2, BitRAM.Data.set])
    (by simp +decide [s2, BitRAM.Data.set])).mono
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_) le_rfl
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  change (if _ then _ else _) at hy2_res
  rw [show s2.toBitMemoryState = x.toBitMemoryState from hy1_st, hs2_mem] at hy2_res
  refine ⟨hy2_st_x, hy2_wf, hy2_er,
    (hy2_hi 36 (by decide)).trans (by simp +decide [s2, BitRAM.Data.set]), hy2_res,
    fun r hr => ?_⟩
  rw [hy2_hi r (by omega)]
  dsimp only [s2, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  rw [hy1_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-! ## Section 4: Overflow search initialization (`initOvfSearchRegCode`) -/

/-- Initialize overflow search registers (`BitRAM.Code .standard 280`) when `0 < bucketBits N`:
sets `r42 = gmSlabMetaBase N`, `r43 = gmSlabDirBase N`, `r44 = dirSlabsPerBucket N`,
`r37 = q_b`, `r38 = r_b`, `r39 = q_b * slabSize N`, `r40 = bCount N gm b`,
`r30 = min (bCount N gm b) (effBucketCap N)`, and `r41 = p_init`.
Preserves `r32..r36` and `r ≥ 45`. -/
@[expose]
def initOvfSearchRegCode : BitRAM.Code .standard 280 :=
  .seq computeGMBasesRegCode
  (.seq (.op (.copy 42 25))
  (.seq (.op (.copy 43 22))
  (.seq (.op (.copy 44 20))
  (.seq (.op (.const 13 3))
  (.seq (.op (.bin .mul 12 13 272))
  (.seq (.op (.const 13 4))
  (.seq (.op (.bin .add 12 13 12))
  (.seq (readGMRegCode 12 0)
  (.seq (.op (.copy 37 0))
  (.seq (.op (.const 13 3))
  (.seq (.op (.bin .mul 12 13 272))
  (.seq (.op (.const 13 5))
  (.seq (.op (.bin .add 12 13 12))
  (.seq (readGMRegCode 12 0)
  (.seq (.op (.copy 38 0))
  (.seq (.op (.bin .mul 39 37 250))
  (.seq (.op (.bin .add 40 39 38))
  (.seq (.op (.copy 30 251))
        (.branch (.lt 251 40)
          (.branch (.lt 251 39)
            (.seq (.op (.const 13 1))
            (.seq (.op (.bin .sub 12 44 13))
            (.seq (.op (.bin .mul 13 272 44))
            (.seq (.op (.bin .add 12 13 12))
            (.seq (.op (.bin .add 12 43 12))
            (.seq (readGMRegCode 12 0)
            (.seq (.op (.copy 13 0))
            (.seq (.op (.const 14 4))
            (.seq (.op (.bin .mul 12 14 13))
            (.seq (.op (.const 14 3))
            (.seq (.op (.bin .add 12 12 14))
            (.seq (.op (.bin .add 12 42 12))
            (.seq (readGMRegCode 12 0)
                  (.op (.copy 41 0)))))))))))))))
            (.op (.const 41 0)))
          (.seq (.op (.const 41 0))
                (.op (.copy 30 40))))))))))))))))))))))

theorem initOvfSearchRegCode_exec {U V w N b : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hr272 : x.regs 272 = b) :
    let gm := gmAtBit U w N x.mem
    let qK := gm (Succinct.gmQIdx b) * slabSize N
    let c := Succinct.bCount N gm b
    BitRAM.DemonicExecWithin w initOvfSearchRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 30 + (c - effBucketCap N) = c ∧
        y.regs 39 = qK ∧
        y.regs 40 = c ∧
        y.regs 42 = Succinct.gmSlabMetaBase N ∧
        (effBucketCap N < c → y.regs 30 = effBucketCap N) ∧
        (y.regs 30 < c → y.regs 30 < qK →
          y.regs 41 = Succinct.slabPtrOf N gm b (y.regs 30 / slabSize N)) ∧
        (∀ r : Fin 280, (32 ≤ r.val ∧ r.val ≤ 36) ∨ 45 ≤ r.val → y.regs r = x.regs r))
      225 := by
  intro gm qK c
  obtain ⟨_, _, _, _, _, h250, h251, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    her.active hN_pos
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hK : 0 < slabSize N := slabSize_pos N
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hq_lt : 4 + 3 * b < globalMetaLen N := Succinct.gmQIdx_lt hb_pos hb
  have hr_lt : 5 + 3 * b < globalMetaLen N := by
    rw [show 5 + 3 * b = 4 + 3 * b + 1 by omega]
    exact Succinct.gmRIdx_lt hb_pos hb
  have hbc_le : c ≤ N := Succinct.bCount_le_n_max hslot b
  have hqK_le_c : qK ≤ c := by
    dsimp only [qK, c]; unfold Succinct.bCount Succinct.gmQIdx Succinct.gmRIdx
    simp [hb0, hb]
  have hbc_eq : gm (Succinct.gmQIdx b) * slabSize N + gm (Succinct.gmRIdx b) = c := by
    dsimp only [c]; unfold Succinct.bCount Succinct.gmQIdx Succinct.gmRIdx; simp [hb0, hb]
  unfold initOvfSearchRegCode
  refine .seq (T₂ := 214)
    (computeGMBasesRegCode_exec hw hN_pos hb_pos hx her hsz)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_20, _, hy1_22, _, _, hy1_25, hy1_regs⟩ => ?_) le_rfl
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
    change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
  have hy1_272 : y1.regs 272 = b := (hy1_regs 272 (Or.inr (by decide))).trans hr272
  refine step_dExec_copy (v := Succinct.gmSlabMetaBase N) (T := 213) hy1_25 ?_
  refine step_dExec_copy (v := Succinct.gmSlabDirBase N) (T := 212)
    (by simp +decide [BitRAM.Data.set, hy1_22]) ?_
  refine step_dExec_copy (v := dirSlabsPerBucket N) (T := 211)
    (by simp +decide [BitRAM.Data.set, hy1_20]) ?_
  refine DemonicExecWithin.step_const (T := 210) (hfit_gm 3 (by omega)) ?_
  refine step_dExec_bin (v := 3 * b) (T := 209)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy1_272]) (hfit_gm (3 * b) (by omega)) ?_
  refine DemonicExecWithin.step_const (T := 208) (hfit_gm 4 (by omega)) ?_
  refine step_dExec_bin (v := 4 + 3 * b) (T := 207)
    (by simp +decide [BitRAM.Data.set, BinOp.eval]) (hfit_gm (4 + 3 * b) (by omega)) ?_
  set s2 := ((((((y1.set 42 (Succinct.gmSlabMetaBase N)).set 43 (Succinct.gmSlabDirBase N)).set 44
    (dirSlabsPerBucket N)).set 13 3).set 12 (3 * b)).set 13 4).set 12 (4 + 3 * b)
  have hs2_wf : s2.WellFormed w :=
    wf_set 12 (wf_set 13 (wf_set 12 (wf_set 13 (wf_set 44
      (wf_set 43 (wf_set 42 hy1_wf (by rw [← hy1_25]; exact hy1_wf.regs_fits 25))
        (by rw [← hy1_22]; exact hy1_wf.regs_fits 22))
        (by rw [← hy1_20]; exact hy1_wf.regs_fits 20))
      (hfit_gm 3 (by omega))) (hfit_gm (3 * b) (by omega))) (hfit_gm 4 (by omega)))
      (hfit_gm (4 + 3 * b) (by omega))
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₂ := 162)
    (readGMRegCode_exec (idx := 4 + 3 * b) (rIdx := 12) (rDst := 0) (by decide) hw hN_pos hnU hU
      hs2_wf hs2_er hq_lt (by simp +decide [s2, BitRAM.Data.set]) hy1_sz)
    (fun y2 ⟨hy2_st, hy2_wf, hy2_0, hy2_regs⟩ => ?_) le_rfl
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  have hy2_er : EpochRegs U V w N y2 :=
    hs2_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy2_sz : epochMetaBits U w N ≤ y2.bitSize := by
    change epochMetaBits U w N ≤ y2.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy2_st_x]; exact hsz
  have hy2_272 : y2.regs 272 = b := by
    rw [hy2_regs 272 (by decide) (by decide)]; simp +decide [s2, BitRAM.Data.set, hy1_272]
  have hy2_0_eq : y2.regs 0 = gm (Succinct.gmQIdx b) := by
    rw [hy2_0]; change gmAtBit U w N y1.mem (4 + 3 * b) = _; rw [hy1_mem]; rfl
  refine step_dExec_copy (v := gm (Succinct.gmQIdx b)) (T := 161) hy2_0_eq ?_
  refine DemonicExecWithin.step_const (T := 160) (hfit_gm 3 (by omega)) ?_
  refine step_dExec_bin (v := 3 * b) (T := 159)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy2_272]) (hfit_gm (3 * b) (by omega)) ?_
  refine DemonicExecWithin.step_const (T := 158) (hfit_gm 5 (by omega)) ?_
  refine step_dExec_bin (v := 5 + 3 * b) (T := 157)
    (by simp +decide [BitRAM.Data.set, BinOp.eval]) (hfit_gm (5 + 3 * b) (by omega)) ?_
  set s3 := ((((y2.set 37 (gm (Succinct.gmQIdx b))).set 13 3).set 12 (3 * b)).set 13 5).set 12
    (5 + 3 * b)
  have hs3_wf : s3.WellFormed w :=
    wf_set 12 (wf_set 13 (wf_set 12 (wf_set 13
      (wf_set 37 hy2_wf (by rw [← hy2_0_eq]; exact hy2_wf.regs_fits 0)) (hfit_gm 3 (by omega)))
      (hfit_gm (3 * b) (by omega))) (hfit_gm 5 (by omega))) (hfit_gm (5 + 3 * b) (by omega))
  have hs3_er : EpochRegs U V w N s3 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₂ := 112)
    (readGMRegCode_exec (idx := 5 + 3 * b) (rIdx := 12) (rDst := 0) (by decide) hw hN_pos hnU hU
      hs3_wf hs3_er hr_lt (by simp +decide [s3, BitRAM.Data.set]) hy2_sz)
    (fun y3 ⟨hy3_st, hy3_wf, hy3_0, hy3_regs⟩ => ?_) le_rfl
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_er : EpochRegs U V w N y3 :=
    hs3_er.congr_regs (fun r hr1 _ =>
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy3_sz : epochMetaBits U w N ≤ y3.bitSize := by
    change epochMetaBits U w N ≤ y3.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy3_st_x]; exact hsz
  have hy3_0_eq : y3.regs 0 = gm (Succinct.gmRIdx b) := by
    rw [hy3_0]; change gmAtBit U w N y2.mem (5 + 3 * b) = _
    rw [hy2_mem, show 5 + 3 * b = Succinct.gmRIdx b by unfold Succinct.gmRIdx; omega]
  have hy3_37 : y3.regs 37 = gm (Succinct.gmQIdx b) := by
    rw [hy3_regs 37 (by decide) (by decide)]; simp +decide [s3, BitRAM.Data.set]
  have ⟨_, _, _, _, _, hy3_250, hy3_251, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    hy3_er.active hN_pos
  have hfit_qK : Fits w qK := hfit_N qK (by omega)
  have hfit_c : Fits w c := hfit_N c (by omega)
  refine step_dExec_copy (v := gm (Succinct.gmRIdx b)) (T := 111) hy3_0_eq ?_
  refine step_dExec_bin (v := qK) (T := 110)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy3_37, hy3_250]; rfl) hfit_qK ?_
  refine step_dExec_bin (v := c) (T := 109)
    (by
      simp +decide only [BinOp.eval, Fin.isValue, BitRAM.Data.set_regs, Function.update_self,
        ne_eq, Function.update_of_ne]
      exact hbc_eq) hfit_c ?_
  refine step_dExec_copy (v := effBucketCap N) (T := 108)
    (by simp +decide [BitRAM.Data.set, hy3_251]) ?_
  set s4 := (((y3.set 38 (gm (Succinct.gmRIdx b))).set 39 qK).set 40 c).set 30 (effBucketCap N)
  have hs4_wf : s4.WellFormed w :=
    wf_set 30 (wf_set 40 (wf_set 39
      (wf_set 38 hy3_wf (by rw [← hy3_0_eq]; exact hy3_wf.regs_fits 0)) hfit_qK) hfit_c)
      (by rw [← hy3_251]; exact hy3_wf.regs_fits 251)
  have hs4_er : EpochRegs U V w N s4 :=
    hy3_er.congr_regs (fun r hr1 _ => by
      dsimp only [s4, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs4_42 : s4.regs 42 = Succinct.gmSlabMetaBase N := by
    dsimp only [s4, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy3_regs 42 (by decide) (by decide)]
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy2_regs 42 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set]
  have hs4_43 : s4.regs 43 = Succinct.gmSlabDirBase N := by
    dsimp only [s4, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy3_regs 43 (by decide) (by decide)]
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy2_regs 43 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set]
  have hs4_44 : s4.regs 44 = dirSlabsPerBucket N := by
    dsimp only [s4, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy3_regs 44 (by decide) (by decide)]
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy2_regs 44 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set]
  have hs4_272 : s4.regs 272 = b := by
    dsimp only [s4, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hy3_regs 272 (by decide) (by decide)]
    simp +decide [s3, BitRAM.Data.set, hy2_272]
  have hs4_251 : s4.regs 251 = effBucketCap N := by
    simp +decide [s4, BitRAM.Data.set, hy3_251]
  have hs4_39 : s4.regs 39 = qK := by simp +decide [s4, BitRAM.Data.set]
  have hs4_40 : s4.regs 40 = c := by simp +decide [s4, BitRAM.Data.set]
  have hs4_30 : s4.regs 30 = effBucketCap N := by simp +decide [s4, BitRAM.Data.set]
  have hs4_hi :
      ∀ r : Fin 280, (32 ≤ r.val ∧ r.val ≤ 36) ∨ 45 ≤ r.val → s4.regs r = x.regs r := by
    intro r hr
    dsimp only [s4, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    rw [hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    rw [hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hy1_regs r (Or.inr (by omega))
  by_cases hcap_c : effBucketCap N < c
  · have hcond1 : BitRAM.CondHolds (.lt 251 40) s4 := by
      change s4.regs 251 < s4.regs 40; rw [hs4_251, hs4_40]; exact hcap_c
    refine (dExec_branch_pos (T := 107) hcond1 ?_).mono (fun z hz => hz) (by omega)
    by_cases hcap_q : effBucketCap N < qK
    · have hcond2 : BitRAM.CondHolds (.lt 251 39) s4 := by
        change s4.regs 251 < s4.regs 39; rw [hs4_251, hs4_39]; exact hcap_q
      refine (dExec_branch_pos (T := 102) hcond2 ?_).mono (fun z hz => hz) (by omega)
      have hdir_pos := Succinct.dirSlabsPerBucket_pos_of_pos hb_pos
      have hcap_dir := Succinct.effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
      have hdir_lt_q : dirSlabsPerBucket N < gm (Succinct.gmQIdx b) :=
        (Nat.mul_lt_mul_right hK).mp (by rwa [← hcap_dir])
      have hslab := hslot.multi_slab hb_pos
      have hs_last_dir : dirSlabsPerBucket N - 1 < dirSlabsPerBucket N := by omega
      have hs_last_q : dirSlabsPerBucket N - 1 < gm (Succinct.gmQIdx b) := by omega
      have hdir_idx_lt : Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N +
          (dirSlabsPerBucket N - 1) < globalMetaLen N :=
        Succinct.gmSlabDirIdx_lt hb_pos hb hs_last_dir
      have hdir_eq : Succinct.gmSlabDirBase N + (b * dirSlabsPerBucket N +
          (dirSlabsPerBucket N - 1)) =
          Succinct.gmSlabDirIdx N b (dirSlabsPerBucket N - 1) := by
        unfold Succinct.gmSlabDirIdx; omega
      refine DemonicExecWithin.step_const (T := 101) (hfit_gm 1 (by omega)) ?_
      refine step_dExec_bin (v := dirSlabsPerBucket N - 1) (T := 100)
        (by simp +decide [BitRAM.Data.set, BinOp.eval, hs4_44])
        (hfit_gm (dirSlabsPerBucket N - 1) (by omega)) ?_
      refine step_dExec_bin (v := b * dirSlabsPerBucket N) (T := 99)
        (by simp +decide [BitRAM.Data.set, BinOp.eval, hs4_272, hs4_44])
        (hfit_gm (b * dirSlabsPerBucket N) (by omega)) ?_
      refine step_dExec_bin (v := b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) (T := 98)
        (by simp +decide [BitRAM.Data.set, BinOp.eval])
        (hfit_gm (b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) (by omega)) ?_
      refine step_dExec_bin
        (v := Succinct.gmSlabDirBase N + (b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)))
        (T := 97)
        (by simp +decide [BitRAM.Data.set, BinOp.eval, hs4_43])
        (hfit_gm _ (by omega)) ?_
      set s5 := ((((s4.set 13 1).set 12 (dirSlabsPerBucket N - 1)).set 13
        (b * dirSlabsPerBucket N)).set 12
        (b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1))).set 12
        (Succinct.gmSlabDirBase N + (b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)))
      have hs5_wf : s5.WellFormed w :=
        wf_set 12 (wf_set 12 (wf_set 13 (wf_set 12 (wf_set 13 hs4_wf (hfit_gm 1 (by omega)))
          (hfit_gm _ (by omega))) (hfit_gm _ (by omega))) (hfit_gm _ (by omega)))
          (hfit_gm _ (by omega))
      have hs5_er : EpochRegs U V w N s5 :=
        hs4_er.congr_regs (fun r hr1 _ => by
          dsimp only [s5, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      refine .seq (T₂ := 52)
        (readGMRegCode_exec
          (idx := Succinct.gmSlabDirBase N + (b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)))
          (rIdx := 12) (rDst := 0) (by decide) hw hN_pos hnU hU
          hs5_wf hs5_er (by rw [hdir_eq]; exact hdir_idx_lt)
          (by simp +decide [s5, BitRAM.Data.set]) hy3_sz)
        (fun y4 ⟨hy4_st, hy4_wf, hy4_0, hy4_regs⟩ => ?_) le_rfl
      have hy4_st_x : y4.toBitMemoryState = x.toBitMemoryState := hy4_st.trans hy3_st_x
      have hy4_mem : y4.mem = x.mem := congrArg BitMemory.State.mem hy4_st_x
      have hy4_er : EpochRegs U V w N y4 :=
        hs5_er.congr_regs (fun r hr1 _ =>
          hy4_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
      have hy4_sz : epochMetaBits U w N ≤ y4.bitSize := by
        change epochMetaBits U w N ≤ y4.toBitMemoryState.bitSize
        rw [congrArg BitMemory.State.bitSize hy4_st_x]; exact hsz
      set p_prev := Succinct.slabPtrOf N gm b (dirSlabsPerBucket N - 1)
      have hy4_0_eq : y4.regs 0 = p_prev := by
        rw [hy4_0, hdir_eq]
        change gmAtBit U w N y3.mem (Succinct.gmSlabDirIdx N b (dirSlabsPerBucket N - 1)) = _
        rw [hy3_mem]
        exact hslab.dir_eq b hb (dirSlabsPerBucket N - 1) hs_last_q hs_last_dir
      have hp_prev_lt : p_prev < maxFullSlabs N :=
        lt_of_lt_of_le (hslab.ptr_lt b hb _ hs_last_q) hslab.nslabs_le
      have habv_lt : Succinct.gmSlabMetaBase N + 4 * p_prev + 3 < globalMetaLen N :=
        Succinct.gmSlabAboveIdx_lt hb_pos hp_prev_lt
      have habv_eq : Succinct.gmSlabMetaBase N + (4 * p_prev + 3) =
          Succinct.gmSlabAboveIdx N p_prev := by
        unfold Succinct.gmSlabAboveIdx; omega
      have hy4_42 : y4.regs 42 = Succinct.gmSlabMetaBase N := by
        rw [hy4_regs 42 (by decide) (by decide)]; simp +decide [s5, BitRAM.Data.set, hs4_42]
      refine step_dExec_copy (v := p_prev) (T := 51) hy4_0_eq ?_
      refine DemonicExecWithin.step_const (T := 50) (hfit_gm 4 (by omega)) ?_
      refine step_dExec_bin (v := 4 * p_prev) (T := 49)
        (by simp +decide [BitRAM.Data.set, BinOp.eval])
        (hfit_gm (4 * p_prev) (by omega)) ?_
      refine DemonicExecWithin.step_const (T := 48) (hfit_gm 3 (by omega)) ?_
      refine step_dExec_bin (v := 4 * p_prev + 3) (T := 47)
        (by simp +decide [BitRAM.Data.set, BinOp.eval])
        (hfit_gm (4 * p_prev + 3) (by omega)) ?_
      refine step_dExec_bin (v := Succinct.gmSlabMetaBase N + (4 * p_prev + 3)) (T := 46)
        (by simp +decide [BitRAM.Data.set, BinOp.eval, hy4_42])
        (hfit_gm _ (by omega)) ?_
      set s6 := (((((y4.set 13 p_prev).set 14 4).set 12 (4 * p_prev)).set 14 3).set 12
        (4 * p_prev + 3)).set 12 (Succinct.gmSlabMetaBase N + (4 * p_prev + 3))
      have hs6_wf : s6.WellFormed w :=
        wf_set 12 (wf_set 12 (wf_set 14 (wf_set 12 (wf_set 14
          (wf_set 13 hy4_wf (by rw [← hy4_0_eq]; exact hy4_wf.regs_fits 0))
          (hfit_gm 4 (by omega))) (hfit_gm _ (by omega))) (hfit_gm 3 (by omega)))
          (hfit_gm _ (by omega))) (hfit_gm _ (by omega))
      have hs6_er : EpochRegs U V w N s6 :=
        hy4_er.congr_regs (fun r hr1 _ => by
          dsimp only [s6, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      refine .seq (T₂ := 1)
        (readGMRegCode_exec (idx := Succinct.gmSlabMetaBase N + (4 * p_prev + 3))
          (rIdx := 12) (rDst := 0) (by decide) hw hN_pos hnU hU
          hs6_wf hs6_er (by rw [habv_eq]; exact habv_lt)
          (by simp +decide [s6, BitRAM.Data.set]) hy4_sz)
        (fun y5 ⟨hy5_st, hy5_wf, hy5_0, hy5_regs⟩ => ?_) le_rfl
      have hy5_st_x : y5.toBitMemoryState = x.toBitMemoryState := hy5_st.trans hy4_st_x
      have hy5_er : EpochRegs U V w N y5 :=
        hs6_er.congr_regs (fun r hr1 _ =>
          hy5_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
      have hy5_0_eq : y5.regs 0 = Succinct.slabPtrOf N gm b (effBucketCap N / slabSize N) := by
        rw [hy5_0, habv_eq]
        change gmAtBit U w N y4.mem (Succinct.gmSlabAboveIdx N p_prev) = _
        rw [hy4_mem, hslab.above_eq b hb (dirSlabsPerBucket N - 1) hs_last_q
          (by dsimp only [gm] at hdir_lt_q; omega),
          show dirSlabsPerBucket N - 1 + 1 = dirSlabsPerBucket N by omega,
          hcap_dir, Nat.mul_div_cancel _ hK]
      refine DemonicExecWithin.copy ?_
      have hy5_30 : (y5.set 41 (y5.regs 0)).regs 30 = effBucketCap N := by
        dsimp only [BitRAM.Data.set]
        rw [Function.update_of_ne (by decide), hy5_regs 30 (by decide) (by decide)]
        simp +decide [s6, BitRAM.Data.set, hy4_regs 30 (by decide) (by decide), s5, hs4_30]
      refine ⟨hy5_st_x, wf_set 41 hy5_wf (hy5_wf.regs_fits 0),
        hy5_er.congr_regs (fun r hr1 _ => by
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
        by rw [hy5_30]; omega,
        by
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne (by decide), hy5_regs 39 (by decide) (by decide)]
          simp +decide [s6, BitRAM.Data.set, hy4_regs 39 (by decide) (by decide), s5, hs4_39],
        by
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne (by decide), hy5_regs 40 (by decide) (by decide)]
          simp +decide [s6, BitRAM.Data.set, hy4_regs 40 (by decide) (by decide), s5, hs4_40],
        by
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne (by decide), hy5_regs 42 (by decide) (by decide)]
          simp +decide [s6, BitRAM.Data.set, hy4_42],
        fun _ => hy5_30,
        fun _ _ => by rw [hy5_30]; simp +decide [BitRAM.Data.set, hy5_0_eq],
        fun r hr => ?_⟩
      dsimp only [BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
        hy5_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s6, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      rw [hy4_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s5, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hs4_hi r hr
    · have hcond2 : ¬BitRAM.CondHolds (.lt 251 39) s4 := by
        change ¬(s4.regs 251 < s4.regs 39); rw [hs4_251, hs4_39]; exact hcap_q
      refine (dExec_branch_neg (T := 1) hcond2 (DemonicExecWithin.const (fits_zero w) ?_)).mono
        (fun z hz => hz) (by omega)
      refine ⟨hy3_st_x, wf_set 41 hs4_wf (fits_zero w),
        hs4_er.congr_regs (fun r hr1 _ => by
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
        by simp +decide [BitRAM.Data.set, hs4_30]; omega,
        by simp +decide [BitRAM.Data.set, hs4_39],
        by simp +decide [BitRAM.Data.set, hs4_40],
        by simp +decide [BitRAM.Data.set, hs4_42],
        fun _ => by simp +decide [BitRAM.Data.set, hs4_30],
        fun _ hlt => by simp +decide [BitRAM.Data.set, hs4_30] at hlt; omega,
        fun r hr => ?_⟩
      dsimp only [BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hs4_hi r hr
  · have hcond1 : ¬BitRAM.CondHolds (.lt 251 40) s4 := by
      change ¬(s4.regs 251 < s4.regs 40); rw [hs4_251, hs4_40]; exact hcap_c
    refine (dExec_branch_neg (T := 2) hcond1 ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 1) (fits_zero w) ?_
    refine DemonicExecWithin.copy ?_
    refine ⟨hy3_st_x, wf_set 30 (wf_set 41 hs4_wf (fits_zero w)) (hs4_wf.regs_fits 40),
      hs4_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      by simp +decide [BitRAM.Data.set, hs4_40]; omega,
      by simp +decide [BitRAM.Data.set, hs4_39],
      by simp +decide [BitRAM.Data.set, hs4_40],
      by simp +decide [BitRAM.Data.set, hs4_42],
      fun h => (hcap_c h).elim,
      fun hlt _ => by simp +decide [BitRAM.Data.set, hs4_40] at hlt,
      fun r hr => ?_⟩
    dsimp only [BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hs4_hi r hr

end Cslib.DataStructure.Dictionary.BitResizable
