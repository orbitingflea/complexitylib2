/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.MicroSearch

/-!
# Uniform Bucket Search, Dictionary Query, and Hit Update on `BitRAM`

This module builds on `MicroSearch.lean` to provide parameter-free `BitRAM.Code .standard 280`
programs for:
1. Phase 2 overflow slab/tail search (`initOvfSearchRegCode`, `resolveOvfStepRegCode`,
   `ovfStepRegCode`, `searchOverflowRegCode`).
2. Two-phase bucket search (`searchBucketRegCode`), full dictionary query (`queryRegCode`),
   and in-place hit update (`insertHitRegCode`), with worst-case (`probeExcess`) and
   expected `O(1)` instruction bounds.
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
open scoped BigOperators ENNReal

/-! ## Section 1: Phase 2 overflow search (`resolveOvfStepRegCode`, `ovfStepRegCode`) -/

/-- Single-step overflow slot and dense-index resolver (`BitRAM.Code .standard 280`):
given `r272 = b`, `r30 = j < bCount N gm b`, `r39 = q_b * slabSize N`, `r41 = p_cur`,
`r42 = gmSlabMetaBase N`, and `r36 = 0`:
sets `r14 = slotOf N gm b j`, `r15 = denseOfPhys N gm td r14`, and advances `r41` to
`slabPtrOf N gm b ((j + 1) / slabSize N)` when `j + 1 < q_b * slabSize N`.
Preserves all registers `r ≥ 30` with `r ≠ 41`. -/
@[expose]
def resolveOvfStepRegCode : BitRAM.Code .standard 280 :=
  .branch (.lt 30 39)
    (.seq (.op (.const 13 1))
    (.seq (.op (.bin .sub 16 250 13))
    (.seq (.op (.bin .mod 17 30 250))
    (.seq (.op (.bin .sub 16 16 17))
    (.seq (.op (.bin .mul 14 41 250))
    (.seq (.op (.bin .add 14 14 16))
    (.seq (.op (.bin .add 17 30 13))
    (.seq (.branch (.eq 16 36)
            (.branch (.lt 17 39)
              (.seq (.op (.const 13 4))
              (.seq (.op (.bin .mul 12 13 41))
              (.seq (.op (.const 13 3))
              (.seq (.op (.bin .add 12 12 13))
              (.seq (.op (.bin .add 12 42 12))
              (.seq (readGMRegCode 12 0)
                    (.op (.copy 41 0))))))))
              nopRegCode)
            nopRegCode)
          denseOfPhysRegCode))))))))
    resolveIndexedSlotRegCode

theorem resolveOvfStepRegCode_exec {U V w N b j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr272 : x.regs 272 = b)
    (hr30 : x.regs 30 = j)
    (hr36 : x.regs 36 = 0)
    (hr39 : x.regs 39 = gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N)
    (hr42 : x.regs 42 = Succinct.gmSlabMetaBase N)
    (hp : j < gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N →
      x.regs 41 = Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N)) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    let qK := gm (Succinct.gmQIdx b) * slabSize N
    BitRAM.DemonicExecWithin w resolveOvfStepRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 14 = Succinct.slotOf N gm b j ∧
        y.regs 15 = denseOfPhys N gm td (Succinct.slotOf N gm b j) ∧
        (j + 1 < qK → y.regs 41 = Succinct.slabPtrOf N gm b ((j + 1) / slabSize N)) ∧
        (∀ r : Fin 280, 30 ≤ r.val → r ≠ 41 → y.regs r = x.regs r))
      235 := by
  intro gm td qK
  obtain ⟨_, _, _, _, _, h250, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    her.active hN_pos
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hK : 0 < slabSize N := slabSize_pos N
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hbc_le : Succinct.bCount N (gmAtBit U w N x.mem) b ≤ N := Succinct.bCount_le_n_max hslot b
  have hj_le_N : j ≤ N := le_of_lt (lt_of_lt_of_le hj_bc hbc_le)
  unfold resolveOvfStepRegCode
  by_cases hj_slab : j < qK
  · have hcond : BitRAM.CondHolds (.lt 30 39) x := by
      change x.regs 30 < x.regs 39; rw [hr30, hr39]; exact hj_slab
    refine (dExec_branch_pos (T := 165) hcond ?_).mono (fun z hz => hz) (by omega)
    have hp_eq := hp hj_slab
    set p_cur := Succinct.slabPtrOf N gm b (j / slabSize N)
    have hslab := hslot.multi_slab hb_pos
    have hs_lt : j / slabSize N < gm (Succinct.gmQIdx b) :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hp_lt_0 : p_cur < gm 0 := by
      change p_cur < gmAtBit U w N x.mem 0
      rw [hslab.nslabs_eq]; exact hslab.ptr_lt b hb _ hs_lt
    have hp_lt_max : p_cur < maxFullSlabs N :=
      lt_of_lt_of_le (hslab.ptr_lt b hb _ hs_lt) hslab.nslabs_le
    have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
    set off := (slabSize N - 1) - j % slabSize N
    have hphys_eq : p_cur * slabSize N + off = Succinct.slotOf N gm b j := by
      unfold Succinct.slotOf
      rw [ite_eq_right hb0, ite_eq_left hj_slab]
    have hphys_lt : p_cur * slabSize N + off < N := by
      rw [hphys_eq]
      exact (Succinct.slotOf_lt_and_injective hslot).1 b hb j hj_bc
    have hpK_le : p_cur * slabSize N ≤ N := by omega
    have hK_le : slabSize N ≤ N := by
      have h1 : 1 * slabSize N ≤ gm 0 * slabSize N :=
        Nat.mul_le_mul_right _ (show 1 ≤ gm 0 by omega)
      have htot := hslot.multi_total_le hb_pos
      change gm 0 * slabSize N + gm 1 ≤ N at htot
      omega
    refine DemonicExecWithin.step_const (T := 164) (hfit_N 1 (by omega)) ?_
    refine step_dExec_bin (v := slabSize N - 1) (T := 163)
      (by simp +decide [BitRAM.Data.set, BinOp.eval, h250])
      (hfit_N (slabSize N - 1) (by omega)) ?_
    refine step_dExec_bin (v := j % slabSize N) (T := 162)
      (by simp +decide [BitRAM.Data.set, BinOp.eval, hr30, h250])
      (hfit_N (j % slabSize N) (by omega)) ?_
    refine step_dExec_bin (v := off) (T := 161)
      (by simp +decide [BitRAM.Data.set, BinOp.eval]; rfl)
      (hfit_N off (by omega)) ?_
    refine step_dExec_bin (v := p_cur * slabSize N) (T := 160)
      (by simp +decide [BitRAM.Data.set, BinOp.eval, hp_eq, h250])
      (hfit_N (p_cur * slabSize N) (by omega)) ?_
    refine step_dExec_bin (v := Succinct.slotOf N gm b j) (T := 159)
      (by simp +decide [BitRAM.Data.set, BinOp.eval, hphys_eq])
      (by rw [← hphys_eq]; exact hfit_N _ (by omega)) ?_
    refine step_dExec_bin (v := j + 1) (T := 158)
      (by simp +decide [BitRAM.Data.set, BinOp.eval, hr30])
      (hfit_N (j + 1) (by omega)) ?_
    set s1 := ((((((x.set 13 1).set 16 (slabSize N - 1)).set 17 (j % slabSize N)).set 16
      off).set 14 (p_cur * slabSize N)).set 14 (Succinct.slotOf N gm b j)).set 17 (j + 1)
    have hs1_wf : s1.WellFormed w :=
      wf_set 17 (wf_set 14 (wf_set 14 (wf_set 16 (wf_set 17 (wf_set 16
        (wf_set 13 hx (hfit_N 1 (by omega))) (hfit_N _ (by omega))) (hfit_N _ (by omega)))
        (hfit_N _ (by omega))) (hfit_N _ (by omega)))
        (by rw [← hphys_eq]; exact hfit_N _ (by omega))) (hfit_N (j + 1) (by omega))
    have hs1_er : EpochRegs U V w N s1 :=
      her.congr_regs (fun r hr1 _ => by
        dsimp only [s1, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs1_14 : s1.regs 14 = Succinct.slotOf N gm b j := by simp +decide [s1, BitRAM.Data.set]
    have hs1_16 : s1.regs 16 = off := by simp +decide [s1, BitRAM.Data.set]
    have hs1_17 : s1.regs 17 = j + 1 := by simp +decide [s1, BitRAM.Data.set]
    have hs1_36 : s1.regs 36 = 0 := by simp +decide [s1, BitRAM.Data.set, hr36]
    have hs1_39 : s1.regs 39 = qK := by simp +decide [s1, BitRAM.Data.set, hr39]; rfl
    have hs1_41 : s1.regs 41 = p_cur := by simp +decide [s1, BitRAM.Data.set, hp_eq]
    have hs1_42 : s1.regs 42 = Succinct.gmSlabMetaBase N := by
      simp +decide [s1, BitRAM.Data.set, hr42]
    have hs1_regs : ∀ r : Fin 280, 30 ≤ r.val → s1.regs r = x.regs r := by
      intro r hr
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    have hstep_branch : BitRAM.DemonicExecWithin w
        (.branch (.eq 16 36)
          (.branch (.lt 17 39)
            (.seq (.op (.const 13 4))
            (.seq (.op (.bin .mul 12 13 41))
            (.seq (.op (.const 13 3))
            (.seq (.op (.bin .add 12 12 13))
            (.seq (.op (.bin .add 12 42 12))
            (.seq (readGMRegCode 12 0)
                  (.op (.copy 41 0))))))))
            nopRegCode)
          nopRegCode) s1
        (fun y1 =>
          y1.toBitMemoryState = x.toBitMemoryState ∧
          y1.WellFormed w ∧
          EpochRegs U V w N y1 ∧
          y1.regs 14 = Succinct.slotOf N gm b j ∧
          (j + 1 < qK → y1.regs 41 = Succinct.slabPtrOf N gm b ((j + 1) / slabSize N)) ∧
          (∀ r : Fin 280, 30 ≤ r.val → r ≠ 41 → y1.regs r = x.regs r))
        53 := by
      by_cases hoff : off = 0
      · have hcond_off : BitRAM.CondHolds (.eq 16 36) s1 := by
          change s1.regs 16 = s1.regs 36; rw [hs1_16, hs1_36, hoff]
        refine (dExec_branch_pos (T := 52) hcond_off ?_).mono (fun z hz => hz) (by omega)
        by_cases hj1_slab : j + 1 < qK
        · have hcond_j1 : BitRAM.CondHolds (.lt 17 39) s1 := by
            change s1.regs 17 < s1.regs 39; rw [hs1_17, hs1_39]; exact hj1_slab
          refine (dExec_branch_pos (T := 51) hcond_j1 ?_).mono (fun z hz => hz) (by omega)
          obtain ⟨hdiv_eq, hmul_eq⟩ := Succinct.div_succ_of_sub_mod_eq_zero hK hoff
          have hs1_lt : j / slabSize N + 1 < gm (Succinct.gmQIdx b) := by
            have : (j / slabSize N + 1) * slabSize N < qK := by rwa [hmul_eq]
            exact (Nat.mul_lt_mul_right hK).mp this
          have habv_lt : Succinct.gmSlabMetaBase N + 4 * p_cur + 3 < globalMetaLen N :=
            Succinct.gmSlabAboveIdx_lt hb_pos hp_lt_max
          have habv_eq : Succinct.gmSlabMetaBase N + (4 * p_cur + 3) =
              Succinct.gmSlabAboveIdx N p_cur := by
            unfold Succinct.gmSlabAboveIdx; omega
          refine DemonicExecWithin.step_const (T := 50) (hfit_gm 4 (by omega)) ?_
          refine step_dExec_bin (v := 4 * p_cur) (T := 49)
            (by simp +decide [BitRAM.Data.set, BinOp.eval, hs1_41])
            (hfit_gm (4 * p_cur) (by omega)) ?_
          refine DemonicExecWithin.step_const (T := 48) (hfit_gm 3 (by omega)) ?_
          refine step_dExec_bin (v := 4 * p_cur + 3) (T := 47)
            (by simp +decide [BitRAM.Data.set, BinOp.eval])
            (hfit_gm (4 * p_cur + 3) (by omega)) ?_
          refine step_dExec_bin (v := Succinct.gmSlabMetaBase N + (4 * p_cur + 3)) (T := 46)
            (by simp +decide [BitRAM.Data.set, BinOp.eval, hs1_42])
            (hfit_gm _ (by omega)) ?_
          set s2 := ((((s1.set 13 4).set 12 (4 * p_cur)).set 13 3).set 12 (4 * p_cur + 3)).set 12
            (Succinct.gmSlabMetaBase N + (4 * p_cur + 3))
          have hs2_wf : s2.WellFormed w :=
            wf_set 12 (wf_set 12 (wf_set 13 (wf_set 12 (wf_set 13 hs1_wf (hfit_gm 4 (by omega)))
              (hfit_gm _ (by omega))) (hfit_gm 3 (by omega))) (hfit_gm _ (by omega)))
              (hfit_gm _ (by omega))
          have hs2_er : EpochRegs U V w N s2 :=
            hs1_er.congr_regs (fun r hr1 _ => by
              dsimp only [s2, BitRAM.Data.set]
              repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
          refine .seq (T₂ := 1)
            (readGMRegCode_exec (idx := Succinct.gmSlabMetaBase N + (4 * p_cur + 3))
              (rIdx := 12) (rDst := 0) (by decide) hw hN_pos hnU hU
              hs2_wf hs2_er (by rw [habv_eq]; exact habv_lt)
              (by simp +decide [s2, BitRAM.Data.set]) hsz)
            (fun y0 ⟨hy0_st, hy0_wf, hy0_0, hy0_regs⟩ => ?_) le_rfl
          have hy0_er : EpochRegs U V w N y0 :=
            hs2_er.congr_regs (fun r hr1 _ =>
              hy0_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
          have hy0_0_eq : y0.regs 0 = Succinct.slabPtrOf N gm b ((j + 1) / slabSize N) := by
            rw [hy0_0, habv_eq]
            change gmAtBit U w N x.mem (Succinct.gmSlabAboveIdx N p_cur) = _
            rw [hslab.above_eq b hb (j / slabSize N) hs_lt hs1_lt, hdiv_eq]
          refine DemonicExecWithin.copy ?_
          refine ⟨hy0_st, wf_set 41 hy0_wf (hy0_wf.regs_fits 0),
            hy0_er.congr_regs (fun r hr1 _ => by
              dsimp only [BitRAM.Data.set]
              rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
            by
              dsimp only [BitRAM.Data.set]
              rw [Function.update_of_ne (by decide), hy0_regs 14 (by decide) (by decide)]
              simp +decide [s2, BitRAM.Data.set, hs1_14],
            fun _ => by simp +decide [BitRAM.Data.set, hy0_0_eq],
            fun r hr hne41 => ?_⟩
          dsimp only [BitRAM.Data.set]
          rw [Function.update_of_ne hne41,
            hy0_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
          dsimp only [s2, BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
          exact hs1_regs r hr
        · have hcond_j1 : ¬BitRAM.CondHolds (.lt 17 39) s1 := by
            change ¬(s1.regs 17 < s1.regs 39); rw [hs1_17, hs1_39]; exact hj1_slab
          refine (dExec_branch_neg (T := 1) hcond_j1 (nopRegCode_exec ?_)).mono
            (fun z hz => hz) (by omega)
          exact ⟨rfl, hs1_wf, hs1_er, hs1_14, fun h => (hj1_slab h).elim,
            fun r hr _ => hs1_regs r hr⟩
      · have hcond_off : ¬BitRAM.CondHolds (.eq 16 36) s1 := by
          change s1.regs 16 ≠ s1.regs 36; rw [hs1_16, hs1_36]; exact hoff
        refine (dExec_branch_neg (T := 1) hcond_off (nopRegCode_exec ?_)).mono
          (fun z hz => hz) (by omega)
        have hdiv_eq := Succinct.div_succ_of_sub_mod_ne_zero hK hoff
        exact ⟨rfl, hs1_wf, hs1_er, hs1_14, fun _ => by rw [hs1_41, hdiv_eq],
          fun r hr _ => hs1_regs r hr⟩
    refine .seq (T₂ := 105) hstep_branch
      (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_14, hy1_41, hy1_regs⟩ => ?_) (by omega)
    have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
      change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
      rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
    have hphys_lt_N : Succinct.slotOf N gm b j < N :=
      (Succinct.slotOf_lt_and_injective hslot).1 b hb j hj_bc
    refine (denseOfPhysRegCode_exec hw hN_pos hnU hU hy1_wf hy1_er
      (by rw [hy1_mem, hm1]) hy1_sz (by rwa [hy1_mem]) (by rwa [hy1_mem]) hy1_14 hphys_lt_N
      (fun hb_pos' hge => by
        rw [hy1_mem] at hge ⊢
        exact slotOf_tail_valid hslot hb hj_bc hb_pos' hge)).mono
      (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_15, hy2_14, hy2_regs⟩ => ?_) le_rfl
    refine ⟨hy2_st.trans hy1_st, hy2_wf, hy2_er, hy2_14,
      by simpa [hy1_mem] using hy2_15,
      fun hj1 => (hy2_regs 41 (by decide)).trans (hy1_41 hj1),
      fun r hr hne41 => (hy2_regs r (by omega)).trans (hy1_regs r hr hne41)⟩
  · have hcond : ¬BitRAM.CondHolds (.lt 30 39) x := by
      change ¬(x.regs 30 < x.regs 39); rw [hr30, hr39]; exact hj_slab
    refine (dExec_branch_neg (T := 230) hcond ?_).mono (fun z hz => hz) (by omega)
    have hj_ge : qK ≤ j := Nat.le_of_not_lt hj_slab
    refine (resolveIndexedSlotRegCode_exec hw hN_pos hnU hU hx her hm1 hsz hslot htd hb hj_bc
      (Or.inr hj_ge) hr272 hr30).mono
      (fun y ⟨hy_st, hy_wf, hy_er, hy_14, hy_15, hy_regs⟩ => ?_) le_rfl
    refine ⟨hy_st, hy_wf, hy_er, hy_14, hy_15,
      fun hj1 => by omega,
      fun r hr _ => hy_regs r hr⟩

/-- Single step of Phase 2 overflow search (`BitRAM.Code .standard 280`):
resolves `(phys, dense, p_next)` via `resolveOvfStepRegCode`, copies `r15` to `r16` and `r14` to
`r17`, reads `q_val` at `dense` via `readDenseQRegCode 16 0`, and on match (`q_val = q_target`)
records `(r32 = 1, r33 = j, r34 = phys, r35 = dense)` and sets `r30 = r40` to exit the loop;
otherwise increments `r30` (`j := j + 1`). Preserves all registers `r ≥ 45`. -/
@[expose]
def ovfStepRegCode : BitRAM.Code .standard 280 :=
  .seq resolveOvfStepRegCode
  (.seq (.op (.copy 16 15))
  (.seq (.op (.copy 17 14))
  (.seq (readDenseQRegCode 16 0)
        (.branch (.eq 0 271)
          (.seq (.op (.const 32 1))
          (.seq (.op (.copy 33 30))
          (.seq (.op (.copy 34 17))
          (.seq (.op (.copy 35 16))
                (.op (.copy 30 40))))))
          (.seq (.op (.const 13 1))
                (.op (.bin .add 30 30 13)))))))

theorem ovfStepRegCode_exec {U V w N b q_target j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr271 : x.regs 271 = q_target)
    (hr272 : x.regs 272 = b)
    (hr30 : x.regs 30 = j)
    (hr32 : x.regs 32 = 0)
    (hr36 : x.regs 36 = 0)
    (hr39 : x.regs 39 = gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N)
    (hr40 : x.regs 40 = Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr42 : x.regs 42 = Succinct.gmSlabMetaBase N)
    (hp : j < gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N →
      x.regs 41 = Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N)) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    let qK := gm (Succinct.gmQIdx b) * slabSize N
    let c := Succinct.bCount N gm b
    let phys := Succinct.slotOf N gm b j
    let dense := denseOfPhys N gm td phys
    let q_val := virtualQuotAt U V w N x.toBitMemoryState phys
    BitRAM.DemonicExecWithin w ovfStepRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 36 = 0 ∧
        y.regs 39 = qK ∧
        y.regs 40 = c ∧
        y.regs 42 = Succinct.gmSlabMetaBase N ∧
        (if q_val = q_target then
          y.regs 30 = c ∧ y.regs 32 = 1 ∧ y.regs 33 = j ∧
          y.regs 34 = phys ∧ y.regs 35 = dense
        else
          y.regs 30 = j + 1 ∧ y.regs 32 = 0 ∧
          (j + 1 < qK → y.regs 41 = Succinct.slabPtrOf N gm b ((j + 1) / slabSize N))) ∧
        (∀ r : Fin 280, 45 ≤ r.val → y.regs r = x.regs r))
      285 := by
  intro gm td qK c phys dense q_val
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hbc_le : Succinct.bCount N (gmAtBit U w N x.mem) b ≤ N := Succinct.bCount_le_n_max hslot b
  have hj_le_N : j ≤ N := le_of_lt (lt_of_lt_of_le hj_bc hbc_le)
  unfold ovfStepRegCode
  refine .seq (T₂ := 50)
    (resolveOvfStepRegCode_exec hw hN_pos hnU hU hb_pos hx her hm1 hsz_meta hslot htd hb hj_bc
      hr272 hr30 hr36 hr39 hr42 hp)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_14, hy1_15, hy1_41, hy1_regs⟩ => ?_) le_rfl
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  refine step_dExec_copy (v := y1.regs 15) (T := 49) rfl ?_
  refine step_dExec_copy (v := y1.regs 14) (T := 48)
    (by simp +decide [BitRAM.Data.set]) ?_
  set s2 := (y1.set 16 (y1.regs 15)).set 17 (y1.regs 14)
  have hs2_wf : s2.WellFormed w :=
    wf_set 17 (wf_set 16 hy1_wf (hy1_wf.regs_fits 15)) (hy1_wf.regs_fits 14)
  have hs2_er : EpochRegs U V w N s2 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hd_lt : dense < Succinct.totalSlots N gm :=
    (denseOfPhys_slotOf_lt_and_injective hslot htd).1 b hb j hj_bc
  have hs2_sz : itemBitOff U V w N (Succinct.totalSlots N gm) ≤ s2.bitSize := by
    change dictBitSize U V w N (Succinct.totalSlots N gm) ≤ y1.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
  refine .seq (T₂ := 6)
    (readDenseQRegCode_exec (rD := 16) (rDst := 0) (by decide) hw (le_of_lt hU) hs2_wf hs2_er hd_lt
      (by simp +decide [s2, BitRAM.Data.set, hy1_15, dense, phys, gm, td]) hs2_sz
      (by rw [show s2.mem = x.mem from hy1_mem, hm2])
      (by rw [show s2.mem = x.mem from hy1_mem, hm3]))
    (fun y2 ⟨hy2_st, hy2_wf, hy2_0, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_er : EpochRegs U V w N y2 :=
    hs2_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy2_0_eq : y2.regs 0 = q_val := by
    have h1 : y2.regs 0 = denseQuotAt U V w N x.toBitMemoryState dense := by
      rw [hy2_0]
      change denseQuotAt U V w N y1.toBitMemoryState dense = _
      rw [hy1_st]
    exact h1.trans (virtualQuotAt_slotOf_eq_denseQuotAt
      (s_bit := x.toBitMemoryState) hslot hb hj_bc).symm
  have hy2_16 : y2.regs 16 = dense := by
    rw [hy2_regs 16 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_15, dense, phys, gm, td]
  have hy2_17 : y2.regs 17 = phys := by
    rw [hy2_regs 17 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_14, phys, gm]
  have hy2_30 : y2.regs 30 = j := by
    rw [hy2_regs 30 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 30 (by decide) (by decide), hr30]
  have hy2_32 : y2.regs 32 = 0 := by
    rw [hy2_regs 32 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 32 (by decide) (by decide), hr32]
  have hy2_36 : y2.regs 36 = 0 := by
    rw [hy2_regs 36 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 36 (by decide) (by decide), hr36]
  have hy2_39 : y2.regs 39 = qK := by
    rw [hy2_regs 39 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 39 (by decide) (by decide), hr39, qK, gm]
  have hy2_40 : y2.regs 40 = c := by
    rw [hy2_regs 40 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 40 (by decide) (by decide), hr40, c, gm]
  have hy2_42 : y2.regs 42 = Succinct.gmSlabMetaBase N := by
    rw [hy2_regs 42 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 42 (by decide) (by decide), hr42]
  have hy2_271 : y2.regs 271 = q_target := by
    rw [hy2_regs 271 (by decide) (by decide)]
    simp +decide [s2, BitRAM.Data.set, hy1_regs 271 (by decide) (by decide), hr271]
  have hy2_41 : j + 1 < qK → y2.regs 41 = Succinct.slabPtrOf N gm b ((j + 1) / slabSize N) :=
    fun hj1 => by
      rw [hy2_regs 41 (by decide) (by decide)]
      simp +decide [s2, BitRAM.Data.set, hy1_41 hj1]
      rfl
  have hy2_hi : ∀ r : Fin 280, 45 ≤ r.val → y2.regs r = x.regs r := by
    intro r hr
    rw [hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s2, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)
  by_cases hmatch : q_val = q_target
  · have hcond : BitRAM.CondHolds (.eq 0 271) y2 := by
      change y2.regs 0 = y2.regs 271; rw [hy2_0_eq, hy2_271, hmatch]
    refine (dExec_branch_pos (T := 5) hcond ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 4) (hfit_N 1 (by omega)) ?_
    refine step_dExec_copy (v := j) (T := 3)
      (by simp +decide [BitRAM.Data.set, hy2_30]) ?_
    refine step_dExec_copy (v := phys) (T := 2)
      (by simp +decide [BitRAM.Data.set, hy2_17]) ?_
    refine step_dExec_copy (v := dense) (T := 1)
      (by simp +decide [BitRAM.Data.set, hy2_16]) ?_
    refine DemonicExecWithin.copy ?_
    refine ⟨hy2_st_x,
      wf_set 30 (wf_set 35 (wf_set 34 (wf_set 33 (wf_set 32 hy2_wf (hfit_N 1 (by omega)))
        (by rw [← hy2_30]; exact hy2_wf.regs_fits 30))
        (by rw [← hy2_17]; exact hy2_wf.regs_fits 17))
        (by rw [← hy2_16]; exact hy2_wf.regs_fits 16))
        (by
          dsimp only [BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by decide)]
          exact hy2_wf.regs_fits 40),
      hy2_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      by simp +decide [BitRAM.Data.set, hy2_36],
      by simp +decide [BitRAM.Data.set, hy2_39],
      by simp +decide [BitRAM.Data.set, hy2_40],
      by simp +decide [BitRAM.Data.set, hy2_42],
      ?_, fun r hr => ?_⟩
    · rw [ite_eq_left hmatch]
      simp +decide [BitRAM.Data.set, hy2_40]
    · dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hy2_hi r hr
  · have hcond : ¬BitRAM.CondHolds (.eq 0 271) y2 := by
      change y2.regs 0 ≠ y2.regs 271; rw [hy2_0_eq, hy2_271]; exact hmatch
    refine (dExec_branch_neg (T := 2) hcond ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 1) (hfit_N 1 (by omega)) ?_
    refine DemonicExecWithin.bin
      (by simpa [BitRAM.Data.set, BinOp.eval, hy2_30] using hfit_N (j + 1) (by omega)) ?_
    refine ⟨hy2_st_x,
      wf_set 30 (wf_set 13 hy2_wf (hfit_N 1 (by omega)))
        (by simpa [BitRAM.Data.set, BinOp.eval, hy2_30] using hfit_N (j + 1) (by omega)),
      hy2_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      by simp +decide [BitRAM.Data.set, hy2_36],
      by simp +decide [BitRAM.Data.set, hy2_39],
      by simp +decide [BitRAM.Data.set, hy2_40],
      by simp +decide [BitRAM.Data.set, hy2_42],
      ?_, fun r hr => ?_⟩
    · rw [ite_eq_right hmatch]
      refine ⟨by simp +decide [BitRAM.Data.set, BinOp.eval, hy2_30],
        by simp +decide [BitRAM.Data.set, hy2_32],
        fun hj1 => by simp +decide [BitRAM.Data.set, hy2_41 hj1]⟩
    · dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hy2_hi r hr

open Classical in
theorem ovfLoop_exec {U V w N b q_target : ℕ} (m : ℕ) {j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hjm : j + m = Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr271 : x.regs 271 = q_target)
    (hr272 : x.regs 272 = b)
    (hr30 : x.regs 30 = j)
    (hr32 : x.regs 32 = 0)
    (hr36 : x.regs 36 = 0)
    (hr39 : x.regs 39 = gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N)
    (hr40 : x.regs 40 = Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hr42 : x.regs 42 = Succinct.gmSlabMetaBase N)
    (hp : j < Succinct.bCount N (gmAtBit U w N x.mem) b →
      j < gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N →
      x.regs 41 = Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N)) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    BitRAM.DemonicExecWithin w (.loop (.lt 30 40) ovfStepRegCode) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (if ∃ k, j ≤ k ∧ k < j + m ∧
            virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target then
          y.regs 32 = 1 ∧
          j ≤ y.regs 33 ∧ y.regs 33 < j + m ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) =
            q_target ∧
          y.regs 34 = Succinct.slotOf N gm b (y.regs 33) ∧
          y.regs 35 = denseOfPhys N gm td (Succinct.slotOf N gm b (y.regs 33))
        else
          y.regs 32 = 0) ∧
        (∀ r : Fin 280, 45 ≤ r.val → y.regs r = x.regs r))
      (2 + 287 * m) := by
  intro gm td
  induction m generalizing j x with
  | zero =>
    have hj_eq : j = Succinct.bCount N gm b := by omega
    have hcond : ¬BitRAM.CondHolds (.lt 30 40) x := by
      change ¬(x.regs 30 < x.regs 40); rw [hr30, hr40, hj_eq]; omega
    refine .loop_exit hcond ?_ (by omega)
    refine ⟨rfl, hx, her, ?_, fun _ _ => rfl⟩
    have hno : ¬∃ k, j ≤ k ∧ k < j + 0 ∧
        virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target := by
      rintro ⟨k, hk1, hk2, _⟩; omega
    rw [ite_eq_right hno]
    exact hr32
  | succ m ih =>
    have hj_bc : j < Succinct.bCount N gm b := by dsimp only [gm]; omega
    have hcond : BitRAM.CondHolds (.lt 30 40) x := by
      change x.regs 30 < x.regs 40; rw [hr30, hr40]; exact hj_bc
    refine .loop_iter (T₁ := 285) (T₂ := 2 + 287 * m) hcond
      (ovfStepRegCode_exec hw hN_pos hnU hU hb_pos hx her hm1 hm2 hm3 hsz hslot htd hb hj_bc
        hr271 hr272 hr30 hr32 hr36 hr39 hr40 hr42 (hp hj_bc))
      (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_36, hy1_39, hy1_40, hy1_42, hy1_step, hy1_hi⟩ => ?_)
      (by omega)
    have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy1_271 : y1.regs 271 = q_target := (hy1_hi 271 (by decide)).trans hr271
    have hy1_272 : y1.regs 272 = b := (hy1_hi 272 (by decide)).trans hr272
    by_cases hmatch : virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) =
        q_target
    · rw [ite_eq_left hmatch] at hy1_step
      obtain ⟨hy1_30, hy1_32, hy1_33, hy1_34, hy1_35⟩ := hy1_step
      have hcond_exit : ¬BitRAM.CondHolds (.lt 30 40) y1 := by
        change ¬(y1.regs 30 < y1.regs 40); rw [hy1_30, hy1_40]; omega
      refine .loop_exit hcond_exit ?_ (by omega)
      have hex : ∃ k, j ≤ k ∧ k < j + (m + 1) ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target :=
        ⟨j, le_rfl, by omega, hmatch⟩
      refine ⟨hy1_st, hy1_wf, hy1_er, ?_, hy1_hi⟩
      rw [ite_eq_left hex, hy1_33]
      exact ⟨hy1_32, le_rfl, by omega, hmatch, hy1_34, hy1_35⟩
    · rw [ite_eq_right hmatch] at hy1_step
      obtain ⟨hy1_30, hy1_32, hy1_41⟩ := hy1_step
      have hy1_sz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
          y1.bitSize := by
        change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
          y1.toBitMemoryState.bitSize
        rw [hy1_mem, congrArg BitMemory.State.bitSize hy1_st]; exact hsz
      refine (ih (j := j + 1) (x := y1) hy1_wf hy1_er (by rw [hy1_mem, hm1]) (by rw [hy1_mem, hm2])
        (by rw [hy1_mem, hm3]) hy1_sz (by rwa [hy1_mem])
        (by rwa [hy1_mem]) (by rw [hy1_mem]; dsimp only [gm] at hj_bc ⊢; omega)
        hy1_271 hy1_272 hy1_30 hy1_32 hy1_36
        (by rw [hy1_mem]; exact hy1_39) (by rw [hy1_mem]; exact hy1_40) hy1_42
        (fun _ hj1 => by rw [hy1_mem] at hj1 ⊢; exact hy1_41 hj1)).mono
        (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_) le_rfl
      have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
      rw [hy1_st, hy1_mem] at hy2_res
      refine ⟨hy2_st_x, hy2_wf, hy2_er, ?_,
        fun r hr => (hy2_hi r hr).trans (hy1_hi r hr)⟩
      by_cases hex_rest : ∃ k, j + 1 ≤ k ∧ k < j + 1 + m ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target
      · rw [ite_eq_left hex_rest] at hy2_res
        obtain ⟨hy2_32, hy2_lo, hy2_hi_k, hy2_q, hy2_34, hy2_35⟩ := hy2_res
        have hex : ∃ k, j ≤ k ∧ k < j + (m + 1) ∧
            virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target := by
          obtain ⟨k, hk1, hk2, hqk⟩ := hex_rest
          exact ⟨k, by omega, by omega, hqk⟩
        rw [ite_eq_left hex]
        exact ⟨hy2_32, by omega, by omega, hy2_q, hy2_34, hy2_35⟩
      · rw [ite_eq_right hex_rest] at hy2_res
        have hno : ¬∃ k, j ≤ k ∧ k < j + (m + 1) ∧
            virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target := by
          rintro ⟨k, hk1, hk2, hqk⟩
          rcases eq_or_lt_of_le hk1 with rfl | hlt
          · exact hmatch hqk
          · exact hex_rest ⟨k, by omega, by omega, hqk⟩
        rw [ite_eq_right hno]
        exact hy2_res

/-- Phase 2 overflow search (`BitRAM.Code .standard 280`):
given `r271 = q_target`, `r272 = b`, `r32 = 0`, `r36 = 0`, scans overflow slots
`j ∈ [effBucketCap N, bCount N gm b)` when `0 < bucketBits N`, setting
`r32 = 1`, `r33 = j_found`, `r34 = phys_found`, `r35 = dense_found` on hit or leaving `r32 = 0` on
miss. Preserves all registers `r ≥ 45`. -/
@[expose]
def searchOverflowRegCode : BitRAM.Code .standard 280 :=
  .branch (.lt 36 245)
    (.seq initOvfSearchRegCode
          (.loop (.lt 30 40) ovfStepRegCode))
    nopRegCode

open Classical in
theorem searchOverflowRegCode_exec {U V w N b q_target : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hr271 : x.regs 271 = q_target)
    (hr272 : x.regs 272 = b)
    (hr32 : x.regs 32 = 0)
    (hr36 : x.regs 36 = 0) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    BitRAM.DemonicExecWithin w searchOverflowRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (if ∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
            virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q_target then
          y.regs 32 = 1 ∧
          effBucketCap N ≤ y.regs 33 ∧ y.regs 33 < Succinct.bCount N gm b ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) =
            q_target ∧
          y.regs 34 = Succinct.slotOf N gm b (y.regs 33) ∧
          y.regs 35 = denseOfPhys N gm td (Succinct.slotOf N gm b (y.regs 33))
        else
          y.regs 32 = 0) ∧
        (∀ r : Fin 280, 45 ≤ r.val → y.regs r = x.regs r))
      (230 + 287 * (Succinct.bCount N gm b - effBucketCap N)) := by
  intro gm td
  obtain ⟨h245, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    her.active hN_pos
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  unfold searchOverflowRegCode
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hcond : ¬BitRAM.CondHolds (.lt 36 245) x := by
      change ¬(x.regs 36 < x.regs 245); rw [hr36, h245, hb0]; omega
    refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
    have hbc_le : Succinct.bCount N gm b ≤ N := Succinct.bCount_le_n_max hslot b
    have hlt_cap : N < effBucketCap N := lt_effBucketCap_of_bucketBits_eq_zero hb0
    have hno : ¬∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
        virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q_target := by
      rintro ⟨j, hj1, hj2, _⟩; omega
    refine ⟨rfl, hx, her, ?_, fun _ _ => rfl⟩
    rw [ite_eq_right hno]
    exact hr32
  · have hcond : BitRAM.CondHolds (.lt 36 245) x := by
      change x.regs 36 < x.regs 245; rw [hr36, h245]; exact hb_pos
    refine (dExec_branch_pos (T := 227 + 287 * (Succinct.bCount N gm b - effBucketCap N))
      hcond ?_).mono (fun z hz => hz) (by omega)
    refine .seq (T₂ := 2 + 287 * (Succinct.bCount N gm b - effBucketCap N))
      (initOvfSearchRegCode_exec hw hN_pos hnU hU hb_pos hx her hsz_meta hslot hb hr272)
      (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_jm, hy1_39, hy1_40, hy1_42, hy1_30_cap, hy1_41,
        hy1_regs⟩ => ?_) (by omega)
    have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy1_sz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
        y1.bitSize := by
      change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
        y1.toBitMemoryState.bitSize
      rw [hy1_mem, congrArg BitMemory.State.bitSize hy1_st]; exact hsz
    have hy1_32 : y1.regs 32 = 0 := (hy1_regs 32 (Or.inl ⟨by decide, by decide⟩)).trans hr32
    have hy1_36 : y1.regs 36 = 0 := (hy1_regs 36 (Or.inl ⟨by decide, by decide⟩)).trans hr36
    have hy1_271 : y1.regs 271 = q_target := (hy1_regs 271 (Or.inr (by decide))).trans hr271
    have hy1_272 : y1.regs 272 = b := (hy1_regs 272 (Or.inr (by decide))).trans hr272
    have hp1 : y1.regs 30 < Succinct.bCount N (gmAtBit U w N y1.mem) b →
        y1.regs 30 < gmAtBit U w N y1.mem (Succinct.gmQIdx b) * slabSize N →
        y1.regs 41 = Succinct.slabPtrOf N (gmAtBit U w N y1.mem) b (y1.regs 30 / slabSize N) := by
      rw [hy1_mem]; exact hy1_41
    refine (ovfLoop_exec (Succinct.bCount N gm b - effBucketCap N) (j := y1.regs 30) (x := y1)
      hw hN_pos hnU hU hb_pos hy1_wf hy1_er (by rw [hy1_mem, hm1]) (by rw [hy1_mem, hm2])
      (by rw [hy1_mem, hm3]) hy1_sz
      (by rwa [hy1_mem]) (by rwa [hy1_mem]) hb (by rw [hy1_mem]; exact hy1_jm)
      hy1_271 hy1_272 rfl hy1_32 hy1_36 (by rw [hy1_mem]; exact hy1_39)
      (by rw [hy1_mem]; exact hy1_40) hy1_42 hp1).mono
      (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_) le_rfl
    have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
    rw [hy1_st, hy1_mem] at hy2_res
    refine ⟨hy2_st_x, hy2_wf, hy2_er, ?_,
      fun r hr => (hy2_hi r hr).trans (hy1_regs r (Or.inr hr))⟩
    by_cases hovf : effBucketCap N < Succinct.bCount N gm b
    · have hj0_eq : y1.regs 30 = effBucketCap N := hy1_30_cap hovf
      have hjm_eq : effBucketCap N + (Succinct.bCount N gm b - effBucketCap N) =
          Succinct.bCount N gm b := by omega
      rw [hj0_eq, hjm_eq] at hy2_res
      exact hy2_res
    · have hsub0 : Succinct.bCount N gm b - effBucketCap N = 0 := by omega
      rw [hsub0] at hy2_res
      have hno1 : ¬∃ k, y1.regs 30 ≤ k ∧ k < y1.regs 30 + 0 ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b k) = q_target := by
        rintro ⟨k, hk1, hk2, _⟩; omega
      have hno2 : ¬∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q_target := by
        rintro ⟨j, hj1, hj2, _⟩; omega
      rw [ite_eq_right hno1] at hy2_res
      rw [ite_eq_right hno2]
      exact hy2_res

/-! ## Section 2: Combined two-phase bucket search (`searchBucketRegCode`) -/

/-- Two-phase bucket search (`BitRAM.Code .standard 280`):
given `r271 = q_target`, `r272 = b`, `r273 = m`:
first searches micro-chain `(b, m)` via `searchMicroChainRegCode`; if not found (`r32 = 0`),
searches overflow slots via `searchOverflowRegCode`.
Sets `r32 = 1`, `r33 = j_found`, `r34 = phys_found`, `r35 = dense_found` on hit or `r32 = 0` on
miss. Preserves all registers `r ≥ 45`. -/
@[expose]
def searchBucketRegCode : BitRAM.Code .standard 280 :=
  .seq searchMicroChainRegCode
        (.branch (.eq 32 36)
          searchOverflowRegCode
          nopRegCode)

open Classical in
theorem searchBucketRegCode_exec {U V w N b m q_target : ℕ} {L : List ℕ}
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
    BitRAM.DemonicExecWithin w searchBucketRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (if (∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
              (Succinct.slotOf N gm b j) = q_target) ∨
            (∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
              virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q_target) then
          y.regs 32 = 1 ∧
          y.regs 33 < Succinct.bCount N gm b ∧
          (y.regs 33 ∈ L ∨ effBucketCap N ≤ y.regs 33) ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) =
            q_target ∧
          y.regs 34 = Succinct.slotOf N gm b (y.regs 33) ∧
          y.regs 35 = denseOfPhys N gm td (Succinct.slotOf N gm b (y.regs 33))
        else
          y.regs 32 = 0) ∧
        (∀ r : Fin 280, 45 ≤ r.val → y.regs r = x.regs r))
      (295 + 350 * L.length + 287 * (Succinct.bCount N gm b - effBucketCap N)) := by
  intro gm td
  unfold searchBucketRegCode
  refine .seq (T₂ := 235 + 287 * (Succinct.bCount N gm b - effBucketCap N))
    (searchMicroChainRegCode_exec hw hN_pos hnU hU hx her hm1 hm2 hm3 hsz hslot htd hb hm hchain
      hc_lt hr271 hr272 hr273)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_36, hy1_res, hy1_hi⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  by_cases hex1 : ∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
      (Succinct.slotOf N gm b j) = q_target
  · rw [ite_eq_left hex1] at hy1_res
    obtain ⟨hy1_32, hy1_in, hy1_q, hy1_34, hy1_35⟩ := hy1_res
    have hcond : ¬BitRAM.CondHolds (.eq 32 36) y1 := by
      change y1.regs 32 ≠ y1.regs 36; rw [hy1_32, hy1_36]; omega
    refine (dExec_branch_neg (T := 1) hcond (nopRegCode_exec ?_)).mono (fun z hz => hz) (by omega)
    refine ⟨hy1_st, hy1_wf, hy1_er, ?_, fun r hr => hy1_hi r (by omega)⟩
    rw [ite_eq_left (Or.inl hex1)]
    exact ⟨hy1_32, hc_lt _ hy1_in, Or.inl hy1_in, hy1_q, hy1_34, hy1_35⟩
  · rw [ite_eq_right hex1] at hy1_res
    have hcond : BitRAM.CondHolds (.eq 32 36) y1 := by
      change y1.regs 32 = y1.regs 36; rw [hy1_res, hy1_36]
    refine (dExec_branch_pos (T := 230 + 287 * (Succinct.bCount N gm b - effBucketCap N))
      hcond ?_).mono (fun z hz => hz) (by omega)
    have hy1_sz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
        y1.bitSize := by
      change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
        y1.toBitMemoryState.bitSize
      rw [hy1_mem, congrArg BitMemory.State.bitSize hy1_st]; exact hsz
    refine (searchOverflowRegCode_exec (b := b) (q_target := q_target) (x := y1)
      hw hN_pos hnU hU hy1_wf hy1_er
      (by rw [hy1_mem, hm1]) (by rw [hy1_mem, hm2]) (by rw [hy1_mem, hm3]) hy1_sz
      (by rwa [hy1_mem]) (by rwa [hy1_mem]) hb
      ((hy1_hi 271 (by decide)).trans hr271) ((hy1_hi 272 (by decide)).trans hr272)
      hy1_res hy1_36).mono
      (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_)
      (by rw [hy1_mem])
    have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
    rw [hy1_st, hy1_mem] at hy2_res
    refine ⟨hy2_st_x, hy2_wf, hy2_er, ?_,
      fun r hr => (hy2_hi r hr).trans (hy1_hi r (by omega))⟩
    by_cases hex2 : ∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
        virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q_target
    · rw [ite_eq_left hex2] at hy2_res
      obtain ⟨hy2_32, hy2_lo, hy2_lt, hy2_q, hy2_34, hy2_35⟩ := hy2_res
      rw [ite_eq_left (Or.inr hex2)]
      exact ⟨hy2_32, hy2_lt, Or.inr hy2_lo, hy2_q, hy2_34, hy2_35⟩
    · rw [ite_eq_right hex2] at hy2_res
      have hno : ¬((∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
            (Succinct.slotOf N gm b j) = q_target) ∨
          (∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
            virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q_target)) := by
        rintro (h | h)
        · exact hex1 h
        · exact hex2 h
      rw [ite_eq_right hno]
      exact hy2_res

/-! ## Section 3: Dictionary query (`queryRegCode`) and hit update (`insertHitRegCode`) -/

theorem evalOp_preserves_fits {B : Basis} {r w : ℕ} {o : WordRAM.Op B r}
    {x y : BitRAM.Data r}
    (h : BitRAM.evalOp w o x = some y)
    (hregs : ∀ i : Fin r, Fits w (x.regs i))
    (hmem : ∀ a : ℕ, Fits w (x.mem a)) :
    (∀ i : Fin r, Fits w (y.regs i)) ∧ (∀ a : ℕ, Fits w (y.mem a)) := by
  cases o with
  | const d v =>
    simp only [BitRAM.evalOp, BitRAM.Data.put] at h
    split_ifs at h with hv
    cases h
    refine ⟨fun i => ?_, hmem⟩
    by_cases hi : i = d
    · subst hi; simp [BitRAM.Data.set, hv]
    · simp [BitRAM.Data.set, hi, hregs i]
  | copy d s =>
    simp only [BitRAM.evalOp, Option.some.injEq] at h
    subst h
    refine ⟨fun i => ?_, hmem⟩
    by_cases hi : i = d
    · subst hi; simp [BitRAM.Data.set, hregs s]
    · simp [BitRAM.Data.set, hi, hregs i]
  | alu f d args =>
    simp only [BitRAM.evalOp, Bind.bind, Option.bind] at h
    split at h
    · contradiction
    · simp only [BitRAM.Data.put] at h
      split_ifs at h with hv
      cases h
      refine ⟨fun i => ?_, hmem⟩
      by_cases hi : i = d
      · subst hi; simp [BitRAM.Data.set, hv]
      · simp [BitRAM.Data.set, hi, hregs i]
  | load d a =>
    simp only [BitRAM.evalOp] at h
    split_ifs at h with ha
    cases h
    refine ⟨fun i => ?_, hmem⟩
    by_cases hi : i = d
    · subst hi; simp [BitRAM.Data.set, hmem (x.regs a)]
    · simp [BitRAM.Data.set, hi, hregs i]
  | store a s =>
    simp only [BitRAM.evalOp] at h
    split_ifs at h with ha
    cases h
    refine ⟨hregs, fun q => ?_⟩
    by_cases hq : q = x.regs a
    · subst hq; simp [BitRAM.Data.write, hregs s]
    · simp [BitRAM.Data.write, hq, hmem q]

theorem dExec_with_fits {B : Basis} {r w : ℕ} {c : BitRAM.Code B r} {x : BitRAM.Data r}
    {P : BitRAM.Data r → Prop} {T : ℕ}
    (h : BitRAM.DemonicExecWithin w c x P T)
    (hregs : ∀ i : Fin r, Fits w (x.regs i))
    (hmem : ∀ a : ℕ, Fits w (x.mem a)) :
    BitRAM.DemonicExecWithin w c x
      (fun y => P y ∧ (∀ i : Fin r, Fits w (y.regs i)) ∧ (∀ a : ℕ, Fits w (y.mem a))) T := by
  induction h with
  | op heval hp h1 =>
    exact .op heval ⟨hp, evalOp_preserves_fits heval hregs hmem⟩ h1
  | @grow dst δReg x P T hfits hcost hp =>
    refine .grow hfits hcost fun s' hs' => ⟨hp s' hs', fun i => ?_, hs'.2.2.1⟩
    by_cases hi : i = dst
    · subst hi
      simpa using Fits.of_le hfits (Nat.le_add_right _ _)
    · simpa [Function.update_of_ne hi] using hregs i
  | @shrink δReg x P T hle hcost hp =>
    exact .shrink hle hcost ⟨hp, hregs, fun q => BitMemory.clearRangeMem_fits w x.mem _ _ q⟩
  | @size dst x P T hfits hp h1 =>
    refine .size hfits ⟨hp, fun i => ?_, hmem⟩ h1
    by_cases hi : i = dst
    · subst hi; simp [BitRAM.Data.set, hfits]
    · simp [BitRAM.Data.set, hi, hregs i]
  | seq _ _ hsum ih₁ ih₂ =>
    exact .seq (ih₁ hregs hmem) (fun y ⟨hyP, hyR, hyM⟩ => ih₂ y hyP hyR hyM) hsum
  | branch_pos hc _ hsum ih =>
    exact .branch_pos hc (ih hregs hmem) hsum
  | branch_neg hc _ hsum ih =>
    exact .branch_neg hc (ih hregs hmem) hsum
  | loop_exit hc hp h2 =>
    exact .loop_exit hc ⟨hp, hregs, hmem⟩ h2
  | loop_iter hc _ _ hsum ih₁ ih₂ =>
    exact .loop_iter hc (ih₁ hregs hmem) (fun y ⟨hyP, hyR, hyM⟩ => ih₂ y hyP hyR hyM) hsum

theorem virtualValAt_slotOf_eq_denseValAt {U V w N b j : ℕ} {s_bit : BitMemory.State}
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N s_bit.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b) :
    virtualValAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) =
      denseValAt U V w N s_bit
        (denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)
          (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j)) := by
  have hphys_lt : Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j < N :=
    (Succinct.slotOf_lt_and_injective hslot).1 b hb j hj_bc
  unfold virtualValAt
  change (if Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j < N then
    denseValAt U V w N s_bit
      (denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)
        (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j))
    else 0) = _
  rw [ite_eq_left hphys_lt]

/-- Uniform parameter-free dictionary query (`BitRAM.Code .standard 280`):
given `r270 = u`, splits `u` via `feistelSplitRegCode` into `r271 = q`, `r272 = b`, `r273 = m`,
searches bucket `b` via `searchBucketRegCode`, and sets `(r0, r1) = (1, val)` on hit or
`(r0, r1) = (0, 0)` on miss. Preserves all registers `r ≥ 274`. -/
@[expose]
def queryRegCode : BitRAM.Code .standard 280 :=
  .seq feistelSplitRegCode
  (.seq searchBucketRegCode
  (.seq (.op (.const 36 0))
        (.branch (.eq 32 36)
          (.seq (.op (.const 0 0))
                (.op (.const 1 0)))
          (.seq (.op (.copy 16 35))
          (.seq (readDenseVRegCode 16 1)
                (.op (.const 0 1)))))))

open Classical in
theorem queryRegCode_exec {U V w N u : ℕ}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hfit_meta : Fits w (epochMetaWords U w N))
    (θ : Succinct.QuotHashSeed U N) (hu : u < U)
    {L : List ℕ} {x : BitRAM.Data 280}
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize)
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hchain : Succinct.IsDLChain N
      (Succinct.lmHead N (lmAtBit U w N x.mem)
        (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u)
        (Succinct.mOfSeed U N θ (keyQuotient (bucketBits N) u)))
      (Succinct.lmPrev N (lmAtBit U w N x.mem)
        (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u))
      (Succinct.lmNext N (lmAtBit U w N x.mem)
        (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u)) L)
    (hc_lt : ∀ j ∈ L, j < Succinct.bCount N (gmAtBit U w N x.mem)
      (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u))
    (hr270 : x.regs 270 = u) :
    let gm := gmAtBit U w N x.mem
    let q := keyQuotient (bucketBits N) u
    let b := feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u
    BitRAM.DemonicExecWithin w queryRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (if (∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
              (Succinct.slotOf N gm b j) = q) ∨
            (∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
              virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q) then
          y.regs 0 = 1 ∧
          y.regs 33 < Succinct.bCount N gm b ∧
          (y.regs 33 ∈ L ∨ effBucketCap N ≤ y.regs 33) ∧
          virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) = q ∧
          y.regs 1 = virtualValAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33))
        else
          y.regs 0 = 0 ∧ y.regs 1 = 0) ∧
        (∀ r : Fin 280, 274 ≤ r.val → y.regs r = x.regs r))
      (142987 + 350 * L.length + 287 * (Succinct.bCount N gm b - effBucketCap N)) := by
  intro gm q b
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hadm_meta : epochMetaWords U w N ≤ x.wordSize w :=
    epochMetaWords_le_wordSize_of_bitSize hw hsz_meta
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (Succinct.hValOfSeed U N θ) u
  have hm_lt : Succinct.mOfSeed U N θ q < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
  unfold queryRegCode
  refine .seq (T₁ := 142643)
    (T₂ := 344 + 350 * L.length + 287 * (Succinct.bCount N gm b - effBucketCap N))
    (dExec_with_fits
      (feistelSplitRegCode_exec hN_pos hnU (le_of_lt hU) hfit_meta θ hu x her hr270 hadm_meta
        hrep_hash) hx.regs_fits hx.mem_wf.mem_fits)
    (fun y1 ⟨⟨hy1_270, hy1_271, hy1_272, hy1_273, hy1_er, hy1_hi, hy1_mem, hy1_sz⟩,
      hy1_rfits, _⟩ => ?_)
    (by omega)
  have hy1_st : y1.toBitMemoryState = x.toBitMemoryState := by
    ext a
    · exact congrFun hy1_mem a
    · exact hy1_sz
  have hy1_wf : y1.WellFormed w := ⟨hy1_rfits, hy1_st ▸ hx.mem_wf⟩
  have hy1_sz_dict : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N y1.mem)) ≤
      y1.bitSize := by
    rw [hy1_mem, hy1_sz]; exact hsz
  refine .seq (T₂ := 49)
    (searchBucketRegCode_exec (b := b) (m := Succinct.mOfSeed U N θ q) (q_target := q)
      (L := L) (x := y1) hw hN_pos hnU hU hy1_wf hy1_er
      (by rw [hy1_mem, hm1]) (by rw [hy1_mem, hm2]) (by rw [hy1_mem, hm3]) hy1_sz_dict
      (by rwa [hy1_mem]) (by rwa [hy1_mem]) hb_lt hm_lt (by rwa [hy1_mem]) (by rwa [hy1_mem])
      hy1_271 hy1_272 hy1_273)
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_res, hy2_hi⟩ => ?_)
    (by rw [hy1_mem]; dsimp only [gm]; omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  rw [hy1_st, hy1_mem] at hy2_res
  refine DemonicExecWithin.step_const (T := 48) (fits_zero w) ?_
  set s2 := y2.set 36 0
  have hs2_wf : s2.WellFormed w := wf_set 36 hy2_wf (fits_zero w)
  have hs2_er : EpochRegs U V w N s2 :=
    hy2_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs2_hi : ∀ r : Fin 280, 274 ≤ r.val → s2.regs r = x.regs r := by
    intro r hr
    dsimp only [s2, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact (hy2_hi r (by omega)).trans (hy1_hi r hr)
  by_cases hex : (∃ j ∈ L, virtualQuotAt U V w N x.toBitMemoryState
        (Succinct.slotOf N gm b j) = q) ∨
      (∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
        virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q)
  · rw [ite_eq_left hex] at hy2_res
    obtain ⟨hy2_32, hy2_33_lt, hy2_33_in, hy2_q, hy2_34, hy2_35⟩ := hy2_res
    have hcond : ¬BitRAM.CondHolds (.eq 32 36) s2 := by
      change s2.regs 32 ≠ s2.regs 36
      simp +decide [s2, BitRAM.Data.set, hy2_32]
    refine (dExec_branch_neg (T := 46) hcond ?_).mono (fun z hz => hz) (by omega)
    set j_found := y2.regs 33
    set phys := Succinct.slotOf N gm b j_found
    set dense := denseOfPhys N gm (tdAtBit U w N x.mem) phys
    have hd_lt : dense < Succinct.totalSlots N gm :=
      (denseOfPhys_slotOf_lt_and_injective hslot htd).1 b hb_lt j_found hy2_33_lt
    refine step_dExec_copy (v := dense) (T := 45)
      (by simp +decide [s2, BitRAM.Data.set, hy2_35]) ?_
    set s3 := s2.set 16 dense
    have hs3_wf : s3.WellFormed w :=
      wf_set 16 hs2_wf (by rw [← hy2_35]; exact hy2_wf.regs_fits 35)
    have hs3_er : EpochRegs U V w N s3 :=
      hs2_er.congr_regs (fun r hr1 _ => by
        dsimp only [s3, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs3_sz : itemBitOff U V w N (Succinct.totalSlots N gm) ≤ s3.bitSize := by
      change dictBitSize U V w N (Succinct.totalSlots N gm) ≤ y2.toBitMemoryState.bitSize
      rw [congrArg BitMemory.State.bitSize hy2_st_x]; exact hsz
    refine .seq (T₁ := 44) (T₂ := 1)
      (readDenseVRegCode_exec (d := dense) (rD := 16) (rDst := 1) (by decide) hw hV hs3_wf hs3_er
        hd_lt (by simp +decide [s3, BitRAM.Data.set]) hs3_sz
        (by rw [show s3.mem = x.mem from hy2_mem, hm2])
        (by rw [show s3.mem = x.mem from hy2_mem, hm3]))
      (fun y3 ⟨hy3_st, hy3_wf, hy3_1, hy3_regs⟩ => ?_) le_rfl
    have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
    have hy3_er : EpochRegs U V w N y3 :=
      hs3_er.congr_regs (fun r hr1 _ =>
        hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
    have hy3_1_eq : y3.regs 1 = virtualValAt U V w N x.toBitMemoryState phys := by
      have h1 : y3.regs 1 = denseValAt U V w N x.toBitMemoryState dense := by
        rw [hy3_1]
        change denseValAt U V w N y2.toBitMemoryState dense = _
        rw [hy2_st_x]
      exact h1.trans (virtualValAt_slotOf_eq_denseValAt
        (s_bit := x.toBitMemoryState) hslot hb_lt hy2_33_lt).symm
    have hy3_33 : y3.regs 33 = j_found := by
      rw [hy3_regs 33 (by decide) (by decide)]
      simp +decide [s3, s2, BitRAM.Data.set]
      rfl
    refine DemonicExecWithin.const hfit_1 ?_
    refine ⟨hy3_st_x, wf_set 0 hy3_wf hfit_1,
      hy3_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      ?_, fun r hr => ?_⟩
    · rw [ite_eq_left hex]
      have h33_set : (y3.set 0 1).regs 33 = j_found := by
        simp +decide [BitRAM.Data.set, hy3_33]
      rw [h33_set]
      exact ⟨by simp +decide [BitRAM.Data.set], hy2_33_lt, hy2_33_in, hy2_q,
        by simp +decide [BitRAM.Data.set, hy3_1_eq]; rfl⟩
    · dsimp only [BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
        hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s3, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hs2_hi r hr
  · rw [ite_eq_right hex] at hy2_res
    have hcond : BitRAM.CondHolds (.eq 32 36) s2 := by
      change s2.regs 32 = s2.regs 36
      simp +decide [s2, BitRAM.Data.set, hy2_res]
    refine (dExec_branch_pos (T := 2) hcond ?_).mono (fun z hz => hz) (by omega)
    refine DemonicExecWithin.step_const (T := 1) (fits_zero w) ?_
    refine DemonicExecWithin.const (fits_zero w) ?_
    refine ⟨hy2_st_x, wf_set 1 (wf_set 0 hs2_wf (fits_zero w)) (fits_zero w),
      hs2_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      ?_, fun r hr => ?_⟩
    · rw [ite_eq_right hex]
      simp +decide [BitRAM.Data.set]
    · dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      exact hs2_hi r hr

/-- Uniform parameter-free in-place value update on insert hit (`BitRAM.Code .standard 280`):
given `r35 = dense` (from a prior `searchBucketRegCode` hit) and `r274 = v_new`, writes `v_new`
into the dense value slice at index `r35` in `57` instructions, preserving `r ≥ 18`. -/
@[expose]
def insertHitRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 16 35))
  (.seq (.op (.copy 17 274))
        (writeDenseVRegCode 16 17))

theorem insertHitRegCode_exec {U V w N n_t d v : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hr35 : x.regs 35 = d) (hr274 : x.regs 274 = v)
    (hv : Fits (valBits V) v)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w insertHitRegCode x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (itemValBitOff U V w N d) (valBits V) v)).1 ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 57 := by
  unfold insertHitRegCode
  refine step_dExec_copy (v := d) (T := 56) hr35 ?_
  refine step_dExec_copy (v := v) (T := 55)
    (by simp +decide [BitRAM.Data.set, hr274]) ?_
  set s1 := (x.set 16 d).set 17 v
  have hs1_wf : s1.WellFormed w :=
    wf_set 17 (wf_set 16 hx (hr35 ▸ hx.regs_fits 35)) (hr274 ▸ hx.regs_fits 274)
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (writeDenseVRegCode_exec (rD := 16) (rV := 17) (by decide) (by decide)
    hw hV hs1_wf hs1_er hd (by simp +decide [s1, BitRAM.Data.set])
    (by simp +decide [s1, BitRAM.Data.set]) hv hsz hm2 hm3).mono
    (fun y ⟨hy_st, hy_wf, hy_er, hy_regs⟩ => ?_) le_rfl
  refine ⟨hy_st, hy_wf, hy_er, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

end Cslib.DataStructure.Dictionary.BitResizable
