/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.TailPoolOps
public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabPool

/-!
# Bit-Resizable Dictionary: Slab Pool `GM` Operations and Coupled Tail Compaction

This file compiles the slab-pool `GlobalMeta` operations (`gmPushSlab`, `gmUnlinkTopSlab`,
`gmCompactSlab`, `gmPopSlab` from `SuccinctSlabBijection.lean` and `SuccinctSlabPool.lean`) and
the coupled tail-compaction operations (`appendTailItemRightRegCode`, `removeLastTailRightRegCode`,
`removeLastTailLeftRegCode`) to uniform `BitRAM.Code .standard 280` programs.
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

/-! ## Section 1: Conditional-write combinators for `GMState` -/

theorem gmAtBit_lt (U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    gmAtBit U w N mem idx < 2 ^ globalPtrBits N := by
  unfold gmAtBit
  split_ifs
  · exact readPacked_lt (offGM U w N) (globalPtrBits N) w mem idx
  · exact Nat.two_pow_pos _

theorem step_gm_ite_write2D {U V w N base stride b k val T : ℕ}
    {P : Prop} [Decidable P] {cond : Cond 280}
    {rBase rStride rB rK rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrStride_ge : 14 ≤ rStride.val)
    (hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hcond : BitRAM.CondHolds cond x ↔ P)
    (hrBase : rf rBase = base) (hrStride : rf rStride = stride)
    (hrB : rf rB = b) (hrK : rf rK = k) (hrVal : rf rVal = val)
    (hidx : P → base + b * stride + k < globalMetaLen N)
    (hval : P → val < 2 ^ globalPtrBits N)
    (hrest : ∀ y,
      GMState U V w N (if P then Function.update gm (base + b * stride + k) val else gm) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w
      (.seq (.branch cond (writeGM2DRegCode rBase rStride rB rK rVal) nopRegCode) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 60) := by
  by_cases hP : P
  · have hc : BitRAM.CondHolds cond x := hcond.mpr hP
    have hbr : BitRAM.DemonicExecWithin w
        (.branch cond (writeGM2DRegCode rBase rStride rB rK rVal) nopRegCode) x
        (fun y => GMUpdatePost U V w N x y
          (Function.update (gmAtBit U w N x.mem) (base + b * stride + k) val) ∧
          ∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r) 60 :=
      dExec_branch_pos hc
        (writeGM2DRegCode_gmUpdate hrBase_ge hrStride_ge hrB_ge hrK_ge hrVal_ge
          hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
          ((hs.regs_eq rBase hrBase_ge).trans hrBase)
          ((hs.regs_eq rStride hrStride_ge).trans hrStride)
          ((hs.regs_eq rB hrB_ge).trans hrB)
          ((hs.regs_eq rK hrK_ge).trans hrK)
          ((hs.regs_eq rVal hrVal_ge).trans hrVal) (hidx hP) (hval hP))
    refine .seq (T₁ := 60) (T₂ := T) hbr (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
    have hs_y : GMState U V w N
        (if P then Function.update gm (base + b * stride + k) val else gm) rf y :=
      ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
       by rw [ite_eq_left hP, hpost.2.2.2.2.1, hs.gm_eq],
       fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
    exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl
  · have hc : ¬BitRAM.CondHolds cond x := fun h => hP (hcond.mp h)
    have hbr : BitRAM.DemonicExecWithin w
        (.branch cond (writeGM2DRegCode rBase rStride rB rK rVal) nopRegCode) x
        (fun y => y = x) 3 :=
      dExec_branch_neg hc (nopRegCode_exec rfl)
    refine .seq (T₁ := 3) (T₂ := T) hbr (fun y hy => ?_) (by omega)
    cases hy
    have hs_x : GMState U V w N
        (if P then Function.update gm (base + b * stride + k) val else gm) rf x :=
      ⟨hs.wf, hs.er, hs.gb, hs.sz, by rw [ite_eq_right hP, hs.gm_eq], hs.regs_eq⟩
    exact hrest x hs_x

theorem step_gm_ite_writeBucket {U V w N c b val T : ℕ}
    {P : Prop} [Decidable P] {cond : Cond 280}
    {rB rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrB_ge : 14 ≤ rB.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hcond : BitRAM.CondHolds cond x ↔ P)
    (hrB : rf rB = b) (hrVal : rf rVal = val)
    (hidx : P → 4 + 3 * b + c < globalMetaLen N)
    (hval : P → val < 2 ^ globalPtrBits N)
    (hrest : ∀ y,
      GMState U V w N (if P then Function.update gm (4 + 3 * b + c) val else gm) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w
      (.seq (.branch cond (writeGMBucketRegCode c rB rVal) nopRegCode) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 61) := by
  by_cases hP : P
  · have hc : BitRAM.CondHolds cond x := hcond.mpr hP
    have hbr : BitRAM.DemonicExecWithin w
        (.branch cond (writeGMBucketRegCode c rB rVal) nopRegCode) x
        (fun y => GMUpdatePost U V w N x y
          (Function.update (gmAtBit U w N x.mem) (4 + 3 * b + c) val) ∧
          ∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r) 61 :=
      dExec_branch_pos hc
        (writeGMBucketRegCode_gmUpdate hrB_ge hrVal_ge
          hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
          ((hs.regs_eq rB hrB_ge).trans hrB)
          ((hs.regs_eq rVal hrVal_ge).trans hrVal) (hidx hP) (hval hP))
    refine .seq (T₁ := 61) (T₂ := T) hbr (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
    have hs_y : GMState U V w N
        (if P then Function.update gm (4 + 3 * b + c) val else gm) rf y :=
      ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
       by rw [ite_eq_left hP, hpost.2.2.2.2.1, hs.gm_eq],
       fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
    exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl
  · have hc : ¬BitRAM.CondHolds cond x := fun h => hP (hcond.mp h)
    have hbr : BitRAM.DemonicExecWithin w
        (.branch cond (writeGMBucketRegCode c rB rVal) nopRegCode) x
        (fun y => y = x) 3 :=
      dExec_branch_neg hc (nopRegCode_exec rfl)
    refine .seq (T₁ := 3) (T₂ := T) hbr (fun y hy => ?_) (by omega)
    cases hy
    have hs_x : GMState U V w N
        (if P then Function.update gm (4 + 3 * b + c) val else gm) rf x :=
      ⟨hs.wf, hs.er, hs.gb, hs.sz, by rw [ite_eq_right hP, hs.gm_eq], hs.regs_eq⟩
    exact hrest x hs_x

theorem step_gm_ite_writeAffine {U V w N base a c idx val T : ℕ}
    {P : Prop} [Decidable P] {cond : Cond 280}
    {rBase rIdx rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val) (hrVal_ge : 14 ≤ rVal.val)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hcond : BitRAM.CondHolds cond x ↔ P)
    (hrBase : rf rBase = base) (hrIdx : rf rIdx = idx) (hrVal : rf rVal = val)
    (hidx : P → base + a * idx + c < globalMetaLen N)
    (hval : P → val < 2 ^ globalPtrBits N)
    (hrest : ∀ y,
      GMState U V w N (if P then Function.update gm (base + a * idx + c) val else gm) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w
      (.seq (.branch cond (writeGMAffineRegCode rBase a c rIdx rVal) nopRegCode) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 62) := by
  by_cases hP : P
  · have hc : BitRAM.CondHolds cond x := hcond.mpr hP
    have hbr : BitRAM.DemonicExecWithin w
        (.branch cond (writeGMAffineRegCode rBase a c rIdx rVal) nopRegCode) x
        (fun y => GMUpdatePost U V w N x y
          (Function.update (gmAtBit U w N x.mem) (base + a * idx + c) val) ∧
          ∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r) 62 :=
      dExec_branch_pos hc
        (writeGMAffineRegCode_gmUpdate hrBase_ge hrIdx_ge hrVal_ge ha_le hc_le
          hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
          ((hs.regs_eq rBase hrBase_ge).trans hrBase)
          ((hs.regs_eq rIdx hrIdx_ge).trans hrIdx)
          ((hs.regs_eq rVal hrVal_ge).trans hrVal) (hidx hP) (hval hP))
    refine .seq (T₁ := 62) (T₂ := T) hbr (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
    have hs_y : GMState U V w N
        (if P then Function.update gm (base + a * idx + c) val else gm) rf y :=
      ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
       by rw [ite_eq_left hP, hpost.2.2.2.2.1, hs.gm_eq],
       fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
    exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl
  · have hc : ¬BitRAM.CondHolds cond x := fun h => hP (hcond.mp h)
    have hbr : BitRAM.DemonicExecWithin w
        (.branch cond (writeGMAffineRegCode rBase a c rIdx rVal) nopRegCode) x
        (fun y => y = x) 3 :=
      dExec_branch_neg hc (nopRegCode_exec rfl)
    refine .seq (T₁ := 3) (T₂ := T) hbr (fun y hy => ?_) (by omega)
    cases hy
    have hs_x : GMState U V w N
        (if P then Function.update gm (base + a * idx + c) val else gm) rf x :=
      ⟨hs.wf, hs.er, hs.gb, hs.sz, by rw [ite_eq_right hP, hs.gm_eq], hs.regs_eq⟩
    exact hrest x hs_x

/-! ## Section 2: `gmPushSlabRegCode` and `gmUnlinkTopSlabRegCode` -/

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.gmPushSlab N gm b` on
`gmAtBit` (`26 ≤ rB.val`, `T = 630`). -/
@[expose]
def gmPushSlabRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMBucketRegCode 0 rB 14)
  (.seq (readGMConstRegCode 0 15)
  (.seq (readGMBucketRegCode 2 rB 16)
  (.seq (writeGMAffineRegCode 25 4 0 15 rB)
  (.seq (writeGMAffineRegCode 25 4 1 15 14)
  (.seq (writeGMAffineRegCode 25 4 2 15 16)
  (.seq (.op (.const 17 0))
  (.seq (.branch (.lt 17 14) (writeGMAffineRegCode 25 4 3 16 15) nopRegCode)
  (.seq (.branch (.lt 14 20) (writeGM2DRegCode 22 20 rB 14 15) nopRegCode)
  (.seq (writeGMBucketRegCode 2 rB 15)
  (.seq (.op (.const 17 1))
  (.seq (.op (.bin .add 18 14 17))
  (.seq (writeGMBucketRegCode 0 rB 18)
  (.seq (.op (.bin .add 19 15 17))
        (writeGMConstRegCode 0 19))))))))))))))

theorem gmPushSlabRegCode_exec {U V w N b : ℕ} {rB : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 26 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b)
    (hslab : Succinct.SlabBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N x.mem 0))
    (hp_lt : gmAtBit U w N x.mem 0 < maxFullSlabs N) :
    BitRAM.DemonicExecWithin w (gmPushSlabRegCode rB) x
      (fun z =>
        GMUpdatePost U V w N x z (Succinct.gmPushSlab N (gmAtBit U w N x.mem) b)) 630 := by
  set gm := gmAtBit U w N x.mem
  set q_b := gm (Succinct.gmQIdx b)
  set p_new := gm 0
  set top_old := gm (Succinct.gmSlabTopIdx b)
  have hq_idx_lt : 4 + 3 * b + 0 < globalMetaLen N := by
    simpa [Succinct.gmQIdx] using Succinct.gmQIdx_lt hb_pos hb
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen N := Succinct.gmSlabTopIdx_lt hb_pos hb
  have hownB_lt : Succinct.gmSlabMetaBase N + 4 * p_new + 0 < globalMetaLen N := by
    simpa [Succinct.gmSlabOwnerBIdx] using Succinct.gmSlabOwnerBIdx_lt hb_pos hp_lt
  have hownS_lt : Succinct.gmSlabMetaBase N + 4 * p_new + 1 < globalMetaLen N :=
    Succinct.gmSlabOwnerSIdx_lt hb_pos hp_lt
  have hbel_lt : Succinct.gmSlabMetaBase N + 4 * p_new + 2 < globalMetaLen N :=
    Succinct.gmSlabBelowIdx_lt hb_pos hp_lt
  have habv_lt : 0 < q_b → Succinct.gmSlabMetaBase N + 4 * top_old + 3 < globalMetaLen N := by
    intro hq_pos
    have htop_eq := hslab.top_eq b hb (q_b - 1) (by omega) (by omega)
    have htop_lt : top_old < p_new := by
      dsimp only [top_old, p_new]
      rw [htop_eq]
      exact hslab.ptr_lt b hb (q_b - 1) (by omega)
    exact Succinct.gmSlabAboveIdx_lt hb_pos (lt_trans htop_lt hp_lt)
  have hdir_lt : q_b < dirSlabsPerBucket N →
      Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N + q_b < globalMetaLen N :=
    fun hdir => Succinct.gmSlabDirIdx_lt hb_pos hb hdir
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hq_le_p : q_b ≤ p_new := Succinct.q_le_nslabs_of_slabBijection hslab hb
  have hb_val_lt : b < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by omega)
  have hq_val_lt : q_b < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hp_val_lt : p_new < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have htop_val_lt : top_old < 2 ^ globalPtrBits N :=
    gmAtBit_lt U w N x.mem (Succinct.gmSlabTopIdx b)
  have hq1_val_lt : q_b + 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hp1_val_lt : p_new + 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hfit_0 : Fits w 0 := fits_of_le_N hw hnU hU (by omega)
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_q1 : Fits w (q_b + 1) := fits_of_le_N hw hnU hU (by omega)
  have hfit_p1 : Fits w (p_new + 1) := fits_of_le_N hw hnU hU (by omega)
  have hs0 : GMState U V w N gm x.regs x := GMState.init hx her hgb hsz
  have h20 : x.regs 20 = dirSlabsPerBucket N := hgb.1
  have h22 : x.regs 22 = Succinct.gmSlabDirBase N := hgb.2.2.1
  have h25 : x.regs 25 = Succinct.gmSlabMetaBase N := hgb.2.2.2.2.2
  have hrB_ne : ∀ r : Fin 280, r.val < 26 → rB ≠ r := fun _ _ h => by subst h; omega
  have h14 : rB ≠ 14 := hrB_ne 14 (by decide)
  have h15 : rB ≠ 15 := hrB_ne 15 (by decide)
  have h16 : rB ≠ 16 := hrB_ne 16 (by decide)
  have h17 : rB ≠ 17 := hrB_ne 17 (by decide)
  have h18 : rB ≠ 18 := hrB_ne 18 (by decide)
  have hownB_eq : Succinct.gmSlabMetaBase N + 4 * p_new + 0 =
      Succinct.gmSlabOwnerBIdx N p_new := by
    unfold Succinct.gmSlabOwnerBIdx; omega
  have hq_idx_eq : 4 + 3 * b + 0 = Succinct.gmQIdx b := by
    unfold Succinct.gmQIdx; omega
  unfold gmPushSlabRegCode Succinct.gmPushSlab
  refine step_gm_readBucket (c := 0) (rB := rB) (rDst := 14)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hs0 hrB hq_idx_lt (fun y1 hs1 => ?_)
  refine step_gm_readConst (idx := 0) (rDst := 15)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs1 (fun y2 hs2 => ?_)
  refine step_gm_readBucket (c := 2) (rB := rB) (rDst := 16)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hs2
    (by simp [h14, h15, hrB]) htop_idx_lt (fun y3 hs3 => ?_)
  refine step_gm_writeAffine (rBase := 25) (a := 4) (c := 0) (rIdx := 15) (rVal := rB)
    (by decide) (by decide) (by omega) (by decide) (by decide) hw hN_pos hnU hU hs3
    (by simp +decide [h25]) (by simp +decide [p_new]) (by simp [h14, h15, h16, hrB])
    hownB_lt hb_val_lt (fun y4 hs4 => ?_)
  refine step_gm_writeAffine (rBase := 25) (a := 4) (c := 1) (rIdx := 15) (rVal := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs4
    (by simp +decide [h25]) (by simp +decide [p_new]) (by simp +decide [q_b, hq_idx_eq])
    hownS_lt hq_val_lt (fun y5 hs5 => ?_)
  refine step_gm_writeAffine (rBase := 25) (a := 4) (c := 2) (rIdx := 15) (rVal := 16)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs5
    (by simp +decide [h25]) (by simp +decide [p_new])
    (by simp +decide [top_old, Succinct.gmSlabTopIdx])
    hbel_lt htop_val_lt (fun y6 hs6 => ?_)
  refine step_gm_const (rDst := 17) (c := 0) (by decide) (by decide) hs6 hfit_0 (fun hs7 => ?_)
  refine step_gm_ite_writeAffine (P := 0 < q_b) (cond := .lt 17 14)
    (rBase := 25) (a := 4) (c := 3) (rIdx := 16) (rVal := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs7
    (by
      change (y6.set 17 0).regs 17 < (y6.set 17 0).regs 14 ↔ 0 < q_b
      rw [hs7.regs_eq 17 (by decide), hs7.regs_eq 14 (by decide)]
      simp +decide [q_b, hq_idx_eq])
    (by simp +decide [h25]) (by simp +decide [top_old, Succinct.gmSlabTopIdx])
    (by simp +decide [p_new]) habv_lt (fun _ => hp_val_lt) (fun y8 hs8 => ?_)
  refine step_gm_ite_write2D (P := q_b < dirSlabsPerBucket N) (cond := .lt 14 20)
    (rBase := 22) (rStride := 20) (rB := rB) (rK := 14) (rVal := 15)
    (by decide) (by decide) (by omega) (by decide) (by decide) hw hN_pos hnU hU hs8
    (by
      change y8.regs 14 < y8.regs 20 ↔ q_b < dirSlabsPerBucket N
      rw [hs8.regs_eq 14 (by decide), hs8.regs_eq 20 (by decide)]
      simp +decide [h20, q_b, hq_idx_eq])
    (by simp +decide [h22]) (by simp +decide [h20]) (by simp [h14, h15, h16, h17, hrB])
    (by simp +decide [q_b, hq_idx_eq]) (by simp +decide [p_new]) hdir_lt (fun _ => hp_val_lt)
    (fun y9 hs9 => ?_)
  refine step_gm_writeBucket (c := 2) (rB := rB) (rVal := 15)
    (by omega) (by decide) hw hN_pos hnU hU hs9
    (by simp [h14, h15, h16, h17, hrB]) (by simp +decide [p_new])
    htop_idx_lt hp_val_lt (fun y10 hs10 => ?_)
  refine step_gm_const (rDst := 17) (c := 1) (by decide) (by decide) hs10 hfit_1 (fun hs11 => ?_)
  refine step_gm_bin (op := .add) (rDst := 18) (rA := 14) (rB := 17) (v := q_b + 1)
    (by decide) (by decide) (by decide) (by decide)
    hs11 (by simp +decide [BinOp.eval, q_b, hq_idx_eq]) hfit_q1 (fun hs12 => ?_)
  refine step_gm_writeBucket (c := 0) (rB := rB) (rVal := 18)
    (by omega) (by decide) hw hN_pos hnU hU hs12
    (by simp [h14, h15, h16, h17, h18, hrB]) (by simp +decide)
    hq_idx_lt hq1_val_lt (fun y13 hs13 => ?_)
  refine step_gm_bin (op := .add) (rDst := 19) (rA := 15) (rB := 17) (v := p_new + 1)
    (by decide) (by decide) (by decide) (by decide)
    hs13 (by simp +decide [BinOp.eval, p_new]) hfit_p1 (fun hs14 => ?_)
  have hdone := done_gm_writeConst (idx := 0) (rVal := 19)
    (by decide) (by decide) hw hN_pos hnU hU hs14 (by simp +decide) hp1_val_lt
  refine hdone.mono (fun z hz => hz.congr_gm ?_) le_rfl
  rw [hownB_eq, hq_idx_eq]
  rfl

theorem done_gm_ite_writeBucket {U V w N c b val : ℕ}
    {P : Prop} [Decidable P] {cond : Cond 280}
    {rB rVal : Fin 280}
    {gm : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    (hrB_ge : 14 ≤ rB.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hcond : BitRAM.CondHolds cond x ↔ P)
    (hrB : rf rB = b) (hrVal : rf rVal = val)
    (hidx : P → 4 + 3 * b + c < globalMetaLen N)
    (hval : P → val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w
      (.branch cond (writeGMBucketRegCode c rB rVal) nopRegCode) x
      (fun z =>
        GMUpdatePost U V w N x z
          (if P then Function.update gm (4 + 3 * b + c) val else gm)) 61 := by
  by_cases hP : P
  · have hc : BitRAM.CondHolds cond x := hcond.mpr hP
    rw [ite_eq_left hP]
    exact dExec_branch_pos hc
      ((writeGMBucketRegCode_gmUpdate hrB_ge hrVal_ge
        hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
        ((hs.regs_eq rB hrB_ge).trans hrB)
        ((hs.regs_eq rVal hrVal_ge).trans hrVal) (hidx hP) (hval hP)).mono
        (fun _ ⟨hpost, _⟩ => hpost.congr_gm (by rw [hs.gm_eq])) le_rfl)
  · have hc : ¬BitRAM.CondHolds cond x := fun h => hP (hcond.mp h)
    rw [ite_eq_right hP]
    exact (dExec_branch_neg hc (nopRegCode_exec rfl)).mono
      (fun y hy => by
        subst hy
        exact ⟨rfl, hs.wf, hs.er, hs.gb, hs.gm_eq, rfl, rfl, rfl,
          fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩) (by omega)

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.gmUnlinkTopSlab N gm b` on
`gmAtBit` (`26 ≤ rB.val`, `T = 270`). -/
@[expose]
def gmUnlinkTopSlabRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMBucketRegCode 0 rB 14)
  (.seq (readGMBucketRegCode 2 rB 15)
  (.seq (readGMAffineRegCode 25 4 2 15 16)
  (.seq (writeGMBucketRegCode 2 rB 16)
  (.seq (.op (.const 17 1))
  (.seq (.op (.bin .sub 18 14 17))
        (writeGMBucketRegCode 0 rB 18))))))

theorem gmUnlinkTopSlabRegCode_exec {U V w N b : ℕ} {rB : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 26 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b)
    (hslab : Succinct.SlabBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N x.mem 0))
    (hq_pos : 1 ≤ gmAtBit U w N x.mem (Succinct.gmQIdx b)) :
    BitRAM.DemonicExecWithin w (gmUnlinkTopSlabRegCode rB) x
      (fun z =>
        GMUpdatePost U V w N x z (Succinct.gmUnlinkTopSlab N (gmAtBit U w N x.mem) b)) 270 := by
  set gm := gmAtBit U w N x.mem
  set q_b := gm (Succinct.gmQIdx b)
  set p_del := gm (Succinct.gmSlabTopIdx b)
  set bel_del := gm (Succinct.gmSlabBelowIdx N p_del)
  have hq_idx_lt : 4 + 3 * b + 0 < globalMetaLen N := by
    simpa [Succinct.gmQIdx] using Succinct.gmQIdx_lt hb_pos hb
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen N := Succinct.gmSlabTopIdx_lt hb_pos hb
  have htop_eq := hslab.top_eq b hb (q_b - 1) (by omega) (by omega)
  have hp_del_lt : p_del < gm 0 := by
    dsimp only [p_del]; rw [htop_eq]; exact hslab.ptr_lt b hb (q_b - 1) (by omega)
  have hp_del_cap : p_del < maxFullSlabs N := lt_of_lt_of_le hp_del_lt hslab.nslabs_le
  have hbel_idx_lt : Succinct.gmSlabMetaBase N + 4 * p_del + 2 < globalMetaLen N :=
    Succinct.gmSlabBelowIdx_lt hb_pos hp_del_cap
  have hbel_val_lt : bel_del < 2 ^ globalPtrBits N :=
    gmAtBit_lt U w N x.mem (Succinct.gmSlabBelowIdx N p_del)
  have hq_val_lt : q_b < 2 ^ globalPtrBits N := gmAtBit_lt U w N x.mem (Succinct.gmQIdx b)
  have hq1_val_lt : q_b - 1 < 2 ^ globalPtrBits N := by omega
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hq_le_p : q_b ≤ gm 0 := Succinct.q_le_nslabs_of_slabBijection hslab hb
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_q1 : Fits w (q_b - 1) := fits_of_le_N hw hnU hU (by have := hslab.nslabs_le; omega)
  have hs0 : GMState U V w N gm x.regs x := GMState.init hx her hgb hsz
  have h25 : x.regs 25 = Succinct.gmSlabMetaBase N := hgb.2.2.2.2.2
  have hrB_ne : ∀ r : Fin 280, r.val < 26 → rB ≠ r := fun _ _ h => by subst h; omega
  have h14 : rB ≠ 14 := hrB_ne 14 (by decide)
  have h15 : rB ≠ 15 := hrB_ne 15 (by decide)
  have h16 : rB ≠ 16 := hrB_ne 16 (by decide)
  have h17 : rB ≠ 17 := hrB_ne 17 (by decide)
  have h18 : rB ≠ 18 := hrB_ne 18 (by decide)
  have hq_idx_eq : 4 + 3 * b + 0 = Succinct.gmQIdx b := by unfold Succinct.gmQIdx; omega
  unfold gmUnlinkTopSlabRegCode Succinct.gmUnlinkTopSlab
  refine step_gm_readBucket (c := 0) (rB := rB) (rDst := 14)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hs0 hrB hq_idx_lt (fun y1 hs1 => ?_)
  refine step_gm_readBucket (c := 2) (rB := rB) (rDst := 15)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hs1
    (by simp [h14, hrB]) htop_idx_lt (fun y2 hs2 => ?_)
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 2) (rIdx := 15) (rDst := 16)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs2 (by simp +decide [h25]) (by simp +decide [p_del, Succinct.gmSlabTopIdx])
    hbel_idx_lt (fun y3 hs3 => ?_)
  refine step_gm_writeBucket (c := 2) (rB := rB) (rVal := 16)
    (by omega) (by decide) hw hN_pos hnU hU hs3
    (by simp [h14, h15, h16, hrB])
    (by simp +decide [bel_del, p_del, Succinct.gmSlabBelowIdx, Succinct.gmSlabTopIdx])
    htop_idx_lt hbel_val_lt (fun y4 hs4 => ?_)
  refine step_gm_const (rDst := 17) (c := 1) (by decide) (by decide) hs4 hfit_1 (fun hs5 => ?_)
  refine step_gm_bin (op := .sub) (rDst := 18) (rA := 14) (rB := 17) (v := q_b - 1)
    (by decide) (by decide) (by decide) (by decide)
    hs5 (by simp +decide [BinOp.eval, q_b, hq_idx_eq]) hfit_q1 (fun hs6 => ?_)
  have hdone := done_gm_writeBucket (c := 0) (rB := rB) (rVal := 18)
    (by omega) (by decide) hw hN_pos hnU hU hs6
    (by simp [h14, h15, h16, h17, h18, hrB]) (by simp +decide) hq_idx_lt hq1_val_lt
  refine hdone.mono (fun z hz => hz.congr_gm ?_) le_rfl
  rw [hq_idx_eq]
  rfl

/-! ## Section 3: `gmRelinkMovedSlabRegCode`, `gmLinkMovedNeighborsRegCode`, `gmCompactSlabRegCode`,
and `gmPopSlabRegCode` -/

/-- Pure bounds invariant for `gmRelinkMovedSlabRegCode` and `gmLinkMovedNeighborsRegCode`. -/
@[expose]
def GmMovedSlabBitInv (N p_del p_last : ℕ) (gm : ℕ → ℕ) : Prop :=
  let b_last := gm (Succinct.gmSlabOwnerBIdx N p_last)
  let s_last := gm (Succinct.gmSlabOwnerSIdx N p_last)
  let bel_last := gm (Succinct.gmSlabBelowIdx N p_last)
  let abv_last := gm (Succinct.gmSlabAboveIdx N p_last)
  let q_last := gm (Succinct.gmQIdx b_last)
  p_del < maxFullSlabs N ∧
  p_last < maxFullSlabs N ∧
  b_last < numBuckets N ∧
  s_last + 1 ≤ N ∧
  (0 < s_last → bel_last < maxFullSlabs N) ∧
  (s_last + 1 < q_last → abv_last < maxFullSlabs N)

/-- Uniform `BitRAM.Code .standard 280` program executing
`Succinct.gmRelinkMovedSlab N gm p_del p_last` (`26 ≤ rPDel.val`, `26 ≤ rPLast.val`, `T = 272`). -/
@[expose]
def gmRelinkMovedSlabRegCode (rPDel rPLast : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMAffineRegCode 25 4 0 rPLast 14)
  (.seq (readGMAffineRegCode 25 4 1 rPLast 15)
  (.seq (readGMBucketRegCode 0 14 16)
  (.seq (.branch (.lt 15 20) (writeGM2DRegCode 22 20 14 15 rPDel) nopRegCode)
  (.seq (.op (.const 17 1))
  (.seq (.op (.bin .add 17 15 17))
        (.branch (.eq 17 16) (writeGMBucketRegCode 2 14 rPDel) nopRegCode))))))

theorem gmRelinkMovedSlabRegCode_exec {U V w N p_del p_last : ℕ}
    {rPDel rPLast : Fin 280} {x : BitRAM.Data 280}
    (hrPDel_ge : 26 ≤ rPDel.val) (hrPLast_ge : 26 ≤ rPLast.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrPDel : x.regs rPDel = p_del) (hrPLast : x.regs rPLast = p_last)
    (hinv : GmMovedSlabBitInv N p_del p_last (gmAtBit U w N x.mem)) :
    BitRAM.DemonicExecWithin w (gmRelinkMovedSlabRegCode rPDel rPLast) x
      (fun z =>
        GMUpdatePost U V w N x z
          (Succinct.gmRelinkMovedSlab N (gmAtBit U w N x.mem) p_del p_last)) 272 := by
  rcases hinv with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, _, _⟩
  set gm := gmAtBit U w N x.mem
  set b_last := gm (Succinct.gmSlabOwnerBIdx N p_last)
  set s_last := gm (Succinct.gmSlabOwnerSIdx N p_last)
  set q_last := gm (Succinct.gmQIdx b_last)
  have hownB_lt : Succinct.gmSlabMetaBase N + 4 * p_last + 0 < globalMetaLen N := by
    simpa [Succinct.gmSlabOwnerBIdx] using Succinct.gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_lt : Succinct.gmSlabMetaBase N + 4 * p_last + 1 < globalMetaLen N :=
    Succinct.gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hq_lt : 4 + 3 * b_last + 0 < globalMetaLen N := by
    simpa [Succinct.gmQIdx] using Succinct.gmQIdx_lt hb_pos hb_last
  have hdir_lt : s_last < dirSlabsPerBucket N →
      Succinct.gmSlabDirBase N + b_last * dirSlabsPerBucket N + s_last < globalMetaLen N :=
    fun hdir => Succinct.gmSlabDirIdx_lt hb_pos hb_last hdir
  have htop_lt : s_last + 1 = q_last → 4 + 3 * b_last + 2 < globalMetaLen N :=
    fun _ => Succinct.gmSlabTopIdx_lt hb_pos hb_last
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val_lt : p_del < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_s1 : Fits w (s_last + 1) := fits_of_le_N hw hnU hU (hs_le.trans (Nat.le_max_left N 1))
  have hs0 : GMState U V w N gm x.regs x := GMState.init hx her hgb hsz
  have h20 : x.regs 20 = dirSlabsPerBucket N := hgb.1
  have h22 : x.regs 22 = Succinct.gmSlabDirBase N := hgb.2.2.1
  have h25 : x.regs 25 = Succinct.gmSlabMetaBase N := hgb.2.2.2.2.2
  have hPLast_ne : ∀ r : Fin 280, r.val < 26 → rPLast ≠ r := fun _ _ h => by subst h; omega
  have hPDel_ne : ∀ r : Fin 280, r.val < 26 → rPDel ≠ r := fun _ _ h => by subst h; omega
  have hownB_eq : Succinct.gmSlabMetaBase N + 4 * p_last + 0 =
      Succinct.gmSlabOwnerBIdx N p_last := by unfold Succinct.gmSlabOwnerBIdx; omega
  have hq_eq : 4 + 3 * b_last + 0 = Succinct.gmQIdx b_last := by unfold Succinct.gmQIdx; omega
  unfold gmRelinkMovedSlabRegCode Succinct.gmRelinkMovedSlab
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 0) (rIdx := rPLast) (rDst := 14)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs0 (by simp +decide [h25]) hrPLast hownB_lt (fun y1 hs1 => ?_)
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 1) (rIdx := rPLast) (rDst := 15)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs1 (by simp +decide [h25])
    (by simp [hPLast_ne 14 (by decide), hrPLast]) hownS_lt (fun y2 hs2 => ?_)
  refine step_gm_readBucket (c := 0) (rB := 14) (rDst := 16)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs2
    (by simp +decide [b_last, hownB_eq]) hq_lt (fun y3 hs3 => ?_)
  refine step_gm_ite_write2D (P := s_last < dirSlabsPerBucket N) (cond := .lt 15 20)
    (rBase := 22) (rStride := 20) (rB := 14) (rK := 15) (rVal := rPDel)
    (by decide) (by decide) (by decide) (by decide) (by omega) hw hN_pos hnU hU hs3
    (by
      change y3.regs 15 < y3.regs 20 ↔ s_last < dirSlabsPerBucket N
      rw [hs3.regs_eq 15 (by decide), hs3.regs_eq 20 (by decide)]
      simp +decide [h20, s_last, Succinct.gmSlabOwnerSIdx])
    (by simp +decide [h22]) (by simp +decide [h20]) (by simp +decide [b_last, hownB_eq])
    (by simp +decide [s_last, Succinct.gmSlabOwnerSIdx])
    (by simp [hPDel_ne 16 (by decide), hPDel_ne 15 (by decide), hPDel_ne 14 (by decide), hrPDel])
    hdir_lt (fun _ => hp_del_val_lt) (fun y4 hs4 => ?_)
  refine step_gm_const (rDst := 17) (c := 1) (by decide) (by decide) hs4 hfit_1 (fun hs5 => ?_)
  refine step_gm_bin (op := .add) (rDst := 17) (rA := 15) (rB := 17) (v := s_last + 1)
    (by decide) (by decide) (by decide) (by decide)
    hs5 (by simp +decide [BinOp.eval, s_last, Succinct.gmSlabOwnerSIdx]) hfit_s1 (fun hs6 => ?_)
  exact done_gm_ite_writeBucket (P := s_last + 1 = q_last) (cond := .eq 17 16)
    (c := 2) (rB := 14) (rVal := rPDel)
    (by decide) (by omega) hw hN_pos hnU hU hs6
    (by
      change ((y4.set 17 1).set 17 (s_last + 1)).regs 17 =
        ((y4.set 17 1).set 17 (s_last + 1)).regs 16 ↔ s_last + 1 = q_last
      rw [hs6.regs_eq 17 (by decide), hs6.regs_eq 16 (by decide)]
      simp +decide [q_last, b_last, hq_eq, hownB_eq])
    (by simp +decide [b_last, hownB_eq])
    (by
      simp [hPDel_ne 17 (by decide), hPDel_ne 16 (by decide), hPDel_ne 15 (by decide),
        hPDel_ne 14 (by decide), hrPDel])
    htop_lt (fun _ => hp_del_val_lt)

/-- Uniform `BitRAM.Code .standard 280` program executing
`Succinct.gmLinkMovedNeighbors N gm p_del p_last` (`26 ≤ rPDel.val`, `26 ≤ rPLast.val`,
`T = 616`). -/
@[expose]
def gmLinkMovedNeighborsRegCode (rPDel rPLast : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMAffineRegCode 25 4 0 rPLast 14)
  (.seq (readGMAffineRegCode 25 4 1 rPLast 15)
  (.seq (readGMAffineRegCode 25 4 2 rPLast 16)
  (.seq (readGMAffineRegCode 25 4 3 rPLast 17)
  (.seq (readGMBucketRegCode 0 14 18)
  (.seq (.op (.const 19 0))
  (.seq (.branch (.lt 19 15) (writeGMAffineRegCode 25 4 3 16 rPDel) nopRegCode)
  (.seq (.op (.const 19 1))
  (.seq (.op (.bin .add 19 15 19))
  (.seq (.branch (.lt 19 18) (writeGMAffineRegCode 25 4 2 17 rPDel) nopRegCode)
  (.seq (writeGMAffineRegCode 25 4 0 rPDel 14)
  (.seq (writeGMAffineRegCode 25 4 1 rPDel 15)
  (.seq (writeGMAffineRegCode 25 4 2 rPDel 16)
        (writeGMAffineRegCode 25 4 3 rPDel 17)))))))))))))

theorem gmLinkMovedNeighborsRegCode_exec {U V w N p_del p_last : ℕ}
    {rPDel rPLast : Fin 280} {x : BitRAM.Data 280}
    (hrPDel_ge : 26 ≤ rPDel.val) (hrPLast_ge : 26 ≤ rPLast.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrPDel : x.regs rPDel = p_del) (hrPLast : x.regs rPLast = p_last)
    (hinv : GmMovedSlabBitInv N p_del p_last (gmAtBit U w N x.mem)) :
    BitRAM.DemonicExecWithin w (gmLinkMovedNeighborsRegCode rPDel rPLast) x
      (fun z =>
        GMUpdatePost U V w N x z
          (Succinct.gmLinkMovedNeighbors N (gmAtBit U w N x.mem) p_del p_last)) 620 := by
  rcases hinv with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap⟩
  set gm := gmAtBit U w N x.mem
  set b_last := gm (Succinct.gmSlabOwnerBIdx N p_last)
  set s_last := gm (Succinct.gmSlabOwnerSIdx N p_last)
  set bel_last := gm (Succinct.gmSlabBelowIdx N p_last)
  set abv_last := gm (Succinct.gmSlabAboveIdx N p_last)
  set q_last := gm (Succinct.gmQIdx b_last)
  have hownB_last_lt : Succinct.gmSlabMetaBase N + 4 * p_last + 0 < globalMetaLen N := by
    simpa [Succinct.gmSlabOwnerBIdx] using Succinct.gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last_lt : Succinct.gmSlabMetaBase N + 4 * p_last + 1 < globalMetaLen N :=
    Succinct.gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_last_lt : Succinct.gmSlabMetaBase N + 4 * p_last + 2 < globalMetaLen N :=
    Succinct.gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_last_lt : Succinct.gmSlabMetaBase N + 4 * p_last + 3 < globalMetaLen N :=
    Succinct.gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hq_last_lt : 4 + 3 * b_last + 0 < globalMetaLen N := by
    simpa [Succinct.gmQIdx] using Succinct.gmQIdx_lt hb_pos hb_last
  have hownB_del_lt : Succinct.gmSlabMetaBase N + 4 * p_del + 0 < globalMetaLen N := by
    simpa [Succinct.gmSlabOwnerBIdx] using Succinct.gmSlabOwnerBIdx_lt hb_pos hp_del_cap
  have hownS_del_lt : Succinct.gmSlabMetaBase N + 4 * p_del + 1 < globalMetaLen N :=
    Succinct.gmSlabOwnerSIdx_lt hb_pos hp_del_cap
  have hbel_del_lt : Succinct.gmSlabMetaBase N + 4 * p_del + 2 < globalMetaLen N :=
    Succinct.gmSlabBelowIdx_lt hb_pos hp_del_cap
  have habv_del_lt : Succinct.gmSlabMetaBase N + 4 * p_del + 3 < globalMetaLen N :=
    Succinct.gmSlabAboveIdx_lt hb_pos hp_del_cap
  have habv_bel_lt : 0 < s_last →
      Succinct.gmSlabMetaBase N + 4 * bel_last + 3 < globalMetaLen N :=
    fun hs => Succinct.gmSlabAboveIdx_lt hb_pos (hbel_cap hs)
  have hbel_abv_lt : s_last + 1 < q_last →
      Succinct.gmSlabMetaBase N + 4 * abv_last + 2 < globalMetaLen N :=
    fun hs => Succinct.gmSlabBelowIdx_lt hb_pos (habv_cap hs)
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val_lt : p_del < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hb_val_lt : b_last < 2 ^ globalPtrBits N := gmAtBit_lt U w N x.mem _
  have hs_val_lt : s_last < 2 ^ globalPtrBits N := gmAtBit_lt U w N x.mem _
  have hbel_val_lt : bel_last < 2 ^ globalPtrBits N := gmAtBit_lt U w N x.mem _
  have habv_val_lt : abv_last < 2 ^ globalPtrBits N := gmAtBit_lt U w N x.mem _
  have hfit_0 : Fits w 0 := fits_of_le_N hw hnU hU (by omega)
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_s1 : Fits w (s_last + 1) := fits_of_le_N hw hnU hU (hs_le.trans (Nat.le_max_left N 1))
  have hs0 : GMState U V w N gm x.regs x := GMState.init hx her hgb hsz
  have h25 : x.regs 25 = Succinct.gmSlabMetaBase N := hgb.2.2.2.2.2
  have hPLast_ne : ∀ r : Fin 280, r.val < 26 → rPLast ≠ r := fun _ _ h => by subst h; omega
  have hPDel_ne : ∀ r : Fin 280, r.val < 26 → rPDel ≠ r := fun _ _ h => by subst h; omega
  have hPL14 : rPLast ≠ 14 := hPLast_ne 14 (by decide)
  have hPL15 : rPLast ≠ 15 := hPLast_ne 15 (by decide)
  have hPL16 : rPLast ≠ 16 := hPLast_ne 16 (by decide)
  have hPD14 : rPDel ≠ 14 := hPDel_ne 14 (by decide)
  have hPD15 : rPDel ≠ 15 := hPDel_ne 15 (by decide)
  have hPD16 : rPDel ≠ 16 := hPDel_ne 16 (by decide)
  have hPD17 : rPDel ≠ 17 := hPDel_ne 17 (by decide)
  have hPD18 : rPDel ≠ 18 := hPDel_ne 18 (by decide)
  have hPD19 : rPDel ≠ 19 := hPDel_ne 19 (by decide)
  have hownB_last_eq : Succinct.gmSlabMetaBase N + 4 * p_last + 0 =
      Succinct.gmSlabOwnerBIdx N p_last := by unfold Succinct.gmSlabOwnerBIdx; omega
  have hownB_del_eq : Succinct.gmSlabMetaBase N + 4 * p_del + 0 =
      Succinct.gmSlabOwnerBIdx N p_del := by unfold Succinct.gmSlabOwnerBIdx; omega
  have hq_eq : 4 + 3 * b_last + 0 = Succinct.gmQIdx b_last := by unfold Succinct.gmQIdx; omega
  unfold gmLinkMovedNeighborsRegCode Succinct.gmLinkMovedNeighbors
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 0) (rIdx := rPLast) (rDst := 14)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs0 (by simp +decide [h25]) hrPLast hownB_last_lt (fun y1 hs1 => ?_)
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 1) (rIdx := rPLast) (rDst := 15)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs1 (by simp +decide [h25]) (by simp [hPL14, hrPLast]) hownS_last_lt
    (fun y2 hs2 => ?_)
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 2) (rIdx := rPLast) (rDst := 16)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs2 (by simp +decide [h25]) (by simp [hPL14, hPL15, hrPLast]) hbel_last_lt
    (fun y3 hs3 => ?_)
  refine step_gm_readAffine (rBase := 25) (a := 4) (c := 3) (rIdx := rPLast) (rDst := 17)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs3 (by simp +decide [h25]) (by simp [hPL14, hPL15, hPL16, hrPLast])
    habv_last_lt (fun y4 hs4 => ?_)
  refine step_gm_readBucket (c := 0) (rB := 14) (rDst := 18)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs4
    (by simp +decide [b_last, hownB_last_eq]) hq_last_lt (fun y5 hs5 => ?_)
  refine step_gm_const (rDst := 19) (c := 0) (by decide) (by decide) hs5 hfit_0 (fun hs6 => ?_)
  refine step_gm_ite_writeAffine (P := 0 < s_last) (cond := .lt 19 15)
    (rBase := 25) (a := 4) (c := 3) (rIdx := 16) (rVal := rPDel)
    (by decide) (by decide) (by omega) (by decide) (by decide) hw hN_pos hnU hU hs6
    (by
      change (y5.set 19 0).regs 19 < (y5.set 19 0).regs 15 ↔ 0 < s_last
      rw [hs6.regs_eq 19 (by decide), hs6.regs_eq 15 (by decide)]
      simp +decide [s_last, Succinct.gmSlabOwnerSIdx])
    (by simp +decide [h25]) (by simp +decide [bel_last, Succinct.gmSlabBelowIdx])
    (by simp [hPD14, hPD15, hPD16, hPD17, hPD18, hPD19, hrPDel])
    habv_bel_lt (fun _ => hp_del_val_lt) (fun y7 hs7 => ?_)
  refine step_gm_const (rDst := 19) (c := 1) (by decide) (by decide) hs7 hfit_1 (fun hs8 => ?_)
  refine step_gm_bin (op := .add) (rDst := 19) (rA := 15) (rB := 19) (v := s_last + 1)
    (by decide) (by decide) (by decide) (by decide)
    hs8 (by simp +decide [BinOp.eval, s_last, Succinct.gmSlabOwnerSIdx]) hfit_s1 (fun hs9 => ?_)
  refine step_gm_ite_writeAffine (P := s_last + 1 < q_last) (cond := .lt 19 18)
    (rBase := 25) (a := 4) (c := 2) (rIdx := 17) (rVal := rPDel)
    (by decide) (by decide) (by omega) (by decide) (by decide) hw hN_pos hnU hU hs9
    (by
      change ((y7.set 19 1).set 19 (s_last + 1)).regs 19 <
        ((y7.set 19 1).set 19 (s_last + 1)).regs 18 ↔ s_last + 1 < q_last
      rw [hs9.regs_eq 19 (by decide), hs9.regs_eq 18 (by decide)]
      simp +decide [q_last, b_last, hq_eq, hownB_last_eq])
    (by simp +decide [h25]) (by simp +decide [abv_last, Succinct.gmSlabAboveIdx])
    (by simp [hPD14, hPD15, hPD16, hPD17, hPD18, hPD19, hrPDel])
    hbel_abv_lt (fun _ => hp_del_val_lt) (fun y10 hs10 => ?_)
  refine step_gm_writeAffine (rBase := 25) (a := 4) (c := 0) (rIdx := rPDel) (rVal := 14)
    (by decide) (by omega) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs10
    (by simp +decide [h25]) (by simp [hPD14, hPD15, hPD16, hPD17, hPD18, hPD19, hrPDel])
    (by simp +decide [b_last, hownB_last_eq]) hownB_del_lt hb_val_lt (fun y11 hs11 => ?_)
  refine step_gm_writeAffine (rBase := 25) (a := 4) (c := 1) (rIdx := rPDel) (rVal := 15)
    (by decide) (by omega) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs11
    (by simp +decide [h25]) (by simp [hPD14, hPD15, hPD16, hPD17, hPD18, hPD19, hrPDel])
    (by simp +decide [s_last, Succinct.gmSlabOwnerSIdx]) hownS_del_lt hs_val_lt
    (fun y12 hs12 => ?_)
  refine step_gm_writeAffine (rBase := 25) (a := 4) (c := 2) (rIdx := rPDel) (rVal := 16)
    (by decide) (by omega) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs12
    (by simp +decide [h25]) (by simp [hPD14, hPD15, hPD16, hPD17, hPD18, hPD19, hrPDel])
    (by simp +decide [bel_last, Succinct.gmSlabBelowIdx]) hbel_del_lt hbel_val_lt
    (fun y13 hs13 => ?_)
  have hdone := done_gm_writeAffine (rBase := 25) (a := 4) (c := 3) (rIdx := rPDel) (rVal := 17)
    (by decide) (by omega) (by decide) (by decide) (by decide) hw hN_pos hnU hU hs13
    (by simp +decide [h25]) (by simp [hPD14, hPD15, hPD16, hPD17, hPD18, hPD19, hrPDel])
    (by simp +decide [abv_last, Succinct.gmSlabAboveIdx]) habv_del_lt habv_val_lt
  refine hdone.mono (fun z hz => hz.congr_gm ?_) le_rfl
  rw [hownB_del_eq]
  rfl


/-- Pure bounds invariant for `gmCompactSlabRegCode`. -/
@[expose]
def GmCompactSlabBitInv (N p_del : ℕ) (gm : ℕ → ℕ) : Prop :=
  let p_last := gm 0 - 1
  1 ≤ gm 0 ∧
  gm 0 ≤ maxFullSlabs N ∧
  p_del < gm 0 ∧
  (p_del < p_last → GmMovedSlabBitInv N p_del p_last gm)

theorem gmMovedSlabBitInv_after_relink {N p_del p_last : ℕ} {gm : ℕ → ℕ}
    (hinv : GmMovedSlabBitInv N p_del p_last gm) :
    GmMovedSlabBitInv N p_del p_last (Succinct.gmRelinkMovedSlab N gm p_del p_last) := by
  rcases hinv with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap⟩
  rcases Succinct.gmRelinkMovedSlab_preserves_meta gm (p_del := p_del) hb_last with
    ⟨_, hpQ, hpGe⟩
  have hB : Succinct.gmSlabMetaBase N ≤ Succinct.gmSlabOwnerBIdx N p_last := by
    unfold Succinct.gmSlabOwnerBIdx; omega
  have hS : Succinct.gmSlabMetaBase N ≤ Succinct.gmSlabOwnerSIdx N p_last := by
    unfold Succinct.gmSlabOwnerSIdx; omega
  have hBel : Succinct.gmSlabMetaBase N ≤ Succinct.gmSlabBelowIdx N p_last := by
    unfold Succinct.gmSlabBelowIdx; omega
  have hAbv : Succinct.gmSlabMetaBase N ≤ Succinct.gmSlabAboveIdx N p_last := by
    unfold Succinct.gmSlabAboveIdx; omega
  unfold GmMovedSlabBitInv
  dsimp only
  rw [hpGe _ hB, hpGe _ hS, hpGe _ hBel, hpGe _ hAbv, hpQ]
  exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap⟩

/-- Postcondition for `gmCompactSlabRegCode` and `gmPopSlabRegCode` (uses registers `26, 27` as
scratch and preserves all registers `r ≥ 28`). -/
@[expose]
def GMUpdatePost28 (U V w N : ℕ) (x y : BitRAM.Data 280) (gm' : ℕ → ℕ) : Prop :=
  y.bitSize = x.bitSize ∧
  y.WellFormed w ∧
  EpochRegs U V w N y ∧
  GMBasesLoaded N y ∧
  gmAtBit U w N y.mem = gm' ∧
  lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
  tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
  dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
  (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
  (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
      denseQuotAt U V w N x.toBitMemoryState d ∧
    denseValAt U V w N y.toBitMemoryState d =
      denseValAt U V w N x.toBitMemoryState d) ∧
  (∀ r : Fin 280, 28 ≤ r.val → y.regs r = x.regs r)

theorem GMUpdatePost.to28 {U V w N : ℕ} {x y : BitRAM.Data 280} {gm' : ℕ → ℕ}
    (h : GMUpdatePost U V w N x y gm') :
    GMUpdatePost28 U V w N x y gm' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun r hr => h11 r (by omega)⟩

theorem GMUpdatePost28.congr_gm {U V w N : ℕ} {x y : BitRAM.Data 280} {gm₁ gm₂ : ℕ → ℕ}
    (h : GMUpdatePost28 U V w N x y gm₁) (heq : gm₁ = gm₂) :
    GMUpdatePost28 U V w N x y gm₂ := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact ⟨h1, h2, h3, h4, h5.trans heq, h6, h7, h8, h9, h10, h11⟩

theorem GMUpdatePost28.trans {U V w N : ℕ} {x y z : BitRAM.Data 280} {gm₁ gm₂ : ℕ → ℕ}
    (hxy : GMUpdatePost28 U V w N x y gm₁) (hyz : GMUpdatePost28 U V w N y z gm₂) :
    GMUpdatePost28 U V w N x z gm₂ := by
  rcases hxy with ⟨hxy_sz, _, _, _, _, hxy_lm, hxy_td, hxy_dt, hxy_out, hxy_items, hxy_regs⟩
  rcases hyz with ⟨hyz_sz, hyz_wf, hyz_er, hyz_gb, hyz_gm, hyz_lm, hyz_td, hyz_dt,
    hyz_out, hyz_items, hyz_regs⟩
  refine ⟨hyz_sz.trans hxy_sz, hyz_wf, hyz_er, hyz_gb, hyz_gm,
    hyz_lm.trans hxy_lm, hyz_td.trans hxy_td, hyz_dt.trans hxy_dt,
    fun a ha => (hyz_out a ha).trans (hxy_out a ha),
    fun d => ⟨(hyz_items d).1.trans (hxy_items d).1, (hyz_items d).2.trans (hxy_items d).2⟩,
    fun r hr => (hyz_regs r hr).trans (hxy_regs r hr)⟩

theorem GMUpdatePost28.of_state_eq {U V w N : ℕ} {x y z : BitRAM.Data 280} {gm' : ℕ → ℕ}
    (hst : y.toBitMemoryState = x.toBitMemoryState)
    (hregs : ∀ r : Fin 280, 28 ≤ r.val → y.regs r = x.regs r)
    (hyz : GMUpdatePost28 U V w N y z gm') :
    GMUpdatePost28 U V w N x z gm' := by
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  rcases hyz with ⟨hyz_sz, hyz_wf, hyz_er, hyz_gb, hyz_gm, hyz_lm, hyz_td, hyz_dt,
    hyz_out, hyz_items, hyz_regs⟩
  refine ⟨hyz_sz.trans hsz, hyz_wf, hyz_er, hyz_gb, hyz_gm,
    hyz_lm.trans (by rw [hmem]), hyz_td.trans (by rw [hmem]), hyz_dt.trans (by rw [hmem]),
    fun a ha => (hyz_out a ha).trans (congrFun hmem a),
    fun d => ⟨(hyz_items d).1.trans (by rw [hst]), (hyz_items d).2.trans (by rw [hst])⟩,
    fun r hr => (hyz_regs r hr).trans (hregs r hr)⟩

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.gmCompactSlab N gm p_del`
(`rPDel = 26`, using register `27` for `p_last`, preserving all registers `28 ≤ r.val`,
`T = 999`). -/
@[expose]
def gmCompactSlabRegCode (rPDel : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMConstRegCode 0 14)
  (.seq (.op (.const 15 1))
  (.seq (.op (.bin .sub 27 14 15))
        (.branch (.lt rPDel 27)
          (.seq (gmRelinkMovedSlabRegCode rPDel 27)
          (.seq (gmLinkMovedNeighborsRegCode rPDel 27)
                (writeGMConstRegCode 0 27)))
          (writeGMConstRegCode 0 27))))

theorem gmCompactSlabRegCode_exec {U V w N p_del : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hr26 : x.regs 26 = p_del)
    (hinv : GmCompactSlabBitInv N p_del (gmAtBit U w N x.mem)) :
    BitRAM.DemonicExecWithin w (gmCompactSlabRegCode 26) x
      (fun z =>
        GMUpdatePost28 U V w N x z (Succinct.gmCompactSlab N (gmAtBit U w N x.mem) p_del)) 999 := by
  rcases hinv with ⟨h0_pos, h0_le, _, hcond⟩
  set gm := gmAtBit U w N x.mem
  set p_last := gm 0 - 1
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_last_val_lt : p_last < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_plast : Fits w p_last := fits_of_le_N hw hnU hU (by omega)
  unfold gmCompactSlabRegCode
  refine .seq (T₁ := 46) (T₂ := 953)
    (readGMConstRegCode_exec (idx := 0) (rDst := 14) (by decide) (by decide) (by decide)
      hw hN_pos hnU hU hx her hsz)
    (fun y1 ⟨hst1, hy1_wf, hy1_er, h14, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hst1
  have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
    have h : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst1
    omega
  have hy1_gb : GMBasesLoaded N y1 :=
    hgb.congr_regs (fun r hr1 _ => hy1_regs r (by omega) (by intro h; subst h; omega))
  have hy1_26 : y1.regs 26 = p_del := by rw [hy1_regs 26 (by decide) (by decide), hr26]
  refine DemonicExecWithin.step_const (T := 952) hfit_1 ?_
  refine step_dExec_bin (v := p_last) (T := 951)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, h14, p_last, gm]) hfit_plast ?_
  set y3 := (y1.set 15 1).set 27 p_last
  have hy3_st : y3.toBitMemoryState = x.toBitMemoryState := hst1
  have hy3_mem : y3.mem = x.mem := hy1_mem
  have hy3_wf : y3.WellFormed w := wf_set 27 (wf_set 15 hy1_wf hfit_1) hfit_plast
  have hy3_er : EpochRegs U V w N y3 :=
    hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [y3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hy3_gb : GMBasesLoaded N y3 :=
    hy1_gb.congr_regs (fun r hr1 _ => by
      dsimp only [y3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hy3_26 : y3.regs 26 = p_del := by simp +decide [y3, BitRAM.Data.set, hy1_26]
  have hy3_27 : y3.regs 27 = p_last := by simp +decide [y3, BitRAM.Data.set]
  have hy3_regs : ∀ r : Fin 280, 28 ≤ r.val → y3.regs r = x.regs r := by
    intro r hr
    dsimp only [y3, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)
  by_cases hlt : p_del < p_last
  · have hc : BitRAM.CondHolds (.lt 26 27) y3 := by
      change y3.regs 26 < y3.regs 27
      rw [hy3_26, hy3_27]
      exact hlt
    refine dExec_branch_pos (T := 950) hc ?_
    have hm1 : GmMovedSlabBitInv N p_del p_last (gmAtBit U w N y3.mem) := by
      rw [hy3_mem]; exact hcond hlt
    refine .seq (T₁ := 272) (T₂ := 677)
      (gmRelinkMovedSlabRegCode_exec (rPDel := 26) (rPLast := 27)
        (by decide) (by decide) hw hN_pos hnU hU hb_pos
        hy3_wf hy3_er hy3_gb hy1_sz hy3_26 hy3_27 hm1)
      (fun y4 hy4 => ?_) (by omega)
    have hm2 : GmMovedSlabBitInv N p_del p_last (gmAtBit U w N y4.mem) := by
      rw [hy4.2.2.2.2.1, hy3_mem]; exact gmMovedSlabBitInv_after_relink (hcond hlt)
    refine .seq (T₁ := 620) (T₂ := 57)
      (gmLinkMovedNeighborsRegCode_exec (rPDel := 26) (rPLast := 27)
        (by decide) (by decide) hw hN_pos hnU hU hb_pos
        hy4.2.1 hy4.2.2.1 hy4.2.2.2.1 (hy4.1.symm ▸ hy1_sz)
        (by rw [hy4.2.2.2.2.2.2.2.2.2.2 26 (by decide), hy3_26])
        (by rw [hy4.2.2.2.2.2.2.2.2.2.2 27 (by decide), hy3_27]) hm2)
      (fun y5 hy5 => ?_) (by omega)
    have h45 : GMUpdatePost U V w N y3 y5
        (Succinct.gmLinkMovedNeighbors N
          (Succinct.gmRelinkMovedSlab N (gmAtBit U w N y3.mem) p_del p_last) p_del p_last) :=
      hy4.trans (hy5.congr_gm (by rw [hy4.2.2.2.2.1]))
    have hy5_27 : y5.regs 27 = p_last := by
      rw [h45.2.2.2.2.2.2.2.2.2.2 27 (by decide), hy3_27]
    exact (writeGMConstRegCode_gmUpdate (idx := 0) (rVal := 27) (by decide) (by decide)
      hw hN_pos hnU hU hy5.2.1 hy5.2.2.1 hy5.2.2.2.1 (h45.1.symm ▸ hy1_sz)
      hy5_27 hp_last_val_lt).mono
      (fun z ⟨hz, _⟩ => by
        have h3z := h45.to28.trans (hz.to28.congr_gm (by rw [h45.2.2.2.2.1, hy3_mem]))
        exact (GMUpdatePost28.of_state_eq hy3_st hy3_regs h3z).congr_gm
          (Succinct.gmCompactSlab_eq_parts gm hlt (hcond hlt).2.2.1)) le_rfl
  · have hc : ¬BitRAM.CondHolds (.lt 26 27) y3 := by
      change ¬y3.regs 26 < y3.regs 27
      rw [hy3_26, hy3_27]
      exact hlt
    refine (dExec_branch_neg (T := 57) hc
      (writeGMConstRegCode_gmUpdate (idx := 0) (rVal := 27) (by decide) (by decide)
        hw hN_pos hnU hU hy3_wf hy3_er hy3_gb hy1_sz hy3_27 hp_last_val_lt)).mono
      (fun z ⟨hz, _⟩ => by
        have h3z := hz.to28.congr_gm (by rw [hy3_mem])
        refine (GMUpdatePost28.of_state_eq hy3_st hy3_regs h3z).congr_gm ?_
        unfold Succinct.gmCompactSlab
        rw [ite_eq_right hlt]) (by omega)

theorem gmCompactSlabBitInv_of_slabBijection {N b : ℕ} {gm : ℕ → ℕ}
    (hb : b < numBuckets N)
    (hslab : Succinct.SlabBijection N gm (fun b' => gm (Succinct.gmQIdx b')) (gm 0))
    (hq_pos : 1 ≤ gm (Succinct.gmQIdx b)) :
    GmCompactSlabBitInv N (gm (Succinct.gmSlabTopIdx b))
      (Succinct.gmUnlinkTopSlab N gm b) := by
  rcases Succinct.gmUnlinkTopSlab_fields gm hb with ⟨hu0, _, _, huQ, _, huGe, _⟩
  have hB_ge : ∀ p, Succinct.gmSlabDirBase N ≤ Succinct.gmSlabOwnerBIdx N p :=
    fun _ => by
      unfold Succinct.gmSlabOwnerBIdx Succinct.gmSlabMetaBase Succinct.gmTailOwnerBase
        Succinct.gmTailPtrBase
      omega
  have hS_ge : ∀ p, Succinct.gmSlabDirBase N ≤ Succinct.gmSlabOwnerSIdx N p :=
    fun _ => by
      unfold Succinct.gmSlabOwnerSIdx Succinct.gmSlabMetaBase Succinct.gmTailOwnerBase
        Succinct.gmTailPtrBase
      omega
  have hBel_ge : ∀ p, Succinct.gmSlabDirBase N ≤ Succinct.gmSlabBelowIdx N p :=
    fun _ => by
      unfold Succinct.gmSlabBelowIdx Succinct.gmSlabMetaBase Succinct.gmTailOwnerBase
        Succinct.gmTailPtrBase
      omega
  have hAbv_ge : ∀ p, Succinct.gmSlabDirBase N ≤ Succinct.gmSlabAboveIdx N p :=
    fun _ => by
      unfold Succinct.gmSlabAboveIdx Succinct.gmSlabMetaBase Succinct.gmTailOwnerBase
        Succinct.gmTailPtrBase
      omega
  have htop_eq := hslab.top_eq b hb (gm (Succinct.gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : gm (Succinct.gmSlabTopIdx b) < gm 0 := by
    rw [htop_eq]; exact hslab.ptr_lt b hb (gm (Succinct.gmQIdx b) - 1) (by omega)
  unfold GmCompactSlabBitInv GmMovedSlabBitInv
  dsimp only
  rw [hu0]
  refine ⟨by omega, hslab.nslabs_le, hp_del_lt, ?_⟩
  intro hlt
  rw [huGe _ (hB_ge _), huGe _ (hS_ge _), huGe _ (hBel_ge _), huGe _ (hAbv_ge _)]
  obtain ⟨hb_last, hs_last, hptr_last⟩ := hslab.owner_valid (gm 0 - 1) (by omega)
  have hq_last_le : gm (Succinct.gmQIdx (gm (Succinct.gmSlabOwnerBIdx N (gm 0 - 1)))) ≤ gm 0 :=
    Succinct.q_le_nslabs_of_slabBijection hslab hb_last
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  refine ⟨lt_of_lt_of_le hp_del_lt hslab.nslabs_le,
    lt_of_lt_of_le (by omega : gm 0 - 1 < gm 0) hslab.nslabs_le,
    hb_last, by have := hslab.nslabs_le; omega, ?_, ?_⟩
  · intro hs_pos
    have hbel_eq := hslab.below_eq _ hb_last _ hs_last hs_pos
    rw [hptr_last] at hbel_eq
    rw [hbel_eq]
    exact lt_of_lt_of_le (hslab.ptr_lt _ hb_last _ (by omega)) hslab.nslabs_le
  · intro hs_lt_q
    rw [huQ _ hb_last] at hs_lt_q
    have hs1_lt : gm (Succinct.gmSlabOwnerSIdx N (gm 0 - 1)) + 1 <
        gm (Succinct.gmQIdx (gm (Succinct.gmSlabOwnerBIdx N (gm 0 - 1)))) := by
      split_ifs at hs_lt_q with hbeq
      · subst hbeq; omega
      · exact hs_lt_q
    have habv_eq := hslab.above_eq _ hb_last _ hs_last hs1_lt
    rw [hptr_last] at habv_eq
    rw [habv_eq]
    exact lt_of_lt_of_le (hslab.ptr_lt _ hb_last _ hs1_lt) hslab.nslabs_le

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.gmPopSlab N gm b` on
`gmAtBit` (`28 ≤ rB.val`, preserving all registers `28 ≤ r.val`, `T = 1318`). -/
@[expose]
def gmPopSlabRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMBucketRegCode 2 rB 26)
  (.seq (gmUnlinkTopSlabRegCode rB)
        (gmCompactSlabRegCode 26))

theorem gmPopSlabRegCode_exec {U V w N b : ℕ} {rB : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 28 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b)
    (hslab : Succinct.SlabBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N x.mem 0))
    (hq_pos : 1 ≤ gmAtBit U w N x.mem (Succinct.gmQIdx b)) :
    BitRAM.DemonicExecWithin w (gmPopSlabRegCode rB) x
      (fun z =>
        GMUpdatePost28 U V w N x z (Succinct.gmPopSlab N (gmAtBit U w N x.mem) b)) 1318 := by
  have htop_lt : 4 + 3 * b + 2 < globalMetaLen N := Succinct.gmSlabTopIdx_lt hb_pos hb
  unfold gmPopSlabRegCode
  refine .seq (T₁ := 49) (T₂ := 1269)
    (readGMBucketRegCode_exec (c := 2) (rB := rB) (rDst := 26)
      (by omega) (by decide) (by decide) hw hN_pos hnU hU hx her hsz hrB htop_lt)
    (fun y1 ⟨hst1, hy1_wf, hy1_er, h26, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hst1
  have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
    have h : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst1
    omega
  have hy1_gb : GMBasesLoaded N y1 :=
    hgb.congr_regs (fun r hr1 _ => hy1_regs r (by omega) (by intro h; subst h; omega))
  have hy1_rB : y1.regs rB = b := by
    rw [hy1_regs rB (by omega) (by intro h; subst h; omega), hrB]
  have hslab1 : Succinct.SlabBijection N (gmAtBit U w N y1.mem)
      (fun b' => gmAtBit U w N y1.mem (Succinct.gmQIdx b'))
      (gmAtBit U w N y1.mem 0) := by rw [hy1_mem]; exact hslab
  have hq1_pos : 1 ≤ gmAtBit U w N y1.mem (Succinct.gmQIdx b) := by rw [hy1_mem]; exact hq_pos
  refine .seq (T₁ := 270) (T₂ := 999)
    (gmUnlinkTopSlabRegCode_exec (rB := rB) (by omega) hw hN_pos hnU hU hb_pos hb
      hy1_wf hy1_er hy1_gb hy1_sz hy1_rB hslab1 hq1_pos)
    (fun y2 hy2 => ?_) (by omega)
  have hy2_26 : y2.regs 26 = gmAtBit U w N x.mem (Succinct.gmSlabTopIdx b) := by
    rw [hy2.2.2.2.2.2.2.2.2.2.2 26 (by decide), h26]; rfl
  have hcomp_inv : GmCompactSlabBitInv N (gmAtBit U w N x.mem (Succinct.gmSlabTopIdx b))
      (gmAtBit U w N y2.mem) := by
    rw [hy2.2.2.2.2.1, hy1_mem]
    exact gmCompactSlabBitInv_of_slabBijection hb hslab hq_pos
  exact (gmCompactSlabRegCode_exec hw hN_pos hnU hU hb_pos
    hy2.2.1 hy2.2.2.1 hy2.2.2.2.1 (hy2.1.symm ▸ hy1_sz) hy2_26 hcomp_inv).mono
    (fun z hz => by
      have h1z := hy2.to28.trans (hz.congr_gm (by rw [hy2.2.2.2.2.1, hy1_mem]))
      exact GMUpdatePost28.of_state_eq hst1
        (fun r hr => hy1_regs r (by omega) (by intro h; subst h; omega)) h1z) le_rfl

end Cslib.DataStructure.Dictionary.BitResizable
