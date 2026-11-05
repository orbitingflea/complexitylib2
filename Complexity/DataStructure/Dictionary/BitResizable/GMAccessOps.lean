/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Companion

/-!
# Bit-Resizable Dictionary: Global Metadata (`GM`) Access Primitives

This file compiles the global-metadata (`GM`), tail-item removal/insertion, and slab-pool
allocation/compaction operations (`SuccinctTailOps.lean`, `SuccinctSlabPool.lean`, and
`SuccinctSlabMove.lean`) to uniform `BitRAM.Code .standard 280` programs and proves their
coupling with `FixedCoupled` / `WindowCoupled`.
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

/-! ## Section 1: Cached `GM` base registers and uniform `GM` field accessors -/

/-- Register predicate stating that `r20..r25` cache the six `GM` layout constants computed by
`computeGMBasesRegCode`. Any helper touching only `r0..r19` and `r ≥ 26` preserves this
predicate. -/
@[expose]
def GMBasesLoaded (N : ℕ) (x : BitRAM.Data 280) : Prop :=
  x.regs 20 = dirSlabsPerBucket N ∧
  x.regs 21 = tailCapPerBucket N ∧
  x.regs 22 = Succinct.gmSlabDirBase N ∧
  x.regs 23 = Succinct.gmTailPtrBase N ∧
  x.regs 24 = Succinct.gmTailOwnerBase N ∧
  x.regs 25 = Succinct.gmSlabMetaBase N

theorem GMBasesLoaded.congr_regs {N : ℕ} {x y : BitRAM.Data 280}
    (hg : GMBasesLoaded N x)
    (h : ∀ r : Fin 280, 20 ≤ r.val → r.val < 26 → y.regs r = x.regs r) :
    GMBasesLoaded N y :=
  ⟨(h 20 (by decide) (by decide)).trans hg.1,
   (h 21 (by decide) (by decide)).trans hg.2.1,
   (h 22 (by decide) (by decide)).trans hg.2.2.1,
   (h 23 (by decide) (by decide)).trans hg.2.2.2.1,
   (h 24 (by decide) (by decide)).trans hg.2.2.2.2.1,
   (h 25 (by decide) (by decide)).trans hg.2.2.2.2.2⟩

theorem computeGMBasesRegCode_gmBases {U V w N : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w computeGMBasesRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        GMBasesLoaded N y ∧
        (∀ r : Fin 280, (r.val < 20 ∨ 26 ≤ r.val) → y.regs r = x.regs r)) 11 :=
  (computeGMBasesRegCode_exec hw hN_pos hb_pos hx her hsz).mono
    (fun _ ⟨hst, hwf, her', h20, h21, h22, h23, h24, h25, hregs⟩ =>
      ⟨hst, hwf, her', ⟨h20, h21, h22, h23, h24, h25⟩, hregs⟩) le_rfl

/-- Read `gmAtBit idx` (for small constant `idx < 4`, e.g., `0` or `1`) into `rDst` using `r12`
as scratch (`T = 46`). -/
@[expose]
def readGMConstRegCode (idx : ℕ) (rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 idx))
       (readGMRegCode 12 rDst)

theorem readGMConstRegCode_exec {U V w N idx : ℕ} {rDst : Fin 280} {x : BitRAM.Data 280}
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 240)
    (hidx_lt4 : idx < 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (readGMConstRegCode idx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs rDst = gmAtBit U w N x.mem idx ∧
        (∀ r : Fin 280, 14 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 46 := by
  have hidx : idx < globalMetaLen N := by unfold globalMetaLen; omega
  have hfit_idx : Fits w idx :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  unfold readGMConstRegCode
  refine DemonicExecWithin.step_const (T := 45) hfit_idx ?_
  set s1 := x.set 12 idx
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _)
  refine (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hidx
    (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
    (fun y ⟨hst, hwf, hrdst, hregs⟩ => ?_) le_rfl
  refine ⟨hst, hwf,
    hs1_er.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega)),
    hrdst, fun r hr hne => ?_⟩
  rw [hregs r (by omega) hne]
  dsimp only [s1, BitRAM.Data.set]
  exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _

/-- Write `rVal` to `gmAtBit idx` (for `idx < 4`) using `r12` as scratch (`T = 57`). -/
@[expose]
def writeGMConstRegCode (idx : ℕ) (rVal : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 idx))
       (writeGMRegCode 12 rVal)

theorem writeGMConstRegCode_exec {U V w N idx val : ℕ} {rVal : Fin 280} {x : BitRAM.Data 280}
    (hrVal_ge : 14 ≤ rVal.val) (hidx_lt4 : idx < 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrVal : x.regs rVal = val) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMConstRegCode idx rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        gmAtBit U w N y.mem = Function.update (gmAtBit U w N x.mem) idx val ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 57 := by
  have hidx : idx < globalMetaLen N := by unfold globalMetaLen; omega
  have hfit_idx : Fits w idx :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  unfold writeGMConstRegCode
  refine DemonicExecWithin.step_const (T := 56) hfit_idx ?_
  set s1 := x.set 12 idx
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _)
  have hs1_val : s1.regs rVal = val := by
    dsimp only [s1, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrVal
  refine (writeGMRegCode_exec (by decide) (by omega) hw hN_pos hnU hU hs1_wf hs1_er hidx hval
    (by simp +decide [s1, BitRAM.Data.set]) hs1_val hsz).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _

/-- Read `gmAtBit (rBase + rOff)` into `rDst` using `r12` as scratch (`T = 46`). -/
@[expose]
def readGMBaseOffRegCode (rBase rOff rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .add 12 rBase rOff))
       (readGMRegCode 12 rDst)

theorem readGMBaseOffRegCode_exec {U V w N base off : ℕ}
    {rBase rOff rDst : Fin 280} {x : BitRAM.Data 280}
    (_hrBase_ge : 14 ≤ rBase.val) (_hrOff_ge : 14 ≤ rOff.val)
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 240)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrOff : x.regs rOff = off)
    (hidx : base + off < globalMetaLen N) :
    BitRAM.DemonicExecWithin w (readGMBaseOffRegCode rBase rOff rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs rDst = gmAtBit U w N x.mem (base + off) ∧
        (∀ r : Fin 280, 14 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 46 := by
  have hfit_idx : Fits w (base + off) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  unfold readGMBaseOffRegCode
  refine step_dExec_bin (v := base + off) (T := 45)
    (by simp [BinOp.eval, hrBase, hrOff]) hfit_idx ?_
  set s1 := x.set 12 (base + off)
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _)
  refine (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hidx
    (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
    (fun y ⟨hst, hwf, hrdst, hregs⟩ => ?_) le_rfl
  refine ⟨hst, hwf,
    hs1_er.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega)),
    hrdst, fun r hr hne => ?_⟩
  rw [hregs r (by omega) hne]
  dsimp only [s1, BitRAM.Data.set]
  exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _

/-- Write `rVal` to `gmAtBit (rBase + rOff)` using `r12` as scratch (`T = 57`). -/
@[expose]
def writeGMBaseOffRegCode (rBase rOff rVal : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .add 12 rBase rOff))
       (writeGMRegCode 12 rVal)

theorem writeGMBaseOffRegCode_exec {U V w N base off val : ℕ}
    {rBase rOff rVal : Fin 280} {x : BitRAM.Data 280}
    (_hrBase_ge : 14 ≤ rBase.val) (_hrOff_ge : 14 ≤ rOff.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrOff : x.regs rOff = off) (hrVal : x.regs rVal = val)
    (hidx : base + off < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMBaseOffRegCode rBase rOff rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        gmAtBit U w N y.mem = Function.update (gmAtBit U w N x.mem) (base + off) val ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 57 := by
  have hfit_idx : Fits w (base + off) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  unfold writeGMBaseOffRegCode
  refine step_dExec_bin (v := base + off) (T := 56)
    (by simp [BinOp.eval, hrBase, hrOff]) hfit_idx ?_
  set s1 := x.set 12 (base + off)
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _)
  have hs1_val : s1.regs rVal = val := by
    dsimp only [s1, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrVal
  refine (writeGMRegCode_exec (by decide) (by omega) hw hN_pos hnU hU hs1_wf hs1_er hidx hval
    (by simp +decide [s1, BitRAM.Data.set]) hs1_val hsz).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _

/-- Read `gmAtBit (4 + 3 * rB + c)` (`c ∈ {0, 1, 2}` for `gmQIdx`, `gmRIdx`, `gmSlabTopIdx`)
into `rDst` using `r12, r13` as scratch (`T = 49`). -/
@[expose]
def readGMBucketRegCode (c : ℕ) (rB rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 13 3))
  (.seq (.op (.bin .mul 12 13 rB))
  (.seq (.op (.const 13 (4 + c)))
  (.seq (.op (.bin .add 12 13 12))
        (readGMRegCode 12 rDst))))

theorem readGMBucketRegCode_exec {U V w N c b : ℕ} {rB rDst : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 14 ≤ rB.val) (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 240)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b) (hidx : 4 + 3 * b + c < globalMetaLen N) :
    BitRAM.DemonicExecWithin w (readGMBucketRegCode c rB rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs rDst = gmAtBit U w N x.mem (4 + 3 * b + c) ∧
        (∀ r : Fin 280, 14 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 49 := by
  have hfit_idx : Fits w (4 + 3 * b + c) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  have hfit_3 : Fits w 3 := Fits.of_le hfit_idx (by omega)
  have hfit_4c : Fits w (4 + c) := Fits.of_le hfit_idx (by omega)
  have hfit_mul : Fits w (3 * b) := Fits.of_le hfit_idx (by omega)
  have hadd_eq : (4 + c) + 3 * b = 4 + 3 * b + c := by omega
  unfold readGMBucketRegCode
  refine DemonicExecWithin.step_const (T := 48) hfit_3 ?_
  refine step_dExec_bin (v := 3 * b) (T := 47)
    (by
      have hne : rB ≠ 13 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrB]) hfit_mul ?_
  refine DemonicExecWithin.step_const (T := 46) hfit_4c ?_
  refine step_dExec_bin (v := 4 + 3 * b + c) (T := 45)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hadd_eq]) hfit_idx ?_
  set s1 := (((x.set 13 3).set 12 (3 * b)).set 13 (4 + c)).set 12 (4 + 3 * b + c)
  have hs1_wf : s1.WellFormed w :=
    wf_set 12 (wf_set 13 (wf_set 12 (wf_set 13 hx hfit_3) hfit_mul) hfit_4c) hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hidx
    (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
    (fun y ⟨hst, hwf, hrdst, hregs⟩ => ?_) le_rfl
  refine ⟨hst, hwf,
    hs1_er.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega)),
    hrdst, fun r hr hne => ?_⟩
  rw [hregs r (by omega) hne]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Write `rVal` to `gmAtBit (4 + 3 * rB + c)` using `r12, r13` as scratch (`T = 60`). -/
@[expose]
def writeGMBucketRegCode (c : ℕ) (rB rVal : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 13 3))
  (.seq (.op (.bin .mul 12 13 rB))
  (.seq (.op (.const 13 (4 + c)))
  (.seq (.op (.bin .add 12 13 12))
        (writeGMRegCode 12 rVal))))

theorem writeGMBucketRegCode_exec {U V w N c b val : ℕ} {rB rVal : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 14 ≤ rB.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b) (hrVal : x.regs rVal = val)
    (hidx : 4 + 3 * b + c < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMBucketRegCode c rB rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        gmAtBit U w N y.mem = Function.update (gmAtBit U w N x.mem) (4 + 3 * b + c) val ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 60 := by
  have hfit_idx : Fits w (4 + 3 * b + c) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  have hfit_3 : Fits w 3 := Fits.of_le hfit_idx (by omega)
  have hfit_4c : Fits w (4 + c) := Fits.of_le hfit_idx (by omega)
  have hfit_mul : Fits w (3 * b) := Fits.of_le hfit_idx (by omega)
  have hadd_eq : (4 + c) + 3 * b = 4 + 3 * b + c := by omega
  unfold writeGMBucketRegCode
  refine DemonicExecWithin.step_const (T := 59) hfit_3 ?_
  refine step_dExec_bin (v := 3 * b) (T := 58)
    (by
      have hne : rB ≠ 13 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrB]) hfit_mul ?_
  refine DemonicExecWithin.step_const (T := 57) hfit_4c ?_
  refine step_dExec_bin (v := 4 + 3 * b + c) (T := 56)
    (by simp +decide [BinOp.eval, BitRAM.Data.set, hadd_eq]) hfit_idx ?_
  set s1 := (((x.set 13 3).set 12 (3 * b)).set 13 (4 + c)).set 12 (4 + 3 * b + c)
  have hs1_wf : s1.WellFormed w :=
    wf_set 12 (wf_set 13 (wf_set 12 (wf_set 13 hx hfit_3) hfit_mul) hfit_4c) hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_val : s1.regs rVal = val := by
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrVal
  refine (writeGMRegCode_exec (by decide) (by omega) hw hN_pos hnU hU hs1_wf hs1_er hidx hval
    (by simp +decide [s1, BitRAM.Data.set]) hs1_val hsz).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Read `gmAtBit (rBase + rB * rStride + rK)` into `rDst` using `r12` as scratch (`T = 48`). -/
@[expose]
def readGM2DRegCode (rBase rStride rB rK rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mul 12 rB rStride))
  (.seq (.op (.bin .add 12 rBase 12))
  (.seq (.op (.bin .add 12 12 rK))
        (readGMRegCode 12 rDst)))

theorem readGM2DRegCode_exec {U V w N base stride b k : ℕ}
    {rBase rStride rB rK rDst : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (_hrStride_ge : 14 ≤ rStride.val)
    (_hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val)
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 240)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrStride : x.regs rStride = stride)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k)
    (hidx : base + b * stride + k < globalMetaLen N) :
    BitRAM.DemonicExecWithin w (readGM2DRegCode rBase rStride rB rK rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs rDst = gmAtBit U w N x.mem (base + b * stride + k) ∧
        (∀ r : Fin 280, 14 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 48 := by
  have hfit_idx : Fits w (base + b * stride + k) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  have hfit_mul : Fits w (b * stride) := Fits.of_le hfit_idx (by omega)
  have hfit_add1 : Fits w (base + b * stride) := Fits.of_le hfit_idx (by omega)
  unfold readGM2DRegCode
  refine step_dExec_bin (v := b * stride) (T := 47)
    (by simp [BinOp.eval, hrB, hrStride]) hfit_mul ?_
  refine step_dExec_bin (v := base + b * stride) (T := 46)
    (by
      have hne : rBase ≠ 12 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrBase]) hfit_add1 ?_
  refine step_dExec_bin (v := base + b * stride + k) (T := 45)
    (by
      have hne : rK ≠ 12 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrK]) hfit_idx ?_
  set s1 := ((x.set 12 (b * stride)).set 12 (base + b * stride)).set 12 (base + b * stride + k)
  have hs1_wf : s1.WellFormed w :=
    wf_set 12 (wf_set 12 (wf_set 12 hx hfit_mul) hfit_add1) hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hidx
    (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
    (fun y ⟨hst, hwf, hrdst, hregs⟩ => ?_) le_rfl
  refine ⟨hst, hwf,
    hs1_er.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega)),
    hrdst, fun r hr hne => ?_⟩
  rw [hregs r (by omega) hne]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Write `rVal` to `gmAtBit (rBase + rB * rStride + rK)` using `r12` as scratch (`T = 59`). -/
@[expose]
def writeGM2DRegCode (rBase rStride rB rK rVal : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mul 12 rB rStride))
  (.seq (.op (.bin .add 12 rBase 12))
  (.seq (.op (.bin .add 12 12 rK))
        (writeGMRegCode 12 rVal)))

theorem writeGM2DRegCode_exec {U V w N base stride b k val : ℕ}
    {rBase rStride rB rK rVal : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (_hrStride_ge : 14 ≤ rStride.val)
    (_hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrStride : x.regs rStride = stride)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k) (hrVal : x.regs rVal = val)
    (hidx : base + b * stride + k < globalMetaLen N)
    (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGM2DRegCode rBase rStride rB rK rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        gmAtBit U w N y.mem =
          Function.update (gmAtBit U w N x.mem) (base + b * stride + k) val ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 59 := by
  have hfit_idx : Fits w (base + b * stride + k) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  have hfit_mul : Fits w (b * stride) := Fits.of_le hfit_idx (by omega)
  have hfit_add1 : Fits w (base + b * stride) := Fits.of_le hfit_idx (by omega)
  unfold writeGM2DRegCode
  refine step_dExec_bin (v := b * stride) (T := 58)
    (by simp [BinOp.eval, hrB, hrStride]) hfit_mul ?_
  refine step_dExec_bin (v := base + b * stride) (T := 57)
    (by
      have hne : rBase ≠ 12 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrBase]) hfit_add1 ?_
  refine step_dExec_bin (v := base + b * stride + k) (T := 56)
    (by
      have hne : rK ≠ 12 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrK]) hfit_idx ?_
  set s1 := ((x.set 12 (b * stride)).set 12 (base + b * stride)).set 12 (base + b * stride + k)
  have hs1_wf : s1.WellFormed w :=
    wf_set 12 (wf_set 12 (wf_set 12 hx hfit_mul) hfit_add1) hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_val : s1.regs rVal = val := by
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrVal
  refine (writeGMRegCode_exec (by decide) (by omega) hw hN_pos hnU hU hs1_wf hs1_er hidx hval
    (by simp +decide [s1, BitRAM.Data.set]) hs1_val hsz).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Read `gmAtBit (rBase + a * rIdx + c)` into `rDst` using `r12, r13` as scratch (`T = 50`). -/
@[expose]
def readGMAffineRegCode (rBase : Fin 280) (a c : ℕ) (rIdx rDst : Fin 280) :
    BitRAM.Code .standard 280 :=
  .seq (.op (.const 13 a))
  (.seq (.op (.bin .mul 12 13 rIdx))
  (.seq (.op (.bin .add 12 rBase 12))
  (.seq (.op (.const 13 c))
  (.seq (.op (.bin .add 12 12 13))
        (readGMRegCode 12 rDst)))))

theorem readGMAffineRegCode_exec {U V w N base a c idx : ℕ}
    {rBase rIdx rDst : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val)
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 240)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrIdx : x.regs rIdx = idx)
    (hidx : base + a * idx + c < globalMetaLen N) :
    BitRAM.DemonicExecWithin w (readGMAffineRegCode rBase a c rIdx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs rDst = gmAtBit U w N x.mem (base + a * idx + c) ∧
        (∀ r : Fin 280, 14 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 50 := by
  have hfit_idx : Fits w (base + a * idx + c) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  have hfit_a : Fits w a :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz (by unfold globalMetaLen; omega)
  have hfit_c : Fits w c :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz (by unfold globalMetaLen; omega)
  have hfit_mul : Fits w (a * idx) := Fits.of_le hfit_idx (by omega)
  have hfit_add1 : Fits w (base + a * idx) := Fits.of_le hfit_idx (by omega)
  unfold readGMAffineRegCode
  refine DemonicExecWithin.step_const (T := 49) hfit_a ?_
  refine step_dExec_bin (v := a * idx) (T := 48)
    (by
      have hne : rIdx ≠ 13 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrIdx]) hfit_mul ?_
  refine step_dExec_bin (v := base + a * idx) (T := 47)
    (by
      have hne1 : rBase ≠ 12 := by intro h; subst h; omega
      have hne2 : rBase ≠ 13 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne1, hne2, hrBase]) hfit_add1 ?_
  refine DemonicExecWithin.step_const (T := 46) hfit_c ?_
  refine step_dExec_bin (v := base + a * idx + c) (T := 45)
    (by simp +decide [BinOp.eval, BitRAM.Data.set]) hfit_idx ?_
  set s1 := ((((x.set 13 a).set 12 (a * idx)).set 12 (base + a * idx)).set 13 c).set 12
    (base + a * idx + c)
  have hs1_wf : s1.WellFormed w :=
    wf_set 12 (wf_set 13 (wf_set 12 (wf_set 12 (wf_set 13 hx hfit_a) hfit_mul) hfit_add1) hfit_c)
      hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hidx
    (by simp +decide [s1, BitRAM.Data.set]) hsz).mono
    (fun y ⟨hst, hwf, hrdst, hregs⟩ => ?_) le_rfl
  refine ⟨hst, hwf,
    hs1_er.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega)),
    hrdst, fun r hr hne => ?_⟩
  rw [hregs r (by omega) hne]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Write `rVal` to `gmAtBit (rBase + a * rIdx + c)` using `r12, r13` as scratch (`T = 61`). -/
@[expose]
def writeGMAffineRegCode (rBase : Fin 280) (a c : ℕ) (rIdx rVal : Fin 280) :
    BitRAM.Code .standard 280 :=
  .seq (.op (.const 13 a))
  (.seq (.op (.bin .mul 12 13 rIdx))
  (.seq (.op (.bin .add 12 rBase 12))
  (.seq (.op (.const 13 c))
  (.seq (.op (.bin .add 12 12 13))
        (writeGMRegCode 12 rVal)))))

theorem writeGMAffineRegCode_exec {U V w N base a c idx val : ℕ}
    {rBase rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val) (hrVal_ge : 14 ≤ rVal.val)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrIdx : x.regs rIdx = idx) (hrVal : x.regs rVal = val)
    (hidx : base + a * idx + c < globalMetaLen N)
    (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMAffineRegCode rBase a c rIdx rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        gmAtBit U w N y.mem =
          Function.update (gmAtBit U w N x.mem) (base + a * idx + c) val ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 61 := by
  have hfit_idx : Fits w (base + a * idx + c) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hidx.le
  have hfit_a : Fits w a :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz (by unfold globalMetaLen; omega)
  have hfit_c : Fits w c :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz (by unfold globalMetaLen; omega)
  have hfit_mul : Fits w (a * idx) := Fits.of_le hfit_idx (by omega)
  have hfit_add1 : Fits w (base + a * idx) := Fits.of_le hfit_idx (by omega)
  unfold writeGMAffineRegCode
  refine DemonicExecWithin.step_const (T := 60) hfit_a ?_
  refine step_dExec_bin (v := a * idx) (T := 59)
    (by
      have hne : rIdx ≠ 13 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne, hrIdx]) hfit_mul ?_
  refine step_dExec_bin (v := base + a * idx) (T := 58)
    (by
      have hne1 : rBase ≠ 12 := by intro h; subst h; omega
      have hne2 : rBase ≠ 13 := by intro h; subst h; omega
      simp [BinOp.eval, BitRAM.Data.set, hne1, hne2, hrBase]) hfit_add1 ?_
  refine DemonicExecWithin.step_const (T := 57) hfit_c ?_
  refine step_dExec_bin (v := base + a * idx + c) (T := 56)
    (by simp +decide [BinOp.eval, BitRAM.Data.set]) hfit_idx ?_
  set s1 := ((((x.set 13 a).set 12 (a * idx)).set 12 (base + a * idx)).set 13 c).set 12
    (base + a * idx + c)
  have hs1_wf : s1.WellFormed w :=
    wf_set 12 (wf_set 13 (wf_set 12 (wf_set 12 (wf_set 13 hx hfit_a) hfit_mul) hfit_add1) hfit_c)
      hfit_idx
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_val : s1.regs rVal = val := by
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrVal
  refine (writeGMRegCode_exec (by decide) (by omega) hw hN_pos hnU hU hs1_wf hs1_er hidx hval
    (by simp +decide [s1, BitRAM.Data.set]) hs1_val hsz).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => ?_⟩
  rw [hy_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-! ## Section 2: `GMUpdatePost` composition combinators -/

/-- Standard postcondition for any `GM`-only update program: `bitSize`, `WellFormed`,
`EpochRegs`, `GMBasesLoaded`, `lmAtBit`, `tdAtBit`, `dtAtBit`, words outside `[offGM, offTD)`,
all dense items, and all registers `r ≥ 20` are preserved, while `gmAtBit` becomes `gm'`. -/
@[expose]
def GMUpdatePost (U V w N : ℕ) (x y : BitRAM.Data 280) (gm' : ℕ → ℕ) : Prop :=
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
  (∀ r : Fin 280, 20 ≤ r.val → y.regs r = x.regs r)

theorem GMUpdatePost.refl {U V w N : ℕ} {x : BitRAM.Data 280}
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x) :
    GMUpdatePost U V w N x x (gmAtBit U w N x.mem) :=
  ⟨rfl, hx, her, hgb, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

theorem GMUpdatePost.congr_gm {U V w N : ℕ} {x y : BitRAM.Data 280} {gm₁ gm₂ : ℕ → ℕ}
    (h : GMUpdatePost U V w N x y gm₁) (heq : gm₁ = gm₂) :
    GMUpdatePost U V w N x y gm₂ := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact ⟨h1, h2, h3, h4, h5.trans heq, h6, h7, h8, h9, h10, h11⟩

theorem GMUpdatePost.trans {U V w N : ℕ} {x y z : BitRAM.Data 280} {gm₁ gm₂ : ℕ → ℕ}
    (hxy : GMUpdatePost U V w N x y gm₁) (hyz : GMUpdatePost U V w N y z gm₂) :
    GMUpdatePost U V w N x z gm₂ := by
  rcases hxy with ⟨hxy_sz, _, _, _, _, hxy_lm, hxy_td, hxy_dt, hxy_out, hxy_items, hxy_regs⟩
  rcases hyz with ⟨hyz_sz, hyz_wf, hyz_er, hyz_gb, hyz_gm, hyz_lm, hyz_td, hyz_dt,
    hyz_out, hyz_items, hyz_regs⟩
  refine ⟨hyz_sz.trans hxy_sz, hyz_wf, hyz_er, hyz_gb, hyz_gm,
    hyz_lm.trans hxy_lm, hyz_td.trans hxy_td, hyz_dt.trans hxy_dt,
    fun a ha => (hyz_out a ha).trans (hxy_out a ha),
    fun d => ⟨(hyz_items d).1.trans (hxy_items d).1, (hyz_items d).2.trans (hxy_items d).2⟩,
    fun r hr => (hyz_regs r hr).trans (hxy_regs r hr)⟩

theorem GMUpdatePost.of_state_eq {U V w N : ℕ} {x y z : BitRAM.Data 280} {gm' : ℕ → ℕ}
    (hst : y.toBitMemoryState = x.toBitMemoryState)
    (hregs : ∀ r : Fin 280, 20 ≤ r.val → y.regs r = x.regs r)
    (hyz : GMUpdatePost U V w N y z gm') :
    GMUpdatePost U V w N x z gm' := by
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  rcases hyz with ⟨hyz_sz, hyz_wf, hyz_er, hyz_gb, hyz_gm, hyz_lm, hyz_td, hyz_dt,
    hyz_out, hyz_items, hyz_regs⟩
  refine ⟨hyz_sz.trans hsz, hyz_wf, hyz_er, hyz_gb, hyz_gm,
    hyz_lm.trans (by rw [hmem]), hyz_td.trans (by rw [hmem]), hyz_dt.trans (by rw [hmem]),
    fun a ha => (hyz_out a ha).trans (congrFun hmem a),
    fun d => ⟨(hyz_items d).1.trans (by rw [hst]), (hyz_items d).2.trans (by rw [hst])⟩,
    fun r hr => (hyz_regs r hr).trans (hregs r hr)⟩

theorem GMUpdatePost.of_set {U V w N : ℕ} {x z : BitRAM.Data 280} {rDst : Fin 280} {v : ℕ}
    {gm' : ℕ → ℕ} (hrDst : rDst.val < 20)
    (hz : GMUpdatePost U V w N (x.set rDst v) z gm') :
    GMUpdatePost U V w N x z gm' :=
  GMUpdatePost.of_state_eq (y := x.set rDst v) rfl
    (fun r hr => by
      dsimp only [BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _) hz

theorem writeGMConstRegCode_gmUpdate {U V w N idx val : ℕ} {rVal : Fin 280} {x : BitRAM.Data 280}
    (hrVal_ge : 14 ≤ rVal.val) (hidx_lt4 : idx < 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrVal : x.regs rVal = val) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMConstRegCode idx rVal) x
      (fun y =>
        GMUpdatePost U V w N x y (Function.update (gmAtBit U w N x.mem) idx val) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 57 :=
  (writeGMConstRegCode_exec hrVal_ge hidx_lt4 hw hN_pos hnU hU hx her hsz hrVal hval).mono
    (fun _ ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
      ⟨⟨hy_sz, hy_wf, hy_er, hgb.congr_regs (fun r hr1 _ => hy_regs r (by omega)),
        hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => hy_regs r (by omega)⟩,
       hy_regs⟩) le_rfl

theorem writeGMBaseOffRegCode_gmUpdate {U V w N base off val : ℕ}
    {rBase rOff rVal : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrOff_ge : 14 ≤ rOff.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrOff : x.regs rOff = off) (hrVal : x.regs rVal = val)
    (hidx : base + off < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMBaseOffRegCode rBase rOff rVal) x
      (fun y =>
        GMUpdatePost U V w N x y (Function.update (gmAtBit U w N x.mem) (base + off) val) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 57 :=
  (writeGMBaseOffRegCode_exec hrBase_ge hrOff_ge hrVal_ge hw hN_pos hnU hU hx her hsz
    hrBase hrOff hrVal hidx hval).mono
    (fun _ ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
      ⟨⟨hy_sz, hy_wf, hy_er, hgb.congr_regs (fun r hr1 _ => hy_regs r (by omega)),
        hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => hy_regs r (by omega)⟩,
       hy_regs⟩) le_rfl

theorem writeGMBucketRegCode_gmUpdate {U V w N c b val : ℕ} {rB rVal : Fin 280}
    {x : BitRAM.Data 280}
    (hrB_ge : 14 ≤ rB.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b) (hrVal : x.regs rVal = val)
    (hidx : 4 + 3 * b + c < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMBucketRegCode c rB rVal) x
      (fun y =>
        GMUpdatePost U V w N x y (Function.update (gmAtBit U w N x.mem) (4 + 3 * b + c) val) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 60 :=
  (writeGMBucketRegCode_exec hrB_ge hrVal_ge hw hN_pos hnU hU hx her hsz hrB hrVal hidx hval).mono
    (fun _ ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
      ⟨⟨hy_sz, hy_wf, hy_er, hgb.congr_regs (fun r hr1 _ => hy_regs r (by omega)),
        hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => hy_regs r (by omega)⟩,
       hy_regs⟩) le_rfl

theorem writeGM2DRegCode_gmUpdate {U V w N base stride b k val : ℕ}
    {rBase rStride rB rK rVal : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrStride_ge : 14 ≤ rStride.val)
    (hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrStride : x.regs rStride = stride)
    (hrB : x.regs rB = b) (hrK : x.regs rK = k) (hrVal : x.regs rVal = val)
    (hidx : base + b * stride + k < globalMetaLen N)
    (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGM2DRegCode rBase rStride rB rK rVal) x
      (fun y =>
        GMUpdatePost U V w N x y
          (Function.update (gmAtBit U w N x.mem) (base + b * stride + k) val) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 59 :=
  (writeGM2DRegCode_exec hrBase_ge hrStride_ge hrB_ge hrK_ge hrVal_ge hw hN_pos hnU hU hx her hsz
    hrBase hrStride hrB hrK hrVal hidx hval).mono
    (fun _ ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
      ⟨⟨hy_sz, hy_wf, hy_er, hgb.congr_regs (fun r hr1 _ => hy_regs r (by omega)),
        hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => hy_regs r (by omega)⟩,
       hy_regs⟩) le_rfl

theorem writeGMAffineRegCode_gmUpdate {U V w N base a c idx val : ℕ}
    {rBase rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val) (hrVal_ge : 14 ≤ rVal.val)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrBase : x.regs rBase = base) (hrIdx : x.regs rIdx = idx) (hrVal : x.regs rVal = val)
    (hidx : base + a * idx + c < globalMetaLen N)
    (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMAffineRegCode rBase a c rIdx rVal) x
      (fun y =>
        GMUpdatePost U V w N x y
          (Function.update (gmAtBit U w N x.mem) (base + a * idx + c) val) ∧
        (∀ r : Fin 280, 14 ≤ r.val → y.regs r = x.regs r)) 61 :=
  (writeGMAffineRegCode_exec hrBase_ge hrIdx_ge hrVal_ge ha_le hc_le hw hN_pos hnU hU hx her hsz
    hrBase hrIdx hrVal hidx hval).mono
    (fun _ ⟨hy_sz, hy_wf, hy_er, hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, hy_regs⟩ =>
      ⟨⟨hy_sz, hy_wf, hy_er, hgb.congr_regs (fun r hr1 _ => hy_regs r (by omega)),
        hy_gm, hy_lm, hy_td, hy_dt, hy_out, hy_items, fun r hr => hy_regs r (by omega)⟩,
       hy_regs⟩) le_rfl


end Cslib.DataStructure.Dictionary.BitResizable
