/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.GMAccessOps

/-!
# Bit-Resizable Dictionary: Tail Array `GM` Operations

This file compiles the tail-pointer and tail-owner global-metadata (`GM`) operations
(`gmAppendTailRegCode`, `gmRemoveTailRegCode`) to uniform `BitRAM.Code .standard 280` programs and
proves their exact execution contracts via `GMState` step combinators.
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

/-- Bundled execution state for `GM` update subroutines: tracks `WellFormed`, `EpochRegs`,
`GMBasesLoaded`, `epochMetaBits ≤ bitSize`, current `gmAtBit = gm`, and high-register functional
view `x.regs r = rf r` for all `r ≥ 14`. -/
structure GMState (U V w N : ℕ) (gm : ℕ → ℕ) (rf : Fin 280 → ℕ) (x : BitRAM.Data 280) : Prop where
  wf : x.WellFormed w
  er : EpochRegs U V w N x
  gb : GMBasesLoaded N x
  sz : epochMetaBits U w N ≤ x.bitSize
  gm_eq : gmAtBit U w N x.mem = gm
  regs_eq : ∀ r : Fin 280, 14 ≤ r.val → x.regs r = rf r

theorem GMState.init {U V w N : ℕ} {x : BitRAM.Data 280}
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    GMState U V w N (gmAtBit U w N x.mem) x.regs x :=
  ⟨hx, her, hgb, hsz, rfl, fun _ _ => rfl⟩

theorem GMState.set_temp {U V w N v : ℕ} {gm : ℕ → ℕ} {rf : Fin 280 → ℕ}
    {rDst : Fin 280} {x : BitRAM.Data 280}
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (hs : GMState U V w N gm rf x) (hfit : Fits w v) :
    GMState U V w N gm (Function.update rf rDst v) (x.set rDst v) := by
  refine ⟨wf_set rDst hs.wf hfit,
    hs.er.congr_regs (fun r hr1 _ => by
      dsimp only [BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _),
    hs.gb.congr_regs (fun r hr1 _ => by
      dsimp only [BitRAM.Data.set]
      exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega) _ _),
    hs.sz, hs.gm_eq, fun r hr => ?_⟩
  dsimp only [BitRAM.Data.set]
  rcases eq_or_ne r rDst with rfl | hne
  · simp
  · rw [Function.update_of_ne hne, Function.update_of_ne hne, hs.regs_eq r hr]

theorem step_gm_const {U V w N c T : ℕ} {rDst : Fin 280} {gm gm' : ℕ → ℕ}
    {rf : Fin 280 → ℕ} {x : BitRAM.Data 280} {rest : BitRAM.Code .standard 280}
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (hs : GMState U V w N gm rf x) (hfit : Fits w c)
    (hrest : GMState U V w N gm (Function.update rf rDst c) (x.set rDst c) →
      BitRAM.DemonicExecWithin w rest (x.set rDst c)
        (fun z => GMUpdatePost U V w N (x.set rDst c) z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.const rDst c)) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 1) :=
  DemonicExecWithin.step_const hfit
    ((hrest (hs.set_temp hrDst_ge hrDst_lt hfit)).mono
      (fun _ hz => GMUpdatePost.of_set hrDst_lt hz) le_rfl)

theorem step_gm_copy {U V w N v T : ℕ} {rDst rSrc : Fin 280} {gm gm' : ℕ → ℕ}
    {rf : Fin 280 → ℕ} {x : BitRAM.Data 280} {rest : BitRAM.Code .standard 280}
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20) (hrSrc_ge : 14 ≤ rSrc.val)
    (hs : GMState U V w N gm rf x) (hrv : rf rSrc = v)
    (hrest : GMState U V w N gm (Function.update rf rDst v) (x.set rDst v) →
      BitRAM.DemonicExecWithin w rest (x.set rDst v)
        (fun z => GMUpdatePost U V w N (x.set rDst v) z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.copy rDst rSrc)) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 1) := by
  have hx_src : x.regs rSrc = v := (hs.regs_eq rSrc hrSrc_ge).trans hrv
  have hfit : Fits w v := hx_src ▸ hs.wf.regs_fits rSrc
  exact step_dExec_copy hx_src
    ((hrest (hs.set_temp hrDst_ge hrDst_lt hfit)).mono
      (fun _ hz => GMUpdatePost.of_set hrDst_lt hz) le_rfl)

theorem step_gm_bin {U V w N v T : ℕ} {op : BinOp} {rDst rA rB : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (hrA_ge : 14 ≤ rA.val) (hrB_ge : 14 ≤ rB.val)
    (hs : GMState U V w N gm rf x) (hev : op.eval (rf rA) (rf rB) = v) (hfit : Fits w v)
    (hrest : GMState U V w N gm (Function.update rf rDst v) (x.set rDst v) →
      BitRAM.DemonicExecWithin w rest (x.set rDst v)
        (fun z => GMUpdatePost U V w N (x.set rDst v) z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.bin op rDst rA rB)) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 1) := by
  have hev' : op.eval (x.regs rA) (x.regs rB) = v := by
    rw [hs.regs_eq rA hrA_ge, hs.regs_eq rB hrB_ge]; exact hev
  exact step_dExec_bin hev' hfit
    ((hrest (hs.set_temp hrDst_ge hrDst_lt hfit)).mono
      (fun _ hz => GMUpdatePost.of_set hrDst_lt hz) le_rfl)

theorem step_gm_readConst {U V w N idx T : ℕ} {rDst : Fin 280} {gm gm' : ℕ → ℕ}
    {rf : Fin 280 → ℕ} {x : BitRAM.Data 280} {rest : BitRAM.Code .standard 280}
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20) (hidx_lt4 : idx < 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrest : ∀ y, GMState U V w N gm (Function.update rf rDst (gm idx)) y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (readGMConstRegCode idx rDst) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 46) := by
  refine .seq (T₁ := 46) (T₂ := T)
    (readGMConstRegCode_exec hrDst_ge (by omega) hidx_lt4 hw hN_pos hnU hU hs.wf hs.er hs.sz)
    (fun y ⟨hst, hwf, her, hrdst, hregs⟩ => ?_) (by omega)
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  have hgb : GMBasesLoaded N y :=
    hs.gb.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega))
  have hs_y : GMState U V w N gm (Function.update rf rDst (gm idx)) y := by
    refine ⟨hwf, her, hgb, hsz.symm ▸ hs.sz, (congrArg (gmAtBit U w N) hmem).trans hs.gm_eq,
      fun r hr => ?_⟩
    rcases eq_or_ne r rDst with rfl | hne
    · rw [Function.update_self, hrdst, hs.gm_eq]
    · rw [Function.update_of_ne hne, hregs r hr hne, hs.regs_eq r hr]
  exact (hrest y hs_y).mono
    (fun _ hz => GMUpdatePost.of_state_eq hst
      (fun r hr => hregs r (by omega) (by intro h; subst h; omega)) hz) le_rfl

theorem step_gm_readBaseOff {U V w N base off T : ℕ} {rBase rOff rDst : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrOff_ge : 14 ≤ rOff.val)
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrOff : rf rOff = off)
    (hidx : base + off < globalMetaLen N)
    (hrest : ∀ y, GMState U V w N gm (Function.update rf rDst (gm (base + off))) y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (readGMBaseOffRegCode rBase rOff rDst) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 46) := by
  refine .seq (T₁ := 46) (T₂ := T)
    (readGMBaseOffRegCode_exec hrBase_ge hrOff_ge hrDst_ge (by omega) hw hN_pos hnU hU
      hs.wf hs.er hs.sz ((hs.regs_eq rBase hrBase_ge).trans hrBase)
      ((hs.regs_eq rOff hrOff_ge).trans hrOff) hidx)
    (fun y ⟨hst, hwf, her, hrdst, hregs⟩ => ?_) (by omega)
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  have hgb : GMBasesLoaded N y :=
    hs.gb.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega))
  have hs_y : GMState U V w N gm (Function.update rf rDst (gm (base + off))) y := by
    refine ⟨hwf, her, hgb, hsz.symm ▸ hs.sz, (congrArg (gmAtBit U w N) hmem).trans hs.gm_eq,
      fun r hr => ?_⟩
    rcases eq_or_ne r rDst with rfl | hne
    · rw [Function.update_self, hrdst, hs.gm_eq]
    · rw [Function.update_of_ne hne, hregs r hr hne, hs.regs_eq r hr]
  exact (hrest y hs_y).mono
    (fun _ hz => GMUpdatePost.of_state_eq hst
      (fun r hr => hregs r (by omega) (by intro h; subst h; omega)) hz) le_rfl

theorem step_gm_readBucket {U V w N c b T : ℕ} {rB rDst : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrB_ge : 14 ≤ rB.val) (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x) (hrB : rf rB = b)
    (hidx : 4 + 3 * b + c < globalMetaLen N)
    (hrest : ∀ y, GMState U V w N gm (Function.update rf rDst (gm (4 + 3 * b + c))) y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (readGMBucketRegCode c rB rDst) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 49) := by
  refine .seq (T₁ := 49) (T₂ := T)
    (readGMBucketRegCode_exec hrB_ge hrDst_ge (by omega) hw hN_pos hnU hU hs.wf hs.er hs.sz
      ((hs.regs_eq rB hrB_ge).trans hrB) hidx)
    (fun y ⟨hst, hwf, her, hrdst, hregs⟩ => ?_) (by omega)
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  have hgb : GMBasesLoaded N y :=
    hs.gb.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega))
  have hs_y : GMState U V w N gm (Function.update rf rDst (gm (4 + 3 * b + c))) y := by
    refine ⟨hwf, her, hgb, hsz.symm ▸ hs.sz, (congrArg (gmAtBit U w N) hmem).trans hs.gm_eq,
      fun r hr => ?_⟩
    rcases eq_or_ne r rDst with rfl | hne
    · rw [Function.update_self, hrdst, hs.gm_eq]
    · rw [Function.update_of_ne hne, hregs r hr hne, hs.regs_eq r hr]
  exact (hrest y hs_y).mono
    (fun _ hz => GMUpdatePost.of_state_eq hst
      (fun r hr => hregs r (by omega) (by intro h; subst h; omega)) hz) le_rfl

theorem step_gm_read2D {U V w N base stride b k T : ℕ}
    {rBase rStride rB rK rDst : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrStride_ge : 14 ≤ rStride.val)
    (hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val)
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrStride : rf rStride = stride)
    (hrB : rf rB = b) (hrK : rf rK = k)
    (hidx : base + b * stride + k < globalMetaLen N)
    (hrest : ∀ y, GMState U V w N gm (Function.update rf rDst (gm (base + b * stride + k))) y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (readGM2DRegCode rBase rStride rB rK rDst) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 48) := by
  refine .seq (T₁ := 48) (T₂ := T)
    (readGM2DRegCode_exec hrBase_ge hrStride_ge hrB_ge hrK_ge hrDst_ge (by omega)
      hw hN_pos hnU hU hs.wf hs.er hs.sz
      ((hs.regs_eq rBase hrBase_ge).trans hrBase)
      ((hs.regs_eq rStride hrStride_ge).trans hrStride)
      ((hs.regs_eq rB hrB_ge).trans hrB)
      ((hs.regs_eq rK hrK_ge).trans hrK) hidx)
    (fun y ⟨hst, hwf, her, hrdst, hregs⟩ => ?_) (by omega)
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  have hgb : GMBasesLoaded N y :=
    hs.gb.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega))
  have hs_y : GMState U V w N gm (Function.update rf rDst (gm (base + b * stride + k))) y := by
    refine ⟨hwf, her, hgb, hsz.symm ▸ hs.sz, (congrArg (gmAtBit U w N) hmem).trans hs.gm_eq,
      fun r hr => ?_⟩
    rcases eq_or_ne r rDst with rfl | hne
    · rw [Function.update_self, hrdst, hs.gm_eq]
    · rw [Function.update_of_ne hne, hregs r hr hne, hs.regs_eq r hr]
  exact (hrest y hs_y).mono
    (fun _ hz => GMUpdatePost.of_state_eq hst
      (fun r hr => hregs r (by omega) (by intro h; subst h; omega)) hz) le_rfl

theorem step_gm_readAffine {U V w N base a c idx T : ℕ}
    {rBase rIdx rDst : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val)
    (hrDst_ge : 14 ≤ rDst.val) (hrDst_lt : rDst.val < 20)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrIdx : rf rIdx = idx)
    (hidx : base + a * idx + c < globalMetaLen N)
    (hrest : ∀ y, GMState U V w N gm (Function.update rf rDst (gm (base + a * idx + c))) y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (readGMAffineRegCode rBase a c rIdx rDst) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 50) := by
  refine .seq (T₁ := 50) (T₂ := T)
    (readGMAffineRegCode_exec hrBase_ge hrIdx_ge hrDst_ge (by omega) ha_le hc_le
      hw hN_pos hnU hU hs.wf hs.er hs.sz
      ((hs.regs_eq rBase hrBase_ge).trans hrBase)
      ((hs.regs_eq rIdx hrIdx_ge).trans hrIdx) hidx)
    (fun y ⟨hst, hwf, her, hrdst, hregs⟩ => ?_) (by omega)
  have hmem : y.mem = x.mem := congrArg BitMemory.State.mem hst
  have hsz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hst
  have hgb : GMBasesLoaded N y :=
    hs.gb.congr_regs (fun r hr1 _ => hregs r (by omega) (by intro h; subst h; omega))
  have hs_y : GMState U V w N gm (Function.update rf rDst (gm (base + a * idx + c))) y := by
    refine ⟨hwf, her, hgb, hsz.symm ▸ hs.sz, (congrArg (gmAtBit U w N) hmem).trans hs.gm_eq,
      fun r hr => ?_⟩
    rcases eq_or_ne r rDst with rfl | hne
    · rw [Function.update_self, hrdst, hs.gm_eq]
    · rw [Function.update_of_ne hne, hregs r hr hne, hs.regs_eq r hr]
  exact (hrest y hs_y).mono
    (fun _ hz => GMUpdatePost.of_state_eq hst
      (fun r hr => hregs r (by omega) (by intro h; subst h; omega)) hz) le_rfl

theorem step_gm_writeConst {U V w N idx val T : ℕ} {rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrVal_ge : 14 ≤ rVal.val) (hidx_lt4 : idx < 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x) (hrVal : rf rVal = val)
    (hval : val < 2 ^ globalPtrBits N)
    (hrest : ∀ y, GMState U V w N (Function.update gm idx val) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (writeGMConstRegCode idx rVal) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 57) := by
  refine .seq (T₁ := 57) (T₂ := T)
    (writeGMConstRegCode_gmUpdate hrVal_ge hidx_lt4 hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
      ((hs.regs_eq rVal hrVal_ge).trans hrVal) hval)
    (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
  have hs_y : GMState U V w N (Function.update gm idx val) rf y :=
    ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
     hpost.2.2.2.2.1.trans (by rw [hs.gm_eq]),
     fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
  exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl

theorem done_gm_writeConst {U V w N idx val : ℕ} {rVal : Fin 280}
    {gm : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    (hrVal_ge : 14 ≤ rVal.val) (hidx_lt4 : idx < 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x) (hrVal : rf rVal = val)
    (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMConstRegCode idx rVal) x
      (fun z => GMUpdatePost U V w N x z (Function.update gm idx val)) 57 :=
  (writeGMConstRegCode_gmUpdate hrVal_ge hidx_lt4 hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
    ((hs.regs_eq rVal hrVal_ge).trans hrVal) hval).mono
    (fun _ ⟨hpost, _⟩ => hpost.congr_gm (by rw [hs.gm_eq])) le_rfl

theorem step_gm_writeBaseOff {U V w N base off val T : ℕ} {rBase rOff rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrOff_ge : 14 ≤ rOff.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrOff : rf rOff = off) (hrVal : rf rVal = val)
    (hidx : base + off < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N)
    (hrest : ∀ y, GMState U V w N (Function.update gm (base + off) val) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (writeGMBaseOffRegCode rBase rOff rVal) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 57) := by
  refine .seq (T₁ := 57) (T₂ := T)
    (writeGMBaseOffRegCode_gmUpdate hrBase_ge hrOff_ge hrVal_ge hw hN_pos hnU hU
      hs.wf hs.er hs.gb hs.sz
      ((hs.regs_eq rBase hrBase_ge).trans hrBase)
      ((hs.regs_eq rOff hrOff_ge).trans hrOff)
      ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval)
    (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
  have hs_y : GMState U V w N (Function.update gm (base + off) val) rf y :=
    ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
     hpost.2.2.2.2.1.trans (by rw [hs.gm_eq]),
     fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
  exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl

theorem step_gm_writeBucket {U V w N c b val T : ℕ} {rB rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrB_ge : 14 ≤ rB.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x) (hrB : rf rB = b) (hrVal : rf rVal = val)
    (hidx : 4 + 3 * b + c < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N)
    (hrest : ∀ y, GMState U V w N (Function.update gm (4 + 3 * b + c) val) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (writeGMBucketRegCode c rB rVal) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 60) := by
  refine .seq (T₁ := 60) (T₂ := T)
    (writeGMBucketRegCode_gmUpdate hrB_ge hrVal_ge hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
      ((hs.regs_eq rB hrB_ge).trans hrB) ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval)
    (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
  have hs_y : GMState U V w N (Function.update gm (4 + 3 * b + c) val) rf y :=
    ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
     hpost.2.2.2.2.1.trans (by rw [hs.gm_eq]),
     fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
  exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl

theorem done_gm_writeBucket {U V w N c b val : ℕ} {rB rVal : Fin 280}
    {gm : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    (hrB_ge : 14 ≤ rB.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x) (hrB : rf rB = b) (hrVal : rf rVal = val)
    (hidx : 4 + 3 * b + c < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMBucketRegCode c rB rVal) x
      (fun z => GMUpdatePost U V w N x z (Function.update gm (4 + 3 * b + c) val)) 60 :=
  (writeGMBucketRegCode_gmUpdate hrB_ge hrVal_ge hw hN_pos hnU hU hs.wf hs.er hs.gb hs.sz
    ((hs.regs_eq rB hrB_ge).trans hrB) ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval).mono
    (fun _ ⟨hpost, _⟩ => hpost.congr_gm (by rw [hs.gm_eq])) le_rfl

theorem step_gm_write2D {U V w N base stride b k val T : ℕ}
    {rBase rStride rB rK rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrStride_ge : 14 ≤ rStride.val)
    (hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrStride : rf rStride = stride)
    (hrB : rf rB = b) (hrK : rf rK = k) (hrVal : rf rVal = val)
    (hidx : base + b * stride + k < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N)
    (hrest : ∀ y, GMState U V w N (Function.update gm (base + b * stride + k) val) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (writeGM2DRegCode rBase rStride rB rK rVal) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 59) := by
  refine .seq (T₁ := 59) (T₂ := T)
    (writeGM2DRegCode_gmUpdate hrBase_ge hrStride_ge hrB_ge hrK_ge hrVal_ge hw hN_pos hnU hU
      hs.wf hs.er hs.gb hs.sz
      ((hs.regs_eq rBase hrBase_ge).trans hrBase)
      ((hs.regs_eq rStride hrStride_ge).trans hrStride)
      ((hs.regs_eq rB hrB_ge).trans hrB)
      ((hs.regs_eq rK hrK_ge).trans hrK)
      ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval)
    (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
  have hs_y : GMState U V w N (Function.update gm (base + b * stride + k) val) rf y :=
    ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
     hpost.2.2.2.2.1.trans (by rw [hs.gm_eq]),
     fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
  exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl

theorem done_gm_write2D {U V w N base stride b k val : ℕ}
    {rBase rStride rB rK rVal : Fin 280}
    {gm : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrStride_ge : 14 ≤ rStride.val)
    (hrB_ge : 14 ≤ rB.val) (hrK_ge : 14 ≤ rK.val) (hrVal_ge : 14 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrStride : rf rStride = stride)
    (hrB : rf rB = b) (hrK : rf rK = k) (hrVal : rf rVal = val)
    (hidx : base + b * stride + k < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGM2DRegCode rBase rStride rB rK rVal) x
      (fun z => GMUpdatePost U V w N x z (Function.update gm (base + b * stride + k) val)) 59 :=
  (writeGM2DRegCode_gmUpdate hrBase_ge hrStride_ge hrB_ge hrK_ge hrVal_ge hw hN_pos hnU hU
    hs.wf hs.er hs.gb hs.sz
    ((hs.regs_eq rBase hrBase_ge).trans hrBase)
    ((hs.regs_eq rStride hrStride_ge).trans hrStride)
    ((hs.regs_eq rB hrB_ge).trans hrB)
    ((hs.regs_eq rK hrK_ge).trans hrK)
    ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval).mono
    (fun _ ⟨hpost, _⟩ => hpost.congr_gm (by rw [hs.gm_eq])) le_rfl

theorem step_gm_writeAffine {U V w N base a c idx val T : ℕ}
    {rBase rIdx rVal : Fin 280}
    {gm gm' : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    {rest : BitRAM.Code .standard 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val) (hrVal_ge : 14 ≤ rVal.val)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrIdx : rf rIdx = idx) (hrVal : rf rVal = val)
    (hidx : base + a * idx + c < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N)
    (hrest : ∀ y, GMState U V w N (Function.update gm (base + a * idx + c) val) rf y →
      BitRAM.DemonicExecWithin w rest y (fun z => GMUpdatePost U V w N y z gm') T) :
    BitRAM.DemonicExecWithin w (.seq (writeGMAffineRegCode rBase a c rIdx rVal) rest) x
      (fun z => GMUpdatePost U V w N x z gm') (T + 61) := by
  refine .seq (T₁ := 61) (T₂ := T)
    (writeGMAffineRegCode_gmUpdate hrBase_ge hrIdx_ge hrVal_ge ha_le hc_le hw hN_pos hnU hU
      hs.wf hs.er hs.gb hs.sz
      ((hs.regs_eq rBase hrBase_ge).trans hrBase)
      ((hs.regs_eq rIdx hrIdx_ge).trans hrIdx)
      ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval)
    (fun y ⟨hpost, hregs⟩ => ?_) (by omega)
  have hs_y : GMState U V w N (Function.update gm (base + a * idx + c) val) rf y :=
    ⟨hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.1.symm ▸ hs.sz,
     hpost.2.2.2.2.1.trans (by rw [hs.gm_eq]),
     fun r hr => (hregs r hr).trans (hs.regs_eq r hr)⟩
  exact (hrest y hs_y).mono (fun _ hz => hpost.trans hz) le_rfl

theorem done_gm_writeAffine {U V w N base a c idx val : ℕ}
    {rBase rIdx rVal : Fin 280}
    {gm : ℕ → ℕ} {rf : Fin 280 → ℕ} {x : BitRAM.Data 280}
    (hrBase_ge : 14 ≤ rBase.val) (hrIdx_ge : 14 ≤ rIdx.val) (hrVal_ge : 14 ≤ rVal.val)
    (ha_le : a ≤ 4) (hc_le : c ≤ 4)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hs : GMState U V w N gm rf x)
    (hrBase : rf rBase = base) (hrIdx : rf rIdx = idx) (hrVal : rf rVal = val)
    (hidx : base + a * idx + c < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) :
    BitRAM.DemonicExecWithin w (writeGMAffineRegCode rBase a c rIdx rVal) x
      (fun z => GMUpdatePost U V w N x z (Function.update gm (base + a * idx + c) val)) 61 :=
  (writeGMAffineRegCode_gmUpdate hrBase_ge hrIdx_ge hrVal_ge ha_le hc_le hw hN_pos hnU hU
    hs.wf hs.er hs.gb hs.sz
    ((hs.regs_eq rBase hrBase_ge).trans hrBase)
    ((hs.regs_eq rIdx hrIdx_ge).trans hrIdx)
    ((hs.regs_eq rVal hrVal_ge).trans hrVal) hidx hval).mono
    (fun _ ⟨hpost, _⟩ => hpost.congr_gm (by rw [hs.gm_eq])) le_rfl

/-! ## Section 3: Tail-pool `GlobalMeta` updates (`gmAppendTailRegCode`, `gmRemoveTailRegCode`) -/

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.gmAppendTail N gm b` on
`gmAtBit` (`26 ≤ rB.val`, `T = 331`). -/
@[expose]
def gmAppendTailRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMBucketRegCode 1 rB 14)
  (.seq (readGMConstRegCode 1 15)
  (.seq (.op (.bin .mul 16 rB 21))
  (.seq (.op (.bin .add 16 16 14))
  (.seq (writeGMBaseOffRegCode 23 16 15)
  (.seq (writeGMBaseOffRegCode 24 15 16)
  (.seq (.op (.const 17 1))
  (.seq (.op (.bin .add 18 14 17))
  (.seq (writeGMBucketRegCode 1 rB 18)
  (.seq (.op (.bin .add 19 15 17))
        (writeGMConstRegCode 1 19))))))))))

theorem gmAppendTailRegCode_exec {U V w N b : ℕ} {rB : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 26 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b)
    (htail : Succinct.TailBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmRIdx b'))
      (gmAtBit U w N x.mem 1))
    (hr_lt : gmAtBit U w N x.mem (Succinct.gmRIdx b) < tailCapPerBucket N) :
    BitRAM.DemonicExecWithin w (gmAppendTailRegCode rB) x
      (fun z =>
        GMUpdatePost U V w N x z (Succinct.gmAppendTail N (gmAtBit U w N x.mem) b)) 331 := by
  set gm := gmAtBit U w N x.mem
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
  have hptr_idx_lt : Succinct.gmTailPtrBase N + (b * tailCapPerBucket N + gm (Succinct.gmRIdx b)) <
      globalMetaLen N := Succinct.gmTailPtrIdx_lt hb_pos hb hr_lt
  have ht_cap : gm 1 < maxTailItems N := Succinct.ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have hmax_tail_le : maxTailItems N ≤ N := maxTailItems_le N
  have hown_idx_lt : Succinct.gmTailOwnerBase N + gm 1 < globalMetaLen N :=
    Succinct.gmTailOwnerIdx_lt hb_pos ht_cap
  have ht_val_lt : gm 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hd_val_lt : b * tailCapPerBucket N + gm (Succinct.gmRIdx b) < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold Succinct.gmTailPtrBase at hptr_idx_lt; omega)
  have hr1_val_lt : gm (Succinct.gmRIdx b) + 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold Succinct.gmTailPtrBase Succinct.gmSlabDirBase at hptr_idx_lt; omega)
  have ht1_val_lt : gm 1 + 1 < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_d : Fits w (b * tailCapPerBucket N + gm (Succinct.gmRIdx b)) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz (by omega)
  have hfit_mul : Fits w (b * tailCapPerBucket N) := Fits.of_le hfit_d (by omega)
  have hfit_r1 : Fits w (gm (Succinct.gmRIdx b) + 1) :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz
      (by unfold Succinct.gmTailPtrBase Succinct.gmSlabDirBase at hptr_idx_lt; omega)
  have hfit_t1 : Fits w (gm 1 + 1) := fits_of_le_N hw hnU hU (by omega)
  have hs0 : GMState U V w N gm x.regs x := GMState.init hx her hgb hsz
  have h21 : x.regs 21 = tailCapPerBucket N := hgb.2.1
  have h23 : x.regs 23 = Succinct.gmTailPtrBase N := hgb.2.2.2.1
  have h24 : x.regs 24 = Succinct.gmTailOwnerBase N := hgb.2.2.2.2.1
  have hrB_ne : ∀ r : Fin 280, r.val < 26 → rB ≠ r := fun _ _ h => by subst h; omega
  have h14 : rB ≠ 14 := hrB_ne 14 (by decide)
  have h15 : rB ≠ 15 := hrB_ne 15 (by decide)
  have h16 : rB ≠ 16 := hrB_ne 16 (by decide)
  have h17 : rB ≠ 17 := hrB_ne 17 (by decide)
  have h18 : rB ≠ 18 := hrB_ne 18 (by decide)
  unfold gmAppendTailRegCode Succinct.gmAppendTail Succinct.gmRIdx
    Succinct.gmTailPtrFlatIdx Succinct.gmTailOwnerIdx
  refine step_gm_readBucket (rB := rB) (rDst := 14)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hs0 hrB hr_idx_lt (fun y1 hs1 => ?_)
  refine step_gm_readConst (rDst := 15) (idx := 1)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs1 (fun y2 hs2 => ?_)
  refine step_gm_bin (op := .mul) (rDst := 16) (rA := rB) (rB := 21) (v := b * tailCapPerBucket N)
    (by decide) (by decide) (by omega) (by decide)
    hs2 (by simp [BinOp.eval, h14, h15, hrB, h21]) hfit_mul
    (fun hs3 => ?_)
  refine step_gm_bin (op := .add) (rDst := 16) (rA := 16) (rB := 14)
    (v := b * tailCapPerBucket N + gm (4 + 3 * b + 1)) (by decide) (by decide) (by decide)
    (by decide) hs3 (by simp +decide [BinOp.eval]) hfit_d (fun hs4 => ?_)
  refine step_gm_writeBaseOff (rBase := 23) (rOff := 16) (rVal := 15)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs4
    (by simp +decide [h23]) (by simp +decide [Succinct.gmRIdx]) (by simp +decide)
    hptr_idx_lt ht_val_lt (fun y5 hs5 => ?_)
  refine step_gm_writeBaseOff (rBase := 24) (rOff := 15) (rVal := 16)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs5
    (by simp +decide [h24]) (by simp +decide) (by simp +decide [Succinct.gmRIdx])
    hown_idx_lt hd_val_lt (fun y6 hs6 => ?_)
  refine step_gm_const (rDst := 17) (c := 1) (by decide) (by decide) hs6 hfit_1 (fun hs7 => ?_)
  refine step_gm_bin (op := .add) (rDst := 18) (rA := 14) (rB := 17)
    (v := gm (4 + 3 * b + 1) + 1) (by decide) (by decide) (by decide) (by decide)
    hs7 (by simp +decide [BinOp.eval]) hfit_r1 (fun hs8 => ?_)
  refine step_gm_writeBucket (c := 1) (rB := rB) (rVal := 18)
    (by omega) (by decide) hw hN_pos hnU hU hs8
    (by simp [h14, h15, h16, h17, h18, hrB])
    (by simp +decide [Succinct.gmRIdx]) hr_idx_lt hr1_val_lt (fun y9 hs9 => ?_)
  refine step_gm_bin (op := .add) (rDst := 19) (rA := 15) (rB := 17) (v := gm 1 + 1)
    (by decide) (by decide) (by decide) (by decide)
    hs9 (by simp +decide [BinOp.eval]) hfit_t1 (fun hs10 => ?_)
  exact done_gm_writeConst (idx := 1) (rVal := 19)
    (by decide) (by decide) hw hN_pos hnU hU hs10 (by simp +decide) ht1_val_lt

/-- Uniform `BitRAM.Code .standard 280` program executing `Succinct.gmRemoveTail N gm b` on
`gmAtBit` (`26 ≤ rB.val`, `T = 423`). -/
@[expose]
def gmRemoveTailRegCode (rB : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readGMBucketRegCode 1 rB 14)
  (.seq (.op (.const 15 1))
  (.seq (.op (.bin .sub 14 14 15))
  (.seq (readGM2DRegCode 23 21 rB 14 16)
  (.seq (readGMConstRegCode 1 17)
  (.seq (.op (.bin .sub 17 17 15))
  (.seq (readGMBaseOffRegCode 24 17 18)
  (.seq (writeGMBaseOffRegCode 23 18 16)
  (.seq (writeGMBaseOffRegCode 24 16 18)
  (.seq (writeGMBucketRegCode 1 rB 14)
        (writeGMConstRegCode 1 17))))))))))

theorem gmRemoveTailRegCode_exec {U V w N b : ℕ} {rB : Fin 280} {x : BitRAM.Data 280}
    (hrB_ge : 26 ≤ rB.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x) (hgb : GMBasesLoaded N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hrB : x.regs rB = b)
    (htail : Succinct.TailBijection N (gmAtBit U w N x.mem)
      (fun b' => gmAtBit U w N x.mem (Succinct.gmRIdx b'))
      (gmAtBit U w N x.mem 1))
    (hr_pos : 1 ≤ gmAtBit U w N x.mem (Succinct.gmRIdx b)) :
    BitRAM.DemonicExecWithin w (gmRemoveTailRegCode rB) x
      (fun z =>
        GMUpdatePost U V w N x z (Succinct.gmRemoveTail N (gmAtBit U w N x.mem) b)) 423 := by
  set gm := gmAtBit U w N x.mem
  have hnt_le : gm 1 ≤ N := htail.ntails_le.trans (maxTailItems_le N)
  set r_del := gm (Succinct.gmRIdx b) - 1
  set t_del := gm (Succinct.gmTailPtrIdx N b r_del)
  set t_last := gm 1 - 1
  set d_last := gm (Succinct.gmTailOwnerIdx N t_last)
  have hr_del_lt : r_del < gm (Succinct.gmRIdx b) := by omega
  have hr_del_cap : r_del < tailCapPerBucket N := lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt b hb r_del hr_del_lt
  have ht_last_lt : t_last < gm 1 := by omega
  have hvalid_last := htail.owner_valid t_last ht_last_lt
  dsimp only at hvalid_last
  rcases hvalid_last with ⟨hb_last, hr_last, _⟩
  have hr_last_cap : d_last % tailCapPerBucket N < tailCapPerBucket N :=
    lt_of_lt_of_le hr_last (htail.r_le _ hb_last)
  have hd_last_lt : d_last < maxTailItems N := by
    have hdiv_mod := Nat.div_add_mod d_last (tailCapPerBucket N)
    rw [Nat.mul_comm] at hdiv_mod
    unfold maxTailItems
    have h1 : (d_last / tailCapPerBucket N + 1) * tailCapPerBucket N ≤
        numBuckets N * tailCapPerBucket N :=
      Nat.mul_le_mul_right _ hb_last
    nlinarith
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
  have hptr_del_lt :
      Succinct.gmTailPtrBase N + b * tailCapPerBucket N + r_del < globalMetaLen N := by
    have h := Succinct.gmTailPtrIdx_lt hb_pos hb hr_del_cap
    unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx at h
    omega
  have ht_last_cap : t_last < maxTailItems N := lt_of_lt_of_le ht_last_lt htail.ntails_le
  have hown_last_lt : Succinct.gmTailOwnerBase N + t_last < globalMetaLen N :=
    Succinct.gmTailOwnerIdx_lt hb_pos ht_last_cap
  have hptr_last_lt : Succinct.gmTailPtrBase N + d_last < globalMetaLen N :=
    Succinct.gmTailPtrFlatIdx_lt hb_pos hd_last_lt
  have ht_del_cap : t_del < maxTailItems N := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have hown_del_lt : Succinct.gmTailOwnerBase N + t_del < globalMetaLen N :=
    Succinct.gmTailOwnerIdx_lt hb_pos ht_del_cap
  have ht_del_val_lt : t_del < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hd_last_val_lt : d_last < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold Succinct.gmTailPtrBase at hptr_last_lt; omega)
  have hr_del_val_lt : r_del < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold Succinct.gmTailPtrBase Succinct.gmSlabDirBase at hptr_del_lt; omega)
  have ht_last_val_lt : t_last < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hfit_1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
  have hfit_rdel : Fits w r_del :=
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz
      (by unfold Succinct.gmTailPtrBase Succinct.gmSlabDirBase at hptr_del_lt; omega)
  have hfit_tlast : Fits w t_last := fits_of_le_N hw hnU hU (by omega)
  have hs0 : GMState U V w N gm x.regs x := GMState.init hx her hgb hsz
  have h21 : x.regs 21 = tailCapPerBucket N := hgb.2.1
  have h23 : x.regs 23 = Succinct.gmTailPtrBase N := hgb.2.2.2.1
  have h24 : x.regs 24 = Succinct.gmTailOwnerBase N := hgb.2.2.2.2.1
  have hrB_ne : ∀ r : Fin 280, r.val < 26 → rB ≠ r := by
    intro r hr h; subst h; omega
  have h14 : rB ≠ 14 := hrB_ne 14 (by decide)
  have h15 : rB ≠ 15 := hrB_ne 15 (by decide)
  have h16 : rB ≠ 16 := hrB_ne 16 (by decide)
  have h17 : rB ≠ 17 := hrB_ne 17 (by decide)
  have h18 : rB ≠ 18 := hrB_ne 18 (by decide)
  have hptr_eq : Succinct.gmTailPtrBase N + b * tailCapPerBucket N + r_del =
      Succinct.gmTailPtrIdx N b r_del := by
    unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx; omega
  unfold gmRemoveTailRegCode Succinct.gmRemoveTail
  refine step_gm_readBucket (c := 1) (rB := rB) (rDst := 14)
    (by omega) (by decide) (by decide) hw hN_pos hnU hU hs0 hrB hr_idx_lt
    (fun y1 hs1 => ?_)
  refine step_gm_const (rDst := 15) (c := 1) (by decide) (by decide) hs1 hfit_1 (fun hs2 => ?_)
  refine step_gm_bin (op := .sub) (rDst := 14) (rA := 14) (rB := 15) (v := r_del)
    (by decide) (by decide) (by decide) (by decide)
    hs2 (by simp +decide [BinOp.eval, r_del, Succinct.gmRIdx]) hfit_rdel (fun hs3 => ?_)
  refine step_gm_read2D (rBase := 23) (rStride := 21) (rB := rB) (rK := 14) (rDst := 16)
    (by decide) (by decide) (by omega) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs3 (by simp +decide [h23]) (by simp +decide [h21])
    (by simp [h14, h15, hrB])
    (by simp +decide) hptr_del_lt (fun y4 hs4 => ?_)
  refine step_gm_readConst (idx := 1) (rDst := 17)
    (by decide) (by decide) (by decide) hw hN_pos hnU hU hs4
    (fun y5 hs5 => ?_)
  refine step_gm_bin (op := .sub) (rDst := 17) (rA := 17) (rB := 15) (v := t_last)
    (by decide) (by decide) (by decide) (by decide)
    hs5 (by simp +decide [BinOp.eval, t_last]) hfit_tlast (fun hs6 => ?_)
  refine step_gm_readBaseOff (rBase := 24) (rOff := 17) (rDst := 18)
    (by decide) (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs6 (by simp +decide [h24]) (by simp +decide) hown_last_lt
    (fun y7 hs7 => ?_)
  refine step_gm_writeBaseOff (rBase := 23) (rOff := 18) (rVal := 16)
    (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs7 (by simp +decide [h23])
    (by simp +decide [d_last, Succinct.gmTailOwnerIdx])
    (by simp +decide [t_del, hptr_eq]) hptr_last_lt ht_del_val_lt (fun y8 hs8 => ?_)
  refine step_gm_writeBaseOff (rBase := 24) (rOff := 16) (rVal := 18)
    (by decide) (by decide) (by decide)
    hw hN_pos hnU hU hs8 (by simp +decide [h24])
    (by simp +decide [t_del, hptr_eq])
    (by simp +decide [d_last, Succinct.gmTailOwnerIdx]) hown_del_lt hd_last_val_lt
    (fun y9 hs9 => ?_)
  refine step_gm_writeBucket (c := 1) (rB := rB) (rVal := 14)
    (by omega) (by decide) hw hN_pos hnU hU hs9
    (by simp [h14, h15, h16, h17, h18, hrB])
    (by simp +decide) hr_idx_lt hr_del_val_lt (fun y10 hs10 => ?_)
  exact done_gm_writeConst (idx := 1) (rVal := 17)
    (by decide) (by decide) hw hN_pos hnU hU hs10
    (by simp +decide [t_last]) ht_last_val_lt

end Cslib.DataStructure.Dictionary.BitResizable
