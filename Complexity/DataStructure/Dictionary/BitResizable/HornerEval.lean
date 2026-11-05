/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.EpochAccess

/-!
# Uniform `BitRAM.Code .standard 280` Dense-Item Accessors, Hash Evaluation, Query, and Update

This module builds on `Complexity.DataStructure.Dictionary.BitResizable.EpochAccess` to provide
uniform parameter-free `BitRAM.Code .standard 280` machine programs for:
1. Dense item accessors (`readDenseQRegCode`, `readDenseVRegCode`, `writeDenseQRegCode`,
   `writeDenseVRegCode`, `appendDenseRegCode`, `popDenseRegCode`).
2. Two-stage Feistel + reduced 3-wise polynomial hash evaluation (`evalHashRegCode`).
3. Physical slot and circular-window index translation (`slotOfRegCode`, `denseOfCircRegCode`,
   `denseOfPhysRegCode`).
4. Uniform bucket search (`searchBucketRegCode`), dictionary query (`queryRegCode`), and in-place
   update (`insertHitRegCode`) with worst-case and expected `O(1)` instruction bounds.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.Probability
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Uniform dense-item accessors on `BitRAM.Code .standard 280` -/

/-- Parameter-free `BitRAM.Code .standard 280` reading `denseQuotAt U V w N x.toBitMemoryState d`
(where `d = x.regs rD`) into `rDst` (`42` instructions), preserving all registers `r ≥ 16`
(`r ≠ rDst`). -/
@[expose]
def readDenseQRegCode (rD rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 1 rD))
    (.seq (.op (.copy 12 244))
      (.seq (embed16 readDenseQuotRegCode)
        (.op (.copy rDst 0))))

/-- Parameter-free `BitRAM.Code .standard 280` reading `denseValAt U V w N x.toBitMemoryState d`
(where `d = x.regs rD`) into `rDst` (`44` instructions), preserving all registers `r ≥ 16`
(`r ≠ rDst`). -/
@[expose]
def readDenseVRegCode (rD rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 1 rD))
    (.seq (.op (.copy 12 244))
      (.seq (.op (.copy 13 243))
        (.seq (embed16 readDenseValRegCode)
          (.op (.copy rDst 0)))))

/-- Parameter-free `BitRAM.Code .standard 280` writing `x.regs rQ` into the dense quotient at
`x.regs rD` (`53` instructions), preserving all registers `r ≥ 16`. -/
@[expose]
def writeDenseQRegCode (rD rQ : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 1 rD))
    (.seq (.op (.copy 12 244))
      (.seq (.op (.copy 14 rQ))
        (embed16 writeDenseQuotRegCode)))

/-- Parameter-free `BitRAM.Code .standard 280` writing `x.regs rV` into the dense value at
`x.regs rD` (`55` instructions), preserving all registers `r ≥ 16`. -/
@[expose]
def writeDenseVRegCode (rD rV : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 1 rD))
    (.seq (.op (.copy 12 244))
      (.seq (.op (.copy 13 243))
        (.seq (.op (.copy 15 rV))
          (embed16 writeDenseValRegCode))))

/-- Parameter-free `BitRAM.Code .standard 280` appending dense item `(x.regs rQ, x.regs rV)` via
`.grow` (`96` instructions), preserving all registers `r ≥ 16`. -/
@[expose]
def appendDenseRegCode (rQ rV : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 12 244))
    (.seq (.op (.copy 13 243))
      (.seq (.op (.copy 14 rQ))
        (.seq (.op (.copy 15 rV))
          (embed16 appendDenseItemRegCode))))

/-- Parameter-free `BitRAM.Code .standard 280` popping the last dense item via `.shrink`
(`6` instructions), preserving all registers `r ≥ 16`. -/
@[expose]
def popDenseRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 12 244))
    (.seq (.op (.copy 13 243))
      (embed16 popDenseItemRegCode))

theorem readDenseQRegCode_exec {U V w N n_t d : ℕ} {rD rDst : Fin 280} {x : BitRAM.Data 280}
    (_hrD_ge : 16 ≤ rD.val)
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hrD : x.regs rD = d)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (readDenseQRegCode rD rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = denseQuotAt U V w N x.toBitMemoryState d ∧
        (∀ r : Fin 280, 16 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 42 := by
  refine step_dExec_copy (v := d) (T := 41) hrD ?_
  refine step_dExec_copy (v := quotientBits U N) (T := 40)
    (by simp +decide [BitRAM.Data.set, her.r244]) ?_
  set x₁ := (x.set 1 d).set 12 (quotientBits U N)
  have hx₁_wf : (x₁.comap embed16Map).WellFormed w :=
    wf_comap16 (wf_set 12 (wf_set 1 hx (hrD ▸ hx.regs_fits rD)) (her.r244 ▸ hx.regs_fits 244))
  refine .seq (T₁ := 39) (T₂ := 1)
    (embed16_exec
      (readDenseQuotRegCode_exec hw hU hx₁_wf hd hsz hm2 hm3
        (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
        (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])))
    (fun y₁ ⟨⟨hr0, hst, hy₁_wf16, _⟩, hy₁_hi⟩ => ?_) (by omega)
  refine DemonicExecWithin.copy ?_
  have hy_regs : ∀ r : Fin 280, 16 ≤ r.val → y₁.regs r = x.regs r := by
    intro r hr
    rw [hy₁_hi r hr]
    have h12 : r ≠ 12 := by intro h; subst h; omega
    have h1 : r ≠ 1 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, h12, h1]
  have hy₁_wf : y₁.WellFormed w := wf_of_comap16 hx hy₁_wf16 hy_regs
  have hy_wf : (y₁.set rDst (y₁.regs 0)).WellFormed w := wf_set rDst hy₁_wf (hy₁_wf.regs_fits 0)
  refine ⟨hst, hy_wf, ?_, fun r hr hne => ?_⟩
  · simp only [Fin.isValue, BitRAM.Data.set_regs, Function.update_self]
    exact hr0
  · simp [BitRAM.Data.set, hne, hy_regs r hr]

theorem readDenseVRegCode_exec {U V w N n_t d : ℕ} {rD rDst : Fin 280} {x : BitRAM.Data 280}
    (_hrD_ge : 16 ≤ rD.val)
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hrD : x.regs rD = d)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (readDenseVRegCode rD rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = denseValAt U V w N x.toBitMemoryState d ∧
        (∀ r : Fin 280, 16 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 44 := by
  refine step_dExec_copy (v := d) (T := 43) hrD ?_
  refine step_dExec_copy (v := quotientBits U N) (T := 42)
    (by simp +decide [BitRAM.Data.set, her.r244]) ?_
  refine step_dExec_copy (v := valBits V) (T := 41)
    (by simp +decide [BitRAM.Data.set, her.r243]) ?_
  set x₁ := ((x.set 1 d).set 12 (quotientBits U N)).set 13 (valBits V)
  have hx₁_wf : (x₁.comap embed16Map).WellFormed w :=
    wf_comap16 (wf_set 13 (wf_set 12 (wf_set 1 hx (hrD ▸ hx.regs_fits rD))
      (her.r244 ▸ hx.regs_fits 244)) (her.r243 ▸ hx.regs_fits 243))
  refine .seq (T₁ := 40) (T₂ := 1)
    (embed16_exec
      (readDenseValRegCode_exec hw hV hx₁_wf hd hsz hm2 hm3
        (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
        (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
        (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])))
    (fun y₁ ⟨⟨hr0, hst, hy₁_wf16, _⟩, hy₁_hi⟩ => ?_) (by omega)
  refine DemonicExecWithin.copy ?_
  have hy_regs : ∀ r : Fin 280, 16 ≤ r.val → y₁.regs r = x.regs r := by
    intro r hr
    rw [hy₁_hi r hr]
    have h13 : r ≠ 13 := by intro h; subst h; omega
    have h12 : r ≠ 12 := by intro h; subst h; omega
    have h1 : r ≠ 1 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, h13, h12, h1]
  have hy₁_wf : y₁.WellFormed w := wf_of_comap16 hx hy₁_wf16 hy_regs
  have hy_wf : (y₁.set rDst (y₁.regs 0)).WellFormed w := wf_set rDst hy₁_wf (hy₁_wf.regs_fits 0)
  refine ⟨hst, hy_wf, ?_, fun r hr hne => ?_⟩
  · simp only [Fin.isValue, BitRAM.Data.set_regs, Function.update_self]
    exact hr0
  · simp [BitRAM.Data.set, hne, hy_regs r hr]

theorem writeDenseQRegCode_exec {U V w N n_t d q : ℕ} {rD rQ : Fin 280} {x : BitRAM.Data 280}
    (_hrD_ge : 16 ≤ rD.val) (hrQ_ge : 16 ≤ rQ.val)
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hrD : x.regs rD = d) (hrQ : x.regs rQ = q)
    (hq : Fits (quotientBits U N) q)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (writeDenseQRegCode rD rQ) x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (itemQuotBitOff U V w N d) (quotientBits U N) q)).1 ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 53 := by
  refine step_dExec_copy (v := d) (T := 52) hrD ?_
  refine step_dExec_copy (v := quotientBits U N) (T := 51)
    (by simp +decide [BitRAM.Data.set, her.r244]) ?_
  refine step_dExec_copy (v := q) (T := 50)
    (by
      have hne1 : rQ ≠ 1 := by intro h; subst h; omega
      have hne12 : rQ ≠ 12 := by intro h; subst h; omega
      simp [BitRAM.Data.set, hne1, hne12, hrQ]) ?_
  set x₁ := ((x.set 1 d).set 12 (quotientBits U N)).set 14 q
  have hx₁_wf : (x₁.comap embed16Map).WellFormed w :=
    wf_comap16 (wf_set 14 (wf_set 12 (wf_set 1 hx (hrD ▸ hx.regs_fits rD))
      (her.r244 ▸ hx.regs_fits 244)) (hrQ ▸ hx.regs_fits rQ))
  refine (embed16_exec
    (writeDenseQuotRegCode_exec hw hU hx₁_wf hd hsz hm2 hm3
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      hq)).mono
    (fun y ⟨⟨hst, hy_wf16, _⟩, hy_hi⟩ => ?_) le_rfl
  have hy_regs : ∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r := by
    intro r hr
    rw [hy_hi r hr]
    have h14 : r ≠ 14 := by intro h; subst h; omega
    have h12 : r ≠ 12 := by intro h; subst h; omega
    have h1 : r ≠ 1 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, h14, h12, h1]
  have hy_wf : y.WellFormed w := wf_of_comap16 hx hy_wf16 hy_regs
  exact ⟨hst, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), hy_regs⟩

theorem writeDenseVRegCode_exec {U V w N n_t d v : ℕ} {rD rV : Fin 280} {x : BitRAM.Data 280}
    (_hrD_ge : 16 ≤ rD.val) (hrV_ge : 16 ≤ rV.val)
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hrD : x.regs rD = d) (hrV : x.regs rV = v)
    (hv : Fits (valBits V) v)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (writeDenseVRegCode rD rV) x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (itemValBitOff U V w N d) (valBits V) v)).1 ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 55 := by
  refine step_dExec_copy (v := d) (T := 54) hrD ?_
  refine step_dExec_copy (v := quotientBits U N) (T := 53)
    (by simp +decide [BitRAM.Data.set, her.r244]) ?_
  refine step_dExec_copy (v := valBits V) (T := 52)
    (by simp +decide [BitRAM.Data.set, her.r243]) ?_
  refine step_dExec_copy (v := v) (T := 51)
    (by
      have hne1 : rV ≠ 1 := by intro h; subst h; omega
      have hne12 : rV ≠ 12 := by intro h; subst h; omega
      have hne13 : rV ≠ 13 := by intro h; subst h; omega
      simp [BitRAM.Data.set, hne1, hne12, hne13, hrV]) ?_
  set x₁ := (((x.set 1 d).set 12 (quotientBits U N)).set 13 (valBits V)).set 15 v
  have hx₁_wf : (x₁.comap embed16Map).WellFormed w :=
    wf_comap16 (wf_set 15 (wf_set 13 (wf_set 12 (wf_set 1 hx (hrD ▸ hx.regs_fits rD))
      (her.r244 ▸ hx.regs_fits 244)) (her.r243 ▸ hx.regs_fits 243)) (hrV ▸ hx.regs_fits rV))
  refine (embed16_exec
    (writeDenseValRegCode_exec hw hV hx₁_wf hd hsz hm2 hm3
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      hv)).mono
    (fun y ⟨⟨hst, hy_wf16, _⟩, hy_hi⟩ => ?_) le_rfl
  have hy_regs : ∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r := by
    intro r hr
    rw [hy_hi r hr]
    have h15 : r ≠ 15 := by intro h; subst h; omega
    have h13 : r ≠ 13 := by intro h; subst h; omega
    have h12 : r ≠ 12 := by intro h; subst h; omega
    have h1 : r ≠ 1 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, h15, h13, h12, h1]
  have hy_wf : y.WellFormed w := wf_of_comap16 hx hy_wf16 hy_regs
  exact ⟨hst, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), hy_regs⟩

theorem appendDenseRegCode_exec {U V w N q v : ℕ} {rQ rV : Fin 280} {x : BitRAM.Data 280}
    (hrQ_ge : 16 ≤ rQ.val) (hrV_ge : 16 ≤ rV.val)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hrQ : x.regs rQ = q) (hrV : x.regs rV = v)
    (hq : Fits (quotientBits U N) q) (hv : Fits (valBits V) v)
    (hfits : Fits w (x.bitSize + itemBits U V N)) :
    BitRAM.DemonicExecWithin w (appendDenseRegCode rQ rV) x
      (fun y =>
        y.toBitMemoryState = appendDenseItemState U V w N q v x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize + itemBits U V N ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 96 := by
  refine step_dExec_copy (v := quotientBits U N) (T := 95)
    (by simp [her.r244]) ?_
  refine step_dExec_copy (v := valBits V) (T := 94)
    (by simp +decide [BitRAM.Data.set, her.r243]) ?_
  refine step_dExec_copy (v := q) (T := 93)
    (by
      have hne12 : rQ ≠ 12 := by intro h; subst h; omega
      have hne13 : rQ ≠ 13 := by intro h; subst h; omega
      simp [BitRAM.Data.set, hne12, hne13, hrQ]) ?_
  refine step_dExec_copy (v := v) (T := 92)
    (by
      have hne12 : rV ≠ 12 := by intro h; subst h; omega
      have hne13 : rV ≠ 13 := by intro h; subst h; omega
      have hne14 : rV ≠ 14 := by intro h; subst h; omega
      simp [BitRAM.Data.set, hne12, hne13, hne14, hrV]) ?_
  set x₁ := (((x.set 12 (quotientBits U N)).set 13 (valBits V)).set 14 q).set 15 v
  have hx₁_wf : (x₁.comap embed16Map).WellFormed w :=
    wf_comap16 (wf_set 15 (wf_set 14 (wf_set 13 (wf_set 12 hx (her.r244 ▸ hx.regs_fits 244))
      (her.r243 ▸ hx.regs_fits 243)) (hrQ ▸ hx.regs_fits rQ)) (hrV ▸ hx.regs_fits rV))
  refine (embed16_exec
    (appendDenseItemRegCode_exec hw hU hV hx₁_wf
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      hq hv hfits)).mono
    (fun y ⟨⟨hst, hy_wf16, hy_sz, _⟩, hy_hi⟩ => ?_) le_rfl
  have hy_regs : ∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r := by
    intro r hr
    rw [hy_hi r hr]
    have h15 : r ≠ 15 := by intro h; subst h; omega
    have h14 : r ≠ 14 := by intro h; subst h; omega
    have h13 : r ≠ 13 := by intro h; subst h; omega
    have h12 : r ≠ 12 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, h15, h14, h13, h12]
  have hy_wf : y.WellFormed w := wf_of_comap16 hx hy_wf16 hy_regs
  exact ⟨hst, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), hy_sz, hy_regs⟩

theorem popDenseRegCode_exec {U V w N n_t : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : x.bitSize = itemBitOff U V w N (n_t + 1)) :
    BitRAM.DemonicExecWithin w popDenseRegCode x
      (fun y =>
        y.toBitMemoryState = popDenseItemState U V w N x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = itemBitOff U V w N n_t ∧
        (∀ d < n_t,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 6 := by
  refine step_dExec_copy (v := quotientBits U N) (T := 5)
    (by simp [her.r244]) ?_
  refine step_dExec_copy (v := valBits V) (T := 4)
    (by simp +decide [BitRAM.Data.set, her.r243]) ?_
  set x₁ := (x.set 12 (quotientBits U N)).set 13 (valBits V)
  have hx₁_wf : (x₁.comap embed16Map).WellFormed w :=
    wf_comap16 (wf_set 13 (wf_set 12 hx (her.r244 ▸ hx.regs_fits 244))
      (her.r243 ▸ hx.regs_fits 243))
  refine (embed16_exec
    (popDenseItemRegCode_exec hw hU hV hx₁_wf
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embed16Map, BitRAM.Data.set])
      hsz)).mono
    (fun y ⟨⟨hst, hy_wf16, hy_sz, hitems, hmeta, _⟩, hy_hi⟩ => ?_) le_rfl
  have hy_regs : ∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r := by
    intro r hr
    rw [hy_hi r hr]
    have h13 : r ≠ 13 := by intro h; subst h; omega
    have h12 : r ≠ 12 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, h13, h12]
  have hy_wf : y.WellFormed w := wf_of_comap16 hx hy_wf16 hy_regs
  exact ⟨hst, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), hy_sz, hitems, hmeta,
    hy_regs⟩

/-! ## Section 2: Lifting `WordRAM.Code .exact` to `BitRAM.Code .standard` and Hash Evaluation -/

/-- Lift a structured `WordRAM.Code .exact r` program to `BitRAM.Code .standard r`. -/
@[expose]
def ofExactCode {r : ℕ} : WordRAM.Code .exact r → BitRAM.Code .standard r
  | .op o => .op (o.mapSimulates .exactStandard)
  | .seq c₁ c₂ => .seq (ofExactCode c₁) (ofExactCode c₂)
  | .branch c pos neg => .branch c (ofExactCode pos) (ofExactCode neg)
  | .loop c body => .loop c (ofExactCode body)
  | .rand dst src => .rand dst src

/-- Syntactic check that a `WordRAM.Code B r` program contains no `.load`, `.store`, `.loop`, or
`.rand`. -/
@[expose]
def NoLoadStore {B : Basis} {r : ℕ} : WordRAM.Code B r → Bool
  | .op (.load _ _) => false
  | .op (.store _ _) => false
  | .op _ => true
  | .seq c₁ c₂ => NoLoadStore c₁ && NoLoadStore c₂
  | .branch _ pos neg => NoLoadStore pos && NoLoadStore neg
  | .loop _ _ => false
  | .rand _ _ => false

theorem evalOp_of_wordRAM_noLoadStore {B : Basis} {r w : ℕ} {o : WordRAM.Op B r}
    {x : BitRAM.Data r} {y₀ : WordRAM.Data r}
    (hno : match o with | .load _ _ | .store _ _ => False | _ => True)
    (heval : o.eval w x.toWordRAMData = some y₀) :
    BitRAM.evalOp w o x = some ⟨y₀.regs, y₀.mem, x.bitSize⟩ := by
  cases o with
  | const d v =>
    dsimp only [WordRAM.Op.eval, BitRAM.evalOp,
      WordRAM.Data.put, BitRAM.Data.put, BitRAM.Data.toWordRAMData] at heval ⊢
    split_ifs at heval ⊢ with hfit
    · injection heval with hy; subst hy; rfl
  | copy d s =>
    injection heval with hy; subst hy; rfl
  | alu f d args =>
    dsimp only [WordRAM.Op.eval, BitRAM.evalOp, BitRAM.Data.toWordRAMData] at heval ⊢
    rcases hinterp : B.interp w f (x.regs ∘ args) with _ | val <;>
      simp_all [WordRAM.Data.put, BitRAM.Data.put]
    rcases heval with ⟨_, rfl⟩
    rfl
  | load _ _ => cases hno
  | store _ _ => cases hno

theorem evalOp_of_exact_noLoadStore {r w : ℕ} {o : WordRAM.Op .exact r}
    {x : BitRAM.Data r} {y₀ : WordRAM.Data r}
    (hno : NoLoadStore (.op o) = true)
    (heval : o.eval w x.toWordRAMData = some y₀) :
    BitRAM.evalOp w (o.mapSimulates .exactStandard) x =
      some ⟨y₀.regs, y₀.mem, x.bitSize⟩ := by
  refine evalOp_of_wordRAM_noLoadStore ?_
    (WordRAM.Op.eval_mapSimulates_of_some .exactStandard heval)
  cases o <;> simp_all [NoLoadStore, WordRAM.Op.mapSimulates]

theorem dExec_seq_eq {r w : ℕ} {c₁ c₂ : BitRAM.Code .standard r}
    {x y : BitRAM.Data r} {P : BitRAM.Data r → Prop} {T₁ T₂ : ℕ}
    (h₁ : BitRAM.DemonicExecWithin w c₁ x (fun z => z = y) T₁)
    (h₂ : BitRAM.DemonicExecWithin w c₂ y P T₂) :
    BitRAM.DemonicExecWithin w (.seq c₁ c₂) x P (T₁ + T₂) :=
  .seq h₁ (fun _ hz => hz ▸ h₂) le_rfl

theorem dExec_of_exec_noLoadStore {r w : ℕ} {c : WordRAM.Code .exact r}
    {x : BitRAM.Data r} {y₀ : WordRAM.Data r} {T : ℕ}
    (hno : NoLoadStore c = true)
    (hex : WordRAM.Exec w c x.toWordRAMData y₀ T) :
    BitRAM.DemonicExecWithin w (ofExactCode c) x
      (fun y => y = ⟨y₀.regs, y₀.mem, x.bitSize⟩) T := by
  generalize hx₀ : x.toWordRAMData = x₀ at hex
  induction hex generalizing x with
  | @op o x₀ y₀ heval =>
    subst hx₀
    exact .op (evalOp_of_exact_noLoadStore hno heval) rfl le_rfl
  | @seq c₁ c₂ x₀ y₁ y₂ m n _ _ ih₁ ih₂ =>
    subst hx₀
    simp only [NoLoadStore, Bool.and_eq_true] at hno
    refine .seq (ih₁ hno.1 rfl) (fun z hz => ?_) le_rfl
    subst hz
    exact ih₂ hno.2 rfl
  | @branch_pos cond pos neg x₀ y₀ n hc _ ih =>
    subst hx₀
    simp only [NoLoadStore, Bool.and_eq_true] at hno
    exact .branch_pos hc (ih hno.1 rfl) le_rfl
  | @branch_neg cond pos neg x₀ y₀ n hc _ ih =>
    subst hx₀
    simp only [NoLoadStore, Bool.and_eq_true] at hno
    exact .branch_neg hc (ih hno.2 rfl) le_rfl
  | loop_exit => cases hno
  | loop_iter => cases hno

theorem dExec_load_of_exec {r w : ℕ} {d a : Fin r}
    {x : BitRAM.Data r} {y₀ : WordRAM.Data r}
    (hadm : x.regs a < x.wordSize w)
    (hex : WordRAM.Exec (B := .exact) w (.op (.load d a)) x.toWordRAMData y₀ 1) :
    BitRAM.DemonicExecWithin w (ofExactCode (.op (.load d a))) x
      (fun y => y = ⟨y₀.regs, y₀.mem, x.bitSize⟩) 1 := by
  cases hex with
  | op heval =>
    dsimp only [WordRAM.Op.eval, BitRAM.Data.toWordRAMData, WordRAM.Data.set] at heval
    injection heval with hy
    subst hy
    exact DemonicExecWithin.load hadm rfl

theorem exec_op_det {B : Basis} {r w T : ℕ} {o : WordRAM.Op B r}
    {x y : WordRAM.Data r} (h : WordRAM.Exec w (.op o) x y T) :
    o.eval w x = some y ∧ T = 1 := by
  cases h with
  | op heval => exact ⟨heval, rfl⟩

theorem exec_seq_op_inv {B : Basis} {r w T : ℕ} {o : WordRAM.Op B r} {c₂ : WordRAM.Code B r}
    {x y : WordRAM.Data r} (h : WordRAM.Exec w (.seq (.op o) c₂) x y T) :
    ∃ s₁ T₂, o.eval w x = some s₁ ∧ WordRAM.Exec w c₂ s₁ y T₂ ∧ T = 1 + T₂ := by
  cases h with
  | seq h₁ h₂ =>
    obtain ⟨heval, rfl⟩ := exec_op_det h₁
    exact ⟨_, _, heval, h₂, rfl⟩

/-- Unrolled ascending sequence of `BitRAM.Code` programs `f 0; f 1; ...; f (n - 1)`. -/
@[expose]
def seqAscBit {r : ℕ} [NeZero r] (f : ℕ → BitRAM.Code .standard r) :
    ℕ → BitRAM.Code .standard r
  | 0 => .op (.copy 0 0)
  | n + 1 => .seq (seqAscBit f n) (f n)

theorem ofExactCode_seqAsc (g : ℕ → WordRAM.Code .exact 240) (n : ℕ) :
    ofExactCode (ReducedKWise.seqAsc g n) = seqAscBit (fun i => ofExactCode (g i)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ReducedKWise.seqAsc, seqAscBit, ofExactCode, ih]

theorem seqAscBit_dExec {r w : ℕ} [NeZero r] (f : ℕ → BitRAM.Code .standard r) (step : ℕ)
    (P : ℕ → BitRAM.Data r → Prop) (n : ℕ)
    (hstep : ∀ i < n, ∀ x, P i x → BitRAM.DemonicExecWithin w (f i) x (P (i + 1)) step) :
    ∀ x, P 0 x →
      BitRAM.DemonicExecWithin w (seqAscBit f n) x (P n) (n * step + 1) := by
  induction n with
  | zero =>
    intro x hx
    have hset : x.set 0 (x.regs 0) = x := by
      ext i : 2
      · simp
      · rfl
      · rfl
    exact (DemonicExecWithin.copy (P := P 0) (by rw [hset]; exact hx)).mono
      (fun _ h => h) (by omega)
  | succ n ih =>
    intro x hx
    refine .seq (T₁ := n * step + 1) (T₂ := step)
      (ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) x hx)
      (fun y hy => hstep n (Nat.lt_succ_self n) y hy) ?_
    rw [Nat.add_one_mul]
    omega

theorem eval_const_eq {r w : ℕ} {d : Fin r} {v : ℕ} {x y : WordRAM.Data r}
    (h : (WordRAM.Op.const (B := .exact) d v).eval w x = some y) :
    y = x.set d v := by
  dsimp only [WordRAM.Op.eval, WordRAM.Data.put] at h
  split_ifs at h with hfit
  · injection h with hy; exact hy.symm

theorem eval_exactBin_eq {r w : ℕ} {f : BinOp} {d a b : Fin r} {x y : WordRAM.Data r}
    (h : (WordRAM.Op.exactBin f d a b).eval w x = some y) :
    ∃ val, f.evalExact (x.regs a) (x.regs b) = some val ∧ y = x.set d val := by
  change (do let value ← f.evalExact (x.regs a) (x.regs b); x.put w d value) = some y at h
  rcases hf : f.evalExact (x.regs a) (x.regs b) with _ | val
  · rw [hf] at h; cases h
  · rw [hf] at h
    change x.put w d val = some y at h
    dsimp only [WordRAM.Data.put] at h
    split_ifs at h with hfit
    · injection h with hy; exact ⟨val, rfl, hy.symm⟩

theorem noLoadStore_seqAsc (f : ℕ → WordRAM.Code .exact 240) (n : ℕ)
    (hf : ∀ i < n, NoLoadStore (f i) = true) :
    NoLoadStore (ReducedKWise.seqAsc f n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ReducedKWise.seqAsc, NoLoadStore, Bool.and_eq_true]
    exact ⟨ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)), hf n (Nat.lt_succ_self n)⟩

theorem zeroProdCode_dExec {base w w₀ b b' k r_val acc_val : ℕ}
    (x : BitRAM.Data 240)
    (hinv : ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val x.toWordRAMData) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.zeroProdCode L)) x
      (fun y =>
        ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val y.toWordRAMData ∧
        (∀ d < 2 * L, y.regs (ReducedKWise.prodReg d) < 2 ^ c) ∧
        packLimbs c (2 * L) (fun d => y.regs (ReducedKWise.prodReg d)) = 0 ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      (2 * L * 1 + 1) := by
  intro t c L
  obtain ⟨y₀, hex, hy_inv, hy_lt, hy_zero, hy_mem⟩ :=
    ReducedKWise.zeroProdCode_exec x.toWordRAMData hinv
  have hno : NoLoadStore (ReducedKWise.zeroProdCode L) = true :=
    noLoadStore_seqAsc (fun d => .op (.const (ReducedKWise.prodReg d) 0)) (2 * L) (fun _ _ => rfl)
  refine (dExec_of_exec_noLoadStore hno hex).mono (fun y hy => ?_) le_rfl
  subst hy
  exact ⟨hy_inv, hy_lt, hy_zero, hy_mem, rfl⟩

theorem innerClmulStep_dExec {base w w₀ b b' k r_val acc_val i m : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' k))
    (hi : i < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (hm : m < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : BitRAM.Data 240)
    (hadm : base + ReducedKWise.space w w₀ b b' k ≤ x.wordSize w)
    (hinv : ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val x.toWordRAMData)
    (htab : ReducedKWise.TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (ReducedKWise.prodReg d) <
        2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b')) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let u := getLimb c acc_val i
    let v := getLimb c r_val m
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.innerClmulStep i m)) x
      (fun y =>
        ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val y.toWordRAMData ∧
        (∀ d < 2 * L, y.regs (ReducedKWise.prodReg d) < 2 ^ c) ∧
        packLimbs c (2 * L) (fun d => y.regs (ReducedKWise.prodReg d)) =
          packLimbs c (2 * L) (fun d => x.regs (ReducedKWise.prodReg d)) ^^^
            (clmul u v <<< ((i + m) * c)) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      13 := by
  intro t c L u v
  obtain ⟨y₀, hex, hy_inv, hy_lt, hy_pack, hy_mem⟩ :=
    ReducedKWise.innerClmulStep_exec hc_lt hfit_space hi hm x.toWordRAMData hinv htab hprod_lt
  dsimp only [ReducedKWise.innerClmulStep] at hex
  obtain ⟨s1, T1, he1, hex1, hT1⟩ := exec_seq_op_inv hex
  obtain ⟨s2, T2, he2, hex2, hT2⟩ := exec_seq_op_inv hex1
  obtain ⟨s3, T3, he3, hex3, hT3⟩ := exec_seq_op_inv hex2
  obtain ⟨s4, T4, he4, hex4, hT4⟩ := exec_seq_op_inv hex3
  cases hex4 with
  | @seq _ _ _ s5 _ _ _ hex_load hex_rest =>
    obtain ⟨_, rfl⟩ := exec_op_det hex_load
    obtain ⟨v1, hv1, rfl⟩ := eval_exactBin_eq he1
    obtain ⟨v2, hv2, rfl⟩ := eval_exactBin_eq he2
    obtain ⟨v3, hv3, rfl⟩ := eval_exactBin_eq he3
    obtain ⟨v4, hv4, rfl⟩ := eval_exactBin_eq he4
    have ⟨⟨_, h4, h5, _, h7, _, _, _, hxReg⟩, haccReg⟩ := hinv
    have hu_reg : x.toWordRAMData.regs (ReducedKWise.accReg i) = u := haccReg i hi
    have hv_reg : x.toWordRAMData.regs (ReducedKWise.xReg m) = v := hxReg m hm
    have hv1_eq : v1 = u <<< c := by
      dsimp only [BinOp.evalExact] at hv1
      injection hv1 with h; rw [← h, hu_reg, h5]
    have hv2_eq : v2 = (u <<< c) + v := by
      dsimp only [BinOp.evalExact, WordRAM.Data.set] at hv2
      rw [Function.update_self,
        Function.update_of_ne (ReducedKWise.xReg_ne_low m (r := 10) (by decide)),
        hv1_eq, hv_reg] at hv2
      injection hv2 with h; exact h.symm
    have hv3_eq : v3 = ((u <<< c) + v) >>> reducedPackShift t w := by
      dsimp only [BinOp.evalExact, WordRAM.Data.set] at hv3
      simp only [Function.update_self,
        Function.update_of_ne (by decide : (7 : Fin 240) ≠ 10)] at hv3
      injection hv3 with h; rw [← h, hv2_eq, h7]
    have hv4_eq : v4 = ReducedKWise.tabBase base w₀ b b' k + v3 := by
      dsimp only [BinOp.evalExact, WordRAM.Data.set] at hv4
      simp only [Function.update_self,
        Function.update_of_ne (by decide : (4 : Fin 240) ≠ 11),
        Function.update_of_ne (by decide : (4 : Fin 240) ≠ 10)] at hv4
      injection hv4 with h; rw [← h, h4]
    have hidx_lt : (u <<< c) + v < 2 ^ (2 * c) :=
      (ReducedKWise.pair_index_props (getLimb_lt c acc_val i)
        (getLimb_lt c r_val m)).1
    have hwIdx_lt : v3 < reducedTableWords t w := by
      rw [hv3_eq]
      exact shiftRight_lt_reducedTableWords hidx_lt
    have hv4_lt : v4 < x.wordSize w := by
      rw [hv4_eq]
      change v3 < reducedTableWords (reducedTrinomialStep w₀ b b') w at hwIdx_lt
      have : ReducedKWise.tabBase base w₀ b b' k + v3 <
          base + ReducedKWise.space w w₀ b b' k := by
        dsimp only [ReducedKWise.tabBase, ReducedKWise.space, ReducedKWise.tableWords]
        omega
      omega
    have d1 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.exactBin .shiftLeft 10 (ReducedKWise.accReg i) 5))) x
        (fun z => z = ⟨(x.toWordRAMData.set 10 v1).regs, x.mem, x.bitSize⟩) 1 :=
      .op (evalOp_of_exact_noLoadStore rfl he1) rfl le_rfl
    have d2 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.exactBin .add 10 10 (ReducedKWise.xReg m))))
        ⟨(x.toWordRAMData.set 10 v1).regs, x.mem, x.bitSize⟩
        (fun z => z = ⟨((x.toWordRAMData.set 10 v1).set 10 v2).regs, x.mem, x.bitSize⟩) 1 :=
      .op (evalOp_of_exact_noLoadStore rfl he2) rfl le_rfl
    have d3 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.exactBin .shiftRight 11 10 7)))
        ⟨((x.toWordRAMData.set 10 v1).set 10 v2).regs, x.mem, x.bitSize⟩
        (fun z => z = ⟨(((x.toWordRAMData.set 10 v1).set 10 v2).set 11 v3).regs,
          x.mem, x.bitSize⟩) 1 :=
      .op (evalOp_of_exact_noLoadStore rfl he3) rfl le_rfl
    have d4 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.exactBin .add 11 4 11)))
        ⟨(((x.toWordRAMData.set 10 v1).set 10 v2).set 11 v3).regs, x.mem, x.bitSize⟩
        (fun z => z = ⟨((((x.toWordRAMData.set 10 v1).set 10 v2).set 11 v3).set 11 v4).regs,
          x.mem, x.bitSize⟩) 1 :=
      .op (evalOp_of_exact_noLoadStore rfl he4) rfl le_rfl
    have d5 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.load 12 11)))
        ⟨((((x.toWordRAMData.set 10 v1).set 10 v2).set 11 v3).set 11 v4).regs,
          x.mem, x.bitSize⟩
        (fun z => z = ⟨s5.regs, s5.mem, x.bitSize⟩) 1 := by
      refine dExec_load_of_exec ?_ hex_load
      change v4 < x.wordSize w
      exact hv4_lt
    have d_rest := dExec_of_exec_noLoadStore (x := ⟨s5.regs, s5.mem, x.bitSize⟩) rfl hex_rest
    refine (dExec_seq_eq d1 (dExec_seq_eq d2 (dExec_seq_eq d3
      (dExec_seq_eq d4 (dExec_seq_eq d5 d_rest))))).mono
      (fun y hy => ?_) (by omega)
    subst hy
    exact ⟨hy_inv, hy_lt, hy_pack, hy_mem, rfl⟩

theorem outerClmulStep_dExec {base w w₀ b b' k r_val acc_val i : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' k))
    (hi : i < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : BitRAM.Data 240)
    (hadm : base + ReducedKWise.space w w₀ b b' k ≤ x.wordSize w)
    (hinv : ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val x.toWordRAMData)
    (htab : ReducedKWise.TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (ReducedKWise.prodReg d) <
        2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b')) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.outerClmulStep L i)) x
      (fun y =>
        ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val y.toWordRAMData ∧
        (∀ d < 2 * L, y.regs (ReducedKWise.prodReg d) < 2 ^ c) ∧
        packLimbs c (2 * L) (fun d => y.regs (ReducedKWise.prodReg d)) =
          packLimbs c (2 * L) (fun d => x.regs (ReducedKWise.prodReg d)) ^^^
            (clmul (getLimb c acc_val i)
              (truncLimbs c L r_val) <<< (i * c)) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      (L * 13 + 1) := by
  intro t c L
  rw [ReducedKWise.outerClmulStep, ofExactCode_seqAsc]
  set P₀ := packLimbs c (2 * L) (fun d => x.regs (ReducedKWise.prodReg d))
  let P (m : ℕ) (z : BitRAM.Data 240) : Prop :=
    ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val z.toWordRAMData ∧
    (∀ d < 2 * L, z.regs (ReducedKWise.prodReg d) < 2 ^ c) ∧
    packLimbs c (2 * L) (fun d => z.regs (ReducedKWise.prodReg d)) =
      P₀ ^^^ (clmul (getLimb c acc_val i)
        (truncLimbs c m r_val) <<< (i * c)) ∧
    z.mem = x.mem ∧ z.bitSize = x.bitSize
  have hP0 : P 0 x := by
    refine ⟨hinv, hprod_lt, ?_, rfl, rfl⟩
    rw [truncLimbs_zero, clmul_zero_right,
      Nat.zero_shiftLeft, Nat.xor_zero]
  exact seqAscBit_dExec (fun m => ofExactCode (ReducedKWise.innerClmulStep i m)) 13 P L
    (fun m hm z ⟨hz_inv, hz_lt, hz_pack, hz_mem, hz_sz⟩ => by
      have hadm_z : base + ReducedKWise.space w w₀ b b' k ≤ z.wordSize w := by
        dsimp only [BitRAM.Data.wordSize]; rw [hz_sz]; exact hadm
      have htab_z : ReducedKWise.TableRep base w w₀ b b' k z.mem := hz_mem ▸ htab
      refine (innerClmulStep_dExec hc_lt hfit_space hi hm z hadm_z hz_inv htab_z hz_lt).mono
        (fun z' ⟨hz'_inv, hz'_lt, hz'_pack, hz'_mem, hz'_sz⟩ => ?_) le_rfl
      refine ⟨hz'_inv, hz'_lt, ?_, hz'_mem.trans hz_mem, hz'_sz.trans hz_sz⟩
      rw [hz'_pack, hz_pack, Nat.xor_assoc, ← clmul_truncLimbs_right_succ])
    x hP0

theorem clmulLimbsCode_dExec {base w w₀ b b' k r_val acc_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' k))
    (hr_lt : r_val < 2 ^ (reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (hacc_lt : acc_val < 2 ^ (reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (x : BitRAM.Data 240)
    (hadm : base + ReducedKWise.space w w₀ b b' k ≤ x.wordSize w)
    (hinv : ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val x.toWordRAMData)
    (htab : ReducedKWise.TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (ReducedKWise.prodReg d) <
        2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b'))
    (hprod_zero : packLimbs
      (reducedChunkBits (reducedTrinomialStep w₀ b b'))
      (2 * reducedLimbCount (reducedTrinomialStep w₀ b b'))
      (fun d => x.regs (ReducedKWise.prodReg d)) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.clmulLimbsCode L)) x
      (fun y =>
        ReducedKWise.HornerConsts base w w₀ b b' k r_val y.toWordRAMData ∧
        (∀ d < 2 * L, y.regs (ReducedKWise.prodReg d) =
          getLimb c (clmul acc_val r_val) d) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      (L * (L * 13 + 1) + 1) := by
  intro t c L
  rw [ReducedKWise.clmulLimbsCode, ofExactCode_seqAsc]
  let P (i : ℕ) (z : BitRAM.Data 240) : Prop :=
    ReducedKWise.ClmulInv base w w₀ b b' k r_val acc_val z.toWordRAMData ∧
    (∀ d < 2 * L, z.regs (ReducedKWise.prodReg d) < 2 ^ c) ∧
    packLimbs c (2 * L) (fun d => z.regs (ReducedKWise.prodReg d)) =
      clmul (truncLimbs c i acc_val) r_val ∧
    z.mem = x.mem ∧ z.bitSize = x.bitSize
  have hP0 : P 0 x := by
    refine ⟨hinv, hprod_lt, ?_, rfl, rfl⟩
    rw [hprod_zero, truncLimbs_zero, clmul_zero_left]
  refine (seqAscBit_dExec (fun i => ofExactCode (ReducedKWise.outerClmulStep L i))
    (L * 13 + 1) P L
    (fun i hi z ⟨hz_inv, hz_lt, hz_pack, hz_mem, hz_sz⟩ => by
      have hadm_z : base + ReducedKWise.space w w₀ b b' k ≤ z.wordSize w := by
        dsimp only [BitRAM.Data.wordSize]; rw [hz_sz]; exact hadm
      have htab_z : ReducedKWise.TableRep base w w₀ b b' k z.mem := hz_mem ▸ htab
      refine (outerClmulStep_dExec hc_lt hfit_space hi z hadm_z hz_inv htab_z hz_lt).mono
        (fun z' ⟨hz'_inv, hz'_lt, hz'_pack, hz'_mem, hz'_sz⟩ => ?_) le_rfl
      refine ⟨hz'_inv, hz'_lt, ?_, hz'_mem.trans hz_mem, hz'_sz.trans hz_sz⟩
      rw [hz'_pack, hz_pack, truncLimbs_of_lt hr_lt,
        ← clmul_truncLimbs_left_succ])
    x hP0).mono (fun y ⟨hy_inv, hy_lt, hy_pack, hy_mem, hy_sz⟩ => ?_) le_rfl
  rw [truncLimbs_of_lt hacc_lt] at hy_pack
  refine ⟨hy_inv.1, fun d hd => ?_, hy_mem, hy_sz⟩
  rw [← hy_pack, getLimb_packLimbs_of_lt c hd (hy_lt d hd)]

theorem reduceAddStep_dExec {base w w₀ b b' k r_val P_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' k))
    (hP_lt : P_val < 2 ^ (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (θ : ReducedPolySeed w₀ b b' k) (coeffIdx : Fin k) (m : ℕ)
    (hm : m < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : BitRAM.Data 240)
    (hadm : base + ReducedKWise.space w w₀ b b' k ≤ x.wordSize w)
    (hc : ReducedKWise.HornerConsts base w w₀ b b' k r_val x.toWordRAMData)
    (hseed : ReducedKWise.SeedRep base w₀ b b' k θ x.mem)
    (hprod : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (ReducedKWise.prodReg d) =
        getLimb (reducedChunkBits
          (reducedTrinomialStep w₀ b b')) P_val d) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let L₀ := reducedHalfLimbs t
    let newAcc := reduceTrinomialCode t P_val ^^^ (θ.2 coeffIdx).val
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.reduceAddStep L₀ coeffIdx.val m)) x
      (fun y =>
        ReducedKWise.HornerConsts base w w₀ b b' k r_val y.toWordRAMData ∧
        (∀ d < 2 * L, y.regs (ReducedKWise.prodReg d) = getLimb c P_val d) ∧
        y.regs (ReducedKWise.accReg m) = getLimb c newAcc m ∧
        (∀ i < m, y.regs (ReducedKWise.accReg i) = x.regs (ReducedKWise.accReg i)) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      6 := by
  intro t c L L₀ newAcc
  obtain ⟨y₀, hex, hy_hc, hy_prod, hy_m, hy_prev, hy_mem⟩ :=
    ReducedKWise.reduceAddStep_exec hc_lt hfit_space hP_lt θ coeffIdx m hm
      x.toWordRAMData hc hseed hprod
  dsimp only [ReducedKWise.reduceAddStep] at hex
  obtain ⟨s1, T1, he1, hex1, hT1⟩ := exec_seq_op_inv hex
  obtain ⟨s2, T2, he2, hex2, hT2⟩ := exec_seq_op_inv hex1
  cases hex2 with
  | @seq _ _ _ s3 _ _ _ hex_load hex_rest =>
    obtain ⟨_, rfl⟩ := exec_op_det hex_load
    have hs1 := eval_const_eq he1
    subst hs1
    obtain ⟨v2, hv2, rfl⟩ := eval_exactBin_eq he2
    have h0 : x.toWordRAMData.regs 0 = base := hc.1
    set off := 1 + (m + 2 * L₀ * coeffIdx.val)
    have hv2_eq : v2 = base + off := by
      dsimp only [BinOp.evalExact, WordRAM.Data.set] at hv2
      simp only [Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 240) ≠ 10)] at hv2
      injection hv2 with h; rw [← h, h0]
    have hoff_lt_seed : off < ReducedKWise.seedWords w₀ b b' k := by
      dsimp only [off, ReducedKWise.seedWords]
      change 1 + (m + L * coeffIdx.val) < 1 + k * L
      have : m + L * coeffIdx.val < L + L * coeffIdx.val := Nat.add_lt_add_right hm _
      have hmul : L + L * coeffIdx.val ≤ k * L := by
        calc L + L * coeffIdx.val = (coeffIdx.val + 1) * L := by ring
          _ ≤ k * L := Nat.mul_le_mul_right L coeffIdx.isLt
      omega
    have hv2_lt : v2 < x.wordSize w := by
      rw [hv2_eq]
      have : base + off < base + ReducedKWise.space w w₀ b b' k := by
        dsimp only [ReducedKWise.space]; omega
      omega
    have d1 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.const 10 off))) x
        (fun z => z = ⟨(x.toWordRAMData.set 10 off).regs, x.mem, x.bitSize⟩) 1 :=
      .op (evalOp_of_exact_noLoadStore rfl he1) rfl le_rfl
    have d2 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.exactBin .add 10 0 10)))
        ⟨(x.toWordRAMData.set 10 off).regs, x.mem, x.bitSize⟩
        (fun z => z = ⟨((x.toWordRAMData.set 10 off).set 10 v2).regs, x.mem, x.bitSize⟩) 1 :=
      .op (evalOp_of_exact_noLoadStore rfl he2) rfl le_rfl
    have d3 : BitRAM.DemonicExecWithin w
        (ofExactCode (.op (.load 11 10)))
        ⟨((x.toWordRAMData.set 10 off).set 10 v2).regs, x.mem, x.bitSize⟩
        (fun z => z = ⟨s3.regs, s3.mem, x.bitSize⟩) 1 := by
      refine dExec_load_of_exec ?_ hex_load
      change v2 < x.wordSize w
      exact hv2_lt
    have hno_rest : NoLoadStore
        (.seq (if m < L₀ then
            .seq (.op (.exactBin .xor 12 (ReducedKWise.prodReg m)
                  (ReducedKWise.prodReg (3 * L₀ + m))))
                 (.op (.exactBin .xor 12 12 (ReducedKWise.prodReg (2 * L₀ + m))))
          else
            .seq (.op (.exactBin .xor 12 (ReducedKWise.prodReg m)
                  (ReducedKWise.prodReg (L₀ + m))))
                 (.op (.copy 12 12)))
          (.op (.exactBin .xor (ReducedKWise.accReg m) 12 11))) = true := by
      split_ifs <;> rfl
    have d_rest := dExec_of_exec_noLoadStore (x := ⟨s3.regs, s3.mem, x.bitSize⟩) hno_rest hex_rest
    refine (dExec_seq_eq d1 (dExec_seq_eq d2 (dExec_seq_eq d3 d_rest))).mono
      (fun y hy => ?_) (by omega)
    subst hy
    exact ⟨hy_hc, hy_prod, hy_m, hy_prev, hy_mem, rfl⟩

theorem reduceAddCode_dExec {base w w₀ b b' k r_val P_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' k))
    (hP_lt : P_val < 2 ^ (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (θ : ReducedPolySeed w₀ b b' k) (coeffIdx : Fin k)
    (x : BitRAM.Data 240)
    (hadm : base + ReducedKWise.space w w₀ b b' k ≤ x.wordSize w)
    (hc : ReducedKWise.HornerConsts base w w₀ b b' k r_val x.toWordRAMData)
    (hseed : ReducedKWise.SeedRep base w₀ b b' k θ x.mem)
    (hprod : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (ReducedKWise.prodReg d) =
        getLimb (reducedChunkBits
          (reducedTrinomialStep w₀ b b')) P_val d) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let L₀ := reducedHalfLimbs t
    let newAcc := reduceTrinomialCode t P_val ^^^ (θ.2 coeffIdx).val
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.reduceAddCode L₀ coeffIdx.val)) x
      (fun y =>
        ReducedKWise.HornerConsts base w w₀ b b' k r_val y.toWordRAMData ∧
        (∀ m < L, y.regs (ReducedKWise.accReg m) = getLimb c newAcc m) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      (L * 6 + 1) := by
  intro t c L L₀ newAcc
  rw [ReducedKWise.reduceAddCode, ofExactCode_seqAsc]
  let P (n : ℕ) (z : BitRAM.Data 240) : Prop :=
    ReducedKWise.HornerConsts base w w₀ b b' k r_val z.toWordRAMData ∧
    (∀ d < 2 * L, z.regs (ReducedKWise.prodReg d) = getLimb c P_val d) ∧
    (∀ m < n, z.regs (ReducedKWise.accReg m) = getLimb c newAcc m) ∧
    z.mem = x.mem ∧ z.bitSize = x.bitSize
  have hP0 : P 0 x := ⟨hc, hprod, fun _ hm => (Nat.not_lt_zero _ hm).elim, rfl, rfl⟩
  refine (seqAscBit_dExec (fun m => ofExactCode (ReducedKWise.reduceAddStep L₀ coeffIdx.val m))
    6 P L
    (fun m hm z ⟨hz_hc, hz_prod, hz_acc, hz_mem, hz_sz⟩ => by
      have hadm_z : base + ReducedKWise.space w w₀ b b' k ≤ z.wordSize w := by
        dsimp only [BitRAM.Data.wordSize]; rw [hz_sz]; exact hadm
      have hseed_z : ReducedKWise.SeedRep base w₀ b b' k θ z.mem := hz_mem ▸ hseed
      refine (reduceAddStep_dExec hc_lt hfit_space hP_lt θ coeffIdx m hm z hadm_z
        hz_hc hseed_z hz_prod).mono
        (fun z' ⟨hz'_hc, hz'_prod, hz'_m, hz'_prev, hz'_mem, hz'_sz⟩ => ?_) le_rfl
      refine ⟨hz'_hc, hz'_prod, fun i hi => ?_, hz'_mem.trans hz_mem, hz'_sz.trans hz_sz⟩
      rcases eq_or_ne i m with rfl | hne
      · exact hz'_m
      · have hilt : i < m := by omega
        rw [hz'_prev i hilt]
        exact hz_acc i hilt)
    x hP0).mono (fun y ⟨hy_hc, _, hy_acc, hy_mem, hy_sz⟩ => ⟨hy_hc, hy_acc, hy_mem, hy_sz⟩) le_rfl

theorem hornerCode_dExec {base w w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k)
    (r : Fin (2 ^ min w₀ (3 * b)))
    (x : BitRAM.Data 240)
    (hadm : base + ReducedKWise.space w w₀ b b' k ≤ x.wordSize w)
    (hc : ReducedKWise.HornerConsts base w w₀ b b' k r.val x.toWordRAMData)
    (htab : ReducedKWise.TableRep base w w₀ b b' k x.mem)
    (hseed : ReducedKWise.SeedRep base w₀ b b' k θ x.mem)
    (hacc0 : ∀ m < reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (ReducedKWise.accReg m) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let evalVal := (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).val
    BitRAM.DemonicExecWithin w (ofExactCode (ReducedKWise.hornerCode t k)) x
      (fun y =>
        ReducedKWise.HornerConsts base w w₀ b b' k r.val y.toWordRAMData ∧
        (∀ m < L, y.regs (ReducedKWise.accReg m) = getLimb c evalVal m) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      (k * ReducedKWise.hornerStepSteps t + 1) := by
  intro t c L evalVal
  have hLc : L * c = 2 * 3 ^ t := reducedLimbCount_mul_chunkBits t
  have hr_deg : r.val < 2 ^ (2 * 3 ^ t) :=
    r.isLt.trans_le (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b')
  have hx_lt : r.val < 2 ^ (L * c) := by rw [hLc]; exact hr_deg
  set c_field : Fin k → TrinomialField t :=
    fun j => (TrinomialField.equivFin t).symm (θ.2 j)
  set x_field : TrinomialField t :=
    AdjoinRoot.mk (trinomial t) (polyOfCode r.val)
  have hx_val : (TrinomialField.equivFin t x_field).val = r.val :=
    TrinomialField.val_equivFin_mk_polyOfCode t hr_deg
  have hzero_val : (TrinomialField.equivFin t
      (0 : TrinomialField t)).val = 0 := by
    have h0_eq : (0 : TrinomialField t) =
        AdjoinRoot.mk (trinomial t) (polyOfCode 0) := by simp
    rw [h0_eq]
    exact TrinomialField.val_equivFin_mk_polyOfCode t (by positivity)
  rw [ReducedKWise.hornerCode, ofExactCode_seqAsc]
  let P (j : ℕ) (z : BitRAM.Data 240) : Prop :=
    ReducedKWise.HornerConsts base w w₀ b b' k r.val z.toWordRAMData ∧
    (∀ m < L, z.regs (ReducedKWise.accReg m) =
      getLimb c (TrinomialField.equivFin t
        (hornerPrefix t k c_field x_field j)).val m) ∧
    z.mem = x.mem ∧ z.bitSize = x.bitSize
  have hP0 : P 0 x := by
    refine ⟨hc, fun m hm => ?_, rfl, rfl⟩
    rw [hacc0 m hm]
    dsimp only [hornerPrefix]
    rw [hzero_val]
    simp [getLimb]
  refine (seqAscBit_dExec (fun j => ofExactCode (ReducedKWise.hornerStep t k j))
    (ReducedKWise.hornerStepSteps t) P k
    (fun j hj z ⟨hz_hc, hz_acc, hz_mem, hz_sz⟩ => by
      set acc := hornerPrefix t k c_field x_field j
      set acc_val := (TrinomialField.equivFin t acc).val
      have hacc_lt : acc_val < 2 ^ (L * c) := by
        rw [hLc]
        exact (TrinomialField.equivFin t acc).isLt
      have hinv : ReducedKWise.ClmulInv base w w₀ b b' k r.val acc_val z.toWordRAMData :=
        ⟨hz_hc, hz_acc⟩
      refine .seq (zeroProdCode_dExec z hinv)
        (fun z1 ⟨hz1_inv, hz1_lt, hz1_zero, hz1_mem, hz1_sz⟩ => ?_) le_rfl
      have hadm_z1 : base + ReducedKWise.space w w₀ b b' k ≤ z1.wordSize w := by
        dsimp only [BitRAM.Data.wordSize]; rw [hz1_sz, hz_sz]; exact hadm
      have htab_z1 : ReducedKWise.TableRep base w w₀ b b' k z1.mem :=
        (hz1_mem.trans hz_mem) ▸ htab
      refine .seq (clmulLimbsCode_dExec hc_lt hfit_space hx_lt hacc_lt z1 hadm_z1
        hz1_inv htab_z1 hz1_lt hz1_zero)
        (fun z2 ⟨hz2_hc, hz2_prod, hz2_mem, hz2_sz⟩ => ?_) le_rfl
      have hP_lt : clmul acc_val r.val < 2 ^ (2 * L * c) := by
        rw [Nat.mul_assoc]
        exact clmul_lt_two_pow_two_mul hacc_lt hx_lt
      have hadm_z2 : base + ReducedKWise.space w w₀ b b' k ≤ z2.wordSize w := by
        dsimp only [BitRAM.Data.wordSize]; rw [hz2_sz, hz1_sz, hz_sz]; exact hadm
      have hseed_z2 : ReducedKWise.SeedRep base w₀ b b' k θ z2.mem :=
        (hz2_mem.trans (hz1_mem.trans hz_mem)) ▸ hseed
      refine (reduceAddCode_dExec hc_lt hfit_space hP_lt θ ⟨k - 1 - j, by omega⟩ z2 hadm_z2
        hz2_hc hseed_z2 hz2_prod).mono
        (fun z3 ⟨hz3_hc, hz3_acc, hz3_mem, hz3_sz⟩ => ?_) le_rfl
      refine ⟨hz3_hc, fun m hm => ?_,
        hz3_mem.trans (hz2_mem.trans (hz1_mem.trans hz_mem)),
        hz3_sz.trans (hz2_sz.trans (hz1_sz.trans hz_sz))⟩
      rw [hz3_acc m hm]
      congr 1
      have hmul_val : reduceTrinomialCode t (clmul acc_val r.val) =
          (TrinomialField.equivFin t (acc * x_field)).val := by
        rw [TrinomialField.val_equivFin_mul, hx_val]
      have hseed_val : (θ.2 ⟨k - 1 - j, by omega⟩).val =
          (TrinomialField.equivFin t (c_field ⟨k - 1 - j, by omega⟩)).val := by
        have h : TrinomialField.equivFin t (c_field ⟨k - 1 - j, by omega⟩) =
            θ.2 ⟨k - 1 - j, by omega⟩ :=
          (TrinomialField.equivFin t).apply_symm_apply (θ.2 ⟨k - 1 - j, by omega⟩)
        exact (congrArg Fin.val h).symm
      rw [hmul_val, hseed_val, ← TrinomialField.val_equivFin_add]
      dsimp only [hornerPrefix]
      rw [dite_eq_left hj])
    x hP0).mono (fun y ⟨hy_hc, hy_acc, hy_mem, hy_sz⟩ => ?_) le_rfl
  refine ⟨hy_hc, fun m hm => ?_, hy_mem, hy_sz⟩
  rw [hy_acc m hm, hornerPrefix_self_eq_polynomialHash]
  rfl

end Cslib.DataStructure.Dictionary.BitResizable
