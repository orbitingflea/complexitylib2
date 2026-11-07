/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Transition

/-!
# Client Subroutine Theorems for the Bit-Resizable Succinct Dictionary

This module proves Deliverable (d): uniform client subroutine theorems on
`BitRAM.Code .standard 280` showing how an external caller uses the bit-resizable succinct
dictionary as a subroutine in the single linear bit-resizable memory `[0, s.bitSize)` of `BitRAM`,
and how bits released when keys are deleted are immediately reusable by client allocations under
demonic `.grow` (`DirtyGrowOracle` / `BitRAM.DemonicExecWithin`).

All machine programs in this module (`inEpochDeleteOpRegCode`, `clientAllocBitsRegCode`,
`clientFreeBitsRegCode`, `initEmptyRegCode`, `inEpochStepRegCode`) are **fixed parameter-free
`BitRAM.Code .standard 280` terms** defined outside all `U, V, w, N, θ, x, u, b, v` quantifiers,
reading runtime arguments from registers (`r270` for `u`, `r230` for `b`, `r231` for `v_client`).

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.loadClientAllocRegs`: loads `(b, v)` into client
  registers `(r230, r231)`.
* `Cslib.DataStructure.Dictionary.BitResizable.clientAllocBitsRegCode`: fixed parameter-free
  `BitRAM.Code .standard 280` subroutine that grows memory by `r230 = b` bits (`b ≤ w`) and writes
  `r231 = v` into `[y.bitSize, y.bitSize + b)` in `46` instructions under demonic `.grow`,
  preserving all registers `≥ 12` (including `EpochRegs` on `240..269` and `r230 = b`).
* `Cslib.DataStructure.Dictionary.BitResizable.clientFreeBitsRegCode`: fixed parameter-free
  `BitRAM.Code .standard 280` subroutine (`.shrink 230`) releasing the `b`-bit client slice in `1`
  instruction.

## Main results

* `clientAllocBitsRegCode_exec`: `46`-instruction demonic execution certificate for
  `clientAllocBitsRegCode`.
* `stepFn_shrink_eq_of_getBit_eq`, `clientFreeBitsRegCode_exec`: shrinking the `b`-bit client slice
  restores the exact post-delete `BitMemory.State` `y.toBitMemoryState`, `EpochDictInv`, and `Rep`.
* `inEpochDeleteOpRegCode_clientAlloc_subroutine`, `delete_reuses_released_bits_subroutine`:
  uniform subroutine theorem (`∃ code_del code_client` outside `∀ U V w N ... ∀ x u b v_client`)
  proving that deleting an active key shrinks `bitSize` by `itemBits U V N` and subsequent client
  allocation of `b ≤ itemBits U V N` bits under demonic `.grow` reuses those released bits
  (`z.bitSize ≤ x.bitSize`), stores `v_client`, preserves the dictionary's live `Rep` on the
  dictionary prefix, and achieves `O(1)` expected amortized time (`≤ 294450` instructions).
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open scoped ENNReal BigOperators Finset
open Cslib.Probability
open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM

/-! ## Section 1: Parameter-free client bit-allocation and deallocation subroutines -/

/-- Load client allocation arguments `b` and `v` into client registers `r230` and `r231`. -/
@[expose]
def loadClientAllocRegs (b v : ℕ) (y : BitRAM.Data 280) : BitRAM.Data 280 :=
  (y.set 230 b).set 231 v

/-- Fixed parameter-free `BitRAM.Code .standard 280` client subroutine that reads `(b, v)` from
registers `(r230, r231)`, grows the bit-resizable memory by `b` bits (`b ≤ w`) under demonic
`.grow`, and writes `v` into `[y.bitSize, y.bitSize + b)` in at most `46` instructions using
scratch registers `0..11`. -/
@[expose]
def clientAllocBitsRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 1 230))
    (.seq (.grow 1 1)
      (.seq (.op (.copy 2 230))
        (.seq (.op (.copy 3 231))
          (BitRAM.Code.embed12 (by decide) BitRAM.writeBitsCode))))

/-- Fixed parameter-free `BitRAM.Code .standard 280` client subroutine freeing the `b`-bit slice
whose width `b` is held in `r230` in `1` instruction. -/
@[expose]
def clientFreeBitsRegCode : BitRAM.Code .standard 280 :=
  .shrink 230

/-- **Demonic execution certificate for `clientAllocBitsRegCode` (`clientAllocBitsRegCode_exec`):**
from any well-formed `y : BitRAM.Data 280` with `y.regs 230 = b`, `y.regs 231 = v`, `b ≤ w`,
`Fits b v`, and `Fits w (y.bitSize + b)`, `clientAllocBitsRegCode` executes in at most `46`
instructions under demonic `.grow`, producing `z` with `z.bitSize = y.bitSize + b`,
`z.toBitMemoryState.getField w y.bitSize b = v`, all lower bits `< y.bitSize` unchanged, and all
registers `j ≥ 12` unchanged. -/
theorem clientAllocBitsRegCode_exec {w b v : ℕ} (hw : 0 < w) (hbw : b ≤ w) (hv : Fits b v)
    {y : BitRAM.Data 280} (hy : y.WellFormed w) (hgrow_fits : Fits w (y.bitSize + b))
    (hr230 : y.regs 230 = b) (hr231 : y.regs 231 = v) :
    BitRAM.DemonicExecWithin w clientAllocBitsRegCode y
      (fun z =>
        z.WellFormed w ∧
        z.bitSize = y.bitSize + b ∧
        z.toBitMemoryState.getField w y.bitSize b = v ∧
        (∀ i < y.bitSize,
          z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i) ∧
        (∀ j : Fin 280, 12 ≤ j.val → z.regs j = y.regs j))
      46 := by
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have hv_fits : Fits w v := hv.mono hbw
  refine step_dExec_copy (v := b) (T := 45) hr230 ?_
  set y₀ := y.set 1 b
  have hy₀_r1 : y₀.regs 1 = b := by simp [y₀, BitRAM.Data.set]
  have hcost_grow : max 1 ((y₀.regs 1) ⌈/⌉ w) ≤ 1 := by
    rw [hy₀_r1]
    exact (BitMemory.charge_grow_of_le hw hbw y.toBitMemoryState).le
  have hgrow_y₀ : Fits w (y₀.bitSize + y₀.regs 1) := by
    rw [hy₀_r1]; exact hgrow_fits
  refine .seq
    (Q := fun y₁ : BitRAM.Data 280 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w y.toBitMemoryState (.grow b) s₁ y.bitSize ∧
        y₁ = ⟨Function.update y₀.regs 1 y.bitSize, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 44)
    (.grow hgrow_y₀ hcost_grow fun s₁ hs₁ => by
      have hy₀_st : y₀.toBitMemoryState = y.toBitMemoryState := rfl
      have hy₀_sz : y₀.bitSize = y.bitSize := rfl
      rw [hy₀_st, hy₀_r1, hy₀_sz] at hs₁
      exact ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  set y₁ : BitRAM.Data 280 := ⟨Function.update y₀.regs 1 y.bitSize, s₁.mem, s₁.bitSize⟩
  have hy₁_230 : y₁.regs 230 = b := by
    simp [y₁, y₀, BitRAM.Data.set, hr230]
  have hy₁_231 : y₁.regs 231 = v := by
    simp [y₁, y₀, BitRAM.Data.set, hr231]
  refine step_dExec_copy (v := b) (T := 43) hy₁_230 ?_
  set y₂ := y₁.set 2 b
  have hy₂_231 : y₂.regs 231 = v := by
    simp [y₂, BitRAM.Data.set, hy₁_231]
  refine step_dExec_copy (v := v) (T := 42) hy₂_231 ?_
  set y₃ := y₂.set 3 v
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep hw hy.mem_wf
      (show BitMemory.valid w y.toBitMemoryState (.grow b) from hgrow_fits) hs₁
  have hy₁_wf : y₁.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi1 : i = 1
    · subst hi1
      have hr : y₁.regs 1 = y.bitSize := by simp [y₁]
      rw [hr]
      exact hy.mem_wf.bitSize_fits
    · have hr : y₁.regs i = y.regs i := by simp [y₁, y₀, BitRAM.Data.set, hi1]
      rw [hr]
      exact hy.regs_fits i
  have hy₃_wf : y₃.WellFormed w :=
    wf_set 3 (wf_set 2 hy₁_wf hb_fits) hv_fits
  have hy₃_hi : ∀ j : Fin 280, 12 ≤ j.val → y₃.regs j = y.regs j := by
    intro j hj
    have hj3 : j ≠ 3 := by intro h; subst h; omega
    have hj2 : j ≠ 2 := by intro h; subst h; omega
    have hj1 : j ≠ 1 := by intro h; subst h; omega
    simp [y₃, y₂, y₁, y₀, BitRAM.Data.set, hj3, hj2, hj1]
  have hy₃_12_wf : (y₃.comap (embedFin12 (by decide))).WellFormed w := wf_comap12_280 hy₃_wf
  have hv_write : BitMemory.valid w (y₃.comap (embedFin12 (by decide))).toBitMemoryState
      (.writeBits ((y₃.comap (embedFin12 (by decide))).regs 1)
        ((y₃.comap (embedFin12 (by decide))).regs 2)
        ((y₃.comap (embedFin12 (by decide))).regs 3)) := by
    have hr1 : (y₃.comap (embedFin12 (by decide))).regs 1 = y.bitSize := by
      change y₃.regs 1 = y.bitSize
      simp [y₃, y₂, y₁, BitRAM.Data.set]
    have hr2 : (y₃.comap (embedFin12 (by decide))).regs 2 = b := by
      change y₃.regs 2 = b
      simp [y₃, y₂, BitRAM.Data.set]
    have hr3 : (y₃.comap (embedFin12 (by decide))).regs 3 = v := by
      change y₃.regs 3 = v
      simp [y₃, BitRAM.Data.set]
    rw [hr1, hr2, hr3]
    refine ⟨hbw, ?_, hv⟩
    change y.bitSize + b ≤ s₁.bitSize
    rw [hs₁.1]
    exact le_rfl
  refine (DemonicExecWithin.embed12 (by decide)
    (writeBitsCode_exec_wf hw hy₃_12_wf hv_write)).mono
    (fun z ⟨⟨hz_st, hz12_wf⟩, hz_hi⟩ => ?_) le_rfl
  have hz_wf : z.WellFormed w := wf_of_comap12_280 hy₃_wf hz12_wf hz_hi
  have hr1 : (y₃.comap (embedFin12 (by decide))).regs 1 = y.bitSize := by
    change y₃.regs 1 = y.bitSize; simp [y₃, y₂, y₁, BitRAM.Data.set]
  have hr2 : (y₃.comap (embedFin12 (by decide))).regs 2 = b := by
    change y₃.regs 2 = b; simp [y₃, y₂, BitRAM.Data.set]
  have hr3 : (y₃.comap (embedFin12 (by decide))).regs 3 = v := by
    change y₃.regs 3 = v; simp [y₃, BitRAM.Data.set]
  change z.toBitMemoryState =
    ⟨writeFieldMem w 0 s₁.mem ((y₃.comap (embedFin12 (by decide))).regs 1)
      ((y₃.comap (embedFin12 (by decide))).regs 2)
      ((y₃.comap (embedFin12 (by decide))).regs 3), s₁.bitSize⟩ at hz_st
  rw [hr1, hr2, hr3] at hz_st
  have hmem_eq : writeFieldMem w 0 s₁.mem y.bitSize b v =
      writeFieldMem w 0 y.mem y.bitSize b v :=
    writeFieldMem_of_dirtyStep_grow hw hy.mem_wf hbw hs₁
  have hz_mem : z.mem = writeFieldMem w 0 y.mem y.bitSize b v :=
    (congrArg BitMemory.State.mem hz_st).trans hmem_eq
  have hz_sz : z.bitSize = y.bitSize + b :=
    (congrArg BitMemory.State.bitSize hz_st).trans hs₁.1
  refine ⟨hz_wf, hz_sz, ?_, ?_, fun j hj => (hz_hi j hj).trans (hy₃_hi j hj)⟩
  · unfold BitMemory.State.getField
    change readField w 0 z.mem y.bitSize b = v
    rw [hz_mem, readField_writeFieldMem_same hw y.mem hbw hv]
  · intro i hi
    unfold BitMemory.State.getBit
    change readBit w 0 z.mem i = readBit w 0 y.mem i
    rw [hz_mem, readBit_writeFieldMem hw y.mem hbw i, ite_eq_right (by omega)]

/-- Shrinking a well-formed `BitMemory.State` `s₂` of bit size `s₁.bitSize + b` back by `b` bits
recovers `s₁` identically whenever all lower bits `< s₁.bitSize` match `s₁`. -/
theorem stepFn_shrink_eq_of_getBit_eq {w b : ℕ} (hw : 0 < w)
    {s₁ s₂ : BitMemory.State} (hs₁ : s₁.WellFormed w) (hs₂ : s₂.WellFormed w)
    (hsz : s₂.bitSize = s₁.bitSize + b)
    (hbits : ∀ i < s₁.bitSize, s₂.getBit w i = s₁.getBit w i) :
    (BitMemory.stepFn w s₂ (.shrink b)).1 = s₁ := by
  have hsub : s₂.bitSize - b = s₁.bitSize := by omega
  cases s₁ with
  | mk mem₁ sz₁ =>
    dsimp only at hsz hsub
    change (⟨clearRangeMem w s₂.mem (s₂.bitSize - b) s₂.bitSize, s₂.bitSize - b⟩ :
      BitMemory.State) = ⟨mem₁, sz₁⟩
    rw [hsub]
    congr 1
    funext a
    apply word_eq_of_readBit_eq hw (clearRangeMem_fits w s₂.mem sz₁ s₂.bitSize a) (hs₁.mem_fits a)
    intro j hj
    rw [readBit_clearRangeMem hw]
    by_cases hlt : a * w + j < sz₁
    · rw [ite_eq_right (by omega)]
      exact hbits (a * w + j) hlt
    · have hzero₁ : readBit w 0 mem₁ (a * w + j) = false :=
        hs₁.zero_above (a * w + j) (Nat.not_lt.mp hlt)
      rw [hzero₁]
      split_ifs with hmid
      · rfl
      · exact hs₂.zero_above (a * w + j) (by omega)

/-- Executing `clientFreeBitsRegCode` (`.shrink 230`) in `1` instruction frees the `b`-bit client
slice and restores `z'.toBitMemoryState = y.toBitMemoryState`. -/
theorem clientFreeBitsRegCode_exec {w b : ℕ} (hw : 0 < w) (hbw : b ≤ w)
    {y z : BitRAM.Data 280} (hy : y.WellFormed w) (hz : z.WellFormed w)
    (hz_sz : z.bitSize = y.bitSize + b)
    (hz_bits : ∀ i < y.bitSize, z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i)
    (hr230 : z.regs 230 = b) :
    BitRAM.DemonicExecWithin w clientFreeBitsRegCode z
      (fun z' =>
        z'.WellFormed w ∧
        z'.toBitMemoryState = y.toBitMemoryState ∧
        z'.regs = z.regs) 1 := by
  have hle : z.regs 230 ≤ z.bitSize := by omega
  have hcost : max 1 ((z.regs 230) ⌈/⌉ w) ≤ 1 := by
    rw [hr230]
    exact (BitMemory.charge_shrink_of_le hw hbw z.toBitMemoryState).le
  refine .shrink hle hcost ?_
  have hst :
      (BitMemory.stepFn w z.toBitMemoryState (.shrink (z.regs 230))).1 = y.toBitMemoryState := by
    rw [hr230]
    exact stepFn_shrink_eq_of_getBit_eq hw hy.mem_wf hz.mem_wf hz_sz hz_bits
  have hz'_st :
      (⟨z.regs, (BitMemory.stepFn w z.toBitMemoryState (.shrink (z.regs 230))).1.mem,
        z.bitSize - z.regs 230⟩ : BitRAM.Data 280).toBitMemoryState = y.toBitMemoryState := by
    change (⟨(BitMemory.stepFn w z.toBitMemoryState (.shrink (z.regs 230))).1.mem,
      z.bitSize - z.regs 230⟩ : BitMemory.State) = y.toBitMemoryState
    have hsz_eq :
        z.bitSize - z.regs 230 =
          (BitMemory.stepFn w z.toBitMemoryState (.shrink (z.regs 230))).1.bitSize := rfl
    rw [hsz_eq, hst]
  exact ⟨⟨hz.regs_fits, hz'_st ▸ hy.mem_wf⟩, hz'_st, rfl⟩

/-! ## Section 2: Uniform subroutine theorem for `delete` and released-bit reuse -/

/-- **Concrete uniform subroutine theorem (`inEpochDeleteOpRegCode_clientAlloc_subroutine`):**
using the fixed parameter-free programs `inEpochDeleteOpRegCode`, `clientAllocBitsRegCode`, and
`clientFreeBitsRegCode` on `BitRAM.Code .standard 280`:
1. Deleting an active key `u` (`(s_abs u).isSome`, `EpochInv U N m'`) from `x` (with `r270 = u.val`)
   executes in `T_del` instructions under demonic `.grow` (`O(1)` expected amortized overhead
   `≤ 294450`) and shrinks `y.bitSize` to `x.bitSize - itemBits U V N`, establishing `EpochDictInv`
   and `Rep` for `nextState s_abs (.delete u)`.
2. Loading client arguments `(b, v_client)` (`b ≤ itemBits U V N`, `b ≤ w`, `Fits b v_client`) via
   `loadClientAllocRegs b v_client y` and executing `clientAllocBitsRegCode` runs in `46`
   instructions under demonic `.grow`, reusing `[y.bitSize, y.bitSize + b)` inside the released
   interval `[y.bitSize, x.bitSize)` so `z.bitSize = y.bitSize + b ≤ x.bitSize`, writing
   `z.toBitMemoryState.getField w y.bitSize b = v_client`, preserving the live dictionary `Rep` on
   the dictionary prefix
   `(BitMemory.stepFn w z.toBitMemoryState (.shrink b)).1 = y.toBitMemoryState`,
   and allowing `clientFreeBitsRegCode` (`1` instruction) to restore full `EpochDictInv` on `z'`. -/
theorem inEpochDeleteOpRegCode_clientAlloc_subroutine {U V w N : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    {x : BitRAM.Data 280} (hinv : EpochDictInv U V w N θ s_abs s_fix x)
    (u : Fin U) (hsome : (s_abs u).isSome)
    (hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs (.delete u))).card)
    {b v_client : ℕ} (hbw : b ≤ w) (hb_item : b ≤ itemBits U V N) (hv_client : Fits b v_client) :
    let s_abs' := nextState s_abs (.delete u)
    let bit_after_del := x.bitSize - itemBits U V N
    ∃ (s_fix' : Memory.State) (T_del : ℕ),
      T_del + 1967 * inEpochPotential U V w N s_fix' ≤
        1967 * inEpochPotential U V w N s_fix + inEpochStepOverhead U N θ s_abs (.delete u) ∧
      (∑' θ₀ : Succinct.QuotHashSeed U N,
        (epochSeedPMF U N θ₀ : ℝ≥0∞) *
          ((inEpochStepOverhead U N θ₀ s_abs (.delete u) : ℕ) : ℝ≥0∞)) ≤ 294450 ∧
      BitRAM.DemonicExecWithin w inEpochDeleteOpRegCode (x.set 270 u.val)
        (fun y =>
          EpochDictInv U V w N θ s_abs' s_fix' y ∧
          Rep U V w N θ s_abs' y.toBitMemoryState ∧
          y.bitSize = bit_after_del ∧
          BitRAM.DemonicExecWithin w clientAllocBitsRegCode (loadClientAllocRegs b v_client y)
            (fun z =>
              z.WellFormed w ∧
              z.bitSize = bit_after_del + b ∧
              z.bitSize ≤ x.bitSize ∧
              z.toBitMemoryState.getField w bit_after_del b = v_client ∧
              (∀ i < bit_after_del,
                z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i) ∧
              Rep U V w N θ s_abs' (BitMemory.stepFn w z.toBitMemoryState (.shrink b)).1 ∧
              BitRAM.DemonicExecWithin w clientFreeBitsRegCode z
                (fun z' =>
                  EpochDictInv U V w N θ s_abs' s_fix' z' ∧
                  Rep U V w N θ s_abs' z'.toBitMemoryState ∧
                  z'.bitSize = bit_after_del) 1)
            46)
        T_del := by
  intro s_abs' bit_after_del
  let m := (Dynamic.dom s_abs).card
  let m' := (Dynamic.dom s_abs').card
  have hm_pos : 0 < m := Finset.card_pos.mpr ⟨u, Dictionary.mem_dom_iff_isSome.mpr hsome⟩
  have hcard_del : m' = m - 1 := Dynamic.card_dom_delete_eq_of_isSome hsome
  have hx_sz : x.bitSize = dictBitSize U V w N m := hinv.bitSize_eq
  have hdict_sub : dictBitSize U V w N m' = bit_after_del := by
    dsimp only [bit_after_del]
    rw [hx_sz, hcard_del]
    unfold dictBitSize
    have hmul : m * itemBits U V N = (m - 1) * itemBits U V N + itemBits U V N := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m from hm_pos), Nat.add_one_mul]
    omega
  have hu_fits : Fits w u.val := Fits.of_le hU u.isLt.le
  have hx_set_inv : EpochDictInv U V w N θ s_abs s_fix (x.set 270 u.val) :=
    ⟨wf_set 270 hinv.wf hu_fits,
      hinv.epoch_regs.set_of_outside (Or.inr (by decide)) u.val,
      hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
      hinv.bitSize_eq, hinv.hdr_count, hinv.hdr_cap, hinv.hdr_itemBits, hinv.hdr_metaBits,
      hinv.active⟩
  have hr270 : (x.set 270 u.val).regs 270 = u.val := by simp [BitRAM.Data.set]
  obtain ⟨s_fix', T_del, hexec_del, hcost⟩ :=
    inEpochDeleteOpRegCode_exec hw hU hV θ hx_set_inv u hr270
  have hcost' :
      T_del + 1967 * inEpochPotential U V w N s_fix' ≤
        1967 * inEpochPotential U V w N s_fix + inEpochStepOverhead U N θ s_abs (.delete u) := by
    dsimp only [inEpochStepOverhead, opKey]
    omega
  have htsum := tsum_inEpochStepOverhead_le hinv.cap_le s_abs hinv.card_le (.delete u)
  refine ⟨s_fix', T_del, hcost', htsum, ?_⟩
  refine hexec_del.mono (fun y hinv_y => ?_) le_rfl
  change EpochDictInv U V w N θ s_abs' s_fix' y at hinv_y
  have hrep_y : Rep U V w N θ s_abs' y.toBitMemoryState := hinv_y.rep hepoch'
  have hy_sz : y.bitSize = bit_after_del := hinv_y.bitSize_eq.trans hdict_sub
  have hib_le : itemBits U V N ≤ x.bitSize := by
    rw [hx_sz]
    unfold dictBitSize
    have : 1 * itemBits U V N ≤ m * itemBits U V N := Nat.mul_le_mul_right _ hm_pos
    omega
  have hgrow_le : y.bitSize + b ≤ x.bitSize := by
    rw [hy_sz]; dsimp only [bit_after_del]; omega
  have hgrow_fits : Fits w (y.bitSize + b) :=
    Fits.of_le hinv.wf.mem_wf.bitSize_fits hgrow_le
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have hv_fits : Fits w v_client := hv_client.mono hbw
  set y_cl := loadClientAllocRegs b v_client y
  have hy_cl_wf : y_cl.WellFormed w :=
    wf_set 231 (wf_set 230 hinv_y.wf hb_fits) hv_fits
  have hy_cl_er : EpochRegs U V w N y_cl :=
    (hinv_y.epoch_regs.set_of_outside (Or.inl (by decide)) b).set_of_outside
      (Or.inl (by decide)) v_client
  have hr230 : y_cl.regs 230 = b := by
    simp +decide [y_cl, loadClientAllocRegs, BitRAM.Data.set]
  have hr231 : y_cl.regs 231 = v_client := by
    simp +decide [y_cl, loadClientAllocRegs, BitRAM.Data.set]
  refine ⟨hinv_y, hrep_y, hy_sz, ?_⟩
  refine (clientAllocBitsRegCode_exec hw hbw hv_client hy_cl_wf hgrow_fits hr230 hr231).mono
    (fun z ⟨hz_wf, hz_sz, hz_field, hz_bits, hz_hi⟩ => ?_) le_rfl
  have hz_sz' : z.bitSize = bit_after_del + b := by
    change z.bitSize = y_cl.bitSize + b at hz_sz
    change y.bitSize = bit_after_del at hy_sz
    simpa [y_cl, loadClientAllocRegs, hy_sz] using hz_sz
  have hz_le : z.bitSize ≤ x.bitSize := by
    rw [hz_sz', ← hy_sz]; exact hgrow_le
  have hz_field' : z.toBitMemoryState.getField w bit_after_del b = v_client := by
    simpa [y_cl, loadClientAllocRegs, hy_sz] using hz_field
  have hz_bits' : ∀ i < bit_after_del,
      z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i := by
    intro i hi
    exact hz_bits i (by simpa [y_cl, loadClientAllocRegs, hy_sz] using hi)
  have hz_y_sz : z.bitSize = y.bitSize + b := hz_sz'.trans (congrArg (· + b) hy_sz.symm)
  have hshrink_eq : (BitMemory.stepFn w z.toBitMemoryState (.shrink b)).1 = y.toBitMemoryState :=
    stepFn_shrink_eq_of_getBit_eq hw hinv_y.wf.mem_wf hz_wf.mem_wf hz_y_sz
      (fun i hi => hz_bits' i (hy_sz ▸ hi))
  have hz_230 : z.regs 230 = b := (hz_hi 230 (by decide)).trans hr230
  have hz_er : EpochRegs U V w N z :=
    hy_cl_er.congr_regs fun r hr1 _ => hz_hi r (by omega)
  refine ⟨hz_wf, hz_sz', hz_le, hz_field', hz_bits', hshrink_eq ▸ hrep_y, ?_⟩
  refine (clientFreeBitsRegCode_exec hw hbw hinv_y.wf hz_wf hz_y_sz
    (fun i hi => hz_bits' i (hy_sz ▸ hi)) hz_230).mono
    (fun z' ⟨hz'_wf, hz'_st, hz'_regs⟩ => ?_) le_rfl
  have hz'_mem : z'.mem = y.mem := congrArg BitMemory.State.mem hz'_st
  have hz'_sz : z'.bitSize = y.bitSize := congrArg BitMemory.State.bitSize hz'_st
  have hz'_er : EpochRegs U V w N z' :=
    hz_er.congr_regs fun r _ _ => congrFun hz'_regs r
  have hz'_inv : EpochDictInv U V w N θ s_abs' s_fix' z' :=
    ⟨hz'_wf, hz'_er, hinv_y.cap_le, hinv_y.card_le, hinv_y.val_bounded, hinv_y.fit_cap,
      hz'_sz.trans hinv_y.bitSize_eq,
      (congrFun hz'_mem 0).trans hinv_y.hdr_count,
      (congrFun hz'_mem 1).trans hinv_y.hdr_cap,
      (congrFun hz'_mem 2).trans hinv_y.hdr_itemBits,
      (congrFun hz'_mem 3).trans hinv_y.hdr_metaBits,
      fun hp => by
        have hact := hinv_y.active hp
        exact ⟨hact.1, hz'_st.symm ▸ hact.2.1, hz'_mem.symm ▸ hact.2.2⟩⟩
  exact ⟨hz'_inv, hz'_inv.rep hepoch', hz'_sz.trans hy_sz⟩

/-- **Uniform existential subroutine theorem (`delete_reuses_released_bits_subroutine`):**
there exist fixed parameter-free `BitRAM.Code .standard 280` programs `code_del` and `code_client`
(quantified **ahead of** `∀ U V w N ... ∀ x u b v_client`) that delete an active key in `O(1)`
expected amortized instructions (shrinking `bitSize` by `itemBits U V N`) and subsequently allocate
and write a `b`-bit client field under demonic `.grow` inside the released bit interval without
exceeding the pre-delete `x.bitSize`, while preserving the dictionary's live `Rep`. -/
theorem delete_reuses_released_bits_subroutine :
    ∃ (code_del code_client : BitRAM.Code .standard 280),
      ∀ {U V w N : ℕ} (_hw : 0 < w) (_hU : Fits w U) (_hV : Fits w V)
        (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
        {x : BitRAM.Data 280} (_hinv : EpochDictInv U V w N θ s_abs s_fix x)
        (u : Fin U) (_hsome : (s_abs u).isSome)
        (_hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs (.delete u))).card)
        {b v_client : ℕ} (_hbw : b ≤ w) (_hb_item : b ≤ itemBits U V N)
        (_hv_client : Fits b v_client),
        let s_abs' := nextState s_abs (.delete u)
        let bit_after_del := x.bitSize - itemBits U V N
        ∃ (s_fix' : Memory.State) (T_del : ℕ),
          T_del + 1967 * inEpochPotential U V w N s_fix' ≤
            1967 * inEpochPotential U V w N s_fix + inEpochStepOverhead U N θ s_abs (.delete u) ∧
          (∑' θ₀ : Succinct.QuotHashSeed U N,
            (epochSeedPMF U N θ₀ : ℝ≥0∞) *
              ((inEpochStepOverhead U N θ₀ s_abs (.delete u) : ℕ) : ℝ≥0∞)) ≤ 294450 ∧
          BitRAM.DemonicExecWithin w code_del (x.set 270 u.val)
            (fun y =>
              EpochDictInv U V w N θ s_abs' s_fix' y ∧
              Rep U V w N θ s_abs' y.toBitMemoryState ∧
              y.bitSize = bit_after_del ∧
              BitRAM.DemonicExecWithin w code_client (loadClientAllocRegs b v_client y)
                (fun z =>
                  z.WellFormed w ∧
                  z.bitSize = bit_after_del + b ∧
                  z.bitSize ≤ x.bitSize ∧
                  z.toBitMemoryState.getField w bit_after_del b = v_client ∧
                  (∀ i < bit_after_del,
                    z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i) ∧
                  Rep U V w N θ s_abs' (BitMemory.stepFn w z.toBitMemoryState (.shrink b)).1)
                46)
            T_del := by
  refine ⟨inEpochDeleteOpRegCode, clientAllocBitsRegCode, ?_⟩
  intro U V w N hw hU hV θ s_abs s_fix x hinv u hsome hepoch' b v_client hbw hb_item hv_client
  obtain ⟨s_fix', T_del, hcost, htsum, hexec⟩ :=
    inEpochDeleteOpRegCode_clientAlloc_subroutine hw hU hV θ hinv u hsome hepoch'
      hbw hb_item hv_client
  refine ⟨s_fix', T_del, hcost, htsum, ?_⟩
  refine hexec.mono (fun y ⟨hinv_y, hrep_y, hy_sz, hexec_cl⟩ =>
    ⟨hinv_y, hrep_y, hy_sz, hexec_cl.mono
      (fun z ⟨hz_wf, hz_sz, hz_le, hz_f, hz_b, hrep_z, _⟩ =>
        ⟨hz_wf, hz_sz, hz_le, hz_f, hz_b, hrep_z⟩) le_rfl⟩) le_rfl

end Cslib.DataStructure.Dictionary.BitResizable
