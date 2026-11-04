/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.MachinePrimitives

/-!
# Parameter-Free Dense-Item and Translation-Array `BitRAM.Code` Primitives

This module defines uniform `BitRAM.Code .standard` programs operating on the bit-packed dense
`(quotient, value)` item suffix `[epochMetaBits U w N, dictBitSize U V w N n_t)` and on the
translation arrays `td` (`slotOf`) and `dt` (`denseOfPhys`), together with their
`BitRAM.DemonicExecWithin` execution certificates:
* `appendDenseItemRegCode` and `popDenseItemRegCode`: grow/shrink by `itemBits U V N` and write
  `(q, v)` from registers `12..15`.
* `readDenseQuotRegCode`, `readDenseValRegCode`, `writeDenseQuotRegCode`, `writeDenseValRegCode`:
  read/write `denseQuotAt` and `denseValAt` at dense index `r1 = d` using header words `2..3`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM
open Cslib.WordRAM.BitRAM
open Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: Parameter-free dense item programs on `BitRAM.Data 16` -/

/-- Parameter-free `BitRAM.Code .standard 16` program appending one dense `(quotient, value)` item:
given `r12 = quotientBits U N`, `r13 = valBits V`, `r14 = q`, `r15 = v`, grows by `r12` bits and
writes `r14`, then grows by `r13` bits and writes `r15`, preserving `r12..r15`. -/
@[expose] def appendDenseItemRegCode : BitRAM.Code .standard 16 :=
  .seq (.op (.copy 1 12))
    (.seq (.grow 1 1)
      (.seq (.op (.copy 2 12))
        (.seq (.op (.copy 3 14))
          (.seq (BitRAM.writeBitsCode.embed12 (by decide))
            (.seq (.op (.copy 1 13))
              (.seq (.grow 1 1)
                (.seq (.op (.copy 2 13))
                  (.seq (.op (.copy 3 15))
                    (BitRAM.writeBitsCode.embed12 (by decide))))))))))

/-- Parameter-free `BitRAM.Code .standard 16` program popping one dense `(quotient, value)` item:
given `r12 = quotientBits U N` and `r13 = valBits V`, shrinks by `r13` bits and then by `r12` bits,
preserving `r12..r15`. -/
@[expose] def popDenseItemRegCode : BitRAM.Code .standard 16 :=
  .seq (.op (.copy 1 13))
    (.seq (.shrink 1)
      (.seq (.op (.copy 1 12))
        (.shrink 1)))

/-- Parameter-free `BitRAM.Code .standard 16` program reading
`denseQuotAt U V w N x.toBitMemoryState d` into `r0`, given `r1 = d`, `r12 = quotientBits U N`,
and header words `x.mem 2 = itemBits U V N` and `x.mem 3 = epochMetaBits U w N`. Preserves
`r12..r15`, `mem`, and `bitSize`. -/
@[expose] def readDenseQuotRegCode : BitRAM.Code .standard 16 :=
  .seq (.op (.const 4 2))
    (.seq (.op (.load 4 4))
      (.seq (.op (.bin .mul 1 1 4))
        (.seq (.op (.const 4 3))
          (.seq (.op (.load 4 4))
            (.seq (.op (.bin .add 1 4 1))
              (.seq (.op (.copy 2 12))
                (BitRAM.readBitsCode.embed12 (by decide))))))))

/-- Parameter-free `BitRAM.Code .standard 16` program reading
`denseValAt U V w N x.toBitMemoryState d` into `r0`, given `r1 = d`, `r12 = quotientBits U N`,
`r13 = valBits V`, and header words `x.mem 2 = itemBits U V N` and `x.mem 3 = epochMetaBits U w N`.
Preserves `r12..r15`, `mem`, and `bitSize`. -/
@[expose] def readDenseValRegCode : BitRAM.Code .standard 16 :=
  .seq (.op (.const 4 2))
    (.seq (.op (.load 4 4))
      (.seq (.op (.bin .mul 1 1 4))
        (.seq (.op (.const 4 3))
          (.seq (.op (.load 4 4))
            (.seq (.op (.bin .add 1 4 1))
              (.seq (.op (.bin .add 1 1 12))
                (.seq (.op (.copy 2 13))
                  (BitRAM.readBitsCode.embed12 (by decide)))))))))

/-- Parameter-free `BitRAM.Code .standard 16` program writing `q` (`r14`, width
`r12 = quotientBits U N`) at `itemQuotBitOff U V w N d` (`r1 = d`), preserving `r12..r15`. -/
@[expose] def writeDenseQuotRegCode : BitRAM.Code .standard 16 :=
  .seq (.op (.const 4 2))
    (.seq (.op (.load 4 4))
      (.seq (.op (.bin .mul 1 1 4))
        (.seq (.op (.const 4 3))
          (.seq (.op (.load 4 4))
            (.seq (.op (.bin .add 1 4 1))
              (.seq (.op (.copy 2 12))
                (.seq (.op (.copy 3 14))
                  (BitRAM.writeBitsCode.embed12 (by decide)))))))))

/-- Parameter-free `BitRAM.Code .standard 16` program writing `v` (`r15`, width `r13 = valBits V`)
at `itemValBitOff U V w N d` (`r1 = d`, `r12 = quotientBits U N`), preserving `r12..r15`. -/
@[expose] def writeDenseValRegCode : BitRAM.Code .standard 16 :=
  .seq (.op (.const 4 2))
    (.seq (.op (.load 4 4))
      (.seq (.op (.bin .mul 1 1 4))
        (.seq (.op (.const 4 3))
          (.seq (.op (.load 4 4))
            (.seq (.op (.bin .add 1 4 1))
              (.seq (.op (.bin .add 1 1 12))
                (.seq (.op (.copy 2 13))
                  (.seq (.op (.copy 3 15))
                    (BitRAM.writeBitsCode.embed12 (by decide))))))))))

private theorem wf_comap12 {w : ℕ} {x : BitRAM.Data 16} (hx : x.WellFormed w) :
    (x.comap (embedFin12 (by decide : 12 ≤ 16))).WellFormed w where
  regs_fits i := hx.regs_fits (embedFin12 (by decide) i)
  mem_wf := hx.mem_wf

/-- `appendDenseItemRegCode` executes in at most `92` instructions on `BitRAM.Data 16`, producing
`appendDenseItemState U V w N q v x.toBitMemoryState` and preserving `r12..r15` and
`WellFormed w`. -/
theorem appendDenseItemRegCode_exec {U V w N q v : ℕ} {x : BitRAM.Data 16}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hr12 : x.regs 12 = quotientBits U N)
    (hr13 : x.regs 13 = valBits V)
    (hr14 : x.regs 14 = q)
    (hr15 : x.regs 15 = v)
    (hq : Fits (quotientBits U N) q)
    (hv : Fits (valBits V) v)
    (hfits : Fits w (x.bitSize + itemBits U V N)) :
    BitRAM.DemonicExecWithin w appendDenseItemRegCode x
      (fun y =>
        y.toBitMemoryState = appendDenseItemState U V w N q v x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.bitSize = x.bitSize + itemBits U V N ∧
        (∀ j : Fin 16, 12 ≤ j.1 → y.regs j = x.regs j)) 92 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hq_fits : Fits w (quotientBits U N) := Fits.of_le (fits_self w) hqw
  have hv_fits : Fits w (valBits V) := Fits.of_le (fits_self w) hvw
  have hq_val_fits : Fits w q := hq.mono hqw
  have hv_val_fits : Fits w v := hv.mono hvw
  have hgrow1_fits : Fits w (x.bitSize + quotientBits U N) := by
    refine Fits.of_le hfits ?_; unfold itemBits; omega
  have hcost1 : max 1 ((quotientBits U N) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hqw x.toBitMemoryState).le
  refine step_dExec_copy (v := quotientBits U N) (T := 91) hr12 ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 16 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w x.toBitMemoryState (.grow (quotientBits U N)) s₁ x.bitSize ∧
        y₁ = ⟨Function.update (x.set 1 (quotientBits U N)).regs 1 x.bitSize,
          s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 90)
    (.grow hgrow1_fits hcost1 fun s₁ hs₁ => ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  set y₁ : BitRAM.Data 16 :=
    ⟨Function.update (x.set 1 (quotientBits U N)).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩
  refine step_dExec_copy (v := quotientBits U N) (T := 89)
    (by simp +decide [y₁, BitRAM.Data.set, hr12]) ?_
  refine step_dExec_copy (v := q) (T := 88)
    (by simp +decide [y₁, BitRAM.Data.set, hr14]) ?_
  set x₂ := (y₁.set 2 (quotientBits U N)).set 3 q
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (quotientBits U N)) hw hx.mem_wf hgrow1_fits hs₁
  have hx₂_wf : x₂.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi3 : i = 3
    · subst hi3; exact hq_val_fits
    · by_cases hi2 : i = 2
      · subst hi2; exact hq_fits
      · by_cases hi1 : i = 1
        · subst hi1; exact hx.mem_wf.bitSize_fits
        · simp only [x₂, y₁, BitRAM.Data.set, Function.update_of_ne hi3,
            Function.update_of_ne hi2, Function.update_of_ne hi1]
          exact hx.regs_fits i
  have hv_write1 : BitMemory.valid w (x₂.comap (embedFin12 (by decide))).toBitMemoryState
      (.writeBits ((x₂.comap (embedFin12 (by decide))).regs 1)
        ((x₂.comap (embedFin12 (by decide))).regs 2)
        ((x₂.comap (embedFin12 (by decide))).regs 3)) := by
    refine ⟨hqw, ?_, hq⟩
    change x.bitSize + quotientBits U N ≤ s₁.bitSize
    exact hs₁.1.symm.le
  refine .seq (T₁ := 42) (T₂ := 46)
    (DemonicExecWithin.embed12 (by decide)
      (writeBitsCode_exec_wf hw (wf_comap12 hx₂_wf) hv_write1))
    (fun y₂ ⟨⟨hy₂_st, hy₂_wf12⟩, hy₂_hi⟩ => ?_) (by omega)
  change y₂.toBitMemoryState =
    ⟨writeFieldMem w 0 s₁.mem x.bitSize (quotientBits U N) q, s₁.bitSize⟩ at hy₂_st
  have hy₂_13 : y₂.regs 13 = valBits V := by
    rw [hy₂_hi 13 (by decide)]
    simp +decide [x₂, y₁, BitRAM.Data.set, hr13]
  have hy₂_15 : y₂.regs 15 = v := by
    rw [hy₂_hi 15 (by decide)]
    simp +decide [x₂, y₁, BitRAM.Data.set, hr15]
  have hy₂_wf : y₂.WellFormed w := by
    refine ⟨fun i => ?_, hy₂_wf12.mem_wf⟩
    by_cases hi : i.1 < 12
    · exact hy₂_wf12.regs_fits ⟨i.1, hi⟩
    · rw [hy₂_hi i (by omega)]
      exact hx₂_wf.regs_fits i
  have hsz2 : y₂.bitSize = s₁.bitSize := congrArg BitMemory.State.bitSize hy₂_st
  have hgrow2_fits : Fits w (y₂.bitSize + valBits V) := by
    rw [hsz2, hs₁.1]
    change Fits w (x.bitSize + quotientBits U N + valBits V)
    simpa [itemBits, Nat.add_assoc] using hfits
  have hcost2 : max 1 ((valBits V) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hvw y₂.toBitMemoryState).le
  refine step_dExec_copy (v := valBits V) (T := 45) hy₂_13 ?_
  refine .seq
    (Q := fun y₃ : BitRAM.Data 16 =>
      ∃ s₃ : BitMemory.State,
        BitMemory.dirtyStep w y₂.toBitMemoryState (.grow (valBits V)) s₃ y₂.bitSize ∧
        y₃ = ⟨Function.update (y₂.set 1 (valBits V)).regs 1 y₂.bitSize,
          s₃.mem, s₃.bitSize⟩)
    (T₁ := 1) (T₂ := 44)
    (.grow hgrow2_fits hcost2 fun s₃ hs₃ => ⟨s₃, hs₃, rfl⟩)
    (fun y₃ ⟨s₃, hs₃, hy₃_eq⟩ => ?_) (by omega)
  subst hy₃_eq
  set y₃ : BitRAM.Data 16 :=
    ⟨Function.update (y₂.set 1 (valBits V)).regs 1 y₂.bitSize, s₃.mem, s₃.bitSize⟩
  refine step_dExec_copy (v := valBits V) (T := 43)
    (by simp +decide [y₃, BitRAM.Data.set, hy₂_13]) ?_
  refine step_dExec_copy (v := v) (T := 42)
    (by simp +decide [y₃, BitRAM.Data.set, hy₂_15]) ?_
  set x₄ := (y₃.set 2 (valBits V)).set 3 v
  have hs₃_wf : s₃.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (valBits V)) hw hy₂_wf.mem_wf hgrow2_fits hs₃
  have hx₄_wf : x₄.WellFormed w := by
    refine ⟨fun i => ?_, hs₃_wf⟩
    by_cases hi3 : i = 3
    · subst hi3; exact hv_val_fits
    · by_cases hi2 : i = 2
      · subst hi2; exact hv_fits
      · by_cases hi1 : i = 1
        · subst hi1; exact hy₂_wf.mem_wf.bitSize_fits
        · simp only [x₄, y₃, BitRAM.Data.set, Function.update_of_ne hi3,
            Function.update_of_ne hi2, Function.update_of_ne hi1]
          exact hy₂_wf.regs_fits i
  have hv_write2 : BitMemory.valid w (x₄.comap (embedFin12 (by decide))).toBitMemoryState
      (.writeBits ((x₄.comap (embedFin12 (by decide))).regs 1)
        ((x₄.comap (embedFin12 (by decide))).regs 2)
        ((x₄.comap (embedFin12 (by decide))).regs 3)) := by
    refine ⟨hvw, ?_, hv⟩
    change y₂.bitSize + valBits V ≤ s₃.bitSize
    exact hs₃.1.symm.le
  refine (DemonicExecWithin.embed12 (by decide)
    (writeBitsCode_exec_wf hw (wf_comap12 hx₄_wf) hv_write2)).mono
    (fun y ⟨⟨hy_st, hy_wf12⟩, hy_hi⟩ => ?_) le_rfl
  have hs₃' : BitMemory.dirtyStep w
      ⟨writeFieldMem w 0 s₁.mem x.toBitMemoryState.bitSize (quotientBits U N) q, s₁.bitSize⟩
      (.grow (valBits V)) s₃ s₁.bitSize := by
    change BitMemory.dirtyStep w
      ⟨writeFieldMem w 0 s₁.mem x.bitSize (quotientBits U N) q, s₁.bitSize⟩
      (.grow (valBits V)) s₃ s₁.bitSize
    rw [← hy₂_st, ← hsz2]
    exact hs₃
  have hdemonic :=
    appendDenseItemProg_demonic (s₁ := s₁) (s₃ := s₃) hw hU hV hx.mem_wf hq hv hfits hs₁ hs₃'
  have hy_st' : y.toBitMemoryState =
      ⟨writeFieldMem w 0 s₃.mem s₁.bitSize (valBits V) v, s₃.bitSize⟩ := by
    have : y.toBitMemoryState =
        ⟨writeFieldMem w 0 s₃.mem y₂.bitSize (valBits V) v, s₃.bitSize⟩ := hy_st
    rwa [hsz2] at this
  have hy_sz : y.bitSize = x.bitSize + itemBits U V N := by
    calc y.bitSize = y.toBitMemoryState.bitSize := rfl
      _ = s₃.bitSize := by rw [hy_st']
      _ = x.bitSize + itemBits U V N := hdemonic.2.2
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hy_wf12.mem_wf⟩
    by_cases hi : i.1 < 12
    · exact hy_wf12.regs_fits ⟨i.1, hi⟩
    · rw [hy_hi i (by omega)]
      exact hx₄_wf.regs_fits i
  refine ⟨hy_st'.trans hdemonic.1, hy_wf, hy_sz, fun j hj => ?_⟩
  have hj3 : j ≠ 3 := by intro h; subst h; contradiction
  have hj2 : j ≠ 2 := by intro h; subst h; contradiction
  have hj1 : j ≠ 1 := by intro h; subst h; contradiction
  rw [hy_hi j hj]
  simp only [x₄, y₃, BitRAM.Data.set, Function.update_of_ne hj3, Function.update_of_ne hj2,
    Function.update_of_ne hj1]
  rw [hy₂_hi j hj]
  simp only [x₂, y₁, BitRAM.Data.set, Function.update_of_ne hj3, Function.update_of_ne hj2,
    Function.update_of_ne hj1]

/-- `popDenseItemRegCode` executes in at most `4` instructions on `BitRAM.Data 16`, shrinking
`x.bitSize` by `itemBits U V N`, preserving `WellFormed w`, `r12..r15`, all earlier dense items
`d < n_t`, and all metadata words `< epochMetaWords U w N`. -/
theorem popDenseItemRegCode_exec {U V w N n_t : ℕ} {x : BitRAM.Data 16}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hr12 : x.regs 12 = quotientBits U N)
    (hr13 : x.regs 13 = valBits V)
    (hsz : x.bitSize = itemBitOff U V w N (n_t + 1)) :
    BitRAM.DemonicExecWithin w popDenseItemRegCode x
      (fun y =>
        y.toBitMemoryState = popDenseItemState U V w N x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.bitSize = itemBitOff U V w N n_t ∧
        (∀ d < n_t,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ j : Fin 16, 12 ≤ j.1 → y.regs j = x.regs j)) 4 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hq_fits : Fits w (quotientBits U N) := Fits.of_le (fits_self w) hqw
  have hv_fits : Fits w (valBits V) := Fits.of_le (fits_self w) hvw
  have hsz_split : x.bitSize = itemBitOff U V w N n_t + quotientBits U N + valBits V := by
    rw [hsz, itemBitOff_succ]; unfold itemBits; omega
  have hv_le : valBits V ≤ x.bitSize := by omega
  have hcost1 : max 1 ((valBits V) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw hvw x.toBitMemoryState).le
  set s₁ := (BitMemory.stepFn w x.toBitMemoryState (.shrink (valBits V))).1
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink (valBits V)) hw hx.mem_wf hv_le
  have hs₁_sz : s₁.bitSize = itemBitOff U V w N n_t + quotientBits U N := by
    change x.bitSize - valBits V = _; omega
  have hq_le : quotientBits U N ≤ s₁.bitSize := by omega
  have hcost2 : max 1 ((quotientBits U N) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw hqw s₁).le
  set s₂ := (BitMemory.stepFn w s₁ (.shrink (quotientBits U N))).1
  have hs₂_wf : s₂.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink (quotientBits U N)) hw hs₁_wf hq_le
  have hs₂_sz : s₂.bitSize = itemBitOff U V w N n_t := by
    change s₁.bitSize - quotientBits U N = _; omega
  refine step_dExec_copy (v := valBits V) (T := 3) hr13 ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 16 =>
      y₁ = ⟨(x.set 1 (valBits V)).regs, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 2)
    (.shrink hv_le hcost1 rfl)
    (fun y₁ hy₁ => ?_) (by omega)
  subst hy₁
  set y₁ : BitRAM.Data 16 := ⟨(x.set 1 (valBits V)).regs, s₁.mem, s₁.bitSize⟩
  refine step_dExec_copy (v := quotientBits U N) (T := 1)
    (by simp +decide [y₁, BitRAM.Data.set, hr12]) ?_
  refine DemonicExecWithin.shrink hq_le hcost2 ?_
  have hy_wf :
      (⟨(y₁.set 1 (quotientBits U N)).regs, s₂.mem, s₂.bitSize⟩ : BitRAM.Data 16).WellFormed w := by
    refine ⟨fun i => ?_, hs₂_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hq_fits
    · simp only [y₁, BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx.regs_fits i
  have hbit_eq : ∀ i < itemBitOff U V w N n_t, s₂.getBit w i = x.toBitMemoryState.getBit w i := by
    intro i hi
    have hb2 : s₂.getBit w i = s₁.getBit w i :=
      BitMemory.getBit_stepFn_shrink_of_lt hw s₁ (quotientBits U N) (by omega)
    have hb1 : s₁.getBit w i = x.toBitMemoryState.getBit w i :=
      BitMemory.getBit_stepFn_shrink_of_lt hw x.toBitMemoryState (valBits V)
        (by change i < x.bitSize - valBits V; omega)
    rw [hb2, hb1]
  refine ⟨rfl, hy_wf, hs₂_sz, ?_, ?_, fun j hj => ?_⟩
  · intro d hd
    have hd_end : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
    have hd_off : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N n_t := by
      rw [← itemBitOff_succ]; unfold itemBitOff; omega
    refine ⟨?_, ?_⟩
    · unfold denseQuotAt
      have h2' := BitMemory.getField_stepFn_shrink (a := itemQuotBitOff U V w N d)
        hw s₁ (quotientBits U N) hqw (by unfold itemQuotBitOff itemBits at *; omega)
      have h1' := BitMemory.getField_stepFn_shrink (a := itemQuotBitOff U V w N d)
        hw x.toBitMemoryState (valBits V) hqw (by
          change itemQuotBitOff U V w N d + quotientBits U N ≤ x.bitSize - valBits V
          unfold itemQuotBitOff itemBits at *; omega)
      exact h2'.trans h1'
    · unfold denseValAt
      have h2' := BitMemory.getField_stepFn_shrink (a := itemValBitOff U V w N d)
        hw s₁ (quotientBits U N) hvw (by unfold itemValBitOff itemBits at *; omega)
      have h1' := BitMemory.getField_stepFn_shrink (a := itemValBitOff U V w N d)
        hw x.toBitMemoryState (valBits V) hvw (by
          change itemValBitOff U V w N d + valBits V ≤ x.bitSize - valBits V
          unfold itemValBitOff itemBits at *; omega)
      exact h2'.trans h1'
  · intro a ha
    have ha_bits : (a + 1) * w ≤ itemBitOff U V w N n_t := by
      unfold itemBitOff epochMetaBits
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      omega
    apply word_eq_of_readBit_eq hw (hs₂_wf.mem_fits a) (hx.mem_wf.mem_fits a)
    intro j hj
    have hi : a * w + j < itemBitOff U V w N n_t := by
      rw [Nat.add_one_mul] at ha_bits; omega
    exact hbit_eq (a * w + j) hi
  · have hj1 : j ≠ 1 := by intro h; subst h; contradiction
    simp [y₁, BitRAM.Data.set, hj1]

set_option linter.unusedSimpArgs false in
/-- `readDenseQuotRegCode` executes in at most `39` instructions on `BitRAM.Data 16`, storing
`denseQuotAt U V w N x.toBitMemoryState d` in `r0` and preserving `r12..r15`, `mem`, `bitSize`,
and `WellFormed w`. -/
theorem readDenseQuotRegCode_exec {U V w N n_t d : ℕ} {x : BitRAM.Data 16}
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hd : d < n_t)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N)
    (hr1 : x.regs 1 = d)
    (hr12 : x.regs 12 = quotientBits U N) :
    BitRAM.DemonicExecWithin w readDenseQuotRegCode x
      (fun y =>
        y.regs 0 = denseQuotAt U V w N x.toBitMemoryState d ∧
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        (∀ j : Fin 16, 12 ≤ j.1 → y.regs j = x.regs j)) 39 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hd_end : itemBitOff U V w N d + itemBits U V N ≤ x.bitSize := by
    have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
    have h2 : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N n_t := by
      rw [← itemBitOff_succ]; unfold itemBitOff; omega
    omega
  have h4w : 4 * w ≤ x.bitSize := by
    refine le_trans ?_ (le_trans (Nat.le_add_right _ _) hsz)
    unfold epochMetaBits epochMetaWords
    exact Nat.mul_le_mul_right w (by split_ifs <;> omega)
  have hadm4 : 4 ≤ x.wordSize w := by
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    exact Nat.le_of_mul_le_mul_right (h4w.trans hcov) hw
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_2 : Fits w 2 := Fits.of_le hfit_bs (by omega)
  have hfit_3 : Fits w 3 := Fits.of_le hfit_bs (by omega)
  have hfit_off : Fits w (itemBitOff U V w N d) :=
    Fits.of_le hfit_bs (by omega)
  have hfit_mul : Fits w (d * itemBits U V N) :=
    Fits.of_le hfit_off (by unfold itemBitOff; omega)
  refine DemonicExecWithin.step_const (T := 38) hfit_2 ?_
  refine step_dExec_load (v := itemBits U V N) (T := 37)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm2]) ?_
  refine step_dExec_bin (v := d * itemBits U V N) (T := 36)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr1]) hfit_mul ?_
  refine DemonicExecWithin.step_const (T := 35) hfit_3 ?_
  refine step_dExec_load (v := epochMetaBits U w N) (T := 34)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm3]) ?_
  refine step_dExec_bin (v := itemBitOff U V w N d) (T := 33)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, itemBitOff]) hfit_off ?_
  refine step_dExec_copy (v := quotientBits U N) (T := 32)
    (by simp +decide [BitRAM.Data.set, hr12]) ?_
  set x₁ :=
    (((((((x.set 4 2).set 4 (itemBits U V N)).set 1 (d * itemBits U V N)).set 4 3).set 4
      (epochMetaBits U w N)).set 1 (itemBitOff U V w N d)).set 2 (quotientBits U N))
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi2 : i = 2
    · subst hi2; simp +decide [x₁, BitRAM.Data.set, ← hr12, hx.regs_fits 12]
    · by_cases hi1 : i = 1
      · subst hi1; simp +decide [x₁, BitRAM.Data.set, hfit_off]
      · by_cases hi4 : i = 4
        · subst hi4
          have h4 : x₁.regs 4 = epochMetaBits U w N := by simp +decide [x₁, BitRAM.Data.set]
          rw [h4, ← hm3]
          exact hx.mem_wf.mem_fits 3
        · simp [x₁, BitRAM.Data.set, hi2, hi1, hi4, hx.regs_fits i]
  have hv_read : BitMemory.valid w (x₁.comap (embedFin12 (by decide))).toBitMemoryState
      (.readBits ((x₁.comap (embedFin12 (by decide))).regs 1)
        ((x₁.comap (embedFin12 (by decide))).regs 2)) := by
    refine ⟨hqw, ?_⟩
    change itemBitOff U V w N d + quotientBits U N ≤ x.bitSize
    unfold itemBits at hd_end
    omega
  refine (DemonicExecWithin.embed12 (by decide)
    (readBitsCode_exec_wf hw (wf_comap12 hx₁_wf) hv_read)).mono
    (fun y ⟨⟨hr0, hst, hy_wf12⟩, hy_hi⟩ => ?_) le_rfl
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hy_wf12.mem_wf⟩
    by_cases hi : i.1 < 12
    · exact hy_wf12.regs_fits ⟨i.1, hi⟩
    · rw [hy_hi i (by omega)]; exact hx₁_wf.regs_fits i
  refine ⟨hr0, hst, hy_wf, fun j hj => ?_⟩
  rw [hy_hi j hj]
  have hj2 : j ≠ 2 := by intro h; subst h; contradiction
  have hj1 : j ≠ 1 := by intro h; subst h; contradiction
  have hj4 : j ≠ 4 := by intro h; subst h; contradiction
  simp [x₁, BitRAM.Data.set, hj2, hj1, hj4]

set_option linter.unusedSimpArgs false in
/-- `readDenseValRegCode` executes in at most `40` instructions on `BitRAM.Data 16`, storing
`denseValAt U V w N x.toBitMemoryState d` in `r0` and preserving `r12..r15`, `mem`, `bitSize`,
and `WellFormed w`. -/
theorem readDenseValRegCode_exec {U V w N n_t d : ℕ} {x : BitRAM.Data 16}
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hd : d < n_t)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N)
    (hr1 : x.regs 1 = d)
    (hr12 : x.regs 12 = quotientBits U N)
    (hr13 : x.regs 13 = valBits V) :
    BitRAM.DemonicExecWithin w readDenseValRegCode x
      (fun y =>
        y.regs 0 = denseValAt U V w N x.toBitMemoryState d ∧
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        (∀ j : Fin 16, 12 ≤ j.1 → y.regs j = x.regs j)) 40 := by
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hd_end : itemBitOff U V w N d + itemBits U V N ≤ x.bitSize := by
    have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
    have h2 : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N n_t := by
      rw [← itemBitOff_succ]; unfold itemBitOff; omega
    omega
  have h4w : 4 * w ≤ x.bitSize := by
    refine le_trans ?_ (le_trans (Nat.le_add_right _ _) hsz)
    unfold epochMetaBits epochMetaWords
    exact Nat.mul_le_mul_right w (by split_ifs <;> omega)
  have hadm4 : 4 ≤ x.wordSize w := by
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    exact Nat.le_of_mul_le_mul_right (h4w.trans hcov) hw
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_2 : Fits w 2 := Fits.of_le hfit_bs (by omega)
  have hfit_3 : Fits w 3 := Fits.of_le hfit_bs (by omega)
  have hfit_voff : Fits w (itemValBitOff U V w N d) := by
    refine Fits.of_le hfit_bs ?_
    unfold itemValBitOff
    unfold itemBits at hd_end
    omega
  have hfit_off : Fits w (itemBitOff U V w N d) :=
    Fits.of_le hfit_voff (by unfold itemValBitOff; omega)
  have hfit_mul : Fits w (d * itemBits U V N) :=
    Fits.of_le hfit_off (by unfold itemBitOff; omega)
  refine DemonicExecWithin.step_const (T := 39) hfit_2 ?_
  refine step_dExec_load (v := itemBits U V N) (T := 38)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm2]) ?_
  refine step_dExec_bin (v := d * itemBits U V N) (T := 37)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr1]) hfit_mul ?_
  refine DemonicExecWithin.step_const (T := 36) hfit_3 ?_
  refine step_dExec_load (v := epochMetaBits U w N) (T := 35)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm3]) ?_
  refine step_dExec_bin (v := itemBitOff U V w N d) (T := 34)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, itemBitOff]) hfit_off ?_
  refine step_dExec_bin (v := itemValBitOff U V w N d) (T := 33)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr12, itemValBitOff]) hfit_voff ?_
  refine step_dExec_copy (v := valBits V) (T := 32)
    (by simp +decide [BitRAM.Data.set, hr13]) ?_
  set x₁ :=
    ((((((((x.set 4 2).set 4 (itemBits U V N)).set 1 (d * itemBits U V N)).set 4 3).set 4
      (epochMetaBits U w N)).set 1 (itemBitOff U V w N d)).set 1 (itemValBitOff U V w N d)).set 2
      (valBits V))
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi2 : i = 2
    · subst hi2; simp +decide [x₁, BitRAM.Data.set, ← hr13, hx.regs_fits 13]
    · by_cases hi1 : i = 1
      · subst hi1; simp +decide [x₁, BitRAM.Data.set, hfit_voff]
      · by_cases hi4 : i = 4
        · subst hi4
          have h4 : x₁.regs 4 = epochMetaBits U w N := by simp +decide [x₁, BitRAM.Data.set]
          rw [h4, ← hm3]
          exact hx.mem_wf.mem_fits 3
        · simp [x₁, BitRAM.Data.set, hi2, hi1, hi4, hx.regs_fits i]
  have hv_read : BitMemory.valid w (x₁.comap (embedFin12 (by decide))).toBitMemoryState
      (.readBits ((x₁.comap (embedFin12 (by decide))).regs 1)
        ((x₁.comap (embedFin12 (by decide))).regs 2)) := by
    refine ⟨hvw, ?_⟩
    change itemValBitOff U V w N d + valBits V ≤ x.bitSize
    unfold itemValBitOff
    unfold itemBits at hd_end
    omega
  refine (DemonicExecWithin.embed12 (by decide)
    (readBitsCode_exec_wf hw (wf_comap12 hx₁_wf) hv_read)).mono
    (fun y ⟨⟨hr0, hst, hy_wf12⟩, hy_hi⟩ => ?_) le_rfl
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hy_wf12.mem_wf⟩
    by_cases hi : i.1 < 12
    · exact hy_wf12.regs_fits ⟨i.1, hi⟩
    · rw [hy_hi i (by omega)]; exact hx₁_wf.regs_fits i
  refine ⟨hr0, hst, hy_wf, fun j hj => ?_⟩
  rw [hy_hi j hj]
  have hj2 : j ≠ 2 := by intro h; subst h; contradiction
  have hj1 : j ≠ 1 := by intro h; subst h; contradiction
  have hj4 : j ≠ 4 := by intro h; subst h; contradiction
  simp [x₁, BitRAM.Data.set, hj2, hj1, hj4]

set_option linter.unusedSimpArgs false in
/-- `writeDenseQuotRegCode` executes in at most `50` instructions on `BitRAM.Data 16`, updating
the quotient slice at `itemQuotBitOff U V w N d` to `q` (`r14`) and preserving `r12..r15`,
`bitSize`, and `WellFormed w`. -/
theorem writeDenseQuotRegCode_exec {U V w N n_t d q : ℕ} {x : BitRAM.Data 16}
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hd : d < n_t)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N)
    (hr1 : x.regs 1 = d)
    (hr12 : x.regs 12 = quotientBits U N)
    (hr14 : x.regs 14 = q)
    (hq : Fits (quotientBits U N) q) :
    BitRAM.DemonicExecWithin w writeDenseQuotRegCode x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (itemQuotBitOff U V w N d) (quotientBits U N) q)).1 ∧
        y.WellFormed w ∧
        (∀ j : Fin 16, 12 ≤ j.1 → y.regs j = x.regs j)) 50 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hd_end : itemBitOff U V w N d + itemBits U V N ≤ x.bitSize := by
    have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
    have h2 : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N n_t := by
      rw [← itemBitOff_succ]; unfold itemBitOff; omega
    omega
  have h4w : 4 * w ≤ x.bitSize := by
    refine le_trans ?_ (le_trans (Nat.le_add_right _ _) hsz)
    unfold epochMetaBits epochMetaWords
    exact Nat.mul_le_mul_right w (by split_ifs <;> omega)
  have hadm4 : 4 ≤ x.wordSize w := by
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    exact Nat.le_of_mul_le_mul_right (h4w.trans hcov) hw
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_2 : Fits w 2 := Fits.of_le hfit_bs (by omega)
  have hfit_3 : Fits w 3 := Fits.of_le hfit_bs (by omega)
  have hfit_off : Fits w (itemBitOff U V w N d) :=
    Fits.of_le hfit_bs (by omega)
  have hfit_mul : Fits w (d * itemBits U V N) :=
    Fits.of_le hfit_off (by unfold itemBitOff; omega)
  refine DemonicExecWithin.step_const (T := 49) hfit_2 ?_
  refine step_dExec_load (v := itemBits U V N) (T := 48)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm2]) ?_
  refine step_dExec_bin (v := d * itemBits U V N) (T := 47)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr1]) hfit_mul ?_
  refine DemonicExecWithin.step_const (T := 46) hfit_3 ?_
  refine step_dExec_load (v := epochMetaBits U w N) (T := 45)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm3]) ?_
  refine step_dExec_bin (v := itemBitOff U V w N d) (T := 44)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, itemBitOff]) hfit_off ?_
  refine step_dExec_copy (v := quotientBits U N) (T := 43)
    (by simp +decide [BitRAM.Data.set, hr12]) ?_
  refine step_dExec_copy (v := q) (T := 42)
    (by simp +decide [BitRAM.Data.set, hr14]) ?_
  set x₁ :=
    ((((((((x.set 4 2).set 4 (itemBits U V N)).set 1 (d * itemBits U V N)).set 4 3).set 4
      (epochMetaBits U w N)).set 1 (itemBitOff U V w N d)).set 2 (quotientBits U N)).set 3 q)
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi3 : i = 3
    · subst hi3; simp +decide [x₁, BitRAM.Data.set, ← hr14, hx.regs_fits 14]
    · by_cases hi2 : i = 2
      · subst hi2; simp +decide [x₁, BitRAM.Data.set, ← hr12, hx.regs_fits 12]
      · by_cases hi1 : i = 1
        · subst hi1; simp +decide [x₁, BitRAM.Data.set, hfit_off]
        · by_cases hi4 : i = 4
          · subst hi4
            have h4 : x₁.regs 4 = epochMetaBits U w N := by simp +decide [x₁, BitRAM.Data.set]
            rw [h4, ← hm3]
            exact hx.mem_wf.mem_fits 3
          · simp [x₁, BitRAM.Data.set, hi3, hi2, hi1, hi4, hx.regs_fits i]
  have hv_write : BitMemory.valid w (x₁.comap (embedFin12 (by decide))).toBitMemoryState
      (.writeBits ((x₁.comap (embedFin12 (by decide))).regs 1)
        ((x₁.comap (embedFin12 (by decide))).regs 2)
        ((x₁.comap (embedFin12 (by decide))).regs 3)) := by
    refine ⟨hqw, ?_, hq⟩
    change itemBitOff U V w N d + quotientBits U N ≤ x.bitSize
    unfold itemBits at hd_end
    omega
  refine (DemonicExecWithin.embed12 (by decide)
    (writeBitsCode_exec_wf hw (wf_comap12 hx₁_wf) hv_write)).mono
    (fun y ⟨⟨hst, hy_wf12⟩, hy_hi⟩ => ?_) le_rfl
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hy_wf12.mem_wf⟩
    by_cases hi : i.1 < 12
    · exact hy_wf12.regs_fits ⟨i.1, hi⟩
    · rw [hy_hi i (by omega)]; exact hx₁_wf.regs_fits i
  refine ⟨hst, hy_wf, fun j hj => ?_⟩
  rw [hy_hi j hj]
  have hj3 : j ≠ 3 := by intro h; subst h; contradiction
  have hj2 : j ≠ 2 := by intro h; subst h; contradiction
  have hj1 : j ≠ 1 := by intro h; subst h; contradiction
  have hj4 : j ≠ 4 := by intro h; subst h; contradiction
  simp [x₁, BitRAM.Data.set, hj3, hj2, hj1, hj4]

set_option linter.unusedSimpArgs false in
/-- `writeDenseValRegCode` executes in at most `51` instructions on `BitRAM.Data 16`, updating
the value slice at `itemValBitOff U V w N d` to `v` (`r15`) and preserving `r12..r15`, `bitSize`,
and `WellFormed w`. -/
theorem writeDenseValRegCode_exec {U V w N n_t d v : ℕ} {x : BitRAM.Data 16}
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hd : d < n_t)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N)
    (hr1 : x.regs 1 = d)
    (hr12 : x.regs 12 = quotientBits U N)
    (hr13 : x.regs 13 = valBits V)
    (hr15 : x.regs 15 = v)
    (hv : Fits (valBits V) v) :
    BitRAM.DemonicExecWithin w writeDenseValRegCode x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (itemValBitOff U V w N d) (valBits V) v)).1 ∧
        y.WellFormed w ∧
        (∀ j : Fin 16, 12 ≤ j.1 → y.regs j = x.regs j)) 51 := by
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hd_end : itemBitOff U V w N d + itemBits U V N ≤ x.bitSize := by
    have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
    have h2 : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N n_t := by
      rw [← itemBitOff_succ]; unfold itemBitOff; omega
    omega
  have h4w : 4 * w ≤ x.bitSize := by
    refine le_trans ?_ (le_trans (Nat.le_add_right _ _) hsz)
    unfold epochMetaBits epochMetaWords
    exact Nat.mul_le_mul_right w (by split_ifs <;> omega)
  have hadm4 : 4 ≤ x.wordSize w := by
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    exact Nat.le_of_mul_le_mul_right (h4w.trans hcov) hw
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_2 : Fits w 2 := Fits.of_le hfit_bs (by omega)
  have hfit_3 : Fits w 3 := Fits.of_le hfit_bs (by omega)
  have hfit_voff : Fits w (itemValBitOff U V w N d) := by
    refine Fits.of_le hfit_bs ?_
    unfold itemValBitOff
    unfold itemBits at hd_end
    omega
  have hfit_off : Fits w (itemBitOff U V w N d) :=
    Fits.of_le hfit_voff (by unfold itemValBitOff; omega)
  have hfit_mul : Fits w (d * itemBits U V N) :=
    Fits.of_le hfit_off (by unfold itemBitOff; omega)
  refine DemonicExecWithin.step_const (T := 50) hfit_2 ?_
  refine step_dExec_load (v := itemBits U V N) (T := 49)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm2]) ?_
  refine step_dExec_bin (v := d * itemBits U V N) (T := 48)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr1]) hfit_mul ?_
  refine DemonicExecWithin.step_const (T := 47) hfit_3 ?_
  refine step_dExec_load (v := epochMetaBits U w N) (T := 46)
    (by simp only [BitRAM.Data.set_wordSize, BitRAM.Data.set_regs, Function.update_self]; omega)
    (by simp [BitRAM.Data.set, hm3]) ?_
  refine step_dExec_bin (v := itemBitOff U V w N d) (T := 45)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, itemBitOff]) hfit_off ?_
  refine step_dExec_bin (v := itemValBitOff U V w N d) (T := 44)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hr12, itemValBitOff]) hfit_voff ?_
  refine step_dExec_copy (v := valBits V) (T := 43)
    (by simp +decide [BitRAM.Data.set, hr13]) ?_
  refine step_dExec_copy (v := v) (T := 42)
    (by simp +decide [BitRAM.Data.set, hr15]) ?_
  set x₁ :=
    (((((((((x.set 4 2).set 4 (itemBits U V N)).set 1 (d * itemBits U V N)).set 4 3).set 4
      (epochMetaBits U w N)).set 1 (itemBitOff U V w N d)).set 1 (itemValBitOff U V w N d)).set 2
      (valBits V)).set 3 v)
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi3 : i = 3
    · subst hi3; simp +decide [x₁, BitRAM.Data.set, ← hr15, hx.regs_fits 15]
    · by_cases hi2 : i = 2
      · subst hi2; simp +decide [x₁, BitRAM.Data.set, ← hr13, hx.regs_fits 13]
      · by_cases hi1 : i = 1
        · subst hi1; simp +decide [x₁, BitRAM.Data.set, hfit_voff]
        · by_cases hi4 : i = 4
          · subst hi4
            have h4 : x₁.regs 4 = epochMetaBits U w N := by simp +decide [x₁, BitRAM.Data.set]
            rw [h4, ← hm3]
            exact hx.mem_wf.mem_fits 3
          · simp [x₁, BitRAM.Data.set, hi3, hi2, hi1, hi4, hx.regs_fits i]
  have hv_write : BitMemory.valid w (x₁.comap (embedFin12 (by decide))).toBitMemoryState
      (.writeBits ((x₁.comap (embedFin12 (by decide))).regs 1)
        ((x₁.comap (embedFin12 (by decide))).regs 2)
        ((x₁.comap (embedFin12 (by decide))).regs 3)) := by
    refine ⟨hvw, ?_, hv⟩
    change itemValBitOff U V w N d + valBits V ≤ x.bitSize
    unfold itemValBitOff
    unfold itemBits at hd_end
    omega
  refine (DemonicExecWithin.embed12 (by decide)
    (writeBitsCode_exec_wf hw (wf_comap12 hx₁_wf) hv_write)).mono
    (fun y ⟨⟨hst, hy_wf12⟩, hy_hi⟩ => ?_) le_rfl
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hy_wf12.mem_wf⟩
    by_cases hi : i.1 < 12
    · exact hy_wf12.regs_fits ⟨i.1, hi⟩
    · rw [hy_hi i (by omega)]; exact hx₁_wf.regs_fits i
  refine ⟨hst, hy_wf, fun j hj => ?_⟩
  rw [hy_hi j hj]
  have hj3 : j ≠ 3 := by intro h; subst h; contradiction
  have hj2 : j ≠ 2 := by intro h; subst h; contradiction
  have hj1 : j ≠ 1 := by intro h; subst h; contradiction
  have hj4 : j ≠ 4 := by intro h; subst h; contradiction
  simp [x₁, BitRAM.Data.set, hj3, hj2, hj1, hj4]

end Cslib.DataStructure.Dictionary.BitResizable
