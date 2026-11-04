/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.BitResizableRand
public import Complexity.DataStructure.Dictionary.BitResizable.Layout

/-!
# Parameter-Free `BitRAM.Code` Primitives for the Bit-Resizable Succinct Dictionary

This module defines fixed, uniform, parameter-free `BitRAM.Code .standard` subprograms and proves
their `BitRAM.DemonicExecWithin` execution certificates:
* `maskOfWidthCode`: computes `2 ^ k - 1` into `dst` for any `k ≤ w` (`0 < w`) stored in `lenReg`
  without baked-in constants, handling `k = w` without overflow via
  `2 ^ (w - 1) + (2 ^ (w - 1) - 1)`.
* `addrSetupRegCode`, `readPackedRegCode`, `writePackedRegCode`: parameter-free
  `BitRAM.Code .standard 12` implementations of `BitPackedArray.readPacked` and
  `BitPackedArray.writePacked` reading `(base, idx, val, k)` from registers `(0, 1, 2, 9)`.
* `log2LoopBitCode`, `log2BitCode`, `clog2BitCode`: parameter-free `.loop` programs computing
  `Nat.log 2` and `Nat.clog 2` in `O(w)` instructions.
* `appendDenseItemRegCode`, `popDenseItemRegCode`, `readDenseQuotRegCode`, `readDenseValRegCode`,
  `writeDenseQuotRegCode`, `writeDenseValRegCode`: parameter-free `BitRAM.Code .standard 16`
  programs operating on the bit-packed dense item suffix
  `[epochMetaBits U w N, dictBitSize U V w N n_t)` with bit widths and item fields passed in
  registers `12..15` and layout offsets read from the header words `2..3`.
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

/-! ## Section 0: Value-normalizing `DemonicExecWithin` stepping helpers -/

theorem dExec_bin {w r : ℕ} {f : BinOp} {dst i j : Fin r} {d : BitRAM.Data r} {v : ℕ}
    {P : BitRAM.Data r → Prop} (hev : f.eval (d.regs i) (d.regs j) = v) (hfit : Fits w v)
    (hP : P (d.set dst v)) :
    BitRAM.DemonicExecWithin w (.op (.bin f dst i j)) d P 1 :=
  DemonicExecWithin.bin (hev.symm ▸ hfit) (hev.symm ▸ hP)

theorem step_dExec_bin {w r T : ℕ} {f : BinOp} {dst i j : Fin r} {d : BitRAM.Data r} {v : ℕ}
    {k : BitRAM.Code .standard r} {P : BitRAM.Data r → Prop}
    (hev : f.eval (d.regs i) (d.regs j) = v) (hfit : Fits w v)
    (hk : BitRAM.DemonicExecWithin w k (d.set dst v) P T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.bin f dst i j)) k) d P (T + 1) :=
  .seq (Q := fun y => y = d.set dst v) (dExec_bin hev hfit rfl) (fun _ hy => hy ▸ hk) (by omega)

theorem step_dExec_copy {B : Basis} {w r T : ℕ} {dst s : Fin r} {d : BitRAM.Data r} {v : ℕ}
    {k : BitRAM.Code B r} {P : BitRAM.Data r → Prop}
    (hev : d.regs s = v)
    (hk : BitRAM.DemonicExecWithin w k (d.set dst v) P T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.copy dst s)) k) d P (T + 1) :=
  .seq (Q := fun y => y = d.set dst v) (DemonicExecWithin.copy (by rw [hev]))
    (fun _ hy => hy ▸ hk) (by omega)

theorem step_dExec_load {B : Basis} {w r T : ℕ} {dst a : Fin r} {d : BitRAM.Data r} {v : ℕ}
    {k : BitRAM.Code B r} {P : BitRAM.Data r → Prop}
    (hadm : d.regs a < d.wordSize w) (hev : d.mem (d.regs a) = v)
    (hk : BitRAM.DemonicExecWithin w k (d.set dst v) P T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.load dst a)) k) d P (T + 1) :=
  .seq (Q := fun y => y = d.set dst v) (DemonicExecWithin.load hadm (by rw [hev]))
    (fun _ hy => hy ▸ hk) (by omega)

theorem dExec_store {B : Basis} {w r : ℕ} {a s : Fin r} {d : BitRAM.Data r} {addr v : ℕ}
    {P : BitRAM.Data r → Prop}
    (hadm : d.regs a < d.wordSize w) (ha : d.regs a = addr) (hv : d.regs s = v)
    (hP : P (d.write addr v)) :
    BitRAM.DemonicExecWithin (B := B) w (.op (.store a s)) d P 1 :=
  DemonicExecWithin.store hadm (by rw [ha, hv]; exact hP)

theorem step_dExec_store {B : Basis} {w r T : ℕ} {a s : Fin r} {d : BitRAM.Data r} {addr v : ℕ}
    {k : BitRAM.Code B r} {P : BitRAM.Data r → Prop}
    (hadm : d.regs a < d.wordSize w) (ha : d.regs a = addr) (hv : d.regs s = v)
    (hk : BitRAM.DemonicExecWithin w k (d.write addr v) P T) :
    BitRAM.DemonicExecWithin w (.seq (.op (.store a s)) k) d P (T + 1) :=
  .seq (Q := fun y => y = d.write addr v) (dExec_store hadm ha hv rfl)
    (fun _ hy => hy ▸ hk) (by omega)

/-! ## Section 1: Parameter-free bitmask computation (`maskOfWidthCode`) -/

/-- Parameter-free `BitRAM.Code .standard 12` subprogram computing `2 ^ (x.regs lenReg) - 1` into
`dst` for any `x.regs lenReg ≤ w` (`0 < w`), using `tmp1` and `tmp2` as scratch registers.
When `x.regs lenReg = w`, computes `2 ^ (w - 1) + (2 ^ (w - 1) - 1) = 2 ^ w - 1` without
intermediate overflow; when `x.regs lenReg < w`, computes `(1 <<< x.regs lenReg) - 1`. -/
@[expose] def maskOfWidthCode (lenReg dst tmp1 tmp2 : Fin 12) : BitRAM.Code .standard 12 :=
  .seq (.op (.width tmp1))
    (.seq (.op (.const tmp2 1))
      (.branch (.eq lenReg tmp1)
        (.seq (.op (.bin .sub tmp1 tmp1 tmp2))
          (.seq (.op (.bin .shiftLeft dst tmp2 tmp1))
            (.seq (.op (.bin .sub tmp1 dst tmp2))
              (.op (.bin .add dst dst tmp1)))))
        (.seq (.op (.bin .shiftLeft dst tmp2 lenReg))
          (.op (.bin .sub dst dst tmp2)))))

private theorem two_pow_pred_add_pred_eq {w : ℕ} (hw : 0 < w) :
    2 ^ (w - 1) + (2 ^ (w - 1) - 1) = 2 ^ w - 1 := by
  have hpos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
  have hpow : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hw, Nat.pow_succ, Nat.mul_two]
  omega

/-- `maskOfWidthCode lenReg dst tmp1 tmp2` executes in at most `8` instructions whenever
`0 < w`, `x.regs lenReg ≤ w`, and `tmp1, tmp2` are distinct from `lenReg, dst` and each other. -/
theorem maskOfWidthCode_exec {w : ℕ} (hw : 0 < w)
    (lenReg dst tmp1 tmp2 : Fin 12)
    (ht1_len : tmp1 ≠ lenReg) (ht2_len : tmp2 ≠ lenReg)
    (ht1_dst : tmp1 ≠ dst) (ht2_dst : tmp2 ≠ dst) (ht12 : tmp1 ≠ tmp2)
    {x : BitRAM.Data 12} (hlen : x.regs lenReg ≤ w) :
    BitRAM.DemonicExecWithin w (maskOfWidthCode lenReg dst tmp1 tmp2) x
      (fun y =>
        y.regs dst = 2 ^ (x.regs lenReg) - 1 ∧
        (∀ i : Fin 12, i ≠ dst → i ≠ tmp1 → i ≠ tmp2 → y.regs i = x.regs i) ∧
        y.mem = x.mem ∧
        y.bitSize = x.bitSize) 8 := by
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  refine DemonicExecWithin.step_width (T := 7) ?_
  refine DemonicExecWithin.step_const (T := 6) h1 ?_
  set s0 := (x.set tmp1 w).set tmp2 1
  have hr_len : s0.regs lenReg = x.regs lenReg := by
    simp [s0, BitRAM.Data.set, ht1_len.symm, ht2_len.symm]
  have hr_t1 : s0.regs tmp1 = w := by
    simp [s0, BitRAM.Data.set, ht12]
  have hr_t2 : s0.regs tmp2 = 1 := by
    simp [s0, BitRAM.Data.set]
  by_cases heq : x.regs lenReg = w
  · have hc : BitRAM.CondHolds (.eq lenReg tmp1) s0 := by
      change s0.regs lenReg = s0.regs tmp1
      rw [hr_len, hr_t1, heq]
    refine .branch_pos (T₀ := 4) hc ?_ (by omega)
    have hsub1_fits : Fits w (w - 1) := Fits.of_le (fits_self w) (Nat.sub_le w 1)
    have hpow_fits : Fits w (2 ^ (w - 1)) :=
      Nat.pow_lt_pow_right Nat.one_lt_two (Nat.sub_lt hw Nat.one_pos)
    have hsub2_fits : Fits w (2 ^ (w - 1) - 1) :=
      Fits.of_le hpow_fits (Nat.sub_le _ _)
    have hadd_fits : Fits w (2 ^ w - 1) :=
      Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos
    refine step_dExec_bin (v := w - 1) (T := 3)
      (by change s0.regs tmp1 - s0.regs tmp2 = w - 1; rw [hr_t1, hr_t2]) hsub1_fits ?_
    set s1 := s0.set tmp1 (w - 1)
    refine step_dExec_bin (v := 2 ^ (w - 1)) (T := 2)
      (by change s1.regs tmp2 <<< s1.regs tmp1 = 2 ^ (w - 1);
          simp [s1, BitRAM.Data.set, ht12.symm, hr_t2, Nat.shiftLeft_eq]) hpow_fits ?_
    set s2 := s1.set dst (2 ^ (w - 1))
    refine step_dExec_bin (v := 2 ^ (w - 1) - 1) (T := 1)
      (by change s2.regs dst - s2.regs tmp2 = 2 ^ (w - 1) - 1;
          simp [s2, s1, BitRAM.Data.set, ht2_dst, ht12.symm, hr_t2]) hsub2_fits ?_
    set s3 := s2.set tmp1 (2 ^ (w - 1) - 1)
    refine dExec_bin (v := 2 ^ w - 1)
      (by change s3.regs dst + s3.regs tmp1 = 2 ^ w - 1;
          simp [s3, s2, BitRAM.Data.set, ht1_dst.symm, two_pow_pred_add_pred_eq hw]) hadd_fits ?_
    refine ⟨by simp [BitRAM.Data.set, heq], fun i hi_d hi_t1 hi_t2 => ?_, rfl, rfl⟩
    simp [s3, s2, s1, s0, BitRAM.Data.set, hi_d, hi_t1, hi_t2]
  · have hlt : x.regs lenReg < w := Nat.lt_of_le_of_ne hlen heq
    have hc : ¬BitRAM.CondHolds (.eq lenReg tmp1) s0 := by
      change s0.regs lenReg ≠ s0.regs tmp1
      rw [hr_len, hr_t1]
      exact heq
    refine .branch_neg (T₀ := 2) hc ?_ (by omega)
    have hpow_fits : Fits w (2 ^ x.regs lenReg) :=
      Nat.pow_lt_pow_right Nat.one_lt_two hlt
    have hsub_fits : Fits w (2 ^ x.regs lenReg - 1) :=
      Fits.of_le hpow_fits (Nat.sub_le _ _)
    refine step_dExec_bin (v := 2 ^ x.regs lenReg) (T := 1)
      (by change s0.regs tmp2 <<< s0.regs lenReg = 2 ^ x.regs lenReg;
           rw [hr_t2, hr_len, Nat.shiftLeft_eq, one_mul]) hpow_fits ?_
    set s1 := s0.set dst (2 ^ x.regs lenReg)
    refine dExec_bin (v := 2 ^ x.regs lenReg - 1)
      (by change s1.regs dst - s1.regs tmp2 = 2 ^ x.regs lenReg - 1;
          simp [s1, BitRAM.Data.set, ht2_dst, hr_t2]) hsub_fits ?_
    refine ⟨by simp [BitRAM.Data.set], fun i hi_d hi_t1 hi_t2 => ?_, rfl, rfl⟩
    simp [s1, s0, BitRAM.Data.set, hi_d, hi_t1, hi_t2]

/-! ## Section 2: Parameter-free `BitPackedArray` access
(`readPackedRegCode`, `writePackedRegCode`) -/

/-- Parameter-free address and mask setup subprogram on `BitRAM.Data 12`:
Given `r0 = base`, `r1 = idx`, and `r9 = k` (`k ≤ w`, leaving `r0, r1, r2, r9, mem, bitSize`
unchanged), computes:
* `r3 = base + wordOffset k w idx`,
* `r4 = base + wordOffset k w idx + 1`,
* `r5 = bitOffset k w idx`,
* `r6 = lowWidth k w idx`,
* `r7 = 2 ^ lowWidth k w idx - 1`,
* `r8 = 2 ^ highWidth k w idx - 1`. -/
@[expose] def addrSetupRegCode : BitRAM.Code .standard 12 :=
  .seq (.op (.width 8))
  (.seq (.op (.bin .div 3 1 8))
  (.seq (.op (.bin .mul 3 3 9))
  (.seq (.op (.bin .mod 5 1 8))
  (.seq (.op (.bin .mul 5 5 9))
  (.seq (.op (.bin .div 4 5 8))
  (.seq (.op (.bin .add 3 3 4))
  (.seq (.op (.bin .mod 5 5 8))
  (.seq (.op (.bin .add 3 0 3))
  (.seq (.op (.const 4 1))
  (.seq (.op (.bin .add 4 3 4))
  (.seq (.op (.bin .sub 6 8 5))
  (.seq (.branch (.lt 9 6) (.op (.copy 6 9)) (.op (.copy 6 6)))
  (.seq (.op (.bin .sub 8 9 6))
  (.seq (maskOfWidthCode 6 7 10 11)
        (maskOfWidthCode 8 8 10 11)))))))))))))))

/-- Read suffix on `BitRAM.Data 12` after `addrSetupRegCode`: loads the two words at `r3` and `r4`,
extracts and combines the low and high bit slices into `r2`. -/
@[expose] def readPackedFinishBitCode : BitRAM.Code .standard 12 :=
  .seq (.op (.load 9 3))
  (.seq (.op (.bin .shiftRight 9 9 5))
  (.seq (.op (.bin .and 9 9 7))
  (.seq (.op (.load 2 4))
  (.seq (.op (.const 7 0))
  (.seq (.op (.bin .shiftRight 2 2 7))
  (.seq (.op (.bin .and 2 2 8))
  (.seq (.op (.bin .shiftLeft 2 2 6))
        (.op (.bin .xor 2 9 2)))))))))

/-- Parameter-free `BitRAM.Code .standard 12` program reading
`BitPackedArray.readPacked base k w x.mem idx` into `r2`, given `r0 = base`, `r1 = idx`,
`r9 = k`. -/
@[expose] def readPackedRegCode : BitRAM.Code .standard 12 :=
  .seq addrSetupRegCode readPackedFinishBitCode

/-- Write suffix on `BitRAM.Data 12` after `addrSetupRegCode`: updates the low bit slice at `r3` and
the high bit slice at `r4` from `r2 = val`, preserving `r0, r1, r2`. -/
@[expose] def writePackedFinishBitCode : BitRAM.Code .standard 12 :=
  .seq (.op (.load 9 3))
  (.seq (.op (.bin .shiftRight 9 9 5))
  (.seq (.op (.bin .and 9 9 7))
  (.seq (.op (.bin .and 7 2 7))
  (.seq (.op (.bin .xor 9 9 7))
  (.seq (.op (.bin .shiftLeft 9 9 5))
  (.seq (.op (.load 7 3))
  (.seq (.op (.bin .xor 9 7 9))
  (.seq (.op (.store 3 9))
  (.seq (.op (.const 5 0))
  (.seq (.op (.load 9 4))
  (.seq (.op (.bin .shiftRight 9 9 5))
  (.seq (.op (.bin .and 9 9 8))
  (.seq (.op (.bin .shiftRight 7 2 6))
  (.seq (.op (.bin .and 7 7 8))
  (.seq (.op (.bin .xor 9 9 7))
  (.seq (.op (.bin .shiftLeft 9 9 5))
  (.seq (.op (.load 7 4))
  (.seq (.op (.bin .xor 9 7 9))
        (.op (.store 4 9))))))))))))))))))))

/-- Parameter-free `BitRAM.Code .standard 12` program writing `val` (`r2`) at `idx` (`r1`) of the
bit-packed array at `base` (`r0`) with entry width `k` (`r9`). -/
@[expose] def writePackedRegCode : BitRAM.Code .standard 12 :=
  .seq addrSetupRegCode writePackedFinishBitCode

/-- `addrSetupRegCode` executes in at most `32` instructions, preserving `r0, r1, r2, r9, mem,
bitSize` and computing the word addresses, bit offset, widths, and bitmasks into `r3..r8`. -/
theorem addrSetupRegCode_exec {base N k w idx : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hbase : x.regs 0 = base) (hr1 : x.regs 1 = idx) (hr9 : x.regs 9 = k)
    (hfit_idx : Fits w idx)
    (hfit_end : Fits w (base + packedWords N k w)) :
    BitRAM.DemonicExecWithin w addrSetupRegCode x
      (fun y =>
        y.mem = x.mem ∧
        y.bitSize = x.bitSize ∧
        y.regs 0 = base ∧
        y.regs 1 = idx ∧
        y.regs 2 = x.regs 2 ∧
        y.regs 3 = base + wordOffset k w idx ∧
        y.regs 4 = base + wordOffset k w idx + 1 ∧
        y.regs 5 = bitOffset k w idx ∧
        y.regs 6 = lowWidth k w idx ∧
        y.regs 7 = 2 ^ lowWidth k w idx - 1 ∧
        y.regs 8 = 2 ^ highWidth k w idx - 1 ∧
        y.regs 9 = k) 32 := by
  have hfit_w : Fits w w := fits_self w
  have hfit_k : Fits w k := hfit_w.of_le hkw
  have hlt1 : wordOffset k w idx + 1 < packedWords N k w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have hfit_addr1 : Fits w (base + wordOffset k w idx + 1) :=
    hfit_end.of_le (by omega)
  have hfit_addr0 : Fits w (base + wordOffset k w idx) :=
    hfit_addr1.of_le (by omega)
  have hfit_wOff : Fits w (wordOffset k w idx) := hfit_addr0.of_le (by omega)
  have hfit_one : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  have hfit_div_w : Fits w (idx / w) := hfit_idx.of_le (Nat.div_le_self idx w)
  have hfit_div_mul : Fits w ((idx / w) * k) :=
    hfit_wOff.of_le (Nat.le_add_right _ _)
  have hfit_mod_w : Fits w (idx % w) := hfit_w.of_le (Nat.mod_lt idx hw).le
  have hfit_mod_mul : Fits w ((idx % w) * k) := mod_mul_lt_two_pow hw hkw idx
  have hfit_mod_div : Fits w (((idx % w) * k) / w) :=
    hfit_mod_mul.of_le (Nat.div_le_self _ _)
  have hbOff_lt : bitOffset k w idx < w := bitOffset_lt hw
  have hfit_bOff : Fits w (bitOffset k w idx) := hfit_w.of_le hbOff_lt.le
  have hfit_sub_b : Fits w (w - bitOffset k w idx) := hfit_w.of_le (by omega)
  have hk0_le_k : lowWidth k w idx ≤ k := Nat.min_le_left _ _
  have hk0_le_w : lowWidth k w idx ≤ w := hk0_le_k.trans hkw
  have hk1_le_k : highWidth k w idx ≤ k := by unfold highWidth; omega
  have hk1_le_w : highWidth k w idx ≤ w := hk1_le_k.trans hkw
  have hfit_k1 : Fits w (highWidth k w idx) := hfit_k.of_le hk1_le_k
  refine DemonicExecWithin.step_width (T := 31) ?_
  set s1 := x.set 8 w
  refine step_dExec_bin (v := idx / w) (T := 30)
    (by simp +decide [s1, BitRAM.Data.set, BinOp.eval, hr1]) hfit_div_w ?_
  set s2 := s1.set 3 (idx / w)
  refine step_dExec_bin (v := (idx / w) * k) (T := 29)
    (by simp +decide [s2, s1, BitRAM.Data.set, BinOp.eval, hr9]) hfit_div_mul ?_
  set s3 := s2.set 3 ((idx / w) * k)
  refine step_dExec_bin (v := idx % w) (T := 28)
    (by simp +decide [s3, s2, s1, BitRAM.Data.set, BinOp.eval, hr1]) hfit_mod_w ?_
  set s4 := s3.set 5 (idx % w)
  refine step_dExec_bin (v := (idx % w) * k) (T := 27)
    (by simp +decide [s4, s3, s2, s1, BitRAM.Data.set, BinOp.eval, hr9]) hfit_mod_mul ?_
  set s5 := s4.set 5 ((idx % w) * k)
  refine step_dExec_bin (v := ((idx % w) * k) / w) (T := 26)
    (by simp +decide [s5, s4, s3, s2, s1, BitRAM.Data.set, BinOp.eval]) hfit_mod_div ?_
  set s6 := s5.set 4 (((idx % w) * k) / w)
  refine step_dExec_bin (v := wordOffset k w idx) (T := 25)
    (by simp +decide [s6, s5, s4, s3, BitRAM.Data.set, BinOp.eval, wordOffset]) hfit_wOff ?_
  set s7 := s6.set 3 (wordOffset k w idx)
  refine step_dExec_bin (v := bitOffset k w idx) (T := 24)
    (by simp +decide [s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set, BinOp.eval, bitOffset])
    hfit_bOff ?_
  set s8 := s7.set 5 (bitOffset k w idx)
  refine step_dExec_bin (v := base + wordOffset k w idx) (T := 23)
    (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set, BinOp.eval, hbase])
    hfit_addr0 ?_
  set s9 := s8.set 3 (base + wordOffset k w idx)
  refine DemonicExecWithin.step_const (T := 22) hfit_one ?_
  set s10 := s9.set 4 1
  refine step_dExec_bin (v := base + wordOffset k w idx + 1) (T := 21)
    (by simp +decide [s10, s9, BitRAM.Data.set, BinOp.eval]) hfit_addr1 ?_
  set s11 := s10.set 4 (base + wordOffset k w idx + 1)
  refine step_dExec_bin (v := w - bitOffset k w idx) (T := 20)
    (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set, BinOp.eval])
    hfit_sub_b ?_
  set s12 := s11.set 6 (w - bitOffset k w idx)
  have hs12_0 : s12.regs 0 = base := by
    simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set, hbase]
  have hs12_1 : s12.regs 1 = idx := by
    simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set, hr1]
  have hs12_2 : s12.regs 2 = x.regs 2 := by
    simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set]
  have hs12_3 : s12.regs 3 = base + wordOffset k w idx := by
    simp +decide [s12, s11, s10, s9, BitRAM.Data.set]
  have hs12_4 : s12.regs 4 = base + wordOffset k w idx + 1 := by
    simp +decide [s12, s11, BitRAM.Data.set]
  have hs12_5 : s12.regs 5 = bitOffset k w idx := by
    simp +decide [s12, s11, s10, s9, s8, BitRAM.Data.set]
  have hs12_6 : s12.regs 6 = w - bitOffset k w idx := by
    simp +decide [s12, BitRAM.Data.set]
  have hs12_9 : s12.regs 9 = k := by
    simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, BitRAM.Data.set, hr9]
  have e_min :
      BitRAM.DemonicExecWithin w
        (.branch (.lt 9 6) (.op (.copy 6 9)) (.op (.copy 6 6)) : BitRAM.Code .standard 12)
        s12 (fun y => y = s12.set 6 (lowWidth k w idx)) 3 := by
    by_cases hlt_k : k < w - bitOffset k w idx
    · have hc : BitRAM.CondHolds (.lt 9 6) s12 := by
        change s12.regs 9 < s12.regs 6
        rw [hs12_9, hs12_6]
        exact hlt_k
      have hmin : lowWidth k w idx = k := Nat.min_eq_left hlt_k.le
      refine .branch_pos (T₀ := 1) hc (DemonicExecWithin.copy ?_) (by omega)
      rw [hmin, hs12_9]
    · have hc : ¬BitRAM.CondHolds (.lt 9 6) s12 := by
        change ¬(s12.regs 9 < s12.regs 6)
        rw [hs12_9, hs12_6]
        exact hlt_k
      have hmin : lowWidth k w idx = w - bitOffset k w idx :=
        Nat.min_eq_right (not_lt.mp hlt_k)
      refine .branch_neg (T₀ := 1) hc (DemonicExecWithin.copy ?_) (by omega)
      rw [hmin, hs12_6]
  refine .seq (T₁ := 3) (T₂ := 17) e_min (fun s13 hs13 => ?_) (by omega)
  subst hs13
  set s13 := s12.set 6 (lowWidth k w idx)
  refine step_dExec_bin (v := highWidth k w idx) (T := 16)
    (by simp +decide [s13, BitRAM.Data.set, BinOp.eval, hs12_9, highWidth]) hfit_k1 ?_
  set s14 := s13.set 8 (highWidth k w idx)
  have hs14_6 : s14.regs 6 ≤ w := by simp +decide [s14, s13, BitRAM.Data.set, hk0_le_w]
  refine .seq (T₁ := 8) (T₂ := 8)
    (maskOfWidthCode_exec hw 6 7 10 11 (by decide) (by decide) (by decide) (by decide) (by decide)
      hs14_6)
    (fun s15 hs15 => ?_) (by omega)
  rcases hs15 with ⟨hs15_7, hs15_other, hs15_mem, hs15_sz⟩
  have hs15_8_eq : s15.regs 8 = highWidth k w idx := by
    rw [hs15_other 8 (by decide) (by decide) (by decide)]
    simp +decide [s14, BitRAM.Data.set]
  have hs15_8_le : s15.regs 8 ≤ w := by
    rw [hs15_8_eq]
    exact hk1_le_w
  refine (maskOfWidthCode_exec hw 8 8 10 11 (by decide) (by decide) (by decide) (by decide)
    (by decide) hs15_8_le).mono (fun y hy => ?_) (by omega)
  rcases hy with ⟨hy8, hy_other, hy_mem, hy_sz⟩
  have hr_chain (i : Fin 12) (h8 : i ≠ 8) (h7 : i ≠ 7) (h10 : i ≠ 10) (h11 : i ≠ 11) :
      y.regs i = s14.regs i := by
    rw [hy_other i h8 h10 h11, hs15_other i h7 h10 h11]
  refine ⟨hy_mem.trans hs15_mem, hy_sz.trans hs15_sz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr_chain 0 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_0]
  · rw [hr_chain 1 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_1]
  · rw [hr_chain 2 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_2]
  · rw [hr_chain 3 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_3]
  · rw [hr_chain 4 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_4]
  · rw [hr_chain 5 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_5]
  · rw [hr_chain 6 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set]
  · rw [hy_other 7 (by decide) (by decide) (by decide), hs15_7]
    simp +decide [s14, s13, BitRAM.Data.set]
  · rw [hy8, hs15_8_eq]
  · rw [hr_chain 9 (by decide) (by decide) (by decide) (by decide)]
    simp +decide [s14, s13, BitRAM.Data.set, hs12_9]

set_option linter.unusedSimpArgs false in
/-- `readPackedRegCode` executes in at most `41` instructions and sets `r2` to
`BitPackedArray.readPacked base k w x.mem idx`, preserving `r0 = base`, `r1 = idx`, `mem`,
`bitSize`, and `Data.WellFormed w`. -/
theorem readPackedRegCode_exec {base N k w idx : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.WellFormed w)
    (hbase : x.regs 0 = base) (hr1 : x.regs 1 = idx) (hr9 : x.regs 9 = k)
    (hfit_end : Fits w (base + packedWords N k w))
    (hadm_end : base + packedWords N k w ≤ x.wordSize w) :
    BitRAM.DemonicExecWithin w readPackedRegCode x
      (fun y =>
        y.mem = x.mem ∧
        y.bitSize = x.bitSize ∧
        y.regs 0 = base ∧
        y.regs 1 = idx ∧
        y.regs 2 = readPacked base k w x.mem idx ∧
        y.WellFormed w) 41 := by
  have hfit_idx : Fits w idx := hr1 ▸ hx.regs_fits 1
  have hlt1 : wordOffset k w idx + 1 < packedWords N k w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have hadm0 : base + wordOffset k w idx < x.wordSize w := by omega
  have hadm1 : base + wordOffset k w idx + 1 < x.wordSize w := by omega
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set addr₀ := base + wOff
  set addr₁ := base + wOff + 1
  set low := (x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1)
  set high := (x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1)
  have hm0_fit : Fits w (x.mem addr₀) := hx.mem_wf.mem_fits _
  have hm1_fit : Fits w (x.mem addr₁) := hx.mem_wf.mem_fits _
  have hshr0_fit : Fits w (x.mem addr₀ >>> bOff) := hm0_fit.of_le (Nat.shiftRight_le _ _)
  have hlow_lt : low < 2 ^ k₀ := by
    dsimp only [low]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk0_le_w : k₀ ≤ w := (Nat.min_le_left _ _).trans hkw
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hlow_fit : Fits w low :=
    lt_of_lt_of_le hlow_lt (Nat.pow_le_pow_right Nat.two_pos hk0_le_w)
  have hzero_fit : Fits w 0 := fits_zero w
  have hshr1_fit : Fits w (x.mem addr₁ >>> 0) := hm1_fit
  have hhigh_lt : high < 2 ^ k₁ := by
    dsimp only [high]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hhigh_fit : Fits w high :=
    lt_of_lt_of_le hhigh_lt (Nat.pow_le_pow_right Nat.two_pos hk1_le_w)
  have hshl_fit : Fits w (high <<< k₀) := by
    refine shiftLeft_lt_two_pow_of_lt hhigh_lt ?_
    have := lowWidth_add_highWidth k w idx
    omega
  have hread_fit : Fits w (readPacked base k w x.mem idx) :=
    (readPacked_lt base k w x.mem idx).trans_le (Nat.pow_le_pow_right Nat.two_pos hkw)
  have hbody :
      BitRAM.DemonicExecWithin w readPackedRegCode x
        (fun y =>
          y.mem = x.mem ∧
          y.bitSize = x.bitSize ∧
          y.regs 0 = base ∧
          y.regs 1 = idx ∧
          y.regs 2 = readPacked base k w x.mem idx) 41 := by
    refine .seq (T₁ := 32) (T₂ := 9)
      (addrSetupRegCode_exec hw hkw hidx hbase hr1 hr9 hfit_idx hfit_end)
      (fun x₁ hx₁ => ?_) (by omega)
    rcases hx₁ with ⟨hmem, hsz, hr0_1, hr1_1, _, hr3, hr4, hr5, hr6, hr7, hr8, _⟩
    have hw_sz : x₁.wordSize w = x.wordSize w := by
      unfold BitRAM.Data.wordSize
      rw [hsz]
    refine step_dExec_load (v := x.mem addr₀) (T := 8)
      (by rw [hr3, hw_sz]; exact hadm0) (by rw [hmem, hr3]) ?_
    set r1 := x₁.set 9 (x.mem addr₀)
    refine step_dExec_bin (v := x.mem addr₀ >>> bOff) (T := 7)
      (by simp +decide [r1, BitRAM.Data.set, BinOp.eval, hr5, bOff]) hshr0_fit ?_
    set r2 := r1.set 9 (x.mem addr₀ >>> bOff)
    refine step_dExec_bin (v := low) (T := 6)
      (by simp +decide [r2, r1, BitRAM.Data.set, BinOp.eval, hr7, low, k₀]) hlow_fit ?_
    set r3 := r2.set 9 low
    refine step_dExec_load (v := x.mem addr₁) (T := 5)
      (by
        simp only [r3, r2, r1, BitRAM.Data.set_wordSize, BitRAM.Data.set_regs,
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 9), hw_sz, hr4]
        exact hadm1)
      (by simp +decide [r3, r2, r1, BitRAM.Data.set, hmem, hr4, addr₁, wOff]) ?_
    set r4 := r3.set 2 (x.mem addr₁)
    refine DemonicExecWithin.step_const (T := 4) hzero_fit ?_
    set r5 := r4.set 7 0
    refine step_dExec_bin (v := x.mem addr₁ >>> 0) (T := 3)
      (by simp +decide [r5, r4, BitRAM.Data.set, BinOp.eval]) hshr1_fit ?_
    set r6 := r5.set 2 (x.mem addr₁ >>> 0)
    refine step_dExec_bin (v := high) (T := 2)
      (by simp +decide [r6, r5, r4, r3, r2, r1, BitRAM.Data.set, BinOp.eval, hr8, high, k₁])
      hhigh_fit ?_
    set r7 := r6.set 2 high
    refine step_dExec_bin (v := high <<< k₀) (T := 1)
      (by simp +decide [r7, r6, r5, r4, r3, r2, r1, BitRAM.Data.set, BinOp.eval, hr6, k₀])
      hshl_fit ?_
    set r8 := r7.set 2 (high <<< k₀)
    refine dExec_bin (v := readPacked base k w x.mem idx)
      (by simp +decide [r8, r7, r6, r5, r4, r3, BitRAM.Data.set, BinOp.eval, readPacked, addr₀,
            addr₁, wOff, bOff, k₀, k₁, low, high]) hread_fit ?_
    refine ⟨hmem, hsz, ?_, ?_, ?_⟩
    · simp +decide [r8, r7, r6, r5, r4, r3, r2, r1, BitRAM.Data.set, hr0_1]
    · simp +decide [r8, r7, r6, r5, r4, r3, r2, r1, BitRAM.Data.set, hr1_1]
    · simp +decide [BitRAM.Data.set]
  refine (dExec_preserve_regsAndMemFit ⟨hx.regs_fits, hx.mem_wf.mem_fits⟩ hbody).mono
    (fun y ⟨⟨hmem, hsz, hy0, hy1, hy2⟩, hfit⟩ => ⟨hmem, hsz, hy0, hy1, hy2, hfit.1, ?_⟩) le_rfl
  have hst : y.toBitMemoryState = x.toBitMemoryState := by
    ext a
    · exact congrFun hmem a
    · exact hsz
  rw [hst]
  exact hx.mem_wf

set_option linter.unusedSimpArgs false in
/-- `writePackedRegCode` executes in at most `52` instructions and updates `mem` to
`BitPackedArray.writePacked base k w x.mem idx val`, preserving `r0 = base`, `r1 = idx`,
`r2 = val`, `bitSize`, and `Data.WellFormed w` whenever `(base + packedWords N k w) * w ≤ x.bitSize`
(so all modified words lie strictly inside `x.bitSize`). -/
theorem writePackedRegCode_exec {base N k w idx val : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.WellFormed w)
    (hbase : x.regs 0 = base) (hr1 : x.regs 1 = idx) (hr2 : x.regs 2 = val) (hr9 : x.regs 9 = k)
    (hfit_end : Fits w (base + packedWords N k w))
    (hadm_bits : (base + packedWords N k w) * w ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w writePackedRegCode x
      (fun y =>
        y.mem = writePacked base k w x.mem idx val ∧
        y.bitSize = x.bitSize ∧
        y.regs 0 = base ∧
        y.regs 1 = idx ∧
        y.regs 2 = val ∧
        y.WellFormed w) 52 := by
  have hfit_idx : Fits w idx := hr1 ▸ hx.regs_fits 1
  have hfit_val : Fits w val := hr2 ▸ hx.regs_fits 2
  have hlt1 : wordOffset k w idx + 1 < packedWords N k w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
  have hadm_end : base + packedWords N k w ≤ x.wordSize w :=
    Nat.le_of_mul_le_mul_right (hadm_bits.trans hcov) hw
  have hadm0 : base + wordOffset k w idx < x.wordSize w := by omega
  have hadm1 : base + wordOffset k w idx + 1 < x.wordSize w := by omega
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set addr₀ := base + wOff
  set addr₁ := base + wOff + 1
  set old₀ := (x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update x.mem addr₀ (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ addr₁ >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hm0_fit : Fits w (x.mem addr₀) := hx.mem_wf.mem_fits _
  have hshr0_fit : Fits w (x.mem addr₀ >>> bOff) := hm0_fit.of_le (Nat.shiftRight_le _ _)
  have hold0_lt : old₀ < 2 ^ k₀ := by
    dsimp only [old₀]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hval0_lt : val₀ < 2 ^ k₀ := by
    dsimp only [val₀]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk0_le_w : k₀ ≤ w := (Nat.min_le_left _ _).trans hkw
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hold0_fit : Fits w old₀ :=
    lt_of_lt_of_le hold0_lt (Nat.pow_le_pow_right Nat.two_pos hk0_le_w)
  have hval0_fit : Fits w val₀ :=
    lt_of_lt_of_le hval0_lt (Nat.pow_le_pow_right Nat.two_pos hk0_le_w)
  have hδ0_lt : old₀ ^^^ val₀ < 2 ^ k₀ := Nat.xor_lt_two_pow hold0_lt hval0_lt
  have hδ0_fit : Fits w (old₀ ^^^ val₀) := Nat.xor_lt_two_pow hold0_fit hval0_fit
  have hsh0_fit : Fits w ((old₀ ^^^ val₀) <<< bOff) := by
    refine shiftLeft_lt_two_pow_of_lt hδ0_lt ?_
    have := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
    omega
  have hnew0_fit : Fits w (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff)) :=
    Nat.xor_lt_two_pow hm0_fit hsh0_fit
  have hm1_fit : Fits w (mem₁ addr₁) := by
    dsimp only [mem₁]
    rw [Function.update_of_ne (by omega)]
    exact hx.mem_wf.mem_fits addr₁
  have hzero_fit : Fits w 0 := fits_zero w
  have hshr1_fit : Fits w (mem₁ addr₁ >>> 0) := hm1_fit
  have hold1_lt : old₁ < 2 ^ k₁ := by
    dsimp only [old₁]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hval_shr_fit : Fits w (val >>> k₀) := hfit_val.of_le (Nat.shiftRight_le _ _)
  have hval1_lt : val₁ < 2 ^ k₁ := by
    dsimp only [val₁]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hold1_fit : Fits w old₁ :=
    lt_of_lt_of_le hold1_lt (Nat.pow_le_pow_right Nat.two_pos hk1_le_w)
  have hval1_fit : Fits w val₁ :=
    lt_of_lt_of_le hval1_lt (Nat.pow_le_pow_right Nat.two_pos hk1_le_w)
  have hδ1_fit : Fits w (old₁ ^^^ val₁) := Nat.xor_lt_two_pow hold1_fit hval1_fit
  have hsh1_fit : Fits w ((old₁ ^^^ val₁) <<< 0) := hδ1_fit
  have hnew1_fit : Fits w (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0)) :=
    Nat.xor_lt_two_pow hm1_fit hsh1_fit
  have hbody :
      BitRAM.DemonicExecWithin w writePackedRegCode x
        (fun y =>
          y.mem = writePacked base k w x.mem idx val ∧
          y.bitSize = x.bitSize ∧
          y.regs 0 = base ∧
          y.regs 1 = idx ∧
          y.regs 2 = val) 52 := by
    refine .seq (T₁ := 32) (T₂ := 20)
      (addrSetupRegCode_exec hw hkw hidx hbase hr1 hr9 hfit_idx hfit_end)
      (fun x₁ hx₁ => ?_) (by omega)
    rcases hx₁ with ⟨hmem, hsz, hr0_1, hr1_1, hr2_1, hr3, hr4, hr5, hr6, hr7, hr8, _⟩
    rw [hr2] at hr2_1
    have hw_sz : x₁.wordSize w = x.wordSize w := by
      unfold BitRAM.Data.wordSize
      rw [hsz]
    refine step_dExec_load (v := x.mem addr₀) (T := 19)
      (by rw [hr3, hw_sz]; exact hadm0) (by rw [hmem, hr3]) ?_
    set w1 := x₁.set 9 (x.mem addr₀)
    refine step_dExec_bin (v := x.mem addr₀ >>> bOff) (T := 18)
      (by simp +decide [w1, BitRAM.Data.set, BinOp.eval, hr5, bOff]) hshr0_fit ?_
    set w2 := w1.set 9 (x.mem addr₀ >>> bOff)
    refine step_dExec_bin (v := old₀) (T := 17)
      (by simp +decide [w2, w1, BitRAM.Data.set, BinOp.eval, hr7, old₀, k₀]) hold0_fit ?_
    set w3 := w2.set 9 old₀
    refine step_dExec_bin (v := val₀) (T := 16)
      (by simp +decide [w3, w2, w1, BitRAM.Data.set, BinOp.eval, hr2_1, hr7, val₀, k₀]) hval0_fit ?_
    set w4 := w3.set 7 val₀
    refine step_dExec_bin (v := old₀ ^^^ val₀) (T := 15)
      (by simp +decide [w4, w3, BitRAM.Data.set, BinOp.eval]) hδ0_fit ?_
    set w5 := w4.set 9 (old₀ ^^^ val₀)
    refine step_dExec_bin (v := (old₀ ^^^ val₀) <<< bOff) (T := 14)
      (by simp +decide [w5, w4, w3, w2, w1, BitRAM.Data.set, BinOp.eval, hr5, bOff]) hsh0_fit ?_
    set w6 := w5.set 9 ((old₀ ^^^ val₀) <<< bOff)
    refine step_dExec_load (v := x.mem addr₀) (T := 13)
      (by
        simp only [w6, w5, w4, w3, w2, w1, BitRAM.Data.set_wordSize, BitRAM.Data.set_regs,
          Function.update_of_ne (by decide : (3 : Fin 12) ≠ 9),
          Function.update_of_ne (by decide : (3 : Fin 12) ≠ 7), hw_sz, hr3]
        exact hadm0)
      (by simp +decide [w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hmem, hr3, addr₀, wOff]) ?_
    set w7 := w6.set 7 (x.mem addr₀)
    refine step_dExec_bin (v := x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff)) (T := 12)
      (by simp +decide [w7, w6, BitRAM.Data.set, BinOp.eval]) hnew0_fit ?_
    set w8 := w7.set 9 (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
    refine step_dExec_store (addr := addr₀) (v := x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
      (T := 11)
      (by
        simp only [w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set_wordSize, BitRAM.Data.set_regs,
          Function.update_of_ne (by decide : (3 : Fin 12) ≠ 9),
          Function.update_of_ne (by decide : (3 : Fin 12) ≠ 7), hw_sz, hr3]
        exact hadm0)
      (by simp +decide [w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr3, addr₀, wOff])
      (by simp +decide [w8, BitRAM.Data.set]) ?_
    set w9 := w8.write addr₀ (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
    have hw9_mem : w9.mem = mem₁ := by
      change Function.update x₁.mem addr₀ (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff)) = mem₁
      rw [hmem]
    have hw9_0 : w9.regs 0 = base := by
      simp +decide [w9, BitRAM.Data.write, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr0_1]
    have hw9_1 : w9.regs 1 = idx := by
      simp +decide [w9, BitRAM.Data.write, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr1_1]
    have hw9_2 : w9.regs 2 = val := by
      simp +decide [w9, BitRAM.Data.write, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr2_1]
    have hw9_4 : w9.regs 4 = addr₁ := by
      simp +decide [w9, BitRAM.Data.write, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr4,
        addr₁, wOff]
    have hw9_6 : w9.regs 6 = k₀ := by
      simp +decide [w9, BitRAM.Data.write, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr6, k₀]
    have hw9_8 : w9.regs 8 = 2 ^ k₁ - 1 := by
      simp +decide [w9, BitRAM.Data.write, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set, hr8, k₁]
    refine DemonicExecWithin.step_const (T := 10) hzero_fit ?_
    set w10 := w9.set 5 0
    refine step_dExec_load (v := mem₁ addr₁) (T := 9)
      (by
        simp only [w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, BitRAM.Data.set_wordSize,
          BitRAM.Data.write_wordSize, BitRAM.Data.set_regs, BitRAM.Data.write_regs,
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 5),
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 9),
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 7), hw_sz, hr4]
        exact hadm1)
      (by simp +decide [w10, BitRAM.Data.set, hw9_4, hw9_mem]) ?_
    set w11 := w10.set 9 (mem₁ addr₁)
    refine step_dExec_bin (v := mem₁ addr₁ >>> 0) (T := 8)
      (by simp +decide [w11, w10, BitRAM.Data.set, BinOp.eval]) hshr1_fit ?_
    set w12 := w11.set 9 (mem₁ addr₁ >>> 0)
    refine step_dExec_bin (v := old₁) (T := 7)
      (by simp +decide [w12, w11, w10, BitRAM.Data.set, BinOp.eval, hw9_8, old₁]) hold1_fit ?_
    set w13 := w12.set 9 old₁
    refine step_dExec_bin (v := val >>> k₀) (T := 6)
      (by simp +decide [w13, w12, w11, w10, BitRAM.Data.set, BinOp.eval, hw9_2, hw9_6])
      hval_shr_fit ?_
    set w14 := w13.set 7 (val >>> k₀)
    refine step_dExec_bin (v := val₁) (T := 5)
      (by simp +decide [w14, w13, w12, w11, w10, BitRAM.Data.set, BinOp.eval, hw9_8, val₁])
      hval1_fit ?_
    set w15 := w14.set 7 val₁
    refine step_dExec_bin (v := old₁ ^^^ val₁) (T := 4)
      (by simp +decide [w15, w14, w13, BitRAM.Data.set, BinOp.eval]) hδ1_fit ?_
    set w16 := w15.set 9 (old₁ ^^^ val₁)
    refine step_dExec_bin (v := (old₁ ^^^ val₁) <<< 0) (T := 3)
      (by simp +decide [w16, w15, w14, w13, w12, w11, w10, BitRAM.Data.set, BinOp.eval])
      hsh1_fit ?_
    set w17 := w16.set 9 ((old₁ ^^^ val₁) <<< 0)
    refine step_dExec_load (v := mem₁ addr₁) (T := 2)
      (by
        simp only [w17, w16, w15, w14, w13, w12, w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1,
          BitRAM.Data.set_wordSize, BitRAM.Data.write_wordSize, BitRAM.Data.set_regs,
          BitRAM.Data.write_regs,
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 5),
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 9),
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 7), hw_sz, hr4]
        exact hadm1)
      (by simp +decide [w17, w16, w15, w14, w13, w12, w11, w10, BitRAM.Data.set, hw9_4, hw9_mem]) ?_
    set w18 := w17.set 7 (mem₁ addr₁)
    refine step_dExec_bin (v := mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0)) (T := 1)
      (by simp +decide [w18, w17, BitRAM.Data.set, BinOp.eval]) hnew1_fit ?_
    set w19 := w18.set 9 (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0))
    refine dExec_store (addr := addr₁) (v := mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0))
      (by
        simp only [w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, w9, w8, w7, w6, w5, w4, w3,
          w2, w1, BitRAM.Data.set_wordSize, BitRAM.Data.write_wordSize, BitRAM.Data.set_regs,
          BitRAM.Data.write_regs,
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 5),
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 9),
          Function.update_of_ne (by decide : (4 : Fin 12) ≠ 7), hw_sz, hr4]
        exact hadm1)
      (by simp +decide [w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, BitRAM.Data.set, hw9_4])
      (by simp +decide [w19, BitRAM.Data.set]) ?_
    refine ⟨?_, hsz, ?_, ?_, ?_⟩
    · change Function.update w19.mem addr₁ (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0)) =
        writePacked base k w x.mem idx val
      have hw19_mem : w19.mem = mem₁ := hw9_mem
      rw [hw19_mem]
      rfl
    · simp +decide [w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, BitRAM.Data.set,
        BitRAM.Data.write, hw9_0]
    · simp +decide [w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, BitRAM.Data.set,
        BitRAM.Data.write, hw9_1]
    · simp +decide [w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, BitRAM.Data.set,
        BitRAM.Data.write, hw9_2]
  refine (dExec_preserve_regsAndMemFit ⟨hx.regs_fits, hx.mem_wf.mem_fits⟩ hbody).mono
    (fun y ⟨⟨hmem, hsz, hy0, hy1, hy2⟩, hfit⟩ =>
      ⟨hmem, hsz, hy0, hy1, hy2, hfit.1, hfit.2,
        by change Fits w y.bitSize; rw [hsz]; exact hx.mem_wf.bitSize_fits, ?_⟩) le_rfl
  intro i hi
  have hi' : x.bitSize ≤ i := by
    change y.bitSize ≤ i at hi
    omega
  have hword_ge : base + packedWords N k w ≤ i / w := by
    have hmul : (base + packedWords N k w) * w ≤ i := hadm_bits.trans hi'
    exact (Nat.le_div_iff_mul_le hw).mpr hmul
  have hout : ¬(base ≤ i / w ∧ i / w < base + packedWords N k w) := by omega
  have hy_get : y.toBitMemoryState.getBit w i = x.toBitMemoryState.getBit w i := by
    change (y.mem (0 + i / w)).testBit (i % w) = (x.mem (0 + i / w)).testBit (i % w)
    rw [hmem, Nat.zero_add, writePacked_outside hw x.mem hidx val hout]
  rw [hy_get]
  exact hx.mem_wf.zero_above i hi'

/-! ## Section 3: Parameter-free binary logarithms (`log2BitCode`, `clog2BitCode`) -/

/-- One iteration of the floor-`log₂` loop on `BitRAM.Data 12` (`r0 = rem`, `r1 = acc`, `r2 = 1`):
shifts `rem` right by `1` (`rem / 2`) and increments `acc`. -/
@[expose] def log2BodyBitCode : BitRAM.Code .standard 12 :=
  .seq (.op (.bin .shiftRight 0 0 2))
       (.op (.bin .add 1 1 2))

/-- Floor-`log₂` loop `while 1 < rem do [ rem ← rem >>> 1; acc ← acc + 1 ]` on `BitRAM.Data 12`. -/
@[expose] def log2LoopBitCode : BitRAM.Code .standard 12 :=
  .loop (.lt 2 0) log2BodyBitCode

/-- Closed-form final state of `log2LoopBitCode` starting from `rem` in `r0` and `acc` in `r1`. -/
@[expose] def log2LoopBitData (rem acc : ℕ) (x : BitRAM.Data 12) : BitRAM.Data 12 :=
  (x.set 0 (if rem = 0 then 0 else 1)).set 1 (acc + Nat.log 2 rem)

/-- `log2LoopBitCode` executes in `4 * Nat.log 2 rem + 2` instructions on `BitRAM.Data 12`. -/
theorem log2LoopBitCode_exec {w : ℕ} (rem : ℕ) {acc : ℕ} {x : BitRAM.Data 12}
    (hrem : x.regs 0 = rem) (hacc : x.regs 1 = acc) (hone : x.regs 2 = 1)
    (hfit_rem : Fits w rem) (hfit_acc : Fits w (acc + Nat.log 2 rem)) :
    BitRAM.DemonicExecWithin w log2LoopBitCode x
      (fun y => y = log2LoopBitData rem acc x) (4 * Nat.log 2 rem + 2) := by
  induction rem using Nat.strong_induction_on generalizing acc x with
  | _ rem ih =>
    by_cases hlt : 1 < rem
    · have hc : BitRAM.CondHolds (.lt 2 0) x := by
        change x.regs 2 < x.regs 0
        rw [hone, hrem]
        exact hlt
      have hshr : rem >>> 1 = rem / 2 := Nat.shiftRight_eq_div_pow rem 1
      have hlog : Nat.log 2 rem = Nat.log 2 (rem / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by decide) (by omega)
      have hfit_div : Fits w (rem / 2) := hfit_rem.of_le (Nat.div_le_self rem 2)
      have hfit_acc1 : Fits w (acc + 1) := hfit_acc.of_le (by omega)
      set d1 := x.set 0 (rem / 2)
      set d2 := d1.set 1 (acc + 1)
      have hbody : BitRAM.DemonicExecWithin w log2BodyBitCode x (fun y => y = d2) 2 := by
        refine step_dExec_bin (v := rem / 2) (T := 1)
          (by simp [BinOp.eval, hrem, hone, hshr]) hfit_div ?_
        exact dExec_bin (v := acc + 1)
          (by simp +decide [BitRAM.Data.set, BinOp.eval, hacc, hone]) hfit_acc1 rfl
      have hdiv_lt : rem / 2 < rem := Nat.div_lt_self (by omega) (by decide)
      have hrec := ih (rem / 2) hdiv_lt (acc := acc + 1) (x := d2)
        (by simp +decide [d2, d1, BitRAM.Data.set])
        (by simp +decide [d2, BitRAM.Data.set])
        (by simp +decide [d2, d1, BitRAM.Data.set, hone])
        hfit_div
        (by rwa [show acc + 1 + Nat.log 2 (rem / 2) = acc + Nat.log 2 rem by omega])
      have hd : log2LoopBitData (rem / 2) (acc + 1) d2 = log2LoopBitData rem acc x := by
        have hdiv_ne : rem / 2 ≠ 0 := by omega
        have hrem_ne : rem ≠ 0 := by omega
        ext i
        · by_cases hi1 : i = 1
          · subst hi1
            simp +decide [log2LoopBitData, d2, d1, BitRAM.Data.set]
            omega
          · by_cases hi0 : i = 0
            · subst hi0
              simp +decide [log2LoopBitData, d2, d1, BitRAM.Data.set, hdiv_ne, hrem_ne]
            · simp [log2LoopBitData, d2, d1, BitRAM.Data.set, hi1, hi0]
        · rfl
        · rfl
      refine .loop_iter (T₁ := 2) (T₂ := 4 * Nat.log 2 (rem / 2) + 2) hc hbody
        (fun y hy => ?_) (by omega)
      subst hy
      exact hrec.mono (fun z hz => hz.trans hd) le_rfl
    · have hc : ¬BitRAM.CondHolds (.lt 2 0) x := by
        change ¬(x.regs 2 < x.regs 0)
        rw [hone, hrem]
        exact hlt
      have hlog0 : Nat.log 2 rem = 0 := Nat.log_of_lt (by omega)
      have hd : x = log2LoopBitData rem acc x := by
        have hrem_eq : (if rem = 0 then 0 else 1) = rem := by split_ifs <;> omega
        ext i
        · by_cases hi1 : i = 1
          · subst hi1; simp +decide [log2LoopBitData, BitRAM.Data.set, hlog0, hacc]
          · by_cases hi0 : i = 0
            · subst hi0; simp +decide [log2LoopBitData, BitRAM.Data.set, hrem_eq, hrem]
            · simp [log2LoopBitData, BitRAM.Data.set, hi1, hi0]
        · rfl
        · rfl
      exact .loop_exit hc hd (by omega)

/-- Parameter-free `BitRAM.Code .standard 12` program computing `Nat.log 2 (x.regs 0)` into `r1`
using `r0, r1, r2` and preserving `r3..r11`, `mem`, and `bitSize`. -/
@[expose] def log2BitCode : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 0))
    (.seq (.op (.const 2 1))
      log2LoopBitCode)

theorem log_two_lt_of_fits {w n : ℕ} (hw : 0 < w) (hfit : Fits w n) :
    Nat.log 2 n < w := by
  by_cases hn : n = 0
  · subst hn; simpa using hw
  · exact (Nat.log_lt_iff_lt_pow Nat.one_lt_two hn).mpr hfit

/-- `log2BitCode` executes in at most `4 * w + 4` instructions when `0 < w` and `Fits w (x.regs 0)`,
storing `Nat.log 2 (x.regs 0)` in `r1` and preserving `r3..r11`, `mem`, and `bitSize`. -/
theorem log2BitCode_exec {w : ℕ} (hw : 0 < w) {x : BitRAM.Data 12}
    (hfit : Fits w (x.regs 0)) :
    BitRAM.DemonicExecWithin w log2BitCode x
      (fun y =>
        y.regs 1 = Nat.log 2 (x.regs 0) ∧
        (∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → y.regs i = x.regs i) ∧
        y.mem = x.mem ∧
        y.bitSize = x.bitSize) (4 * w + 4) := by
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  have hlog_lt : Nat.log 2 (x.regs 0) < w := log_two_lt_of_fits hw hfit
  have hfit_log : Fits w (0 + Nat.log 2 (x.regs 0)) := by
    rw [Nat.zero_add]
    exact Fits.of_le (fits_self w) hlog_lt.le
  refine DemonicExecWithin.step_const (T := 4 * w + 3) h0 ?_
  refine DemonicExecWithin.step_const (T := 4 * w + 2) h1 ?_
  refine (log2LoopBitCode_exec (x.regs 0)
    (by simp +decide [BitRAM.Data.set])
    (by simp +decide [BitRAM.Data.set])
    (by simp +decide [BitRAM.Data.set])
    hfit hfit_log).mono (fun y hy => ?_) (by omega)
  subst hy
  refine ⟨by simp +decide [log2LoopBitData, BitRAM.Data.set],
    fun i h0' h1' h2' => by simp [log2LoopBitData, BitRAM.Data.set, h0', h1', h2'],
    rfl, rfl⟩

/-- For every `n > 1`, `Nat.clog 2 n = Nat.log 2 (n - 1) + 1`. -/
theorem clog_two_eq_log_pred_add_one {n : ℕ} (hn : 1 < n) :
    Nat.clog 2 n = Nat.log 2 (n - 1) + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.clog_of_one_lt (by decide) hn]
    have hsub : n + 2 - 1 = n + 1 := rfl
    rw [hsub]
    by_cases h2 : 1 < (n + 1) / 2
    · rw [ih ((n + 1) / 2) (by omega) h2]
      have hge2 : 2 ≤ n - 1 := by omega
      rw [Nat.log_of_one_lt_of_le (by decide) hge2]
      have hdiv : (n + 1) / 2 - 1 = (n - 1) / 2 := by omega
      rw [hdiv]
    · have hn2 : n = 2 := by omega
      subst hn2
      decide

/-- Parameter-free `BitRAM.Code .standard 12` program computing `Nat.clog 2 (x.regs 0)` into `r1`
using `r0, r1, r2` and preserving `r3..r11`, `mem`, and `bitSize`. -/
@[expose] def clog2BitCode : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 0))
    (.seq (.op (.const 2 1))
      (.branch (.lt 2 0)
        (.seq (.op (.bin .sub 0 0 2))
          (.seq (.op (.const 1 1))
            log2LoopBitCode))
        (.op (.copy 1 1))))

/-- `clog2BitCode` executes in at most `4 * w + 8` instructions when `0 < w` and
`Fits w (x.regs 0)`, storing `Nat.clog 2 (x.regs 0)` in `r1` and preserving `r3..r11`, `mem`,
and `bitSize`. -/
theorem clog2BitCode_exec {w : ℕ} (hw : 0 < w) {x : BitRAM.Data 12}
    (hfit : Fits w (x.regs 0)) :
    BitRAM.DemonicExecWithin w clog2BitCode x
      (fun y =>
        y.regs 1 = Nat.clog 2 (x.regs 0) ∧
        (∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → y.regs i = x.regs i) ∧
        y.mem = x.mem ∧
        y.bitSize = x.bitSize) (4 * w + 8) := by
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  refine DemonicExecWithin.step_const (T := 4 * w + 7) h0 ?_
  refine DemonicExecWithin.step_const (T := 4 * w + 6) h1 ?_
  set s2 := (x.set 1 0).set 2 1
  by_cases hlt : 1 < x.regs 0
  · have hc : BitRAM.CondHolds (.lt 2 0) s2 := by
      change s2.regs 2 < s2.regs 0
      simp +decide [s2, BitRAM.Data.set, hlt]
    refine .branch_pos (T₀ := 4 * w + 4) hc ?_ (by omega)
    have hpred_fit : Fits w (x.regs 0 - 1) := hfit.of_le (Nat.sub_le _ _)
    have hlog_lt : Nat.log 2 (x.regs 0 - 1) < w := log_two_lt_of_fits hw hpred_fit
    have hfit_acc : Fits w (1 + Nat.log 2 (x.regs 0 - 1)) :=
      Fits.of_le (fits_self w) (by omega)
    refine step_dExec_bin (v := x.regs 0 - 1) (T := 4 * w + 3)
      (by simp +decide [s2, BitRAM.Data.set, BinOp.eval]) hpred_fit ?_
    set s3 := s2.set 0 (x.regs 0 - 1)
    refine DemonicExecWithin.step_const (T := 4 * w + 2) h1 ?_
    refine (log2LoopBitCode_exec (x.regs 0 - 1)
      (by simp +decide [s3, s2, BitRAM.Data.set])
      (by simp +decide [s3, s2, BitRAM.Data.set])
      (by simp +decide [s3, s2, BitRAM.Data.set])
      hpred_fit hfit_acc).mono (fun y hy => ?_) (by omega)
    subst hy
    refine ⟨?_, fun i h0' h1' h2' => by
      simp [log2LoopBitData, s3, s2, BitRAM.Data.set, h0', h1', h2'], rfl, rfl⟩
    simp only [log2LoopBitData, BitRAM.Data.set, Function.update_self]
    rw [clog_two_eq_log_pred_add_one hlt, Nat.add_comm]
  · have hc : ¬BitRAM.CondHolds (.lt 2 0) s2 := by
      change ¬(s2.regs 2 < s2.regs 0)
      simp +decide [s2, BitRAM.Data.set, hlt]
    have hclog0 : Nat.clog 2 (x.regs 0) = 0 := Nat.clog_of_right_le_one (by omega) 2
    refine .branch_neg (T₀ := 1) hc (DemonicExecWithin.copy ?_) (by omega)
    refine ⟨by simp +decide [s2, BitRAM.Data.set, hclog0],
      fun i _ h1' h2' => by simp [s2, BitRAM.Data.set, h1', h2'],
      rfl, rfl⟩

end Cslib.DataStructure.Dictionary.BitResizable
