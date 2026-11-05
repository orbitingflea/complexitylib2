/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.HornerEval

/-!
# Uniform Two-Stage Quotient Hash Evaluation on `BitRAM`

This module defines the parameter-free `BitRAM.Code .standard 280` program `evalHashRegCode` and
its subprograms (`reduceKeyRegCode`, `initLimbsRegCode`, `hornerSetupRegCode`, `hornerRegCode`,
`packOutRegCode`) that evaluate `(Succinct.evalQuotHash U N θ q).val = Succinct.hValOfSeed U N θ q`
from the persistent epoch parameter registers `EpochRegs U V w N`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.reduceKeyRegCode`: Stage 1 multiply-shift reduction.
* `Cslib.DataStructure.Dictionary.BitResizable.initLimbsRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.hornerSetupRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.hornerRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.packOutRegCode`: Stage 2–4 trinomial polynomial
  evaluation and limb packing.
* `Cslib.DataStructure.Dictionary.BitResizable.evalHashRegCode`: full two-stage quotient hash
  evaluation in at most `142637` instructions.

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.evalHashRegCode_exec`: demonic total-correctness and
  step bound (`142637`) for `evalHashRegCode`.
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

/-! ## Section 1: Stage 1 key reduction (`reduceKeyRegCode`) -/

theorem dExec_step {r w : ℕ} {c₁ c₂ : BitRAM.Code .standard r}
    {x y : BitRAM.Data r} {P : BitRAM.Data r → Prop} {T : ℕ}
    (h₁ : BitRAM.DemonicExecWithin w c₁ x (fun z => z = y) 1)
    (h₂ : BitRAM.DemonicExecWithin w c₂ y P T) :
    BitRAM.DemonicExecWithin w (.seq c₁ c₂) x P (T + 1) :=
  .seq h₁ (fun _ hz => hz ▸ h₂) (by omega)

/-- Parameter-free Stage 1a setup (`21` instructions on `BitRAM.Code .standard 280`):
loads `α = x.mem (x.regs 0)` into `reg 4` and computes the half-word split masks and operands
for `m = w₀ - 1` (reading `w₀` from `reg 261` and `u` from `reg 1`). -/
@[expose]
def halfMulSetupRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.load 4 0))
  (.seq (.op (.const 11 1))
  (.seq (.op (.bin .sub 5 261 11))
  (.seq (.op (.bin .shiftRight 6 5 11))
  (.seq (.op (.bin .sub 8 5 6))
  (.seq (.op (.bin .shiftLeft 10 6 11))
  (.seq (.op (.bin .sub 9 5 10))
  (.seq (.op (.bin .shiftLeft 5 11 5))
  (.seq (.op (.bin .sub 5 5 11))
  (.seq (.op (.bin .shiftLeft 7 11 6))
  (.seq (.op (.bin .sub 7 7 11))
  (.seq (.op (.bin .shiftLeft 8 11 8))
  (.seq (.op (.bin .sub 8 8 11))
  (.seq (.op (.bin .shiftLeft 9 11 9))
  (.seq (.op (.bin .sub 9 9 11))
  (.seq (.op (.bin .and 11 1 5))
  (.seq (.op (.bin .and 12 4 7))
  (.seq (.op (.bin .shiftRight 13 4 6))
  (.seq (.op (.bin .and 14 11 7))
        (.op (.bin .shiftRight 15 11 6))))))))))))))))))))

theorem halfMulSetupRegCode_exec {w w₀ : ℕ} (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w)
    (x : BitRAM.Data 280)
    (h261 : x.regs 261 = w₀)
    (hadm0 : x.regs 0 < x.wordSize w)
    (hα : x.mem (x.regs 0) < 2 ^ (w₀ - 1)) :
    let m := w₀ - 1
    let h := m / 2
    let α := x.mem (x.regs 0)
    let x' := x.regs 1 &&& (2 ^ m - 1)
    BitRAM.DemonicExecWithin w halfMulSetupRegCode x
      (fun y =>
        y.regs 0 = x.regs 0 ∧
        y.regs 1 = x.regs 1 ∧
        y.regs 5 = 2 ^ m - 1 ∧
        y.regs 6 = h ∧
        y.regs 8 = 2 ^ (m - h) - 1 ∧
        y.regs 9 = 2 ^ (m - 2 * h) - 1 ∧
        y.regs 10 = 2 * h ∧
        y.regs 12 = α &&& (2 ^ h - 1) ∧
        y.regs 13 = α >>> h ∧
        y.regs 14 = x' &&& (2 ^ h - 1) ∧
        y.regs 15 = x' >>> h ∧
        (∀ j : Fin 280, 20 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      20 := by
  intro m h α x'
  have hm : m < w := by omega
  have hpow_m_lt : 2 ^ m < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hm
  have hfit_m : Fits w (2 ^ m) := hpow_m_lt
  have hfit_1 : Fits w 1 := hfit_m.of_le Nat.one_le_two_pow
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hm_lt_pow : m < 2 ^ m := Nat.lt_two_pow_self
  have hfit_m_val : Fits w m := hfit_m.of_le (le_of_lt hm_lt_pow)
  have hfit_h : Fits w h := hfit_m.of_le (h_le.trans (le_of_lt hm_lt_pow))
  have hfit_mh : Fits w (m - h) := hfit_m.of_le ((Nat.sub_le m h).trans (le_of_lt hm_lt_pow))
  have hfit_2h : Fits w (2 * h) := hfit_m.of_le (h2_le.trans (le_of_lt hm_lt_pow))
  have hfit_m2h : Fits w (m - 2 * h) :=
    hfit_m.of_le ((Nat.sub_le m (2 * h)).trans (le_of_lt hm_lt_pow))
  have hfit_pow_h : Fits w (2 ^ h) := hfit_m.of_le (Nat.pow_le_pow_right two_pos h_le)
  have hfit_pow_mh : Fits w (2 ^ (m - h)) :=
    hfit_m.of_le (Nat.pow_le_pow_right two_pos (Nat.sub_le m h))
  have hfit_pow_m2h : Fits w (2 ^ (m - 2 * h)) :=
    hfit_m.of_le (Nat.pow_le_pow_right two_pos (Nat.sub_le m (2 * h)))
  have hfit_mask_m : Fits w (2 ^ m - 1) := hfit_m.of_le (Nat.sub_le _ _)
  have hfit_mask_h : Fits w (2 ^ h - 1) := hfit_pow_h.of_le (Nat.sub_le _ _)
  have hfit_mask_mh : Fits w (2 ^ (m - h) - 1) := hfit_pow_mh.of_le (Nat.sub_le _ _)
  have hfit_mask_m2h : Fits w (2 ^ (m - 2 * h) - 1) := hfit_pow_m2h.of_le (Nat.sub_le _ _)
  have hx'_lt : x' < 2 ^ m := ReducedKWise.and_two_pow_sub_one_lt (x.regs 1) m
  have hfit_x' : Fits w x' := hfit_m.of_le (le_of_lt hx'_lt)
  have hfit_α0 : Fits w (α &&& (2 ^ h - 1)) :=
    hfit_pow_h.of_le (le_of_lt (ReducedKWise.and_two_pow_sub_one_lt α h))
  have hfit_α1 : Fits w (α >>> h) :=
    hfit_m.of_le ((Nat.shiftRight_le α h).trans (le_of_lt hα))
  have hfit_x0 : Fits w (x' &&& (2 ^ h - 1)) :=
    hfit_pow_h.of_le (le_of_lt (ReducedKWise.and_two_pow_sub_one_lt x' h))
  have hfit_x1 : Fits w (x' >>> h) :=
    hfit_m.of_le ((Nat.shiftRight_le x' h).trans (le_of_lt hx'_lt))
  have hsh_m : 1 <<< m = 2 ^ m := by rw [Nat.shiftLeft_eq, one_mul]
  have hsh_h : 1 <<< h = 2 ^ h := by rw [Nat.shiftLeft_eq, one_mul]
  have hsh_mh : 1 <<< (m - h) = 2 ^ (m - h) := by rw [Nat.shiftLeft_eq, one_mul]
  have hsh_m2h : 1 <<< (m - 2 * h) = 2 ^ (m - 2 * h) := by rw [Nat.shiftLeft_eq, one_mul]
  have h_shr1 : m >>> 1 = h := by rw [Nat.shiftRight_eq_div_pow, pow_one]
  have h_shl1 : h <<< 1 = 2 * h := by rw [Nat.shiftLeft_eq, pow_one, mul_comm]
  unfold halfMulSetupRegCode
  refine dExec_step (DemonicExecWithin.load hadm0 rfl) ?_
  refine dExec_step (DemonicExecWithin.const hfit_1 rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h261] using hfit_m_val) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h261, m, h_shr1] using hfit_h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h261, m, h_shr1] using hfit_mh) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, h_shl1] using hfit_2h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, h_shl1] using hfit_m2h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h261, m, hsh_m] using hfit_m) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h261, m, hsh_m] using hfit_mask_m) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, hsh_h] using hfit_pow_h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, hsh_h] using hfit_mask_h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, hsh_mh] using hfit_pow_mh) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, hsh_mh] using hfit_mask_mh) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, h_shl1, hsh_m2h] using hfit_pow_m2h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1, h_shl1, hsh_m2h] using hfit_mask_m2h) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h261, m, hsh_m] using hfit_x') rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h261, m, h_shr1, hsh_h] using
          hfit_α0) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h261, m, h_shr1] using hfit_α1) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h261, m, h_shr1, hsh_m, hsh_h] using
          hfit_x0) rfl) ?_
  refine DemonicExecWithin.bin
    (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h261, m, h_shr1, hsh_m] using
        hfit_x1) ?_
  refine ⟨by simp, by simp, by simp [m, h261, hsh_m], by simp [m, h, h261, h_shr1],
    by simp [m, h, h261, h_shr1, hsh_mh], by simp [m, h, h261, h_shr1, h_shl1, hsh_m2h],
    by simp [m, h, h261, h_shr1, h_shl1],
    by simp [-Nat.and_two_pow_sub_one_eq_mod, m, h, h261, h_shr1, hsh_h, α],
    by simp [m, h, h261, h_shr1, α],
    by simp [-Nat.and_two_pow_sub_one_eq_mod, m, h, h261, h_shr1, hsh_m, hsh_h, x'],
    by simp [-Nat.and_two_pow_sub_one_eq_mod, m, h, h261, h_shr1, hsh_m, x'],
    fun j hj => ?_, rfl, rfl⟩
  dsimp only [BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro heq; subst heq; omega)]

/-- Stage 1b (`18` instructions on `BitRAM.Code .standard 280`): combines the four half-word
products modulo `2 ^ m`. -/
@[expose]
def halfMulCombineRegCode : BitRAM.Code .standard 280 :=
  embed240 (ofExactCode ReducedKWise.halfMulCombineCode)

/-- Stage 1c (`8` instructions on `BitRAM.Code .standard 280`): combines `halfMulMod` with the low
bit of `u` and shifts right by `reg 262 = w₀ - min w₀ (3 * b)`. -/
@[expose]
def finishReduceRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 6 1))
  (.seq (.op (.bin .shiftRight 11 1 6))
  (.seq (.op (.bin .add 3 11 3))
  (.seq (.op (.bin .and 3 3 5))
  (.seq (.op (.bin .shiftLeft 3 3 6))
  (.seq (.op (.bin .and 11 1 6))
  (.seq (.op (.bin .add 3 11 3))
        (.op (.bin .shiftRight 3 3 262))))))))

theorem finishReduceRegCode_exec {w w₀ b α u : ℕ} (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w)
    (hu : u < 2 ^ w₀) (x : BitRAM.Data 280)
    (h1 : x.regs 1 = u)
    (h3 : x.regs 3 = halfMulMod (w₀ - 1) α (u &&& (2 ^ (w₀ - 1) - 1)))
    (h5 : x.regs 5 = 2 ^ (w₀ - 1) - 1)
    (h262 : x.regs 262 = w₀ - min w₀ (3 * b)) :
    BitRAM.DemonicExecWithin w finishReduceRegCode x
      (fun y =>
        y.regs 0 = x.regs 0 ∧
        y.regs 1 = x.regs 1 ∧
        y.regs 3 = oddMulModWord w₀ α u >>> (w₀ - min w₀ (3 * b)) ∧
        (∀ j : Fin 280, 20 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      8 := by
  set m := w₀ - 1
  have hm_eq : m + 1 = w₀ := Nat.sub_add_cancel hw₀_pos
  have hpow_w0_le : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀
  have hpow_m_mul : 2 * 2 ^ m = 2 ^ w₀ := by rw [← pow_succ', hm_eq]
  have hfit_1 : Fits w 1 := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    change 1 < 2 ^ w; omega
  set p := halfMulMod m α (u &&& (2 ^ m - 1))
  have hp_lt : p < 2 ^ m := halfMulMod_lt m α _
  have hu_shr_lt : u >>> 1 < 2 ^ m := by
    change u >>> 1 < 2 ^ (w₀ - 1)
    exact ReducedKWise.shiftRight_lt_pow_sub hw₀_pos hu
  have hadd_lt : (u >>> 1) + p < 2 ^ w₀ := by linarith
  set q := ((u >>> 1) + p) &&& (2 ^ m - 1)
  have hq_lt : q < 2 ^ m := ReducedKWise.and_two_pow_sub_one_lt _ m
  have hq_shl_lt : q <<< 1 < 2 ^ w₀ := by
    rw [Nat.shiftLeft_eq, pow_one]; linarith
  have hubit_lt : u &&& 1 < 2 ^ w₀ := by
    have : u &&& 1 < 2 ^ 1 := ReducedKWise.and_two_pow_sub_one_lt u 1
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right two_pos hw₀_pos)
  have hodd_lt : oddMulModWord w₀ α u < 2 ^ w₀ := oddMulModWord_lt hw₀_pos α u
  have hpow_m_le : 2 ^ m ≤ 2 ^ w :=
    (Nat.pow_le_pow_right two_pos (Nat.sub_le w₀ 1)).trans hpow_w0_le
  have hfit_ushr : Fits w (u >>> 1) := lt_of_lt_of_le hu_shr_lt hpow_m_le
  have hfit_add : Fits w ((u >>> 1) + p) := lt_of_lt_of_le hadd_lt hpow_w0_le
  have hfit_q : Fits w q := lt_of_lt_of_le hq_lt hpow_m_le
  have hfit_qshl : Fits w (q <<< 1) := lt_of_lt_of_le hq_shl_lt hpow_w0_le
  have hfit_ubit : Fits w (u &&& 1) := lt_of_lt_of_le hubit_lt hpow_w0_le
  have hfit_odd : Fits w (oddMulModWord w₀ α u) := lt_of_lt_of_le hodd_lt hpow_w0_le
  have hfit_res : Fits w (oddMulModWord w₀ α u >>> (w₀ - min w₀ (3 * b))) :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) hfit_odd
  unfold finishReduceRegCode
  refine dExec_step (DemonicExecWithin.const hfit_1 rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h1] using hfit_ushr) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h1, h3, m] using hfit_add) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h1, h3, h5, q, m]
          using hfit_q) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, h1, h3, h5, q, m]
          using hfit_qshl) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_one_is_mod, BinOp.eval, h1] using hfit_ubit) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, -Nat.and_one_is_mod,
          BinOp.eval, h1, h3, h5, oddMulModWord, p, m] using hfit_odd) rfl) ?_
  refine DemonicExecWithin.bin
    (by simpa [-Nat.and_two_pow_sub_one_eq_mod, -Nat.and_one_is_mod,
        BinOp.eval, h1, h3, h5, h262, oddMulModWord, p, m] using hfit_res) ?_
  refine ⟨by simp, by simp,
    by simp [-Nat.and_two_pow_sub_one_eq_mod, -Nat.and_one_is_mod,
        h1, h3, h5, h262, oddMulModWord, p, m],
    fun j hj => ?_, rfl, rfl⟩
  dsimp only [BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro heq; subst heq; omega)]

/-- Complete parameter-free Stage 1 key reduction (`46` instructions on
`BitRAM.Code .standard 280`): computes
`oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b))` into `reg 3`. -/
@[expose]
def reduceKeyRegCode : BitRAM.Code .standard 280 :=
  .seq halfMulSetupRegCode (.seq halfMulCombineRegCode finishReduceRegCode)

theorem reduceKeyRegCode_exec {w w₀ b : ℕ} (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w)
    (x : BitRAM.Data 280)
    (h261 : x.regs 261 = w₀)
    (h262 : x.regs 262 = w₀ - min w₀ (3 * b))
    (hadm0 : x.regs 0 < x.wordSize w)
    (hα : x.mem (x.regs 0) < 2 ^ (w₀ - 1))
    (hu : x.regs 1 < 2 ^ w₀) :
    BitRAM.DemonicExecWithin w reduceKeyRegCode x
      (fun y =>
        y.regs 0 = x.regs 0 ∧
        y.regs 1 = x.regs 1 ∧
        y.regs 3 = oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b)) ∧
        (∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      46 := by
  have hm : w₀ - 1 < w := by omega
  have hx'_lt : x.regs 1 &&& (2 ^ (w₀ - 1) - 1) < 2 ^ (w₀ - 1) :=
    ReducedKWise.and_two_pow_sub_one_lt (x.regs 1) (w₀ - 1)
  refine .seq (T₂ := 26) (halfMulSetupRegCode_exec hw₀_pos hw₀ x h261 hadm0 hα)
    (fun y1 ⟨hy1_0, hy1_1, hy1_5, hy1_6, hy1_8, hy1_9, hy1_10, hy1_12, hy1_13,
      hy1_14, hy1_15, hy1_hi, hy1_mem, hy1_sz⟩ => ?_) le_rfl
  obtain ⟨y2₀, hex2, hy2_0, hy2_1, hy2_3, hy2_5, hy2_mem⟩ :=
    ReducedKWise.halfMulCombineCode_exec hm hα hx'_lt
      (y1.comap embed240Map).toWordRAMData
      hy1_5 hy1_6 hy1_8 hy1_9 hy1_10 hy1_12 hy1_13 hy1_14 hy1_15
  have hd2 := embed240_exec (dExec_of_exec_noLoadStore (x := y1.comap embed240Map) rfl hex2)
  refine .seq (T₂ := 8) hd2 (fun y2 ⟨hy2_eq, hy2_hi⟩ => ?_) le_rfl
  have hy2_regs : ∀ i : Fin 240, y2.regs (embed240Map i) = y2₀.regs i :=
    fun i => congrArg (fun z : BitRAM.Data 240 => z.regs i) hy2_eq
  have hy2_mem' : y2.mem = x.mem := by
    have : (y2.comap embed240Map).mem = y2₀.mem :=
      congrArg BitRAM.Data.mem hy2_eq
    exact this.trans (hy2_mem.trans hy1_mem)
  have hy2_sz' : y2.bitSize = x.bitSize := by
    have : (y2.comap embed240Map).bitSize = y1.bitSize :=
      congrArg BitRAM.Data.bitSize hy2_eq
    exact this.trans hy1_sz
  have h262_y2 : y2.regs 262 = w₀ - min w₀ (3 * b) := by
    rw [hy2_hi 262 (by decide), hy1_hi 262 (by decide), h262]
  refine (finishReduceRegCode_exec hw₀_pos hw₀ hu y2
    ((hy2_regs 1).trans (hy2_1.trans hy1_1))
    ((hy2_regs 3).trans hy2_3)
    ((hy2_regs 5).trans hy2_5)
    h262_y2).mono
    (fun y3 ⟨hy3_0, hy3_1, hy3_3, hy3_hi, hy3_mem, hy3_sz⟩ => ?_) le_rfl
  refine ⟨hy3_0.trans ((hy2_regs 0).trans (hy2_0.trans hy1_0)),
    hy3_1.trans ((hy2_regs 1).trans (hy2_1.trans hy1_1)),
    hy3_3, fun j hj => ?_, hy3_mem.trans hy2_mem', hy3_sz.trans hy2_sz'⟩
  rw [hy3_hi j (by omega), hy2_hi j hj, hy1_hi j (by omega)]

/-! ## Section 2: Parameter-free Stage 2–4 polynomial evaluation (`evalHashRegCode`) -/

/-- Step `m < 54` of parameter-free Stage 2a (`3` instructions on `BitRAM.Code .standard 280`):
extracts `c`-bit limb `m` from `reg 3` into `xReg m` using `reg 265 = 2 ^ c - 1`, shifts `reg 3`
right by `reg 264 = c`, and zeroes `accReg m`. -/
@[expose]
def initLimbRegStep (m : ℕ) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .and (embed240Map (ReducedKWise.xReg m)) 3 265))
  (.seq (.op (.bin .shiftRight 3 3 264))
        (.op (.const (embed240Map (ReducedKWise.accReg m)) 0)))

/-- Parameter-free Stage 2a (`163` instructions on `BitRAM.Code .standard 280`): unpacks up to `54`
limbs of the reduced key from `reg 3` into `xReg 0 .. xReg 53` and zeroes
`accReg 0 .. accReg 53`. -/
@[expose]
def initLimbsRegCode : BitRAM.Code .standard 280 :=
  seqAscBit initLimbRegStep 54

theorem initLimbsRegCode_exec {w t r_val : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hr : r_val < 2 ^ w) (x : BitRAM.Data 280)
    (h3 : x.regs 3 = r_val)
    (h264 : x.regs 264 = reducedChunkBits t)
    (h265 : x.regs 265 = 2 ^ reducedChunkBits t - 1) :
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    BitRAM.DemonicExecWithin w initLimbsRegCode x
      (fun y =>
        y.regs 0 = x.regs 0 ∧
        y.regs 1 = x.regs 1 ∧
        (∀ m < L, y.regs (embed240Map (ReducedKWise.xReg m)) = getLimb c r_val m) ∧
        (∀ m < L, y.regs (embed240Map (ReducedKWise.accReg m)) = 0) ∧
        (∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      163 := by
  intro c L
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hfit_2c : Fits w (2 ^ (2 * c)) := hpow_2c_lt
  have hfit_0 : Fits w 0 := hfit_2c.of_le (Nat.zero_le _)
  let P (n : ℕ) (z : BitRAM.Data 280) : Prop :=
    z.regs 0 = x.regs 0 ∧
    z.regs 1 = x.regs 1 ∧
    z.regs 3 = r_val >>> (n * c) ∧
    (∀ m < n, z.regs (embed240Map (ReducedKWise.xReg m)) = getLimb c r_val m) ∧
    (∀ m < n, z.regs (embed240Map (ReducedKWise.accReg m)) = 0) ∧
    (∀ j : Fin 280, 240 ≤ j.val → z.regs j = x.regs j) ∧
    z.mem = x.mem ∧ z.bitSize = x.bitSize
  have hP0 : P 0 x := by
    refine ⟨rfl, rfl, ?_, fun _ hm => (Nat.not_lt_zero _ hm).elim,
      fun _ hm => (Nat.not_lt_zero _ hm).elim, fun _ _ => rfl, rfl, rfl⟩
    rw [Nat.zero_mul, Nat.shiftRight_zero, h3]
  refine (seqAscBit_dExec initLimbRegStep 3 P 54
    (fun i hi z ⟨hz0, hz1, hz3, hzx, hza, hzhi, hzmem, hzsz⟩ => ?_) x hP0).mono
    (fun y ⟨hy0, hy1, _, hyx, hya, hyhi, hymem, hysz⟩ =>
      ⟨hy0, hy1, fun m hm => hyx m (lt_of_lt_of_le hm hL_le),
        fun m hm => hya m (lt_of_lt_of_le hm hL_le), hyhi, hymem, hysz⟩)
    (by decide)
  have hz264 : z.regs 264 = c := (hzhi 264 (by decide)).trans h264
  have hz265 : z.regs 265 = 2 ^ c - 1 := (hzhi 265 (by decide)).trans h265
  have hfit_limb : Fits w (getLimb c r_val i) :=
    hfit_2c.of_le ((le_of_lt (getLimb_lt c r_val i)).trans
      (Nat.pow_le_pow_right two_pos (by omega)))
  have hfit_shr : Fits w (r_val >>> ((i + 1) * c)) :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) hr
  have hxReg_ne : ∀ r : Fin 280, (r.val < 20 ∨ 240 ≤ r.val) →
      embed240Map (ReducedKWise.xReg i) ≠ r := by
    intro r hr h
    have : (ReducedKWise.xReg i).val = r.val := congrArg Fin.val h
    dsimp only [ReducedKWise.xReg] at this
    omega
  have haccReg_ne : ∀ r : Fin 280, (r.val < 20 ∨ 240 ≤ r.val) →
      embed240Map (ReducedKWise.accReg i) ≠ r := by
    intro r hr h
    have : (ReducedKWise.accReg i).val = r.val := congrArg Fin.val h
    dsimp only [ReducedKWise.accReg] at this
    omega
  unfold initLimbRegStep
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, hz3, hz265, getLimb] using hfit_limb)
      rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by
        dsimp only [BitRAM.Data.set, BinOp.eval]
        rw [Function.update_of_ne (hxReg_ne 3 (Or.inl (by decide))).symm,
          Function.update_of_ne (hxReg_ne 264 (Or.inr (by decide))).symm,
          hz3, hz264, ← Nat.shiftRight_add, ← Nat.succ_mul]
        exact hfit_shr) rfl) ?_
  refine DemonicExecWithin.const hfit_0 ?_
  refine ⟨?_, ?_, ?_, fun m hm => ?_, fun m hm => ?_, fun j hj => ?_, hzmem, hzsz⟩
  · dsimp only [BitRAM.Data.set]
    rw [Function.update_of_ne (haccReg_ne 0 (Or.inl (by decide))).symm,
      Function.update_of_ne (by decide : (0 : Fin 280) ≠ 3),
      Function.update_of_ne (hxReg_ne 0 (Or.inl (by decide))).symm, hz0]
  · dsimp only [BitRAM.Data.set]
    rw [Function.update_of_ne (haccReg_ne 1 (Or.inl (by decide))).symm,
      Function.update_of_ne (by decide : (1 : Fin 280) ≠ 3),
      Function.update_of_ne (hxReg_ne 1 (Or.inl (by decide))).symm, hz1]
  · dsimp only [BitRAM.Data.set, BinOp.eval]
    rw [Function.update_of_ne (haccReg_ne 3 (Or.inl (by decide))).symm,
      Function.update_self, Function.update_of_ne (hxReg_ne 3 (Or.inl (by decide))).symm,
      Function.update_of_ne (hxReg_ne 264 (Or.inr (by decide))).symm,
      hz3, hz264, ← Nat.shiftRight_add, ← Nat.succ_mul]
  · dsimp only [BitRAM.Data.set]
    have hne_acc : embed240Map (ReducedKWise.xReg m) ≠ embed240Map (ReducedKWise.accReg i) :=
      fun h => ReducedKWise.xReg_ne_accReg m i (injective_embed240Map h)
    have hne_3 : embed240Map (ReducedKWise.xReg m) ≠ 3 := by
      intro h; have := congrArg Fin.val h; dsimp [embed240Map, ReducedKWise.xReg] at this; omega
    rw [Function.update_of_ne hne_acc, Function.update_of_ne hne_3]
    rcases eq_or_ne m i with rfl | hne
    · rw [Function.update_self]
      simp [-Nat.and_two_pow_sub_one_eq_mod, BinOp.eval, hz3, hz265, getLimb]
    · have hne_x : embed240Map (ReducedKWise.xReg m) ≠ embed240Map (ReducedKWise.xReg i) :=
        fun h => ReducedKWise.xReg_ne_of_ne (by omega) hi hne (injective_embed240Map h)
      rw [Function.update_of_ne hne_x]
      exact hzx m (by omega)
  · dsimp only [BitRAM.Data.set]
    rcases eq_or_ne m i with rfl | hne
    · exact Function.update_self _ _ _
    · have hne_acc : embed240Map (ReducedKWise.accReg m) ≠ embed240Map (ReducedKWise.accReg i) :=
        fun h => ReducedKWise.accReg_ne_of_ne (by omega) hi hne (injective_embed240Map h)
      have hne_3 : embed240Map (ReducedKWise.accReg m) ≠ 3 := by
        intro h; have := congrArg Fin.val h; dsimp [embed240Map, ReducedKWise.accReg] at this; omega
      have hne_x : embed240Map (ReducedKWise.accReg m) ≠ embed240Map (ReducedKWise.xReg i) :=
        fun h => (ReducedKWise.xReg_ne_accReg i m (injective_embed240Map h.symm)).elim
      rw [Function.update_of_ne hne_acc, Function.update_of_ne hne_3, Function.update_of_ne hne_x]
      exact hza m (by omega)
  · dsimp only [BitRAM.Data.set]
    rw [Function.update_of_ne (haccReg_ne j (Or.inr hj)).symm,
      Function.update_of_ne (by intro h; subst h; omega),
      Function.update_of_ne (hxReg_ne j (Or.inr hj)).symm]
    exact hzhi j hj

/-- Parameter-free Stage 2b (`7` instructions on `BitRAM.Code .standard 280`): copies precomputed
Horner constants from `regs 264..269` into `regs 4..9` and `reg 18`. -/
@[expose]
def hornerSetupRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 4 269))
  (.seq (.op (.copy 5 264))
  (.seq (.op (.copy 6 265))
  (.seq (.op (.copy 7 266))
  (.seq (.op (.copy 8 267))
  (.seq (.op (.bin .add 9 264 264))
        (.op (.copy 18 268)))))))

theorem hornerSetupRegCode_exec {w base w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (x : BitRAM.Data 280)
    (h0 : x.regs 0 = base)
    (h264 : x.regs 264 = reducedChunkBits (reducedTrinomialStep w₀ b b'))
    (h265 : x.regs 265 = 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b') - 1)
    (h266 : x.regs 266 = reducedPackShift (reducedTrinomialStep w₀ b b') w)
    (h267 : x.regs 267 = 2 ^ reducedPackShift (reducedTrinomialStep w₀ b b') w - 1)
    (h268 : x.regs 268 = 2 ^ (2 * reducedChunkBits (reducedTrinomialStep w₀ b b')) - 1)
    (h269 : x.regs 269 = ReducedKWise.tabBase base w₀ b b' k) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    BitRAM.DemonicExecWithin w hornerSetupRegCode x
      (fun y =>
        y.regs 0 = base ∧
        y.regs 1 = x.regs 1 ∧
        y.regs 4 = ReducedKWise.tabBase base w₀ b b' k ∧
        y.regs 5 = c ∧
        y.regs 6 = 2 ^ c - 1 ∧
        y.regs 7 = p ∧
        y.regs 8 = 2 ^ p - 1 ∧
        y.regs 9 = 2 * c ∧
        y.regs 18 = 2 ^ (2 * c) - 1 ∧
        (∀ j : Fin 280, 20 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      7 := by
  intro t c p
  have hfit_2c : Fits w (2 * c) :=
    lt_trans hc_lt Nat.lt_two_pow_self
  unfold hornerSetupRegCode
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h264, Nat.two_mul] using hfit_2c) rfl) ?_
  refine DemonicExecWithin.copy ?_
  refine ⟨by simp [h0], by simp, by simp [h269], by simp [h264, c, t],
    by simp [h265, c, t], by simp [h266, p, t], by simp [h267, p, t],
    by simp [BinOp.eval, h264, c, t, Nat.two_mul],
    by simp [h268, c, t], fun j hj => ?_, rfl, rfl⟩
  dsimp only [BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro heq; subst heq; omega)]

/-- Dispatch on `x.regs 263 = min t 3 ∈ {0, 1, 2, 3}` using scratch registers `10, 11, 12` (`6`
overhead instructions). -/
@[expose]
def branchMinT3 (f : ℕ → BitRAM.Code .standard 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 10 0))
  (.seq (.op (.const 11 1))
  (.seq (.op (.const 12 2))
  (.branch (.eq 263 10) (f 0)
    (.branch (.eq 263 11) (f 1)
      (.branch (.eq 263 12) (f 2) (f 3))))))

theorem branchMinT3_exec {w t T : ℕ} (hw : 2 ≤ w)
    (f : ℕ → BitRAM.Code .standard 280)
    (x : BitRAM.Data 280) (h263 : x.regs 263 = min t 3)
    {P : BitRAM.Data 280 → Prop}
    (hf : BitRAM.DemonicExecWithin w (f (min t 3)) (((x.set 10 0).set 11 1).set 12 2) P T) :
    BitRAM.DemonicExecWithin w (branchMinT3 f) x P (T + 9) := by
  have hpow : 4 ≤ 2 ^ w := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw
  have hfit0 : Fits w 0 := by change 0 < 2 ^ w; omega
  have hfit1 : Fits w 1 := by change 1 < 2 ^ w; omega
  have hfit2 : Fits w 2 := by change 2 < 2 ^ w; omega
  unfold branchMinT3
  refine dExec_step (DemonicExecWithin.const hfit0 rfl) ?_
  refine dExec_step (DemonicExecWithin.const hfit1 rfl) ?_
  refine dExec_step (DemonicExecWithin.const hfit2 rfl) ?_
  set s := ((x.set 10 0).set 11 1).set 12 2
  have hle : min t 3 ≤ 3 := Nat.min_le_right t 3
  rcases (by omega : min t 3 = 0 ∨ min t 3 = 1 ∨ min t 3 = 2 ∨ min t 3 = 3) with h0 | h1 | h2 | h3
  · exact DemonicExecWithin.branch_pos (T₀ := T)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h0]) (h0 ▸ hf) (by omega)
  · refine DemonicExecWithin.branch_neg (T₀ := T + 1)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h1]) ?_ (by omega)
    exact DemonicExecWithin.branch_pos (T₀ := T)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h1]) (h1 ▸ hf) (by omega)
  · refine DemonicExecWithin.branch_neg (T₀ := T + 3)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h2]) ?_ (by omega)
    refine DemonicExecWithin.branch_neg (T₀ := T + 1)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h2]) ?_ (by omega)
    exact DemonicExecWithin.branch_pos (T₀ := T)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h2]) (h2 ▸ hf) (by omega)
  · refine DemonicExecWithin.branch_neg (T₀ := T + 4)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h3]) ?_ (by omega)
    refine DemonicExecWithin.branch_neg (T₀ := T + 2)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h3]) ?_ (by omega)
    exact DemonicExecWithin.branch_neg (T₀ := T)
      (by simp [BitRAM.Data.toWordRAMData, s, h263, h3]) (h3 ▸ hf) (by omega)

theorem hornerStep_min_three (t k j : ℕ) :
    ReducedKWise.hornerStep (min t 3) k j = ReducedKWise.hornerStep t k j := by
  dsimp only [ReducedKWise.hornerStep, reducedHalfLimbs, reducedLimbCount]
  rw [Nat.min_assoc, Nat.min_self]

theorem hornerCode_min_three (t k : ℕ) :
    ReducedKWise.hornerCode (min t 3) k = ReducedKWise.hornerCode t k := by
  dsimp only [ReducedKWise.hornerCode]
  exact congrArg (fun f => ReducedKWise.seqAsc f k) (funext (hornerStep_min_three t k))

theorem reducedLimbCount_min_three (t : ℕ) :
    reducedLimbCount (min t 3) = reducedLimbCount t := by
  dsimp only [reducedLimbCount, reducedHalfLimbs]
  rw [Nat.min_assoc, Nat.min_self]

/-- Parameter-free Stage 3 (`BitRAM.Code .standard 280`): dispatches on `reg 263 = min t 3` to
run `3` Horner evaluation steps of `ReducedKWise.hornerCode`. -/
def hornerRegCode : BitRAM.Code .standard 280 :=
  branchMinT3 (fun t₀ => embed240 (ofExactCode (ReducedKWise.hornerCode t₀ 3)))

theorem hornerStepSteps_le (t : ℕ) : ReducedKWise.hornerStepSteps t ≤ 47250 := by
  dsimp only [ReducedKWise.hornerStepSteps]
  have hL : reducedLimbCount t ≤ 54 := reducedLimbCount_le t
  nlinarith

theorem hornerRegCode_exec {base w w₀ b b' : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + ReducedKWise.space w w₀ b b' 3))
    (θ : ReducedPolySeed w₀ b b' 3)
    (r : Fin (2 ^ min w₀ (3 * b)))
    (x : BitRAM.Data 280)
    (hadm : base + ReducedKWise.space w w₀ b b' 3 ≤ x.wordSize w)
    (h263 : x.regs 263 = min (reducedTrinomialStep w₀ b b') 3)
    (hc : ReducedKWise.HornerConsts base w w₀ b b' 3 r.val
      (x.comap embed240Map).toWordRAMData)
    (htab : ReducedKWise.TableRep base w w₀ b b' 3 x.mem)
    (hseed : ReducedKWise.SeedRep base w₀ b b' 3 θ x.mem)
    (hacc0 : ∀ m < reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (embed240Map (ReducedKWise.accReg m)) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let evalVal := (trinomialPolyEval t 3 (2 ^ min w₀ (3 * b)) θ.2 r).val
    BitRAM.DemonicExecWithin w hornerRegCode x
      (fun y =>
        y.regs 0 = base ∧
        (∀ m < L, y.regs (embed240Map (ReducedKWise.accReg m)) = getLimb c evalVal m) ∧
        (∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      141760 := by
  intro t c L evalVal
  have hw2 : 2 ≤ w := by
    have := reducedChunkBits_pos (reducedTrinomialStep w₀ b b')
    omega
  set s := ((x.set 10 0).set 11 1).set 12 2
  have hs_hc : ReducedKWise.HornerConsts base w w₀ b b' 3 r.val
      (s.comap embed240Map).toWordRAMData := by
    obtain ⟨h0, h4, h5, h6, h7, h8, h9, h18, hx⟩ := hc
    refine ⟨h0, h4, h5, h6, h7, h8, h9, h18, fun m hm => ?_⟩
    have hm_val : 20 ≤ (embed240Map (ReducedKWise.xReg m)).val := by
      dsimp [embed240Map, ReducedKWise.xReg]; omega
    change s.regs (embed240Map (ReducedKWise.xReg m)) = getLimb c r.val m
    dsimp only [s, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hx m hm
  have hs_acc0 : ∀ m < L, (s.comap embed240Map).regs (ReducedKWise.accReg m) = 0 := by
    intro m hm
    have hm_val : 20 ≤ (embed240Map (ReducedKWise.accReg m)).val := by
      dsimp [embed240Map, ReducedKWise.accReg]; omega
    change s.regs (embed240Map (ReducedKWise.accReg m)) = 0
    dsimp only [s, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hacc0 m hm
  have hd := hornerCode_dExec hc_lt hfit_space θ r (s.comap embed240Map)
    hadm hs_hc htab hseed hs_acc0
  dsimp only at hd
  rw [← hornerCode_min_three (reducedTrinomialStep w₀ b b') 3] at hd
  have hemb := embed240_exec hd
  have hsteps : 3 * ReducedKWise.hornerStepSteps t + 1 + 9 ≤ 141760 := by
    have := hornerStepSteps_le t
    omega
  unfold hornerRegCode
  refine (branchMinT3_exec hw2
    (fun t₀ => embed240 (ofExactCode (ReducedKWise.hornerCode t₀ 3)))
    x h263 hemb).mono (fun y ⟨⟨hy_hc, hy_acc, hy_mem, hy_sz⟩, hy_hi⟩ => ?_) hsteps
  refine ⟨hy_hc.1, hy_acc, fun j hj => ?_, hy_mem, hy_sz⟩
  rw [hy_hi j hj]
  dsimp only [s, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Step `m < 54` of parameter-free Stage 4 (`12` instructions on `BitRAM.Code .standard 280`):
computes `reducedOutMask c b' m` and `reducedOutShift c b' m` from `reg 249 = b'`, `reg 264 = c`,
and `reg 13 = min (m * c) b'`, masks and shifts `accReg m` into `reg 2`, and advances `reg 13` to
`min ((m + 1) * c) b'`. -/
@[expose]
def packOutRegStep (m : ℕ) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .sub 10 249 13))
  (.seq (.op (.bin .sub 10 264 10))
  (.seq (.op (.bin .sub 10 264 10))
  (.seq (.op (.const 12 1))
  (.seq (.op (.bin .shiftLeft 10 12 10))
  (.seq (.op (.bin .sub 10 10 12))
  (.seq (.op (.bin .and 12 (embed240Map (ReducedKWise.accReg m)) 10))
  (.seq (.op (.bin .shiftLeft 12 12 13))
  (.seq (.op (.bin .xor 2 2 12))
  (.seq (.op (.bin .add 13 13 264))
  (.seq (.op (.bin .sub 10 249 13))
        (.op (.bin .sub 13 249 10))))))))))))

/-- Parameter-free Stage 4 (`BitRAM.Code .standard 280`): packs the low `b' = reg 249` bits of
`accReg 0 .. accReg (L - 1)` into `reg 2`. -/
def packOutRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 2 0))
  (.seq (.op (.const 13 0))
        (branchMinT3 (fun t₀ => seqAscBit packOutRegStep (reducedLimbCount t₀))))

private theorem one_shiftLeft_min_eq (c b' m : ℕ) :
    1 <<< (c - (c - (b' - min (m * c) b'))) = 2 ^ min c (b' - m * c) := by
  rw [Nat.shiftLeft_eq, one_mul,
    show c - (c - (b' - min (m * c) b')) = min c (b' - m * c) by omega]

private theorem one_shiftLeft_min_sub_one_eq_reducedOutMask (c b' m : ℕ) :
    1 <<< (c - (c - (b' - min (m * c) b'))) - 1 = reducedOutMask c b' m := by
  rw [one_shiftLeft_min_eq, reducedOutMask]

private theorem shift_min_eq_shift_reducedOutShift (c b' m v : ℕ) :
    (v &&& reducedOutMask c b' m) <<< min (m * c) b' =
      (v &&& reducedOutMask c b' m) <<< reducedOutShift c b' m := by
  dsimp only [reducedOutMask, reducedOutShift]
  split_ifs with hlt
  · rw [Nat.min_eq_left (le_of_lt hlt)]
  · have h0 : min c (b' - m * c) = 0 := by omega
    rw [h0]; simp

private theorem min_next_eq (c b' m : ℕ) :
    b' - (b' - (min (m * c) b' + c)) = min ((m + 1) * c) b' := by
  rw [Nat.succ_mul]
  omega

theorem packOutRegStep_exec {w t b' evalVal m : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hb'_le : b' ≤ w)
    (hm : m < reducedLimbCount t)
    (x : BitRAM.Data 280)
    (h2 : x.regs 2 =
      packLimbs (reducedChunkBits t) m (getLimb (reducedChunkBits t) evalVal) &&& (2 ^ b' - 1))
    (h13 : x.regs 13 = min (m * reducedChunkBits t) b')
    (h249 : x.regs 249 = b')
    (h264 : x.regs 264 = reducedChunkBits t)
    (hacc : ∀ i < reducedLimbCount t,
      x.regs (embed240Map (ReducedKWise.accReg i)) = getLimb (reducedChunkBits t) evalVal i) :
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    BitRAM.DemonicExecWithin w (packOutRegStep m) x
      (fun y =>
        y.regs 0 = x.regs 0 ∧
        y.regs 2 = packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1) ∧
        y.regs 13 = min ((m + 1) * c) b' ∧
        (∀ i < L, y.regs (embed240Map (ReducedKWise.accReg i)) = getLimb c evalVal i) ∧
        (∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      12 := by
  intro c L
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hm54 : m < 54 := lt_of_lt_of_le hm hL_le
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hpow_c_lt : Fits w (2 ^ c) :=
    lt_of_le_of_lt (Nat.pow_le_pow_right two_pos (by omega : c ≤ 2 * c)) hpow_2c_lt
  have hfit_1 : Fits w 1 := hpow_c_lt.of_le Nat.one_le_two_pow
  have hfit_b' : Fits w b' := lt_of_le_of_lt hb'_le Nat.lt_two_pow_self
  have hfit_c : Fits w c := lt_trans (by omega : c < w) Nat.lt_two_pow_self
  have hfit_pow_min : Fits w (2 ^ min c (b' - m * c)) :=
    lt_of_le_of_lt (Nat.pow_le_pow_right two_pos (Nat.min_le_left c _)) hpow_c_lt
  have hfit_mask : Fits w (reducedOutMask c b' m) :=
    lt_trans (reducedOutMask_lt c b' m) hpow_c_lt
  set limb := getLimb c evalVal m
  set masked := limb &&& reducedOutMask c b' m
  set shifted := masked <<< reducedOutShift c b' m
  set next2 := packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1)
  have hmasked_lt : Fits w masked :=
    lt_trans (lt_of_le_of_lt Nat.and_le_right (reducedOutMask_lt c b' m)) hpow_c_lt
  have hshifted_lt : Fits w shifted := by
    dsimp only [shifted, masked, reducedOutMask, reducedOutShift]
    split_ifs with hlt
    · have hand : limb &&& (2 ^ min c (b' - m * c) - 1) < 2 ^ (b' - m * c) := by
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
          (Nat.pow_le_pow_right two_pos (Nat.min_le_right _ _))
      rw [Nat.shiftLeft_eq]
      calc (limb &&& (2 ^ min c (b' - m * c) - 1)) * 2 ^ (m * c)
          < 2 ^ (b' - m * c) * 2 ^ (m * c) :=
            Nat.mul_lt_mul_of_pos_right hand (Nat.two_pow_pos _)
        _ = 2 ^ b' := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hb'_le
    · have hmin : min c (b' - m * c) = 0 := by omega
      rw [hmin]
      simp only [pow_zero, Nat.sub_self, Nat.and_zero, Nat.zero_shiftLeft]
      exact Nat.two_pow_pos w
  have hnext2_eq : x.regs 2 ^^^ shifted = next2 := by
    rw [h2, ← packLimbs_and_mask_succ c b' m (getLimb c evalVal)]
  have hnext2_lt : Fits w next2 := by
    calc next2 < 2 ^ b' := ReducedKWise.and_two_pow_sub_one_lt _ b'
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hb'_le
  have hfit_add13 : Fits w (min (m * c) b' + c) := by
    have hw_pos : 1 ≤ w := by have := reducedChunkBits_pos t; omega
    have hw1 : w ≤ 2 ^ (w - 1) := by
      have := Nat.lt_two_pow_self (n := w - 1)
      omega
    have hpow_w : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hw_pos, pow_succ, Nat.mul_two]
    have hmin_le : min (m * c) b' ≤ b' := Nat.min_le_right _ _
    change min (m * c) b' + c < 2 ^ w
    omega
  have hacc_m_ne : ∀ r : Fin 280, r.val < 20 → embed240Map (ReducedKWise.accReg m) ≠ r := by
    intro r hr h
    have := congrArg Fin.val h; dsimp [embed240Map, ReducedKWise.accReg] at this; omega
  have hacc_m_val : x.regs (embed240Map (ReducedKWise.accReg m)) = limb := hacc m hm
  unfold packOutRegStep
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h249, h13] using hfit_b'.of_le (Nat.sub_le b' _)) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h264, h249, h13] using hfit_c.of_le (Nat.sub_le c _)) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h264, h249, h13] using hfit_c.of_le (Nat.sub_le c _)) rfl) ?_
  refine dExec_step (DemonicExecWithin.const hfit_1 rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [Fits, BinOp.eval, h264, h249, h13, one_shiftLeft_min_eq, c]
        using hfit_pow_min) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [Fits, BinOp.eval, h264, h249, h13, one_shiftLeft_min_sub_one_eq_reducedOutMask, c]
          using hfit_mask) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by
        dsimp only [BitRAM.Data.set, BinOp.eval]
        rw [Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 12 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          hacc_m_val]
        simpa [-Nat.and_two_pow_sub_one_eq_mod, Fits, h264, h249, h13,
          one_shiftLeft_min_sub_one_eq_reducedOutMask, masked, limb, c] using hmasked_lt) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by
        dsimp only [BitRAM.Data.set, BinOp.eval]
        rw [Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 12 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          hacc_m_val]
        simpa [-Nat.and_two_pow_sub_one_eq_mod, Fits, h264, h249, h13,
          one_shiftLeft_min_sub_one_eq_reducedOutMask, shift_min_eq_shift_reducedOutShift,
          shifted, masked, limb, c] using hshifted_lt) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by
        dsimp only [BitRAM.Data.set, BinOp.eval]
        rw [Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 12 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          Function.update_of_ne (hacc_m_ne 10 (by decide)),
          hacc_m_val]
        simpa [-Nat.and_two_pow_sub_one_eq_mod, Fits, h264, h249, h13,
          one_shiftLeft_min_sub_one_eq_reducedOutMask, shift_min_eq_shift_reducedOutShift,
          hnext2_eq, shifted, masked, limb, c]
          using hnext2_lt) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h13, h264, c] using hfit_add13) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, h249, h13, h264, c] using hfit_b'.of_le (Nat.sub_le b' _)) rfl) ?_
  refine DemonicExecWithin.bin
    (by simpa [BinOp.eval, h249, h13, h264, c] using hfit_b'.of_le (Nat.sub_le b' _)) ?_
  refine ⟨by simp, ?_, ?_, fun i hi => ?_, fun j hj => ?_, rfl, rfl⟩
  · dsimp only [BitRAM.Data.set, BinOp.eval]
    rw [Function.update_of_ne (by decide : (2 : Fin 280) ≠ 13),
      Function.update_of_ne (by decide : (2 : Fin 280) ≠ 10),
      Function.update_of_ne (by decide : (2 : Fin 280) ≠ 13),
      Function.update_self,
      Function.update_of_ne (hacc_m_ne 10 (by decide)),
      Function.update_of_ne (hacc_m_ne 10 (by decide)),
      Function.update_of_ne (hacc_m_ne 12 (by decide)),
      Function.update_of_ne (hacc_m_ne 10 (by decide)),
      Function.update_of_ne (hacc_m_ne 10 (by decide)),
      Function.update_of_ne (hacc_m_ne 10 (by decide)),
      hacc_m_val]
    simpa [-Nat.and_two_pow_sub_one_eq_mod, h264, h249, h13,
      one_shiftLeft_min_sub_one_eq_reducedOutMask, shift_min_eq_shift_reducedOutShift,
      shifted, masked, limb, c] using hnext2_eq
  · simpa [BinOp.eval, h249, h13, h264, c] using min_next_eq c b' m
  · have hi_ne : ∀ r : Fin 280, r.val < 20 → embed240Map (ReducedKWise.accReg i) ≠ r := by
      intro r hr h
      have := congrArg Fin.val h; dsimp [embed240Map, ReducedKWise.accReg] at this; omega
    dsimp only [BitRAM.Data.set]
    repeat rw [Function.update_of_ne (hi_ne _ (by decide))]
    exact hacc i hi
  · dsimp only [BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro heq; subst heq; omega)]

theorem packOutRegCode_exec {w t b' evalVal : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hb'_le : b' ≤ w)
    (heval_lt : evalVal < 2 ^ (reducedLimbCount t * reducedChunkBits t))
    (x : BitRAM.Data 280)
    (h249 : x.regs 249 = b')
    (h263 : x.regs 263 = min t 3)
    (h264 : x.regs 264 = reducedChunkBits t)
    (hacc : ∀ i < reducedLimbCount t,
      x.regs (embed240Map (ReducedKWise.accReg i)) = getLimb (reducedChunkBits t) evalVal i) :
    BitRAM.DemonicExecWithin w packOutRegCode x
      (fun y =>
        y.regs 0 = x.regs 0 ∧
        y.regs 2 = evalVal &&& (2 ^ b' - 1) ∧
        (∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      660 := by
  set c := reducedChunkBits t
  set L := reducedLimbCount t
  have hw2 : 2 ≤ w := by
    have := reducedChunkBits_pos t
    omega
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  unfold packOutRegCode
  refine dExec_step (DemonicExecWithin.const hfit0 rfl) ?_
  refine dExec_step (DemonicExecWithin.const hfit0 rfl) ?_
  set s0 := (x.set 2 0).set 13 0
  set s := ((s0.set 10 0).set 11 1).set 12 2
  have hs0_263 : s0.regs 263 = min t 3 := by simp [s0, h263]
  let P (n : ℕ) (z : BitRAM.Data 280) : Prop :=
    z.regs 0 = x.regs 0 ∧
    z.regs 2 = packLimbs c n (getLimb c evalVal) &&& (2 ^ b' - 1) ∧
    z.regs 13 = min (n * c) b' ∧
    (∀ i < L, z.regs (embed240Map (ReducedKWise.accReg i)) = getLimb c evalVal i) ∧
    (∀ j : Fin 280, 240 ≤ j.val → z.regs j = x.regs j) ∧
    z.mem = x.mem ∧ z.bitSize = x.bitSize
  have hP0 : P 0 s := by
    refine ⟨by simp [s, s0], by simp [s, s0, packLimbs], by simp [s, s0],
      fun i hi => ?_, fun j hj => ?_, rfl, rfl⟩
    · have hi_ne : ∀ r : Fin 280, r.val < 20 → embed240Map (ReducedKWise.accReg i) ≠ r := by
        intro r hr h
        have := congrArg Fin.val h; dsimp [embed240Map, ReducedKWise.accReg] at this; omega
      dsimp only [s, s0, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (hi_ne _ (by decide))]
      exact hacc i hi
    · dsimp only [s, s0, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  have hloop := seqAscBit_dExec packOutRegStep 12 P (reducedLimbCount t)
    (fun m hm z ⟨hz0, hz2, hz13, hz_acc, hz_hi, hz_mem, hz_sz⟩ =>
      (packOutRegStep_exec hc_lt hb'_le hm z hz2 hz13
        ((hz_hi 249 (by decide)).trans h249)
        ((hz_hi 264 (by decide)).trans h264)
        hz_acc).mono
      (fun z' ⟨hz'0, hz'2, hz'13, hz'_acc, hz'_hi, hz'_mem, hz'_sz⟩ =>
        ⟨hz'0.trans hz0, hz'2, hz'13, hz'_acc,
          fun j hj => (hz'_hi j hj).trans (hz_hi j hj),
          hz'_mem.trans hz_mem, hz'_sz.trans hz_sz⟩)
      le_rfl)
    s hP0
  rw [← reducedLimbCount_min_three t] at hloop
  refine (branchMinT3_exec hw2 (fun t₀ => seqAscBit packOutRegStep (reducedLimbCount t₀))
    s0 hs0_263 hloop).mono
    (fun y ⟨hy0, hy2, _, _, hy_hi, hy_mem, hy_sz⟩ => ?_)
    (by rw [reducedLimbCount_min_three]; change L * 12 + 1 + 9 ≤ 658; omega)
  refine ⟨hy0, ?_, hy_hi, hy_mem, hy_sz⟩
  rw [reducedLimbCount_min_three] at hy2
  rw [hy2, packLimbs_getLimb (reducedChunkBits_pos t) L heval_lt]

/-- Complete parameter-free two-stage hash evaluation program (`BitRAM.Code .standard 280`):
sets `reg 0 = offHash = 4` and evaluates `(Succinct.evalQuotHash U N θ (x.regs 1)).val =
Succinct.hValOfSeed U N θ (x.regs 1)` into `reg 2` in at most `142637` instructions. -/
def evalHashRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 0 offHash))
  (.seq reduceKeyRegCode
  (.seq initLimbsRegCode
  (.seq hornerSetupRegCode
  (.seq hornerRegCode
        packOutRegCode))))

theorem evalHashRegCode_exec {U V w N q : ℕ}
    (hN_pos : 0 < N) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hfit_meta : Fits w (epochMetaWords U w N))
    (θ : Succinct.QuotHashSeed U N)
    (hq : q < 2 ^ quotientBits U N)
    (x : BitRAM.Data 280)
    (hregs : EpochRegs U V w N x)
    (h1 : x.regs 1 = q)
    (hadm_meta : epochMetaWords U w N ≤ x.wordSize w)
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem) :
    BitRAM.DemonicExecWithin w evalHashRegCode x
      (fun y =>
        y.regs 2 = Succinct.hValOfSeed U N θ q ∧
        EpochRegs U V w N y ∧
        (∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      142637 := by
  let w₀ := Succinct.qBits U N
  let b := Succinct.hashB N
  let b' := totalMicroBits N
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  obtain ⟨h245, h246, h247, h248, h249, h250, h251, h252, h253, h254, h255, h256,
    h257, h258, h259, h260, h261, h262, h263, h264, h265, h266, h267, h268, h269⟩ :=
    hregs.active hN_pos
  have hoff_lt_meta : offHash + Succinct.hashSpace U w N ≤ epochMetaWords U w N := by
    rw [epochMetaWords, ite_eq_right (by omega : ¬N = 0)]; unfold offHash; omega
  have hfit_hash : Fits w (offHash + Succinct.hashSpace U w N) :=
    hfit_meta.of_le hoff_lt_meta
  have hadm_hash : offHash + Succinct.hashSpace U w N ≤ x.wordSize w :=
    hoff_lt_meta.trans hadm_meta
  have hw2 : 2 ≤ w := by
    have h8 : 8 ≤ Succinct.hashSpace U w N := Succinct.eight_le_hashSpace U w N
    have hlt : 8 < 2 ^ w := lt_of_le_of_lt (by omega) hfit_hash
    by_contra h
    have hw1 : w ≤ 1 := by omega
    have hpow : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos hw1
    omega
  have hw₀_pos : 0 < w₀ := Succinct.qBits_pos U N
  have hw₀_le : w₀ ≤ w := Succinct.qBits_le_of_le_pow (by omega) hU
  have hb'_le : b' ≤ w := totalMicroBits_le_of_le_pow hNU hU
  have hc_lt : 2 * c < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (Succinct.two_mul_reducedChunkBits_hash_le hw2 hNU hU) hfit_hash
  have hfit_offHash : Fits w offHash := hfit_hash.of_le (by omega)
  have hq_lt_w0 : q < 2 ^ w₀ :=
    lt_of_lt_of_le hq (Succinct.two_pow_quotientBits_le_two_pow_qBits U N)
  unfold evalHashRegCode
  refine .seq (T₁ := 1) (T₂ := 142636)
    (DemonicExecWithin.const (P := fun z => z = x.set 0 offHash) hfit_offHash rfl)
    (fun s0 hs0 => ?_) (Nat.le_of_eq (Nat.add_comm _ _))
  subst hs0
  let s0 := x.set 0 offHash
  have hs0_0 : s0.regs 0 = offHash := by simp [s0]
  have hs0_1 : s0.regs 1 = q := by simp [s0, h1]
  have hs0_adm0 : s0.regs 0 < s0.wordSize w := by
    rw [hs0_0]
    have : 0 < Succinct.hashSpace U w N := by
      have := Succinct.eight_le_hashSpace U w N; omega
    change offHash < x.wordSize w
    omega
  have hs0_α : s0.mem (s0.regs 0) < 2 ^ (w₀ - 1) := by
    rw [hs0_0]; exact hrep_hash.2.1 ▸ θ.1.isLt
  have hs0_u : s0.regs 1 < 2 ^ w₀ := by rw [hs0_1]; exact hq_lt_w0
  refine .seq (T₂ := 142590)
    (reduceKeyRegCode_exec (b := b) hw₀_pos hw₀_le s0 (by simp [s0, h261, w₀])
      (by simp [s0, h262]; rfl) hs0_adm0 hs0_α hs0_u)
    (fun y1 ⟨hy1_0, hy1_1, hy1_3, hy1_hi, hy1_mem, hy1_sz⟩ => ?_)
    (Nat.le_of_eq (Nat.add_comm _ _))
  let u_fin : Fin (2 ^ quotientBits U N) := ⟨q, hq⟩
  let r := multiplyShiftReduced (2 ^ quotientBits U N) w₀ (3 * b) θ.1 u_fin
  have hr_eq : oddMulModWord w₀ (s0.mem (s0.regs 0)) (s0.regs 1) >>> (w₀ - min w₀ (3 * b)) =
      r.val := by
    change oddMulModWord w₀ (x.mem (s0.regs 0)) (s0.regs 1) >>> (w₀ - min w₀ (3 * b)) = r.val
    rw [hs0_0, hrep_hash.2.1, hs0_1, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u_fin
  rw [hr_eq] at hy1_3
  have hr_lt_w : r.val < 2 ^ w :=
    lt_of_lt_of_le r.isLt
      (Nat.pow_le_pow_right two_pos ((Nat.min_le_left w₀ (3 * b)).trans hw₀_le))
  refine .seq (T₂ := 142427)
    (initLimbsRegCode_exec hc_lt hr_lt_w y1 hy1_3
      ((hy1_hi 264 (by decide)).trans (by simp [s0, h264]; rfl))
      ((hy1_hi 265 (by decide)).trans (by simp [s0, h265]; rfl)))
    (fun y2 ⟨hy2_0, hy2_1, hy2_xReg, hy2_accReg, hy2_hi, hy2_mem, hy2_sz⟩ => ?_)
    (Nat.le_of_eq (Nat.add_comm _ _))
  have hy2_hi_x : ∀ j : Fin 280, 240 ≤ j.val → y2.regs j = x.regs j := by
    intro j hj
    rw [hy2_hi j hj, hy1_hi j hj]
    simp [s0, show j ≠ 0 by intro h; subst h; omega]
  refine .seq (T₂ := 142420)
    (hornerSetupRegCode_exec hc_lt y2 (hy2_0.trans (hy1_0.trans hs0_0))
      ((hy2_hi_x 264 (by decide)).trans h264)
      ((hy2_hi_x 265 (by decide)).trans h265)
      ((hy2_hi_x 266 (by decide)).trans h266)
      ((hy2_hi_x 267 (by decide)).trans h267)
      ((hy2_hi_x 268 (by decide)).trans h268)
      ((hy2_hi_x 269 (by decide)).trans h269))
    (fun y3 ⟨hy3_0, hy3_1, hy3_4, hy3_5, hy3_6, hy3_7, hy3_8, hy3_9, hy3_18,
      hy3_hi20, hy3_mem, hy3_sz⟩ => ?_)
    (Nat.le_of_eq (Nat.add_comm _ _))
  have hy3_hi_x : ∀ j : Fin 280, 240 ≤ j.val → y3.regs j = x.regs j :=
    fun j hj => (hy3_hi20 j (by omega)).trans (hy2_hi_x j hj)
  have hy3_mem_x : y3.mem = x.mem := hy3_mem.trans (hy2_mem.trans hy1_mem)
  have hy3_sz_x : y3.bitSize = x.bitSize := hy3_sz.trans (hy2_sz.trans hy1_sz)
  have hy3_consts : ReducedKWise.HornerConsts offHash w w₀ b b' 3 r.val
      (y3.comap embed240Map).toWordRAMData :=
    ⟨hy3_0, hy3_4, hy3_5, hy3_6, hy3_7, hy3_8, hy3_9, hy3_18, fun m hm =>
      (hy3_hi20 (embed240Map (ReducedKWise.xReg m))
        (by dsimp [embed240Map, ReducedKWise.xReg]; omega)).trans (hy2_xReg m hm)⟩
  have hy3_acc0 : ∀ m < L, y3.regs (embed240Map (ReducedKWise.accReg m)) = 0 :=
    fun m hm =>
      (hy3_hi20 (embed240Map (ReducedKWise.accReg m))
        (by dsimp [embed240Map, ReducedKWise.accReg]; omega)).trans (hy2_accReg m hm)
  have hy3_adm : offHash + ReducedKWise.space w w₀ b b' 3 ≤ y3.wordSize w := by
    dsimp only [BitRAM.Data.wordSize]; rw [hy3_sz_x]; exact hadm_hash
  refine .seq (T₂ := 660)
    (hornerRegCode_exec hc_lt hfit_hash θ r y3 hy3_adm
      ((hy3_hi_x 263 (by decide)).trans h263)
      hy3_consts (hy3_mem_x ▸ hrep_hash.1) (hy3_mem_x ▸ hrep_hash.2) hy3_acc0)
    (fun y4 ⟨hy4_0, hy4_acc, hy4_hi, hy4_mem, hy4_sz⟩ => ?_) le_rfl
  have hy4_hi_x : ∀ j : Fin 280, 240 ≤ j.val → y4.regs j = x.regs j :=
    fun j hj => (hy4_hi j hj).trans (hy3_hi_x j hj)
  let evalVal := (trinomialPolyEval t 3 (2 ^ min w₀ (3 * b)) θ.2 r).val
  have heval_lt : evalVal < 2 ^ (L * c) := by
    rw [reducedLimbCount_mul_chunkBits]
    exact (trinomialPolyEval t 3 (2 ^ min w₀ (3 * b)) θ.2 r).isLt
  refine (packOutRegCode_exec hc_lt hb'_le heval_lt y4
    ((hy4_hi_x 249 (by decide)).trans h249)
    ((hy4_hi_x 263 (by decide)).trans h263)
    ((hy4_hi_x 264 (by decide)).trans h264)
    hy4_acc).mono (fun y5 ⟨_, hy5_2, hy5_hi, hy5_mem, hy5_sz⟩ => ?_) le_rfl
  have hy5_hi_x : ∀ j : Fin 280, 240 ≤ j.val → y5.regs j = x.regs j :=
    fun j hj => (hy5_hi j hj).trans (hy4_hi_x j hj)
  refine ⟨?_, hregs.congr_regs (fun j hj1 hj2 => hy5_hi_x j hj1), hy5_hi_x,
    hy5_mem.trans (hy4_mem.trans hy3_mem_x),
    hy5_sz.trans (hy4_sz.trans hy3_sz_x)⟩
  rw [hy5_2]
  have hval := (val_trinomialPolyHash t 3 (2 ^ min w₀ (3 * b)) b' θ.2 r).symm
  dsimp only [Succinct.hValOfSeed, Succinct.evalQuotHash, reducedPolyHash]
  have hmod : q % 2 ^ quotientBits U N = q := Nat.mod_eq_of_lt hq
  have hu_eq : (⟨q % 2 ^ quotientBits U N, Nat.mod_lt _ (by positivity)⟩ :
      Fin (2 ^ quotientBits U N)) = u_fin := Fin.ext hmod
  rw [hu_eq]
  exact hval

end Cslib.DataStructure.Dictionary.BitResizable
