/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.EvalHash

/-!
# Parameter-Free Feistel Splitting, Key Reconstruction, and Slot Resolution on `BitRAM`

This module builds on `EvalHash.lean` and `EpochAccess.lean` to provide parameter-free
`BitRAM.Code .standard 280` subroutines for:
1. One-round Feistel key splitting (`feistelSplitRegCode`) and inverse key reconstruction
   (`feistelReconstructRegCode`).
2. `280`-register dense-item accessors (`readDenseQRegCode`, `readDenseVRegCode`,
   `writeDenseQRegCode`, `writeDenseVRegCode`, `appendDenseRegCode`, `popDenseRegCode`).
3. Physical-to-dense translation (`denseOfPhysRegCode`), bucket cardinality lookup
   (`readBucketCountRegCode`), indexed slot resolution (`resolveIndexedSlotRegCode`), and
   single-step slab/tail slot resolution (`resolveOvfStepRegCode`).
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

/-! ## Section 1: Feistel splitting (`feistelSplitRegCode`) and reconstruction -/

/-- Parameter-free one-round Feistel splitting program (`BitRAM.Code .standard 280`):
given key `u < U` in `reg 270`, writes `q = keyQuotient (bucketBits N) u` into `reg 271`,
`b = feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u` into `reg 272`, and
`m = Succinct.mOfSeed U N θ q` into `reg 273` in at most `142643` instructions. -/
@[expose]
def feistelSplitRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .shiftRight 271 270 245))
  (.seq (.op (.bin .and 272 270 247))
  (.seq (.op (.copy 1 271))
  (.seq evalHashRegCode
  (.seq (.op (.bin .and 273 2 247))
  (.seq (.op (.bin .xor 272 273 272))
        (.op (.bin .shiftRight 273 2 245)))))))

theorem feistelSplitRegCode_exec {U V w N u : ℕ}
    (hN_pos : 0 < N) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hfit_meta : Fits w (epochMetaWords U w N))
    (θ : Succinct.QuotHashSeed U N)
    (hu : u < U)
    (x : BitRAM.Data 280)
    (hregs : EpochRegs U V w N x)
    (h270 : x.regs 270 = u)
    (hadm_meta : epochMetaWords U w N ≤ x.wordSize w)
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem) :
    BitRAM.DemonicExecWithin w feistelSplitRegCode x
      (fun y =>
        let q := keyQuotient (bucketBits N) u
        y.regs 270 = u ∧
        y.regs 271 = q ∧
        y.regs 272 = feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u ∧
        y.regs 273 = Succinct.mOfSeed U N θ q ∧
        EpochRegs U V w N y ∧
        (∀ j : Fin 280, 274 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      142643 := by
  obtain ⟨h245, h246, h247, _⟩ := hregs.active hN_pos
  let q := keyQuotient (bucketBits N) u
  have hq_eq : u >>> bucketBits N = q := Nat.shiftRight_eq_div_pow u (bucketBits N)
  have hq_lt : q < 2 ^ quotientBits U N := keyQuotient_lt_two_pow_quotientBits hNU hu
  have hfit_u : Fits w u := lt_of_lt_of_le hu hU
  have hfit_q : Fits w (u >>> bucketBits N) := hfit_u.of_le (Nat.shiftRight_le u _)
  have hfit_low : Fits w (u &&& (numBuckets N - 1)) := hfit_u.of_le (Nat.and_le_left)
  have hmask_eq : numBuckets N - 1 = 2 ^ bucketBits N - 1 := rfl
  unfold feistelSplitRegCode
  refine dExec_step (DemonicExecWithin.bin (by simpa [BinOp.eval, h270, h245] using hfit_q) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, h270, h247] using hfit_low) rfl) ?_
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  let s1 := ((x.set 271 (x.regs 270 >>> x.regs 245)).set 272 (x.regs 270 &&& x.regs 247)).set 1
    (x.regs 270 >>> x.regs 245)
  have hs1_regs : EpochRegs U V w N s1 :=
    hregs.congr_regs (fun j _ hj2 => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_1 : s1.regs 1 = q := by simp [s1, h270, h245, hq_eq]
  refine .seq (T₂ := 3)
    (evalHashRegCode_exec hN_pos hNU hU hfit_meta θ hq_lt s1 hs1_regs hs1_1 hadm_meta hrep_hash)
    (fun y1 ⟨hy1_2, hy1_regs, hy1_hi, hy1_mem, hy1_sz⟩ => ?_) le_rfl
  have hy1_245 : y1.regs 245 = bucketBits N := (hy1_hi 245 (by decide)).trans (by simp [s1, h245])
  have hy1_247 : y1.regs 247 = numBuckets N - 1 :=
    (hy1_hi 247 (by decide)).trans (by simp [s1, h247])
  have hy1_270 : y1.regs 270 = u := (hy1_hi 270 (by decide)).trans (by simp [s1, h270])
  have hy1_271 : y1.regs 271 = q :=
    (hy1_hi 271 (by decide)).trans (by simp [s1, h270, h245, hq_eq])
  have hy1_272 : y1.regs 272 = u &&& (numBuckets N - 1) :=
    (hy1_hi 272 (by decide)).trans (by simp [s1, h270, h247])
  let hVal := Succinct.hValOfSeed U N θ q
  have hhVal_lt : Fits w hVal := by
    have : hVal < 2 ^ totalMicroBits N := by
      dsimp only [hVal, Succinct.hValOfSeed]; exact (Succinct.evalQuotHash U N θ q).isLt
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right two_pos (totalMicroBits_le_of_le_pow hNU hU))
  have hfit_hlow : Fits w (hVal &&& (numBuckets N - 1)) := hhVal_lt.of_le Nat.and_le_left
  have hfit_b : Fits w ((hVal &&& (numBuckets N - 1)) ^^^ (u &&& (numBuckets N - 1))) := by
    have hb_eq := Succinct.and_mask_xor_eq_feistelBucket (bucketBits N) u hVal
    change (hVal &&& (2 ^ bucketBits N - 1)) ^^^ (u &&& (2 ^ bucketBits N - 1)) < 2 ^ w
    rw [hb_eq]
    have hb_lt : feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u < 2 ^ bucketBits N :=
      feistelBucket_lt (bucketBits N) (Succinct.hValOfSeed U N θ) u
    exact lt_of_lt_of_le hb_lt (Nat.pow_le_pow_right two_pos
      ((bucketBits_le_totalMicroBits N).trans (totalMicroBits_le_of_le_pow hNU hU)))
  have hfit_m : Fits w (hVal >>> bucketBits N) := hhVal_lt.of_le (Nat.shiftRight_le _ _)
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, hy1_2, hy1_247, hVal] using hfit_hlow) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, hy1_2, hy1_247, hy1_272, hVal] using hfit_b) rfl) ?_
  refine DemonicExecWithin.bin
    (by simpa [BinOp.eval, hy1_2, hy1_245, hVal] using hfit_m) ?_
  refine ⟨by simp [hy1_270], by simpa using hy1_271, ?_, ?_, ?_, fun j hj => ?_, hy1_mem, hy1_sz⟩
  · dsimp only [BitRAM.Data.set, BinOp.eval]
    rw [Function.update_of_ne (by decide : (272 : Fin 280) ≠ 273), Function.update_self,
      Function.update_of_ne (by decide : (272 : Fin 280) ≠ 273), Function.update_self,
      hy1_2, hy1_247, hy1_272, hmask_eq]
    exact Succinct.and_mask_xor_eq_feistelBucket (bucketBits N) u hVal
  · dsimp only [BitRAM.Data.set, BinOp.eval, Succinct.mOfSeed]
    rw [Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 280) ≠ 272),
      Function.update_of_ne (by decide : (2 : Fin 280) ≠ 273),
      Function.update_of_ne (by decide : (245 : Fin 280) ≠ 272),
      Function.update_of_ne (by decide : (245 : Fin 280) ≠ 273),
      hy1_2, hy1_245, Nat.shiftRight_eq_div_pow]
  · exact hy1_regs.congr_regs (fun j _ hj2 => by
      dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  · dsimp only [BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    rw [hy1_hi j (by omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Parameter-free one-round Feistel key reconstruction (`BitRAM.Code .standard 280`):
given quotient `q < 2 ^ quotientBits U N` in `reg 271` and bucket `b < numBuckets N` in `reg 272`,
writes `u = feistelReconstruct (bucketBits N) (Succinct.hValOfSeed U N θ) b q` into `reg 270` and
`m = Succinct.mOfSeed U N θ q` into `reg 273` in at most `142644` instructions. -/
@[expose]
def feistelReconstructRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 1 271))
  (.seq evalHashRegCode
  (.seq (.op (.bin .and 273 2 247))
  (.seq (.op (.bin .and 270 272 247))
  (.seq (.op (.bin .xor 270 273 270))
  (.seq (.op (.bin .shiftLeft 273 271 245))
  (.seq (.op (.bin .add 270 273 270))
        (.op (.bin .shiftRight 273 2 245))))))))

theorem feistelReconstructRegCode_exec {U V w N b q : ℕ}
    (hN_pos : 0 < N) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hfit_meta : Fits w (epochMetaWords U w N))
    (θ : Succinct.QuotHashSeed U N)
    (_hb : b < numBuckets N)
    (hq : q < 2 ^ quotientBits U N)
    (x : BitRAM.Data 280)
    (hregs : EpochRegs U V w N x)
    (h271 : x.regs 271 = q)
    (h272 : x.regs 272 = b)
    (hadm_meta : epochMetaWords U w N ≤ x.wordSize w)
    (hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem) :
    BitRAM.DemonicExecWithin w feistelReconstructRegCode x
      (fun y =>
        y.regs 270 = feistelReconstruct (bucketBits N) (Succinct.hValOfSeed U N θ) b q ∧
        y.regs 271 = q ∧
        y.regs 272 = b ∧
        y.regs 273 = Succinct.mOfSeed U N θ q ∧
        EpochRegs U V w N y ∧
        (∀ j : Fin 280, 274 ≤ j.val → y.regs j = x.regs j) ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize)
      142644 := by
  obtain ⟨h245, _, h247, _⟩ := hregs.active hN_pos
  unfold feistelReconstructRegCode
  refine dExec_step (DemonicExecWithin.copy rfl) ?_
  let s1 := x.set 1 (x.regs 271)
  have hs1_regs : EpochRegs U V w N s1 :=
    hregs.congr_regs (fun j hj1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  have hs1_1 : s1.regs 1 = q := by simp [s1, h271]
  refine .seq (T₂ := 6)
    (evalHashRegCode_exec hN_pos hNU hU hfit_meta θ hq s1 hs1_regs hs1_1 hadm_meta hrep_hash)
    (fun y1 ⟨hy1_2, hy1_regs, hy1_hi, hy1_mem, hy1_sz⟩ => ?_) le_rfl
  have hy1_245 : y1.regs 245 = bucketBits N := (hy1_hi 245 (by decide)).trans (by simp [s1, h245])
  have hy1_247 : y1.regs 247 = numBuckets N - 1 :=
    (hy1_hi 247 (by decide)).trans (by simp [s1, h247])
  have hy1_271 : y1.regs 271 = q := (hy1_hi 271 (by decide)).trans (by simp [s1, h271])
  have hy1_272 : y1.regs 272 = b := (hy1_hi 272 (by decide)).trans (by simp [s1, h272])
  let hVal := Succinct.hValOfSeed U N θ q
  have hB_le_w : bucketBits N ≤ w :=
    (bucketBits_le_totalMicroBits N).trans (totalMicroBits_le_of_le_pow hNU hU)
  have hhVal_lt : Fits w hVal := by
    have : hVal < 2 ^ totalMicroBits N := by
      dsimp only [hVal, Succinct.hValOfSeed]; exact (Succinct.evalQuotHash U N θ q).isLt
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right two_pos (totalMicroBits_le_of_le_pow hNU hU))
  have hmask_eq : numBuckets N - 1 = 2 ^ bucketBits N - 1 := rfl
  have hhlow_eq : hVal &&& (numBuckets N - 1) = hVal % 2 ^ bucketBits N := by
    rw [hmask_eq, Nat.and_two_pow_sub_one_eq_mod]
  have hblow_eq : b &&& (numBuckets N - 1) = b % 2 ^ bucketBits N := by
    rw [hmask_eq, Nat.and_two_pow_sub_one_eq_mod]
  have hxor_lt : ((hVal &&& (numBuckets N - 1)) ^^^ (b &&& (numBuckets N - 1))) <
      2 ^ bucketBits N := by
    rw [hhlow_eq, hblow_eq]
    exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
  have hsh_eq : q <<< bucketBits N = q * 2 ^ bucketBits N := Nat.shiftLeft_eq q (bucketBits N)
  have hrec_lt : q * 2 ^ bucketBits N +
      ((hVal &&& (numBuckets N - 1)) ^^^ (b &&& (numBuckets N - 1))) < 2 ^ w := by
    have hsum_bits := quotientBits_add_bucketBits hNU
    have hkw : keyBits U ≤ w := keyBits_le_of_le_pow hU
    have hmul : (q + 1) * 2 ^ bucketBits N ≤ 2 ^ quotientBits U N * 2 ^ bucketBits N :=
      Nat.mul_le_mul_right _ hq
    rw [Nat.add_one_mul, ← Nat.pow_add, hsum_bits] at hmul
    have hlt_key : q * 2 ^ bucketBits N +
        ((hVal &&& (numBuckets N - 1)) ^^^ (b &&& (numBuckets N - 1))) < 2 ^ keyBits U := by omega
    exact lt_of_lt_of_le hlt_key (Nat.pow_le_pow_right two_pos hkw)
  have hfit_hlow : Fits w (hVal &&& (numBuckets N - 1)) := hhVal_lt.of_le Nat.and_le_left
  have hfit_blow : Fits w (b &&& (numBuckets N - 1)) :=
    lt_of_lt_of_le (by rw [hblow_eq]; exact Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right two_pos hB_le_w)
  have hfit_xor : Fits w ((hVal &&& (numBuckets N - 1)) ^^^ (b &&& (numBuckets N - 1))) :=
    lt_of_lt_of_le hxor_lt (Nat.pow_le_pow_right two_pos hB_le_w)
  have hfit_sh : Fits w (q <<< bucketBits N) := by
    rw [hsh_eq]; exact Fits.of_le hrec_lt (Nat.le_add_right _ _)
  have hfit_add : Fits w ((q <<< bucketBits N) +
      ((hVal &&& (numBuckets N - 1)) ^^^ (b &&& (numBuckets N - 1)))) := by
    rwa [hsh_eq]
  have hfit_m : Fits w (hVal >>> bucketBits N) := hhVal_lt.of_le (Nat.shiftRight_le _ _)
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, hy1_2, hy1_247, hVal] using hfit_hlow) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, hy1_272, hy1_247] using hfit_blow) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, hy1_2, hy1_272, hy1_247, hVal] using hfit_xor) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin (by simpa [BinOp.eval, hy1_271, hy1_245] using hfit_sh) rfl) ?_
  refine dExec_step
    (DemonicExecWithin.bin
      (by simpa [BinOp.eval, hy1_2, hy1_271, hy1_272, hy1_245, hy1_247, hVal] using hfit_add)
      rfl) ?_
  refine DemonicExecWithin.bin
    (by simpa [BinOp.eval, hy1_2, hy1_245, hVal] using hfit_m) ?_
  refine ⟨?_, by simpa using hy1_271, by simpa using hy1_272, ?_, ?_, fun j hj => ?_,
    hy1_mem, hy1_sz⟩
  · dsimp only [BitRAM.Data.set, BinOp.eval, feistelReconstruct]
    dsimp only [hVal] at hhlow_eq
    rw [Function.update_of_ne (by decide : (270 : Fin 280) ≠ 273), Function.update_self]
    simp only [Fin.isValue, Function.update_self,
      Function.update_of_ne (by decide : (273 : Fin 280) ≠ 270),
      Function.update_of_ne (by decide : (270 : Fin 280) ≠ 273),
      Function.update_of_ne (by decide : (271 : Fin 280) ≠ 270),
      Function.update_of_ne (by decide : (271 : Fin 280) ≠ 273),
      Function.update_of_ne (by decide : (245 : Fin 280) ≠ 270),
      Function.update_of_ne (by decide : (245 : Fin 280) ≠ 273),
      Function.update_of_ne (by decide : (272 : Fin 280) ≠ 273),
      Function.update_of_ne (by decide : (247 : Fin 280) ≠ 273),
      hy1_2, hy1_271, hy1_272, hy1_245, hy1_247, hsh_eq, hhlow_eq, hblow_eq]
  · dsimp only [BitRAM.Data.set, BinOp.eval, Succinct.mOfSeed]
    rw [Function.update_self]
    simp only [Fin.isValue,
      Function.update_of_ne (by decide : (2 : Fin 280) ≠ 270),
      Function.update_of_ne (by decide : (2 : Fin 280) ≠ 273),
      Function.update_of_ne (by decide : (245 : Fin 280) ≠ 270),
      Function.update_of_ne (by decide : (245 : Fin 280) ≠ 273),
      hy1_2, hy1_245, Nat.shiftRight_eq_div_pow]
  · exact hy1_regs.congr_regs (fun j _ hj2 => by
      dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  · dsimp only [BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    rw [hy1_hi j (by omega)]
    dsimp only [s1, BitRAM.Data.set]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-! ## Section 2: `GlobalMeta` Base Computation, `denseOfPhys`, and Slot Resolution -/

theorem dExec_branch_pos {r w : ℕ} {cond : Cond r} {c₁ c₂ : BitRAM.Code .standard r}
    {x : BitRAM.Data r} {P : BitRAM.Data r → Prop} {T : ℕ}
    (hc : CondHolds cond x)
    (h : BitRAM.DemonicExecWithin w c₁ x P T) :
    BitRAM.DemonicExecWithin w (.branch cond c₁ c₂) x P (T + 1) :=
  DemonicExecWithin.branch_pos hc h le_rfl

theorem dExec_branch_neg {r w : ℕ} {cond : Cond r} {c₁ c₂ : BitRAM.Code .standard r}
    {x : BitRAM.Data r} {P : BitRAM.Data r → Prop} {T : ℕ}
    (hc : ¬CondHolds cond x)
    (h : BitRAM.DemonicExecWithin w c₂ x P T) :
    BitRAM.DemonicExecWithin w (.branch cond c₁ c₂) x P (T + 2) :=
  DemonicExecWithin.branch_neg hc h le_rfl

theorem mul_le_packedWords_mul (M k w : ℕ) (hw : 0 < w) :
    M * k ≤ packedWords M k w * w := by
  unfold packedWords
  have hdiv := Nat.div_add_mod (M * k + w - 1) w
  have hmod : (M * k + w - 1) % w < w := Nat.mod_lt _ hw
  rw [Nat.mul_comm w] at hdiv
  rw [Nat.add_mul]
  omega

theorem fits_of_le_globalMetaLen_of_bitSize {U w N v : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hx : x.WellFormed w)
    (hsz : epochMetaBits U w N ≤ x.bitSize) (hv : v ≤ globalMetaLen N) :
    Fits w v := by
  have hk_pos : 1 ≤ globalPtrBits N := by
    have := lt_two_pow_globalPtrBits N
    by_contra hk0
    have hk0' : globalPtrBits N = 0 := by omega
    rw [hk0', pow_zero] at this
    omega
  have h1 : globalMetaLen N ≤ globalMetaLen N * globalPtrBits N :=
    Nat.le_mul_of_pos_right _ hk_pos
  have h2 : globalMetaLen N * globalPtrBits N ≤
      packedWords (globalMetaLen N) (globalPtrBits N) w * w :=
    mul_le_packedWords_mul _ _ w hw
  have h3 : packedWords (globalMetaLen N) (globalPtrBits N) w ≤ epochMetaWords U w N := by
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT offTD
    omega
  have h4 : packedWords (globalMetaLen N) (globalPtrBits N) w * w ≤ epochMetaBits U w N :=
    Nat.mul_le_mul_right w h3
  have hfits_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  exact Fits.of_le hfits_bs (by omega)

theorem fits_of_le_N {U w N v : ℕ} (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hv : v ≤ max N 1) : Fits w v := by
  have h2 : 2 ≤ 2 ^ w := Nat.le_self_pow (by omega) 2
  change v < 2 ^ w
  omega

/-- Compute the 6 `GlobalMeta` geometry parameters for the multi-bucket regime (`0 < bucketBits N`)
from `EpochRegs` (`246 = numBuckets N`, `250 = slabSize N`, `251 = effBucketCap N`,
`253 = maxTailItems N`) into registers `20..25`:
* `r20 = dirSlabsPerBucket N`
* `r21 = tailCapPerBucket N`
* `r22 = gmSlabDirBase N`
* `r23 = gmTailPtrBase N`
* `r24 = gmTailOwnerBase N`
* `r25 = gmSlabMetaBase N` -/
@[expose]
def computeGMBasesRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .div 20 251 250))
    (.seq (.op (.const 21 2))
      (.seq (.op (.bin .mul 21 21 250))
        (.seq (.op (.const 22 3))
          (.seq (.op (.bin .mul 22 22 246))
            (.seq (.op (.const 23 4))
              (.seq (.op (.bin .add 22 23 22))
                (.seq (.op (.bin .mul 23 246 20))
                  (.seq (.op (.bin .add 23 22 23))
                    (.seq (.op (.bin .add 24 23 253))
                      (.op (.bin .add 25 24 253)))))))))))

theorem computeGMBasesRegCode_exec {U V w N : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w computeGMBasesRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 20 = dirSlabsPerBucket N ∧
        y.regs 21 = tailCapPerBucket N ∧
        y.regs 22 = Succinct.gmSlabDirBase N ∧
        y.regs 23 = Succinct.gmTailPtrBase N ∧
        y.regs 24 = Succinct.gmTailOwnerBase N ∧
        y.regs 25 = Succinct.gmSlabMetaBase N ∧
        (∀ r : Fin 280, (r.val < 20 ∨ 26 ≤ r.val) → y.regs r = x.regs r)) 11 := by
  have hact := her.active hN_pos
  have hr246 : x.regs 246 = numBuckets N := hact.2.1
  have hr250 : x.regs 250 = slabSize N := hact.2.2.2.2.2.1
  have hr251 : x.regs 251 = effBucketCap N := hact.2.2.2.2.2.2.1
  have hr253 : x.regs 253 = maxTailItems N := hact.2.2.2.2.2.2.2.2.1
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hdir_eq : effBucketCap N / slabSize N = dirSlabsPerBucket N := by
    rw [Succinct.effBucketCap_eq_dirSlabs_mul_slabSize hb_pos, Nat.mul_div_cancel _ hK_pos]
  have htail_eq : 2 * slabSize N = tailCapPerBucket N := by
    unfold tailCapPerBucket; rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
  have hmeta_le : 4 + 3 * numBuckets N + numBuckets N * dirSlabsPerBucket N +
      maxTailItems N + maxTailItems N ≤ globalMetaLen N := by
    unfold globalMetaLen globalMetaVarLen maxTailItems
    rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
    linarith
  have hfit_le : ∀ v ≤ 4 + 3 * numBuckets N + numBuckets N * dirSlabsPerBucket N +
      maxTailItems N + maxTailItems N, Fits w v := fun v hv =>
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz (hv.trans hmeta_le)
  have hB_pos : 1 ≤ numBuckets N := numBuckets_pos N
  have hdir_le : dirSlabsPerBucket N ≤ 4 + 3 * numBuckets N +
      numBuckets N * dirSlabsPerBucket N + maxTailItems N + maxTailItems N := by
    have : 1 * dirSlabsPerBucket N ≤ numBuckets N * dirSlabsPerBucket N :=
      Nat.mul_le_mul_right _ hB_pos
    omega
  have htail_le : tailCapPerBucket N ≤ 4 + 3 * numBuckets N +
      numBuckets N * dirSlabsPerBucket N + maxTailItems N + maxTailItems N := by
    have : 1 * tailCapPerBucket N ≤ numBuckets N * tailCapPerBucket N :=
      Nat.mul_le_mul_right _ hB_pos
    unfold maxTailItems
    omega
  have hdirBase_le : 4 + 3 * numBuckets N ≤ 4 + 3 * numBuckets N +
      numBuckets N * dirSlabsPerBucket N + maxTailItems N + maxTailItems N := by omega
  have hptrBase_le : 4 + 3 * numBuckets N + numBuckets N * dirSlabsPerBucket N ≤
      4 + 3 * numBuckets N + numBuckets N * dirSlabsPerBucket N +
        maxTailItems N + maxTailItems N := by omega
  have hownBase_le : 4 + 3 * numBuckets N + numBuckets N * dirSlabsPerBucket N + maxTailItems N ≤
      4 + 3 * numBuckets N + numBuckets N * dirSlabsPerBucket N +
        maxTailItems N + maxTailItems N := by omega
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr251, hr250, Nat.ne_of_gt hK_pos, hdir_eq] using hfit_le _ hdir_le)
    rfl) ?_
  refine dExec_step (DemonicExecWithin.const (hfit_le 2 (by omega)) rfl) ?_
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr250, htail_eq] using hfit_le _ htail_le) rfl) ?_
  refine dExec_step (DemonicExecWithin.const (hfit_le 3 (by omega)) rfl) ?_
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr246] using hfit_le (3 * numBuckets N) (by omega)) rfl) ?_
  refine dExec_step (DemonicExecWithin.const (hfit_le 4 (by omega)) rfl) ?_
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr246] using hfit_le _ hdirBase_le) rfl) ?_
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr246, hr251, hr250, hdir_eq] using
      hfit_le (numBuckets N * dirSlabsPerBucket N) (by omega))
    rfl) ?_
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr246, hr251, hr250, hdir_eq] using hfit_le _ hptrBase_le) rfl) ?_
  refine dExec_step (DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr246, hr251, hr250, hr253, hdir_eq] using hfit_le _ hownBase_le) rfl) ?_
  refine DemonicExecWithin.bin
    (by simpa [BinOp.eval, hr246, hr251, hr250, hr253, hdir_eq] using hfit_le _ le_rfl) ?_
  let s_end :=
    (((((((((((x.set 20 (x.regs 251 / x.regs 250)).set 21 2).set 21
      (2 * x.regs 250)).set 22 3).set 22 (3 * x.regs 246)).set 23 4).set 22
      (4 + 3 * x.regs 246)).set 23 (x.regs 246 * (x.regs 251 / x.regs 250))).set 23
      (4 + 3 * x.regs 246 + x.regs 246 * (x.regs 251 / x.regs 250))).set 24
      (4 + 3 * x.regs 246 + x.regs 246 * (x.regs 251 / x.regs 250) + x.regs 253)).set 25
      (4 + 3 * x.regs 246 + x.regs 246 * (x.regs 251 / x.regs 250) + x.regs 253 +
        x.regs 253))
  have hs_end_wf : s_end.WellFormed w :=
    wf_set 25 (wf_set 24 (wf_set 23 (wf_set 23 (wf_set 22 (wf_set 23 (wf_set 22 (wf_set 22
      (wf_set 21 (wf_set 21 (wf_set 20 hx
        (by simpa [hr251, hr250, hdir_eq] using hfit_le _ hdir_le))
        (hfit_le 2 (by omega)))
        (by simpa [hr250, htail_eq] using hfit_le _ htail_le))
        (hfit_le 3 (by omega)))
        (by simpa [hr246] using hfit_le (3 * numBuckets N) (by omega)))
        (hfit_le 4 (by omega)))
        (by simpa [hr246] using hfit_le _ hdirBase_le))
        (by simpa [hr246, hr251, hr250, hdir_eq] using
          hfit_le (numBuckets N * dirSlabsPerBucket N) (by omega)))
        (by simpa [hr246, hr251, hr250, hdir_eq] using hfit_le _ hptrBase_le))
        (by simpa [hr246, hr251, hr250, hr253, hdir_eq] using hfit_le _ hownBase_le))
        (by simpa [hr246, hr251, hr250, hr253, hdir_eq] using hfit_le _ le_rfl)
  refine ⟨rfl, hs_end_wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact her.congr_regs (fun r hr1 _ => by
      dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  · simp [BitRAM.Data.set, BinOp.eval, hr251, hr250, hdir_eq]
  · simp [BitRAM.Data.set, BinOp.eval, hr250, htail_eq]
  · simp [BitRAM.Data.set, BinOp.eval, hr246, Succinct.gmSlabDirBase]
  · simp [BitRAM.Data.set, BinOp.eval, hr246, hr251, hr250, hdir_eq,
      Succinct.gmTailPtrBase, Succinct.gmSlabDirBase]
  · simp [BitRAM.Data.set, BinOp.eval, hr246, hr251, hr250, hr253, hdir_eq,
      Succinct.gmTailOwnerBase, Succinct.gmTailPtrBase, Succinct.gmSlabDirBase]
  · simp [BitRAM.Data.set, BinOp.eval, hr246, hr251, hr250, hr253, hdir_eq,
      Succinct.gmSlabMetaBase, Succinct.gmTailOwnerBase, Succinct.gmTailPtrBase,
      Succinct.gmSlabDirBase]
  · intro r hr
    dsimp only [BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Parameter-free `BitRAM.Code .standard 280` program mapping a physical slot `phys = x.regs 14`
to its dense item index `r15 = denseOfPhys N gm td phys`, preserving `r14` and all registers
`≥ 20`. -/
@[expose]
def denseOfPhysRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 0))
    (.branch (.eq 245 12)
      (.op (.copy 15 14))
      (.seq (readGMRegCode 12 16)
        (.seq (.op (.bin .mul 16 16 250))
          (.branch (.lt 14 16)
            (.op (.copy 15 14))
            (.seq (.op (.const 12 1))
              (.seq (.op (.load 17 12))
                (.seq (.op (.bin .sub 17 17 12))
                  (.seq (.op (.bin .sub 17 17 14))
                    (.seq (readTDRegCode 17 18)
                      (.seq (.op (.bin .add 18 18 253))
                        (.seq (.op (.bin .mod 19 16 253))
                          (.seq (.op (.bin .sub 18 18 19))
                            (.seq (.op (.bin .mod 18 18 253))
                              (.op (.bin .add 15 16 18)))))))))))))))

theorem denseOfPhysRegCode_exec {U V w N phys : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hr14 : x.regs 14 = phys)
    (hphys_lt : phys < N)
    (htail_valid : 0 < bucketBits N →
      gmAtBit U w N x.mem 0 * slabSize N ≤ phys →
      N - 1 - phys < gmAtBit U w N x.mem 1) :
    BitRAM.DemonicExecWithin w denseOfPhysRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 15 = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem) phys ∧
        y.regs 14 = phys ∧
        (∀ r : Fin 280, 20 ≤ r.val → y.regs r = x.regs r)) 105 := by
  have hact := her.active hN_pos
  have hr245 : x.regs 245 = bucketBits N := hact.1
  have hr250 : x.regs 250 = slabSize N := hact.2.2.2.2.2.1
  have hr253 : x.regs 253 = maxTailItems N := hact.2.2.2.2.2.2.2.2.1
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  refine dExec_step (DemonicExecWithin.const hfit0 rfl) ?_
  let s1 := x.set 12 0
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit0
  have hs1_er : EpochRegs U V w N s1 := her.set_of_outside (by decide) 0
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hc : CondHolds (.eq 245 12) s1 := by
      simp [CondHolds, BitRAM.Data.toWordRAMData, s1, BitRAM.Data.set, hr245, hb0]
    refine (dExec_branch_pos hc (DemonicExecWithin.copy ?_)).mono (fun _ h => h) (by omega)
    refine ⟨rfl, wf_set 15 hs1_wf (hs1_wf.regs_fits 14),
      hs1_er.set_of_outside (by decide) (s1.regs 14),
      ?_, by simp [s1, BitRAM.Data.set, hr14], fun r hr => ?_⟩
    · simp [denseOfPhys, hb0, s1, BitRAM.Data.set, hr14]
    · dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  · have hc : ¬CondHolds (.eq 245 12) s1 := by
      simp [CondHolds, BitRAM.Data.toWordRAMData, s1, BitRAM.Data.set, hr245, Nat.ne_of_gt hb_pos]
    refine dExec_branch_neg hc ?_
    have h0_lt_gm : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    refine .seq (T₂ := 57) (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er h0_lt_gm
      rfl hsz)
      (fun y1 ⟨hy1_st, hy1_wf, hy1_16, hy1_regs⟩ => ?_) (by omega)
    have hy1_er : EpochRegs U V w N y1 := hs1_er.congr_regs (fun r hr1 _ =>
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
    have hy1_14 : y1.regs 14 = phys := by
      rw [hy1_regs 14 (by decide) (by decide)]; simp [BitRAM.Data.set, hr14]
    have hy1_250 : y1.regs 250 = slabSize N := (hy1_er.active hN_pos).2.2.2.2.2.1
    have hy1_253 : y1.regs 253 = maxTailItems N := (hy1_er.active hN_pos).2.2.2.2.2.2.2.2.1
    have htot_le : gmAtBit U w N x.mem 0 * slabSize N + gmAtBit U w N x.mem 1 ≤ N :=
      hslot.multi_total_le hb_pos
    have hfit_base : Fits w (gmAtBit U w N x.mem 0 * slabSize N) :=
      fits_of_le_N hw hnU hU (by omega)
    have hy1_16' : y1.regs 16 = gmAtBit U w N x.mem 0 := hy1_16
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, hy1_16', hy1_250] using hfit_base) rfl) ?_
    let s2 := y1.set 16 (y1.regs 16 * y1.regs 250)
    have hs2_wf : s2.WellFormed w :=
      wf_set 16 hy1_wf (by simpa [hy1_16', hy1_250] using hfit_base)
    have hs2_er : EpochRegs U V w N s2 := hy1_er.set_of_outside (by decide) _
    have hs2_16 : s2.regs 16 = gmAtBit U w N x.mem 0 * slabSize N := by
      simp [s2, BitRAM.Data.set, hy1_16', hy1_250]
    have hs2_14 : s2.regs 14 = phys := by
      dsimp only [s2, BitRAM.Data.set]; rw [Function.update_of_ne (by decide)]; exact hy1_14
    by_cases hlt : phys < gmAtBit U w N x.mem 0 * slabSize N
    · have hc2 : CondHolds (.lt 14 16) s2 := by
        simp [CondHolds, BitRAM.Data.toWordRAMData, hs2_14, hs2_16, hlt]
      refine (dExec_branch_pos hc2 (DemonicExecWithin.copy ?_)).mono (fun _ h => h) (by omega)
      refine ⟨hy1_st, wf_set 15 hs2_wf (hs2_wf.regs_fits 14),
        hs2_er.set_of_outside (by decide) (s2.regs 14),
        ?_, by simp [BitRAM.Data.set, hs2_14], fun r hr => ?_⟩
      · simp [denseOfPhys, Nat.ne_of_gt hb_pos, hlt, BitRAM.Data.set, hs2_14]
      · dsimp only [s2, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
          Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega),
          hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    · have hc2 : ¬CondHolds (.lt 14 16) s2 := by
        simp [CondHolds, BitRAM.Data.toWordRAMData, hs2_14, hs2_16, hlt]
      refine dExec_branch_neg hc2 ?_
      have ht_lt_gm1 : N - 1 - phys < gmAtBit U w N x.mem 1 :=
        htail_valid hb_pos (Nat.le_of_not_lt hlt)
      have hntails_le : gmAtBit U w N x.mem 1 ≤ maxTailItems N :=
        (hslot.multi_tail hb_pos).ntails_le
      have ht_lt_M : N - 1 - phys < maxTailItems N := lt_of_lt_of_le ht_lt_gm1 hntails_le
      have hM_pos : 0 < maxTailItems N := by omega
      have hfit1 : Fits w 1 := fits_of_le_N hw hnU hU (by omega)
      have hy1_ws : epochMetaWords U w N ≤ y1.wordSize w :=
        epochMetaWords_le_wordSize_of_bitSize hw
          (by change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
              rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz)
      have hadm1 : 1 < y1.wordSize w := by
        have h4 : 4 ≤ epochMetaWords U w N := by
          unfold epochMetaWords; rw [ite_eq_right (Nat.ne_of_gt hN_pos)]; omega
        omega
      have hy1_mem1 : y1.mem 1 = N := by
        have : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
        rw [this, hm1]
      have hs2_mem1 : s2.mem 1 = N := hy1_mem1
      refine dExec_step (DemonicExecWithin.const hfit1 rfl) ?_
      refine dExec_step (DemonicExecWithin.load hadm1 rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy1_mem1] using
          fits_of_le_N hw hnU hU (show N - 1 ≤ max N 1 by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy1_mem1, hy1_14] using
          fits_of_le_N hw hnU hU (show N - 1 - phys ≤ max N 1 by omega)) rfl) ?_
      let s3 := (((s2.set 12 1).set 17 (s2.mem 1)).set 17 (s2.mem 1 - 1)).set 17
        (s2.mem 1 - 1 - s2.regs 14)
      have hs3_wf : s3.WellFormed w :=
        wf_set 17 (wf_set 17 (wf_set 17 (wf_set 12 hs2_wf hfit1)
          (hs2_wf.mem_wf.mem_fits 1))
          (by rw [hs2_mem1]; exact fits_of_le_N hw hnU hU (by omega)))
          (by rw [hs2_mem1, hs2_14]; exact fits_of_le_N hw hnU hU (by omega))
      have hs3_er : EpochRegs U V w N s3 := hs2_er.congr_regs (fun r hr1 _ => by
        dsimp only [s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      have hs3_17 : s3.regs 17 = N - 1 - phys := by
        simp [s3, BitRAM.Data.set, hs2_mem1, hs2_14]
      have hs3_sz : epochMetaBits U w N ≤ s3.bitSize := by
        change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
        rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
      refine .seq (T₂ := 5) (readTDRegCode_exec (by decide) hw hN_pos hnU hU hs3_wf hs3_er ht_lt_M
        hs3_17 hs3_sz)
        (fun y2 ⟨hy2_st, hy2_wf, hy2_18, hy2_regs⟩ => ?_) (by omega)
      have hy2_er : EpochRegs U V w N y2 := hs3_er.congr_regs (fun r hr1 _ =>
        hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
      have hy2_mem : y2.mem = x.mem := by
        calc y2.mem = s3.mem := congrArg BitMemory.State.mem hy2_st
          _ = y1.mem := rfl
          _ = x.mem := congrArg BitMemory.State.mem hy1_st
      have hy2_18' : y2.regs 18 = tdAtBit U w N x.mem (N - 1 - phys) := by
        rw [hy2_18]
        exact congrArg (fun m => tdAtBit U w N m (N - 1 - phys))
          (congrArg BitMemory.State.mem hy1_st)
      have hy2_16 : y2.regs 16 = gmAtBit U w N x.mem 0 * slabSize N := by
        rw [hy2_regs 16 (by decide) (by decide)]
        dsimp only [s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by decide)]
        exact hs2_16
      have hy2_14 : y2.regs 14 = phys := by
        rw [hy2_regs 14 (by decide) (by decide)]
        dsimp only [s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by decide)]
        exact hs2_14
      have hy2_253 : y2.regs 253 = maxTailItems N := (hy2_er.active hN_pos).2.2.2.2.2.2.2.2.1
      let c := tdAtBit U w N x.mem (N - 1 - phys)
      let base_tail := gmAtBit U w N x.mem 0 * slabSize N
      have hc_lt : c < maxTailItems N := htd.td_lt (N - 1 - phys) ht_lt_gm1
      have hcM_le : c + maxTailItems N ≤ globalMetaLen N := by
        have hc_lt' : c < numBuckets N * tailCapPerBucket N := hc_lt
        unfold globalMetaLen globalMetaVarLen maxTailItems
        rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
        have h2M : 2 * (numBuckets N * tailCapPerBucket N) ≤
            numBuckets N * (3 + dirSlabsPerBucket N + 2 * tailCapPerBucket N) := by
          calc 2 * (numBuckets N * tailCapPerBucket N)
              = numBuckets N * (2 * tailCapPerBucket N) := by ring
            _ ≤ numBuckets N * (3 + dirSlabsPerBucket N + 2 * tailCapPerBucket N) :=
                Nat.mul_le_mul_left _ (by omega)
        omega
      have hfit_cM : Fits w (c + maxTailItems N) :=
        fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hcM_le
      have hfit_mod1 : Fits w (base_tail % maxTailItems N) :=
        Fits.of_le hfit_cM (le_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hM_pos) (by omega)))
      have hfit_sub : Fits w (c + maxTailItems N - base_tail % maxTailItems N) :=
        Fits.of_le hfit_cM (Nat.sub_le _ _)
      have hfit_mod2 :
          Fits w ((c + maxTailItems N - base_tail % maxTailItems N) % maxTailItems N) :=
        Fits.of_le hfit_cM (le_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hM_pos) (by omega)))
      have hdense_lt :
          denseOfCirc (maxTailItems N) base_tail c < base_tail + gmAtBit U w N x.mem 1 :=
        htd.dense_lt (N - 1 - phys) ht_lt_gm1
      have hdense_eq :
          base_tail + (c + maxTailItems N - base_tail % maxTailItems N) % maxTailItems N =
            denseOfCirc (maxTailItems N) base_tail c := by
        unfold denseOfCirc; rw [ite_eq_right (Nat.ne_of_gt hM_pos)]
      have hfit_res : Fits w (base_tail +
          (c + maxTailItems N - base_tail % maxTailItems N) % maxTailItems N) := by
        rw [hdense_eq]
        exact fits_of_le_N hw hnU hU (by omega)
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, hy2_18', hy2_253, c] using hfit_cM) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_16, hy2_253, Nat.ne_of_gt hM_pos, base_tail]
          using hfit_mod1) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_18', hy2_16, hy2_253, c, base_tail]
          using hfit_sub) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_18', hy2_16, hy2_253, Nat.ne_of_gt hM_pos,
          c, base_tail] using hfit_mod2) rfl) ?_
      refine DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_18', hy2_16, hy2_253, c, base_tail]
          using hfit_res) ?_
      refine ⟨hy2_st.trans hy1_st, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
      · exact wf_set 15 (wf_set 18 (wf_set 18 (wf_set 19 (wf_set 18 hy2_wf
          (by simpa [hy2_18', hy2_253, c] using hfit_cM))
          (by simpa [BitRAM.Data.set, hy2_16, hy2_253, base_tail] using hfit_mod1))
          (by simpa [BitRAM.Data.set, hy2_18', hy2_16, hy2_253, c, base_tail] using hfit_sub))
          (by simpa [BitRAM.Data.set, hy2_18', hy2_16, hy2_253, c, base_tail] using hfit_mod2))
          (by simpa [BitRAM.Data.set, hy2_18', hy2_16, hy2_253, c, base_tail] using hfit_res)
      · exact hy2_er.congr_regs (fun r hr1 _ => by
          dsimp only [BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      · dsimp only [denseOfPhys]
        rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_right hlt, ← hdense_eq]
        simp [BitRAM.Data.set, BinOp.eval, hy2_18', hy2_16, hy2_253, c, base_tail]
      · simp [BitRAM.Data.set, hy2_14]
      · dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s3, s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s1, BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Parameter-free `BitRAM.Code .standard 280` program reading `bCount N gm b` (`b = x.regs 272`)
into `r14`, preserving all registers `≥ 20`. -/
@[expose]
def readBucketCountRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 0))
    (.branch (.eq 245 12)
      (readGMRegCode 12 14)
      (.seq (.op (.const 12 3))
        (.seq (.op (.bin .mul 12 12 272))
          (.seq (.op (.const 13 4))
            (.seq (.op (.bin .add 12 13 12))
              (.seq (readGMRegCode 12 14)
                (.seq (.op (.const 13 1))
                  (.seq (.op (.bin .add 12 12 13))
                    (.seq (readGMRegCode 12 15)
                      (.seq (.op (.bin .mul 14 14 250))
                        (.op (.bin .add 14 14 15))))))))))))

theorem readBucketCountRegCode_exec {U V w N b : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (hb : b < numBuckets N) (hr272 : x.regs 272 = b) :
    BitRAM.DemonicExecWithin w readBucketCountRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 14 = Succinct.bCount N (gmAtBit U w N x.mem) b ∧
        (∀ r : Fin 280, 20 ≤ r.val → y.regs r = x.regs r)) 102 := by
  have hact := her.active hN_pos
  have hr245 : x.regs 245 = bucketBits N := hact.1
  have hr250 : x.regs 250 = slabSize N := hact.2.2.2.2.2.1
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  refine dExec_step (DemonicExecWithin.const hfit0 rfl) ?_
  let s1 := x.set 12 0
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit0
  have hs1_er : EpochRegs U V w N s1 := her.set_of_outside (by decide) 0
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hc : CondHolds (.eq 245 12) s1 := by
      simp [CondHolds, BitRAM.Data.toWordRAMData, s1, BitRAM.Data.set, hr245, hb0]
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hB1 : numBuckets N = 1 := by simp [numBuckets, hb0]
    have hb_eq0 : b = 0 := by omega
    refine (dExec_branch_pos hc
      (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er h0_lt
        rfl hsz)).mono
      (fun y ⟨hmem, hwf, hy14, hregs⟩ => ?_) (by omega)
    refine ⟨hmem, hwf, hs1_er.congr_regs (fun r hr1 _ =>
      hregs r (by omega) (by intro h; have := congrArg Fin.val h; omega)), ?_, fun r hr => ?_⟩
    · subst hb_eq0; simp [Succinct.bCount, hb0, hy14]; rfl
    · rw [hregs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s1, BitRAM.Data.set]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  · have hc : ¬CondHolds (.eq 245 12) s1 := by
      simp [CondHolds, BitRAM.Data.toWordRAMData, s1, BitRAM.Data.set, hr245, Nat.ne_of_gt hb_pos]
    refine dExec_branch_neg hc ?_
    have hq_lt : 4 + 3 * b < globalMetaLen N := Succinct.gmQIdx_lt hb_pos hb
    have hr_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
    have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v := fun v hv =>
      fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
    refine dExec_step (DemonicExecWithin.const (hfit_gm 3 (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, s1, BitRAM.Data.set, hr272] using hfit_gm (3 * b) (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.const (hfit_gm 4 (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, s1, BitRAM.Data.set, hr272] using hfit_gm (4 + 3 * b) (by omega))
      rfl) ?_
    let s2 := (((s1.set 12 3).set 12 (3 * s1.regs 272)).set 13 4).set 12 (4 + 3 * s1.regs 272)
    have hs2_wf : s2.WellFormed w :=
      wf_set 12 (wf_set 13 (wf_set 12 (wf_set 12 hs1_wf (hfit_gm 3 (by omega)))
        (by simpa [s1, BitRAM.Data.set, hr272] using hfit_gm (3 * b) (by omega)))
        (hfit_gm 4 (by omega)))
        (by simpa [s1, BitRAM.Data.set, hr272] using hfit_gm (4 + 3 * b) (by omega))
    have hs2_er : EpochRegs U V w N s2 := hs1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs2_12 : s2.regs 12 = 4 + 3 * b := by simp [s2, s1, BitRAM.Data.set, hr272]
    refine .seq (T₂ := 49)
      (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs2_wf hs2_er hq_lt hs2_12 hsz)
      (fun y1 ⟨hy1_st, hy1_wf, hy1_14, hy1_regs⟩ => ?_) (by omega)
    have hy1_er : EpochRegs U V w N y1 := hs2_er.congr_regs (fun r hr1 _ =>
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
    have hy1_12 : y1.regs 12 = 4 + 3 * b := by
      rw [hy1_regs 12 (by decide) (by decide)]; exact hs2_12
    have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
      change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
      rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
    refine dExec_step (DemonicExecWithin.const (hfit_gm 1 (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, BitRAM.Data.set, hy1_12] using hfit_gm (4 + 3 * b + 1) (by omega))
      rfl) ?_
    let s3 := (y1.set 13 1).set 12 (y1.regs 12 + 1)
    have hs3_wf : s3.WellFormed w :=
      wf_set 12 (wf_set 13 hy1_wf (hfit_gm 1 (by omega)))
        (by simpa [hy1_12] using hfit_gm (4 + 3 * b + 1) (by omega))
    have hs3_er : EpochRegs U V w N s3 := hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs3_12 : s3.regs 12 = 4 + 3 * b + 1 := by simp [s3, BitRAM.Data.set, hy1_12]
    refine .seq (T₂ := 2)
      (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs3_wf hs3_er hr_lt hs3_12 hy1_sz)
      (fun y2 ⟨hy2_st, hy2_wf, hy2_15, hy2_regs⟩ => ?_) (by omega)
    have hy2_er : EpochRegs U V w N y2 := hs3_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
    have hy2_mem : y2.mem = x.mem := by
      calc y2.mem = s3.mem := congrArg BitMemory.State.mem hy2_st
        _ = y1.mem := rfl
        _ = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy2_15' : y2.regs 15 = gmAtBit U w N x.mem (4 + 3 * b + 1) := by
      rw [hy2_15]
      exact congrArg (fun m => gmAtBit U w N m (4 + 3 * b + 1))
        (congrArg BitMemory.State.mem hy1_st)
    have hy2_14 : y2.regs 14 = gmAtBit U w N x.mem (4 + 3 * b) := by
      rw [hy2_regs 14 (by decide) (by decide)]
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      rw [hy1_14]; rfl
    have hy2_250 : y2.regs 250 = slabSize N := (hy2_er.active hN_pos).2.2.2.2.2.1
    have hbc_le : Succinct.bCount N (gmAtBit U w N x.mem) b ≤ N :=
      Succinct.bCount_le_n_max hslot b
    have hbc_eq : gmAtBit U w N x.mem (4 + 3 * b) * slabSize N +
        gmAtBit U w N x.mem (4 + 3 * b + 1) = Succinct.bCount N (gmAtBit U w N x.mem) b := by
      unfold Succinct.bCount Succinct.gmQIdx Succinct.gmRIdx
      simp [Nat.ne_of_gt hb_pos, hb]
    have hfit_bc : Fits w (gmAtBit U w N x.mem (4 + 3 * b) * slabSize N +
        gmAtBit U w N x.mem (4 + 3 * b + 1)) := by
      rw [hbc_eq]; exact fits_of_le_N hw hnU hU (by omega)
    have hfit_qK : Fits w (gmAtBit U w N x.mem (4 + 3 * b) * slabSize N) :=
      Fits.of_le hfit_bc (Nat.le_add_right _ _)
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, hy2_14, hy2_250] using hfit_qK) rfl) ?_
    refine DemonicExecWithin.bin
      (by simpa [BinOp.eval, BitRAM.Data.set, hy2_14, hy2_250, hy2_15'] using hfit_bc) ?_
    refine ⟨hy2_st.trans hy1_st,
      wf_set 14 (wf_set 14 hy2_wf (by simpa [hy2_14, hy2_250] using hfit_qK))
        (by simpa [BitRAM.Data.set, hy2_14, hy2_250, hy2_15'] using hfit_bc),
      hy2_er.congr_regs (fun r hr1 _ => by
        dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
      ?_, fun r hr => ?_⟩
    · simp [BitRAM.Data.set, BinOp.eval, hy2_14, hy2_250, hy2_15', hbc_eq]
    · dsimp only [BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      rw [hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s3, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
      rw [hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
      dsimp only [s2, s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

theorem slotOf_tail_valid {N b j : ℕ} {gm : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N gm b)
    (hb_pos : 0 < bucketBits N)
    (hge : gm 0 * slabSize N ≤ Succinct.slotOf N gm b j) :
    N - 1 - Succinct.slotOf N gm b j < gm 1 := by
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hK : 0 < slabSize N := slabSize_pos N
  have hslab := hslot.multi_slab hb_pos
  have htail := hslot.multi_tail hb_pos
  have htot := hslot.multi_total_le hb_pos
  unfold Succinct.slotOf at hge ⊢
  rw [ite_eq_right hb0] at hge ⊢
  split_ifs at hge ⊢ with hj_slab
  · have hs_q : j / slabSize N < gm (Succinct.gmQIdx b) :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hp_lt : Succinct.slabPtrOf N gm b (j / slabSize N) < gm 0 := by
      rw [hslab.nslabs_eq]; exact hslab.ptr_lt b hb _ hs_q
    have hpK : (Succinct.slabPtrOf N gm b (j / slabSize N) + 1) * slabSize N ≤
        gm 0 * slabSize N := Nat.mul_le_mul_right _ hp_lt
    rw [Nat.add_one_mul] at hpK
    omega
  · unfold Succinct.bCount at hj_bc
    simp only [hb0, ↓reduceIte, hb] at hj_bc
    have hr_lt : j - gm (Succinct.gmQIdx b) * slabSize N < gm (Succinct.gmRIdx b) := by omega
    have ht_lt : gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N)) <
        gm 1 := by
      rw [htail.ntails_eq]; exact htail.ptr_lt b hb _ hr_lt
    omega

/-- Parameter-free `BitRAM.Code .standard 280` program resolving logical slot `(b, j)`
(`b = x.regs 272`, `j = x.regs 30`) to its physical slot `r14 = Succinct.slotOf N gm b j`,
preserving all registers `≥ 30`. -/
@[expose]
def resolveIndexedSlotPhysRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 0))
    (.branch (.eq 245 12)
      (.op (.copy 14 30))
      (.seq computeGMBasesRegCode
        (.seq (.op (.const 12 3))
          (.seq (.op (.bin .mul 12 12 272))
            (.seq (.op (.const 13 4))
              (.seq (.op (.bin .add 12 13 12))
                (.seq (readGMRegCode 12 26)
                  (.seq (.op (.bin .mul 27 26 250))
                    (.branch (.lt 30 27)
                      (.seq (.op (.bin .div 28 30 250))
                        (.seq (.op (.bin .mod 29 30 250))
                          (.seq (.op (.const 12 1))
                            (.seq (.op (.bin .sub 13 250 12))
                              (.seq (.op (.bin .sub 29 13 29))
                                (.seq (.op (.bin .mul 12 272 20))
                                  (.seq (.op (.bin .add 12 22 12))
                                    (.seq (.op (.bin .add 12 12 28))
                                      (.seq (readGMRegCode 12 14)
                                        (.seq (.op (.bin .mul 14 14 250))
                                          (.op (.bin .add 14 14 29))))))))))))
                      (.seq (.op (.bin .sub 28 30 27))
                        (.seq (.op (.bin .mul 12 272 21))
                          (.seq (.op (.bin .add 12 23 12))
                            (.seq (.op (.bin .add 12 12 28))
                              (.seq (readGMRegCode 12 29)
                                (.seq (.op (.const 12 1))
                                  (.seq (.op (.load 14 12))
                                    (.seq (.op (.bin .sub 14 14 12))
                                      (.op (.bin .sub 14 14 29)))))))))))))))))))

/-- Parameter-free `BitRAM.Code .standard 280` program resolving logical slot `(b, j)`
(`b = x.regs 272`, `j = x.regs 30`) to both its physical slot `r14 = Succinct.slotOf N gm b j`
and its dense item index `r15 = denseOfPhys N gm td (Succinct.slotOf N gm b j)`, preserving all
registers `≥ 30`. -/
@[expose]
def resolveIndexedSlotRegCode : BitRAM.Code .standard 280 :=
  .seq resolveIndexedSlotPhysRegCode denseOfPhysRegCode

theorem resolveIndexedSlotPhysRegCode_exec {U V w N b j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hj_reach : j < effBucketCap N ∨
      gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N ≤ j)
    (hr272 : x.regs 272 = b) (hr30 : x.regs 30 = j) :
    BitRAM.DemonicExecWithin w resolveIndexedSlotPhysRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 14 = Succinct.slotOf N (gmAtBit U w N x.mem) b j ∧
        (∀ r : Fin 280, 30 ≤ r.val → y.regs r = x.regs r)) 125 := by
  have hact := her.active hN_pos
  have hr245 : x.regs 245 = bucketBits N := hact.1
  have hr250 : x.regs 250 = slabSize N := hact.2.2.2.2.2.1
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v := fun v hv =>
    fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  refine dExec_step (DemonicExecWithin.const hfit0 rfl) ?_
  let s1 := x.set 12 0
  have hs1_wf : s1.WellFormed w := wf_set 12 hx hfit0
  have hs1_er : EpochRegs U V w N s1 := her.set_of_outside (by decide) 0
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hc : CondHolds (.eq 245 12) s1 := by
      simp [CondHolds, BitRAM.Data.toWordRAMData, s1, BitRAM.Data.set, hr245, hb0]
    refine (dExec_branch_pos hc (DemonicExecWithin.copy ?_)).mono (fun _ h => h) (by omega)
    refine ⟨rfl, wf_set 14 hs1_wf (hs1_wf.regs_fits 30),
      hs1_er.set_of_outside (by decide) (s1.regs 30),
      by simp [Succinct.slotOf, hb0, s1, BitRAM.Data.set, hr30], fun r hr => ?_⟩
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
  · have hc : ¬CondHolds (.eq 245 12) s1 := by
      simp [CondHolds, BitRAM.Data.toWordRAMData, s1, BitRAM.Data.set, hr245, Nat.ne_of_gt hb_pos]
    refine dExec_branch_neg hc ?_
    refine .seq (T₂ := 111) (computeGMBasesRegCode_exec hw hN_pos hb_pos hs1_wf hs1_er hsz)
      (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_20, hy1_21, hy1_22, hy1_23, _, _, hy1_regs⟩ => ?_)
      (by omega)
    have hy1_272 : y1.regs 272 = b := by
      rw [hy1_regs 272 (Or.inr (by decide))]; simp [BitRAM.Data.set, hr272]
    have hy1_30 : y1.regs 30 = j := by
      rw [hy1_regs 30 (Or.inr (by decide))]; simp [BitRAM.Data.set, hr30]
    have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
      change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
      rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
    have hq_lt : 4 + 3 * b < globalMetaLen N := Succinct.gmQIdx_lt hb_pos hb
    refine dExec_step (DemonicExecWithin.const (hfit_gm 3 (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, BitRAM.Data.set, hy1_272] using hfit_gm (3 * b) (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.const (hfit_gm 4 (by omega)) rfl) ?_
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, BitRAM.Data.set, hy1_272] using hfit_gm (4 + 3 * b) (by omega))
      rfl) ?_
    let s2 := (((y1.set 12 3).set 12 (3 * y1.regs 272)).set 13 4).set 12 (4 + 3 * y1.regs 272)
    have hs2_wf : s2.WellFormed w :=
      wf_set 12 (wf_set 13 (wf_set 12 (wf_set 12 hy1_wf (hfit_gm 3 (by omega)))
        (by simpa [hy1_272] using hfit_gm (3 * b) (by omega)))
        (hfit_gm 4 (by omega)))
        (by simpa [hy1_272] using hfit_gm (4 + 3 * b) (by omega))
    have hs2_er : EpochRegs U V w N s2 := hy1_er.congr_regs (fun r hr1 _ => by
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
    have hs2_12 : s2.regs 12 = 4 + 3 * b := by simp [s2, BitRAM.Data.set, hy1_272]
    refine .seq (T₂ := 62)
      (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs2_wf hs2_er hq_lt hs2_12 hy1_sz)
      (fun y2 ⟨hy2_st, hy2_wf, hy2_26, hy2_regs⟩ => ?_) (by omega)
    have hy2_er : EpochRegs U V w N y2 := hs2_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
    have hy2_mem : y2.mem = x.mem := by
      calc y2.mem = y1.mem := congrArg BitMemory.State.mem hy2_st
        _ = x.mem := congrArg BitMemory.State.mem hy1_st
    have hy2_sz : epochMetaBits U w N ≤ y2.bitSize := by
      change epochMetaBits U w N ≤ y2.toBitMemoryState.bitSize
      rw [congrArg BitMemory.State.bitSize (hy2_st.trans hy1_st)]; exact hsz
    have hy2_26' : y2.regs 26 = gmAtBit U w N x.mem (Succinct.gmQIdx b) := by
      rw [hy2_26]
      exact congrArg (fun m => gmAtBit U w N m (4 + 3 * b)) (congrArg BitMemory.State.mem hy1_st)
    have hy2_250 : y2.regs 250 = slabSize N := (hy2_er.active hN_pos).2.2.2.2.2.1
    have hy2_30 : y2.regs 30 = j := by
      rw [hy2_regs 30 (by decide) (by decide)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      exact hy1_30
    have hy2_272 : y2.regs 272 = b := by
      rw [hy2_regs 272 (by decide) (by decide)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      exact hy1_272
    have hy2_20 : y2.regs 20 = dirSlabsPerBucket N := by
      rw [hy2_regs 20 (by decide) (by decide)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      exact hy1_20
    have hy2_21 : y2.regs 21 = tailCapPerBucket N := by
      rw [hy2_regs 21 (by decide) (by decide)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      exact hy1_21
    have hy2_22 : y2.regs 22 = Succinct.gmSlabDirBase N := by
      rw [hy2_regs 22 (by decide) (by decide)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      exact hy1_22
    have hy2_23 : y2.regs 23 = Succinct.gmTailPtrBase N := by
      rw [hy2_regs 23 (by decide) (by decide)]
      dsimp only [s2, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      exact hy1_23
    have hbc_le : Succinct.bCount N (gmAtBit U w N x.mem) b ≤ N :=
      Succinct.bCount_le_n_max hslot b
    have hbc_eq : gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N +
        gmAtBit U w N x.mem (Succinct.gmRIdx b) = Succinct.bCount N (gmAtBit U w N x.mem) b := by
      unfold Succinct.bCount; simp [Nat.ne_of_gt hb_pos, hb]
    have hfit_qK : Fits w (gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) :=
      hfit_N _ (by omega)
    refine dExec_step (DemonicExecWithin.bin
      (by simpa [BinOp.eval, hy2_26', hy2_250] using hfit_qK) rfl) ?_
    let s3 := y2.set 27 (y2.regs 26 * y2.regs 250)
    have hs3_wf : s3.WellFormed w :=
      wf_set 27 hy2_wf (by simpa [hy2_26', hy2_250] using hfit_qK)
    have hs3_er : EpochRegs U V w N s3 := hy2_er.set_of_outside (by decide) _
    have hs3_27 : s3.regs 27 = gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N := by
      simp [s3, BitRAM.Data.set, hy2_26', hy2_250]
    have hs3_30 : s3.regs 30 = j := by
      dsimp only [s3, BitRAM.Data.set]; rw [Function.update_of_ne (by decide)]; exact hy2_30
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hK_le : slabSize N ≤ max N 1 := Succinct.slabSize_le_max_n_one N
    by_cases hj_slab : j < gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N
    · have hc2 : CondHolds (.lt 30 27) s3 := by
        simp [CondHolds, BitRAM.Data.toWordRAMData, hs3_30, hs3_27, hj_slab]
      refine dExec_branch_pos hc2 ?_
      have hj_cap : j < effBucketCap N := by rcases hj_reach with h | h <;> omega
      have hdir_eq := Succinct.effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
      have hs_dir : j / slabSize N < dirSlabsPerBucket N :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hdir_eq]; exact hj_cap)
      have hs_q : j / slabSize N < gmAtBit U w N x.mem (Succinct.gmQIdx b) :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hslab := hslot.multi_slab hb_pos
      have hdir_idx_lt : Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N + j / slabSize N <
          globalMetaLen N := Succinct.gmSlabDirIdx_lt hb_pos hb hs_dir
      have hdiv_le_gm : j / slabSize N ≤ globalMetaLen N :=
        (Nat.le_add_left _ _).trans (le_of_lt hdir_idx_lt)
      have hmul_dir_le_gm : b * dirSlabsPerBucket N ≤ globalMetaLen N :=
        (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (le_of_lt hdir_idx_lt))
      have hadd_dir_le_gm :
          Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N ≤ globalMetaLen N :=
        (Nat.le_add_right _ _).trans (le_of_lt hdir_idx_lt)
      have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK_pos
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_30, hy2_250, Nat.ne_of_gt hK_pos] using
          hfit_gm (j / slabSize N) hdiv_le_gm) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_30, hy2_250, Nat.ne_of_gt hK_pos] using
          hfit_N (j % slabSize N) (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.const (hfit_N 1 (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_250] using
          hfit_N (slabSize N - 1) (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_30, hy2_250, Nat.ne_of_gt hK_pos] using
          hfit_N (slabSize N - 1 - j % slabSize N) (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_272, hy2_20] using
          hfit_gm (b * dirSlabsPerBucket N) hmul_dir_le_gm) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_22, hy2_272, hy2_20] using
          hfit_gm (Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N) hadd_dir_le_gm) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_22, hy2_272, hy2_20, hy2_30, hy2_250] using
          hfit_gm _ (le_of_lt hdir_idx_lt)) rfl) ?_
      let s4 :=
        ((((((((s3.set 28 (s3.regs 30 / s3.regs 250)).set 29 (s3.regs 30 % s3.regs 250)).set 12
          1).set 13 (s3.regs 250 - 1)).set 29 (s3.regs 250 - 1 - s3.regs 30 % s3.regs 250)).set 12
          (s3.regs 272 * s3.regs 20)).set 12 (s3.regs 22 + s3.regs 272 * s3.regs 20)).set 12
          (s3.regs 22 + s3.regs 272 * s3.regs 20 + s3.regs 30 / s3.regs 250))
      have hs4_wf : s4.WellFormed w :=
        wf_set 12 (wf_set 12 (wf_set 12 (wf_set 29 (wf_set 13 (wf_set 12 (wf_set 29
          (wf_set 28 hs3_wf
          (by simpa [s3, BitRAM.Data.set, hy2_30, hy2_250] using
            hfit_gm (j / slabSize N) hdiv_le_gm))
          (by simpa [s3, BitRAM.Data.set, hy2_30, hy2_250] using
            hfit_N (j % slabSize N) (by omega)))
          (hfit_N 1 (by omega)))
          (by simpa [s3, BitRAM.Data.set, hy2_250] using hfit_N (slabSize N - 1) (by omega)))
          (by simpa [s3, BitRAM.Data.set, hy2_30, hy2_250] using
            hfit_N (slabSize N - 1 - j % slabSize N) (by omega)))
          (by simpa [s3, BitRAM.Data.set, hy2_272, hy2_20] using
            hfit_gm (b * dirSlabsPerBucket N) hmul_dir_le_gm))
          (by simpa [s3, BitRAM.Data.set, hy2_22, hy2_272, hy2_20] using
            hfit_gm (Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N) hadd_dir_le_gm))
          (by simpa [s3, BitRAM.Data.set, hy2_22, hy2_272, hy2_20, hy2_30, hy2_250] using
            hfit_gm _ (le_of_lt hdir_idx_lt))
      have hs4_er : EpochRegs U V w N s4 := hs3_er.congr_regs (fun r hr1 _ => by
        dsimp only [s4, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      have hs4_12 : s4.regs 12 =
          Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N + j / slabSize N := by
        simp [s4, s3, BitRAM.Data.set, hy2_22, hy2_272, hy2_20, hy2_30, hy2_250]
      refine .seq (T₂ := 2)
        (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs4_wf hs4_er hdir_idx_lt hs4_12 hy2_sz)
        (fun y3 ⟨hy3_st, hy3_wf, hy3_14, hy3_regs⟩ => ?_) (by omega)
      have hy3_er : EpochRegs U V w N y3 := hs4_er.congr_regs (fun r hr1 _ =>
        hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
      have hy3_250 : y3.regs 250 = slabSize N := (hy3_er.active hN_pos).2.2.2.2.2.1
      have hy3_29 : y3.regs 29 = slabSize N - 1 - j % slabSize N := by
        rw [hy3_regs 29 (by decide) (by decide)]
        simp [BitRAM.Data.set, hy2_250, hy2_30]
      have hy3_14' : y3.regs 14 =
          Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N) := by
        rw [hy3_14]
        have hmem_eq : s4.mem = x.mem := hy2_mem
        have hidx_eq : Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N + j / slabSize N =
            Succinct.gmSlabDirIdx N b (j / slabSize N) := rfl
        have h1 : gmAtBit U w N x.mem
            (Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N + j / slabSize N) =
            Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N) := by
          rw [hidx_eq]; exact hslab.dir_eq b hb _ hs_q hs_dir
        exact (congrArg (fun m => gmAtBit U w N m
          (Succinct.gmSlabDirBase N + b * dirSlabsPerBucket N + j / slabSize N))
          (by change y2.mem = x.mem; exact hy2_mem)).trans h1
      have hp_lt : Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N) <
          gmAtBit U w N x.mem 0 := by
        rw [hslab.nslabs_eq]; exact hslab.ptr_lt b hb _ hs_q
      have htot := hslot.multi_total_le hb_pos
      have hpK_le : (Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N) + 1) *
          slabSize N ≤ gmAtBit U w N x.mem 0 * slabSize N :=
        Nat.mul_le_mul_right _ hp_lt
      rw [Nat.add_one_mul] at hpK_le
      have hfit_pK : Fits w (Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N) *
          slabSize N) := hfit_N _ (by omega)
      have hfit_slot : Fits w (Succinct.slabPtrOf N (gmAtBit U w N x.mem) b (j / slabSize N) *
          slabSize N + (slabSize N - 1 - j % slabSize N)) := hfit_N _ (by omega)
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, hy3_14', hy3_250] using hfit_pK) rfl) ?_
      refine DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy3_14', hy3_250, hy3_29] using hfit_slot) ?_
      refine ⟨hy3_st.trans (hy2_st.trans hy1_st),
        wf_set 14 (wf_set 14 hy3_wf (by simpa [hy3_14', hy3_250] using hfit_pK))
          (by simpa [BitRAM.Data.set, hy3_14', hy3_250, hy3_29] using hfit_slot),
        hy3_er.congr_regs (fun r hr1 _ => by
          dsimp only [BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
        ?_, fun r hr => ?_⟩
      · unfold Succinct.slotOf
        rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_left hj_slab]
        simp [BitRAM.Data.set, BinOp.eval, hy3_14', hy3_250, hy3_29]
      · dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s4, s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy1_regs r (Or.inr (by omega))]
        dsimp only [BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    · have hc2 : ¬CondHolds (.lt 30 27) s3 := by
        simp [CondHolds, BitRAM.Data.toWordRAMData, hs3_30, hs3_27, hj_slab]
      refine dExec_branch_neg hc2 ?_
      have hj_ge : gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N ≤ j :=
        Nat.le_of_not_lt hj_slab
      have htail := hslot.multi_tail hb_pos
      have hr_lt : j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N <
          gmAtBit U w N x.mem (Succinct.gmRIdx b) := by omega
      have hr_cap : j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N <
          tailCapPerBucket N := lt_of_lt_of_le hr_lt (htail.r_le b hb)
      have hptr_idx_lt : Succinct.gmTailPtrBase N + b * tailCapPerBucket N +
          (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) < globalMetaLen N := by
        have := Succinct.gmTailPtrIdx_lt hb_pos hb hr_cap
        unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx at this
        omega
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, s3, BitRAM.Data.set, hy2_30, hy2_26', hy2_250] using
          hfit_gm (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_272, hy2_21] using
          hfit_gm (b * tailCapPerBucket N) (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_23, hy2_272, hy2_21] using
          hfit_gm (Succinct.gmTailPtrBase N + b * tailCapPerBucket N) (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy2_23, hy2_272, hy2_21, hy2_30, hy2_26', hy2_250]
          using hfit_gm _ (le_of_lt hptr_idx_lt)) rfl) ?_
      let s4 :=
        (((s3.set 28 (s3.regs 30 - s3.regs 27)).set 12 (s3.regs 272 * s3.regs 21)).set 12
          (s3.regs 23 + s3.regs 272 * s3.regs 21)).set 12
          (s3.regs 23 + s3.regs 272 * s3.regs 21 + (s3.regs 30 - s3.regs 27))
      have hs4_wf : s4.WellFormed w :=
        wf_set 12 (wf_set 12 (wf_set 12 (wf_set 28 hs3_wf
          (by simpa [s3, BitRAM.Data.set, hy2_30, hy2_26', hy2_250] using
            hfit_gm (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) (by omega)))
          (by simpa [s3, BitRAM.Data.set, hy2_272, hy2_21] using
            hfit_gm (b * tailCapPerBucket N) (by omega)))
          (by simpa [s3, BitRAM.Data.set, hy2_23, hy2_272, hy2_21] using
            hfit_gm (Succinct.gmTailPtrBase N + b * tailCapPerBucket N) (by omega)))
          (by simpa [s3, BitRAM.Data.set, hy2_23, hy2_272, hy2_21, hy2_30, hy2_26', hy2_250] using
            hfit_gm _ (le_of_lt hptr_idx_lt))
      have hs4_er : EpochRegs U V w N s4 := hs3_er.congr_regs (fun r hr1 _ => by
        dsimp only [s4, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
      have hs4_12 : s4.regs 12 = Succinct.gmTailPtrBase N + b * tailCapPerBucket N +
          (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) := by
        simp [s4, s3, BitRAM.Data.set, hy2_23, hy2_272, hy2_21, hy2_30, hy2_26', hy2_250]
      refine .seq (T₂ := 4)
        (readGMRegCode_exec (by decide) hw hN_pos hnU hU hs4_wf hs4_er hptr_idx_lt hs4_12 hy2_sz)
        (fun y3 ⟨hy3_st, hy3_wf, hy3_29, hy3_regs⟩ => ?_) (by omega)
      have hy3_er : EpochRegs U V w N y3 := hs4_er.congr_regs (fun r hr1 _ =>
        hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
      have hy3_mem1 : y3.mem 1 = N := by
        have hmem_eq : y3.mem = x.mem := by
          calc y3.mem = y2.mem := congrArg BitMemory.State.mem hy3_st
            _ = x.mem := hy2_mem
        rw [hmem_eq, hm1]
      have hy3_ws : epochMetaWords U w N ≤ y3.wordSize w :=
        epochMetaWords_le_wordSize_of_bitSize hw
          (by change epochMetaBits U w N ≤ y3.toBitMemoryState.bitSize
              rw [congrArg BitMemory.State.bitSize (hy3_st.trans (hy2_st.trans hy1_st))]
              exact hsz)
      have hadm1 : 1 < y3.wordSize w := by
        have h4 : 4 ≤ epochMetaWords U w N := by
          unfold epochMetaWords; rw [ite_eq_right (Nat.ne_of_gt hN_pos)]; omega
        omega
      have ht_idx_eq : Succinct.gmTailPtrBase N + b * tailCapPerBucket N +
          (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) =
          Succinct.gmTailPtrIdx N b (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N) := by
        unfold Succinct.gmTailPtrIdx Succinct.gmTailPtrFlatIdx; ring
      have hy3_29' : y3.regs 29 = gmAtBit U w N x.mem
          (Succinct.gmTailPtrIdx N b
            (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N)) := by
        rw [hy3_29, ← ht_idx_eq]
        exact congrArg (fun m => gmAtBit U w N m _) hy2_mem
      have ht_lt : gmAtBit U w N x.mem
          (Succinct.gmTailPtrIdx N b
            (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N)) <
          gmAtBit U w N x.mem 1 := by
        rw [htail.ntails_eq]; exact htail.ptr_lt b hb _ hr_lt
      have htot := hslot.multi_total_le hb_pos
      refine dExec_step (DemonicExecWithin.const (hfit_N 1 (by omega)) rfl) ?_
      refine dExec_step (DemonicExecWithin.load hadm1 rfl) ?_
      refine dExec_step (DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy3_mem1] using hfit_N (N - 1) (by omega)) rfl) ?_
      refine DemonicExecWithin.bin
        (by simpa [BinOp.eval, BitRAM.Data.set, hy3_mem1, hy3_29'] using
          hfit_N (N - 1 - gmAtBit U w N x.mem
            (Succinct.gmTailPtrIdx N b
              (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N))) (by omega)) ?_
      refine ⟨hy3_st.trans (hy2_st.trans hy1_st),
        wf_set 14 (wf_set 14 (wf_set 14 (wf_set 12 hy3_wf (hfit_N 1 (by omega)))
          (hy3_wf.mem_wf.mem_fits 1))
          (by simpa [BitRAM.Data.set, hy3_mem1] using hfit_N (N - 1) (by omega)))
          (by simpa [BitRAM.Data.set, hy3_mem1, hy3_29'] using
            hfit_N (N - 1 - gmAtBit U w N x.mem
              (Succinct.gmTailPtrIdx N b
                (j - gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N))) (by omega)),
        hy3_er.congr_regs (fun r hr1 _ => by
          dsimp only [BitRAM.Data.set]
          repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]),
        ?_, fun r hr => ?_⟩
      · unfold Succinct.slotOf
        rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_right hj_slab]
        simp [BitRAM.Data.set, BinOp.eval, hy3_mem1, hy3_29']
      · dsimp only [BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s4, s3, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
        dsimp only [s2, BitRAM.Data.set]
        repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
        rw [hy1_regs r (Or.inr (by omega))]
        dsimp only [BitRAM.Data.set]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

theorem resolveIndexedSlotRegCode_exec {U V w N b j : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm1 : x.mem 1 = N) (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (htd : TailDenseInv N (gmAtBit U w N x.mem 0) (gmAtBit U w N x.mem 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < Succinct.bCount N (gmAtBit U w N x.mem) b)
    (hj_reach : j < effBucketCap N ∨
      gmAtBit U w N x.mem (Succinct.gmQIdx b) * slabSize N ≤ j)
    (hr272 : x.regs 272 = b) (hr30 : x.regs 30 = j) :
    BitRAM.DemonicExecWithin w resolveIndexedSlotRegCode x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.regs 14 = Succinct.slotOf N (gmAtBit U w N x.mem) b j ∧
        y.regs 15 = denseOfPhys N (gmAtBit U w N x.mem) (tdAtBit U w N x.mem)
          (Succinct.slotOf N (gmAtBit U w N x.mem) b j) ∧
        (∀ r : Fin 280, 30 ≤ r.val → y.regs r = x.regs r)) 230 := by
  refine .seq (T₂ := 105)
    (resolveIndexedSlotPhysRegCode_exec hw hN_pos hnU hU hx her hm1 hsz hslot hb hj_bc hj_reach
      hr272 hr30)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_14, hy1_regs⟩ => ?_) le_rfl
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : epochMetaBits U w N ≤ y1.bitSize := by
    change epochMetaBits U w N ≤ y1.toBitMemoryState.bitSize
    rw [congrArg BitMemory.State.bitSize hy1_st]; exact hsz
  have hphys_lt : Succinct.slotOf N (gmAtBit U w N x.mem) b j < N :=
    (Succinct.slotOf_lt_and_injective hslot).1 b hb j hj_bc
  have hslot' : Succinct.SlotStoreInv N (gmAtBit U w N y1.mem) := by rwa [hy1_mem]
  have htd' : TailDenseInv N (gmAtBit U w N y1.mem 0) (gmAtBit U w N y1.mem 1)
      (tdAtBit U w N y1.mem) (dtAtBit U w N y1.mem) := by rwa [hy1_mem]
  refine (denseOfPhysRegCode_exec hw hN_pos hnU hU hy1_wf hy1_er
    (by rw [hy1_mem, hm1]) hy1_sz hslot' htd' hy1_14 hphys_lt
    (fun hb_pos hge => by
      rw [hy1_mem] at hge ⊢
      exact slotOf_tail_valid hslot hb hj_bc hb_pos hge)).mono
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_15, hy2_14, hy2_regs⟩ => ?_) le_rfl
  refine ⟨hy2_st.trans hy1_st, hy2_wf, hy2_er, hy2_14, by simpa [hy1_mem] using hy2_15,
    fun r hr => (hy2_regs r (by omega)).trans (hy1_regs r hr)⟩

end Cslib.DataStructure.Dictionary.BitResizable



