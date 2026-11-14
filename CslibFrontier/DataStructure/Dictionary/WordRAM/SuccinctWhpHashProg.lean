/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Hash, Feistel Quotient, and Salted Fingerprint Subroutines

This module builds parameter-free `Memory.Prog` subroutines over `Basis.exact` (certified with zero
local work via `realize`) for all hash and one-round Feistel operations used by the WHP succinct
dynamic dictionary (`SuccinctWhpModel` and `SuccinctWhpFallback`):

1. `stage1RedGenProg` and `evalHashGenProg`: frontier-independent `Realizes .exact` wrappers around
   `BitPackedDoubleTabulation`'s 4-limb `oddMulModWord` universe reduction and bit-packed double
   tabulation loop (`outerLoopGenProg`).
2. `HashRt` and `mkHashRtGenProg`: compact 38-word runtime parameter bundle extracted from the
   100-word `(WhpParams, base)` input.
3. `bktHashRtProg`, `feistelSplitRtProg`, `feistelReconstructRtProg`, `fpReducedKeyOptRtProg`,
   `fpOfSaltOptRtProg`, `rKeyOfQuotRtProg`, and `fpOfQuotRtProg`: exact `Memory.Prog` refinements of
   `bktHash`, `(feistelBucket, keyQuotient)`, `feistelReconstruct`, `fpReducedKey`, `fpOfSalt`,
   `FastState.rKeyAt`, and `FastState.fpAt` under `SeedWhpMemRep`, each running in `O_c(1)`
   worst-case memory operations without mutating memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.HashRt`, `mkHashRt`, `mkHashRtGenProg`,
  `hashEvalCostWhp`: compact hash runtime parameter tuple and `c`-only cost bound.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bktHashRtProg`, `feistelSplitRtProg`,
  `feistelReconstructRtProg`, `fpReducedKeyOptRtProg`, `fpOfSaltOptRtProg`, `rKeyOfQuotRtProg`,
  `fpOfQuotRtProg`: certified `Memory.Prog` hash and Feistel subroutines.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bktHashRt`,
  `realizes_feistelSplitRt`, `realizes_feistelReconstructRt`, `realizes_fpReducedKeyOptRt`,
  `realizes_fpOfSaltOptRt`, `realizes_rKeyOfQuotRt`, `realizes_fpOfQuotRt`:
  parameter-free `Realizes .exact` certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bktHashRtProg_spec`,
  `feistelSplitRtProg_spec`, `feistelReconstructRtProg_spec`, `fpReducedKeyOptRtProg_spec`,
  `fpOfSaltOptRtProg_spec`, `rKeyOfQuotRtProg_spec`, `fpOfQuotRtProg_spec`:
  exact functional refinement, state preservation, `O_c(1)` `memoryCost`, and `ValidWhpProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.Probability

/-! ## Section 1: Frontier-Independent `stage1RedGenProg` and `evalHashGenProg` -/

/-- `c`-only worst-case `memoryCost` bound for a full bit-packed double-tabulation evaluation. -/
@[expose] def hashEvalCostWhp (c : ℕ) : ℕ :=
  1 + 2 * dTabWhp c * (cTabWhp c + 2)

/-- Precondition for `stage1RedGenProg` (`d = (hp, (hBase, u_val))`), avoiding any `s.frontier`
obligation inside `Realizes`. -/
@[expose] def Stage1RedPre (w : ℕ) (d : HashParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  HashEnv w d.1 d.2.1 ∧
  s.mem d.2.1 ≤ hpMaskM d.1 ∧
  d.2.2 ≤ (hpMaskM d.1 <<< 1) + 1

/-- Parameter-free Stage-1 4-limb `oddMulModWord` universe reduction (`d = (hp, (hBase, u_val))`).
-/
@[irreducible] def stage1RedGenProg (d : HashParams × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let α_val ← Memory.read d.2.1
  let x' ← pure (d.2.2 &&& hpMaskM d.1)
  let α₀ ← pure (α_val &&& hpMaskHalf d.1)
  let α₁ ← pure (α_val >>> hpHalfM d.1)
  let x₀ ← pure (x' &&& hpMaskHalf d.1)
  let x₁ ← pure (x' >>> hpHalfM d.1)
  let p₀ ← pure ((α₀ * x₀) &&& hpMaskM d.1)
  let p₁ ← pure (((α₀ * x₁) &&& hpMaskRem d.1) <<< hpHalfM d.1)
  let p₂ ← pure (((α₁ * x₀) &&& hpMaskRem d.1) <<< hpHalfM d.1)
  let p₃ ← pure (((α₁ &&& hpMaskTop d.1) * (x₁ &&& hpMaskTop d.1)) <<< hpTwoHalfM d.1)
  let s₁ ← pure ((p₀ + p₁) &&& hpMaskM d.1)
  let s₂ ← pure ((s₁ + p₂) &&& hpMaskM d.1)
  let hm ← pure ((s₂ + p₃) &&& hpMaskM d.1)
  let one_v ← pure 1
  pure (((d.2.2 &&& one_v) +
    ((((d.2.2 >>> one_v) + hm) &&& hpMaskM d.1) <<< one_v)) >>> hpShiftR d.1)

private theorem stage1_fits_aux {w₀ w α_val u_val : ℕ} (hw₀ : 0 < w₀) (hw₀_le : w₀ ≤ w)
    (hα : α_val < 2 ^ (w₀ - 1)) (hu : u_val < 2 ^ w₀) :
    let m := w₀ - 1
    let h := m / 2
    let x' := u_val &&& (2 ^ m - 1)
    let α₀ := α_val &&& (2 ^ h - 1)
    let α₁ := α_val >>> h
    let x₀ := x' &&& (2 ^ h - 1)
    let x₁ := x' >>> h
    let p₀ := (α₀ * x₀) &&& (2 ^ m - 1)
    let p₁ := ((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h
    let p₂ := ((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h
    let p₃ := ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)
    let s₁ := (p₀ + p₁) &&& (2 ^ m - 1)
    let s₂ := (s₁ + p₂) &&& (2 ^ m - 1)
    let hm := (s₂ + p₃) &&& (2 ^ m - 1)
    Fits w (α₀ * x₀) ∧
    Fits w (α₀ * x₁) ∧
    Fits w (((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h) ∧
    Fits w (α₁ * x₀) ∧
    Fits w (((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h) ∧
    Fits w ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) ∧
    Fits w (((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)) ∧
    Fits w (p₀ + p₁) ∧
    Fits w (s₁ + p₂) ∧
    Fits w (s₂ + p₃) ∧
    Fits w ((u_val >>> 1) + hm) ∧
    Fits w ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) ∧
    Fits w ((u_val &&& 1) + ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1)) := by
  intro m h x' α₀ α₁ x₀ x₁ p₀ p₁ p₂ p₃ s₁ s₂ hm
  have h2m_le_w : 2 * 2 ^ m ≤ 2 ^ w := by
    calc 2 * 2 ^ m = 2 ^ (m + 1) := (pow_succ' 2 m).symm
      _ = 2 ^ w₀ := by rw [Nat.sub_add_cancel hw₀]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀_le
  have hm_lt_w : 2 ^ m < 2 ^ w := by have := Nat.two_pow_pos m; omega
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hα₀ : α₀ < 2 ^ h := by
    dsimp only [α₀]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hx₀ : x₀ < 2 ^ h := by
    dsimp only [x₀]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hα₁ : α₁ < 2 ^ (m - h) := by
    dsimp only [α₁]; rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rwa [← pow_add, Nat.add_sub_of_le h_le]
  have hx' : x' < 2 ^ m := by
    dsimp only [x']; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hx₁ : x₁ < 2 ^ (m - h) := by
    dsimp only [x₁]; rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rwa [← pow_add, Nat.add_sub_of_le h_le]
  have hp₀_raw : α₀ * x₀ < 2 ^ m := by
    calc α₀ * x₀ < 2 ^ h * 2 ^ h := Nat.mul_lt_mul'' hα₀ hx₀
      _ = 2 ^ (2 * h) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos h2_le
  have hp₁_raw : α₀ * x₁ < 2 ^ m := by
    calc α₀ * x₁ < 2 ^ h * 2 ^ (m - h) := Nat.mul_lt_mul'' hα₀ hx₁
      _ = 2 ^ m := by rw [← pow_add, Nat.add_sub_of_le h_le]
  have hp₂_raw : α₁ * x₀ < 2 ^ m := by
    calc α₁ * x₀ < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul'' hα₁ hx₀
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hp₁_lt : p₁ < 2 ^ m := by
    dsimp only [p₁]; rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod]
    calc ((α₀ * x₁) % 2 ^ (m - h)) * 2 ^ h
        < 2 ^ (m - h) * 2 ^ h :=
          Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hp₂_lt : p₂ < 2 ^ m := by
    dsimp only [p₂]; rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod]
    calc ((α₁ * x₀) % 2 ^ (m - h)) * 2 ^ h
        < 2 ^ (m - h) * 2 ^ h :=
          Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hp₃_mul_lt :
      (α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1)) < 2 ^ (m - 2 * h) := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    rcases (by omega : m - 2 * h = 0 ∨ m - 2 * h = 1) with hd0 | hd1
    · rw [hd0, pow_zero, Nat.mod_one, zero_mul]; exact one_pos
    · rw [hd1, pow_one]
      have h1 : α₁ % 2 < 2 := Nat.mod_lt _ two_pos
      have h2 : x₁ % 2 < 2 := Nat.mod_lt _ two_pos
      rcases (by omega : α₁ % 2 = 0 ∨ α₁ % 2 = 1) with h0 | h1_eq
      · simp [h0]
      · simp [h1_eq, h2]
  have hp₃_lt : p₃ < 2 ^ m := by
    dsimp only [p₃]; rw [Nat.shiftLeft_eq]
    calc _ < 2 ^ (m - 2 * h) * 2 ^ (2 * h) :=
          Nat.mul_lt_mul_of_pos_right hp₃_mul_lt (Nat.two_pow_pos _)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h2_le]
  have hp₀_lt : p₀ < 2 ^ m := by
    dsimp only [p₀]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs₁_lt : s₁ < 2 ^ m := by
    dsimp only [s₁]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs₂_lt : s₂ < 2 ^ m := by
    dsimp only [s₂]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hhm_lt : hm < 2 ^ m := by
    dsimp only [hm]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hu_shr : u_val >>> 1 < 2 ^ m := by
    rw [Nat.shiftRight_eq_div_pow, pow_one]
    refine Nat.div_lt_of_lt_mul ?_
    calc u_val < 2 ^ w₀ := hu
      _ = 2 * 2 ^ m := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
  have hsh_fin : ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) ≤ 2 * 2 ^ m - 2 := by
    rw [Nat.shiftLeft_eq, pow_one, Nat.and_two_pow_sub_one_eq_mod]
    have hmod : ((u_val >>> 1) + hm) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos _)
    omega
  have hubit : u_val &&& 1 < 2 := by
    change u_val &&& (2 ^ 1 - 1) < 2
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ two_pos
  dsimp only [Fits]
  exact ⟨hp₀_raw.trans hm_lt_w, hp₁_raw.trans hm_lt_w, hp₁_lt.trans hm_lt_w,
    hp₂_raw.trans hm_lt_w, hp₂_lt.trans hm_lt_w,
    hp₃_mul_lt.trans_le ((Nat.pow_le_pow_right two_pos (by omega)).trans hm_lt_w.le),
    hp₃_lt.trans hm_lt_w,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem realizes_stage1RedGen :
    Realizes .exact stage1RedGenProg
      (WordEncoding.encode (α := HashParams × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      Stage1RedPre
      (fun _ _ => 0) := by
  unfold stage1RedGenProg
  realize
  all_goals (
    rcases d with ⟨hp, hBase, u_val⟩
    obtain ⟨henv, hα_le, hu_le⟩ := h
    obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, _, _, _, _, _, _, hfit_sp,
      heq_hp⟩ := henv
    subst heq_hp
    dsimp only [hpShiftR, hpHalfM, hpTwoHalfM, hpMaskM, hpMaskHalf, hpMaskRem, hpMaskTop,
      mkHashParams_1, mkHashParams_2, mkHashParams_3, mkHashParams_4,
      mkHashParams_5, mkHashParams_6, mkHashParams_7] at *
    have hα_lt : s.mem hBase < 2 ^ (w₀ - 1) := by
      have : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow; omega
    have hu_lt : u_val < 2 ^ w₀ := by
      rw [Nat.shiftLeft_eq, pow_one] at hu_le
      have hpow : 2 * 2 ^ (w₀ - 1) = 2 ^ w₀ := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
      have : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow; omega
    have hmp := stage1_fits_aux hw₀ hw₀_le hα_lt hu_lt
    change _ < 2 ^ w
    rcases hmp with ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10, h11, _, h13⟩
    first
    | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h7
    | exact h8 | exact h9 | exact h10 | exact h11 | exact h13
    | exact Nat.one_lt_two_pow hw.ne'
  )

private theorem stage1RedGenProg_spec {U w w₀ R c_tab d b_char M_out hBase F : ℕ}
    {θ : BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hw₀ : 0 < w₀) (hh_lt : hBase < F)
    (hrep : BitPackedDoubleTabulation.SeedRep hBase w w₀ c_tab d b_char M_out θ s.mem)
    (u : Fin U) :
    let prog := stage1RedGenProg (mkHashParams w w₀ R c_tab d b_char M_out, (hBase, u.val))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (multiplyShiftReduced U w₀ R θ.1 u).val ∧
    memoryCost prog s = 1 ∧
    ValidWhpProg w F s prog := by
  have hrkey_eq : oddMulModWord w₀ (s.mem hBase) u.val >>> (w₀ - R) =
      (multiplyShiftReduced U w₀ R θ.1 u).val := by
    rw [hrep.1]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀ θ.1 u
  unfold stage1RedGenProg
  simp only [pure_bind, hpMaskM_mk, hpMaskHalf_mk, hpHalfM_mk, hpMaskRem_mk, hpMaskTop_mk,
    hpTwoHalfM_mk, hpShiftR_mk]
  have hr_st : (Memory.spec 0).clientState s (Memory.read hBase) = s := rfl
  have hr_res : (Memory.spec 0).clientResult s (Memory.read hBase) = s.mem hBase := rfl
  have hr_mc : memoryCost (Memory.read hBase) s = 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hr_st]; rfl
  · rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res]
    exact hrkey_eq
  · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hr_mc, hr_st]; rfl
  · refine validWhpProg_bind (validWhpProg_read hh_lt) ?_
    rw [hr_st]
    exact validWhpProg_pure _

/-- Precondition for `evalHashGenProg` (`d = (hp, ((hBase, salt), u_val))`), without `s.frontier`.
-/
@[expose] def EvalHashPre (w : ℕ) (d : HashParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  HashEnv w d.1 d.2.1.1 ∧
  s.mem d.2.1.1 ≤ hpMaskM d.1 ∧
  d.2.1.2 < hpPowB d.1 ∧
  d.2.2 ≤ (hpMaskM d.1 <<< 1) + 1

/-- Frontier-free wrapper equivalent to `BitPackedDoubleTabulation.evalGenProg`. -/
@[irreducible] def evalHashGenProg (d : HashParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ := do
  let rKey ← stage1RedGenProg (d.1, (d.2.1.1, d.2.2))
  let zero_v ← pure 0
  let out ← BitPackedDoubleTabulation.outerLoopGenProg
    (((d.1, (d.2.1.1, (d.2.1.2, rKey))), (zero_v, zero_v)), hpD d.1)
  pure out.2

private theorem evalHashGenProg_eq_evalGenProg (d : HashParams × ((ℕ × ℕ) × ℕ)) :
    evalHashGenProg d = BitPackedDoubleTabulation.evalGenProg d := by
  unfold evalHashGenProg stage1RedGenProg BitPackedDoubleTabulation.evalGenProg
  simp only [pure_bind, bind_assoc]

theorem realizes_evalHashGen :
    Realizes .exact evalHashGenProg
      (WordEncoding.encode (α := HashParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      EvalHashPre
      (fun _ _ => 0) := by
  unfold evalHashGenProg
  have hs1 := realizes_stage1RedGen
  have hol := BitPackedDoubleTabulation.realizes_outerLoopGen
  have hs1_st : ∀ hp hBase u_val (s' : Memory.State),
      (Memory.spec 0).clientState s' (stage1RedGenProg (hp, (hBase, u_val))) = s' := by
    intro hp hBase u_val s'
    unfold stage1RedGenProg
    simp only [pure_bind]
    rfl
  realize
  all_goals (
    rcases d with ⟨hp, ⟨hBase, s_val⟩, u_val⟩
    obtain ⟨henv, hα_le, hs_lt, hu_le⟩ := h
    try simp only [hs1_st] at *
  )
  · exact ⟨henv, hα_le, hu_le⟩
  · obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
      hc1, hd_lt, hfit_sp, rfl⟩ := henv
    exact (BitPackedDoubleTabulation.outerLoop_invariant
      ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt, hc1,
        hd_lt, hfit_sp, rfl⟩ hs_lt d_par 0 0 (by dsimp only [hpD_mk]; omega)
      (by dsimp only [hpMOut_mk]; exact Nat.two_pow_pos M_out)).1

private theorem validWhpProg_innerLoop {w w₀ R c_tab d b_char M_out hBase F j : ℕ}
    (hw : 0 < w) (hj : j < d)
    (hseg : hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out ≤ F) :
    let hp := mkHashParams w w₀ R c_tab d b_char M_out
    ∀ m i y r (s : Memory.State), i + m ≤ c_tab →
      ValidWhpProg w F s (BitPackedDoubleTabulation.innerLoopGenProg
        (((hp, (hBase, j)), ((i, y), r)), m)) ∧
      (Memory.spec 0).clientState s (BitPackedDoubleTabulation.innerLoopGenProg
        (((hp, (hBase, j)), ((i, y), r)), m)) = s := by
  intro hp m
  have htop_seg : hBase + 1 +
      packedWords (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w ≤ F := by
    refine ( ?_ : _ ≤ hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out).trans hseg
    unfold BitPackedDoubleTabulation.space BitPackedDoubleTabulation.topWords
    omega
  induction m with
  | zero =>
    intro i y r s _
    exact ⟨validWhpProg_pure _, rfl⟩
  | succ m ih =>
    intro i y r s him
    have hch_lt : r &&& (2 ^ b_char - 1) < 2 ^ b_char := by
      rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx₁ : (j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1)) <
        BitPackedDoubleTabulation.topEntries c_tab d b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d b_char
        ⟨i, by omega⟩ ⟨j, hj⟩ ⟨_, hch_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords,
        BitPackedDoubleTabulation.topEntries] at h ⊢
      omega
    have hstep_vp : ValidWhpProg w F s
        (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r))) := by
      unfold BitPackedDoubleTabulation.innerStepGenProg
      simp only [hp, pure_bind, hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx₁ htop_seg) ?_
      exact validWhpProg_pure _
    have hstep_st : (Memory.spec 0).clientState s
        (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r))) = s := rfl
    set res₁ := (Memory.spec 0).clientResult s
      (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r)))
    have hi_eq : res₁.1.1 = i + 1 := rfl
    obtain ⟨hvp_m, hst_m⟩ := ih res₁.1.1 res₁.1.2 res₁.2 s (by rw [hi_eq]; omega)
    refine ⟨?_, ?_⟩
    · change ValidWhpProg w F s
        (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r)) >>=
          fun x => BitPackedDoubleTabulation.innerLoopGenProg (((hp, (hBase, j)), x), m))
      refine validWhpProg_bind hstep_vp ?_
      rw [hstep_st]
      exact hvp_m
    · change (Memory.spec 0).clientState s
        (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r)) >>=
          fun x => BitPackedDoubleTabulation.innerLoopGenProg (((hp, (hBase, j)), x), m)) = s
      rw [StateTransitionSpec.clientState_bind, hstep_st]
      exact hst_m

private theorem validWhpProg_outerLoop {w w₀ R c_tab d b_char M_out hBase F s_val rKey : ℕ}
    (henv : HashEnv w (mkHashParams w w₀ R c_tab d b_char M_out) hBase)
    (hw : 0 < w) (hs_lt : s_val < 2 ^ b_char)
    (hseg : hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out ≤ F) :
    let hp := mkHashParams w w₀ R c_tab d b_char M_out
    ∀ m j out (s : Memory.State), j + m ≤ d →
      ValidWhpProg w F s (BitPackedDoubleTabulation.outerLoopGenProg
        ((((hp, (hBase, (s_val, rKey))), (j, out)), m))) := by
  intro hp m
  have htop_seg : hBase + 1 +
      packedWords (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w ≤ F := by
    refine (?_ : _ ≤ hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out).trans hseg
    unfold BitPackedDoubleTabulation.space BitPackedDoubleTabulation.topWords
    omega
  have hbot_seg : hBase + BitPackedDoubleTabulation.offBot w c_tab d b_char +
      packedWords (BitPackedDoubleTabulation.botEntries d b_char) M_out w ≤ F := by
    refine (?_ : _ ≤ hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out).trans hseg
    unfold BitPackedDoubleTabulation.space BitPackedDoubleTabulation.offBot
      BitPackedDoubleTabulation.botWords
    omega
  induction m with
  | zero =>
    intro j out s _
    exact validWhpProg_pure _
  | succ m ih =>
    intro j out s hjm
    have hj : j < d := by omega
    obtain ⟨hvp_in, hst_in⟩ := validWhpProg_innerLoop (w₀ := w₀) (R := R) (M_out := M_out)
      hw hj hseg c_tab 0 0 rKey s (Nat.zero_add _).le
    have hinv_in := BitPackedDoubleTabulation.innerLoop_invariant (s := s) henv
      (by dsimp only [hpD_mk]; exact hj) c_tab 0 0 rKey
      (by dsimp only [hpCTab_mk]; omega) (by dsimp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
    dsimp only [hpPowB_mk] at hinv_in
    have hidx_s : (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val <
        BitPackedDoubleTabulation.topEntries c_tab d b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d b_char
        ⟨c_tab, by omega⟩ ⟨j, hj⟩ ⟨s_val, hs_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords,
        BitPackedDoubleTabulation.topEntries] at h ⊢
      omega
    have hy_lt : ((Memory.spec 0).clientResult s
        (BitPackedDoubleTabulation.innerLoopGenProg
          (((hp, (hBase, j)), ((0, 0), rKey)), c_tab))).1.2 ^^^
        readPacked (hBase + 1) b_char w s.mem
          ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val) < 2 ^ b_char :=
      Nat.xor_lt_two_pow hinv_in.2.2 (readPacked_lt _ _ _ _ _)
    have hidx₂ : j * 2 ^ b_char +
        (((Memory.spec 0).clientResult s
          (BitPackedDoubleTabulation.innerLoopGenProg
            (((hp, (hBase, j)), ((0, 0), rKey)), c_tab))).1.2 ^^^
          readPacked (hBase + 1) b_char w s.mem
            ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val)) <
        BitPackedDoubleTabulation.botEntries d b_char := by
      calc _ < j * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hy_lt _
        _ = (j + 1) * 2 ^ b_char := by ring
        _ ≤ d * 2 ^ b_char := Nat.mul_le_mul_right _ hj
    have hstep_vp : ValidWhpProg w F s
        (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out))) := by
      unfold BitPackedDoubleTabulation.outerStepGenProg
      simp only [hp, pure_bind, hpCTab_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk,
        hpOffBot_mk, hpMOut_mk]
      refine validWhpProg_bind hvp_in ?_
      rw [hst_in]
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx_s htop_seg) ?_
      have hrp1_st : (Memory.spec 0).clientState s
          (BitPackedDoubleTabulation.readPackedGenProg (((hBase, 1), (b_char, w)),
            (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val)) = s := rfl
      have hrp1_res : (Memory.spec 0).clientResult s
          (BitPackedDoubleTabulation.readPackedGenProg (((hBase, 1), (b_char, w)),
            (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val)) =
          readPacked (hBase + 1) b_char w s.mem
            ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val) :=
        BitPackedDoubleTabulation.clientResult_readPackedProg _ _ _ _ _ _
      rw [hrp1_st, hrp1_res]
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx₂ hbot_seg) ?_
      exact validWhpProg_pure _
    have hstep_st : (Memory.spec 0).clientState s
        (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out))) =
        s := by
      unfold BitPackedDoubleTabulation.outerStepGenProg
        BitPackedDoubleTabulation.readPackedGenProg
      simp only [hp, pure_bind, hpCTab_mk]
      rw [StateTransitionSpec.clientState_bind, hst_in,
        StateTransitionSpec.clientState_bind, BitPackedDoubleTabulation.clientState_readPackedProg,
        StateTransitionSpec.clientState_bind, BitPackedDoubleTabulation.clientState_readPackedProg]
      rfl
    set res₁ := (Memory.spec 0).clientResult s
      (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out)))
    have hj_eq : res₁.1 = j + 1 := by
      dsimp only [res₁]
      unfold BitPackedDoubleTabulation.outerStepGenProg
        BitPackedDoubleTabulation.readPackedGenProg
      simp only [hp, pure_bind, hpCTab_mk]
      rw [StateTransitionSpec.clientResult_bind, hst_in,
        StateTransitionSpec.clientResult_bind, BitPackedDoubleTabulation.clientState_readPackedProg,
        StateTransitionSpec.clientResult_bind, BitPackedDoubleTabulation.clientState_readPackedProg]
      rfl
    change ValidWhpProg w F s
      (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out)) >>=
        fun x => BitPackedDoubleTabulation.outerLoopGenProg
          (((hp, (hBase, (s_val, rKey))), x), m))
    refine validWhpProg_bind hstep_vp ?_
    rw [hstep_st]
    have hrec := ih res₁.1 res₁.2 s (by rw [hj_eq]; omega)
    rwa [Prod.mk.eta] at hrec

private theorem evalHashGenProg_spec {U w w₀ R c_tab d b_char M_out s_max hBase F : ℕ}
    {θ : BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (henv : HashEnv w (mkHashParams w w₀ R c_tab d b_char M_out) hBase)
    (hw : 0 < w) (hw₀ : 0 < w₀) (_hU_pow : U ≤ 2 ^ w₀) (hs_max : s_max ≤ 2 ^ b_char)
    (hseg : hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out ≤ F)
    (hrep : BitPackedDoubleTabulation.SeedRep hBase w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (u : Fin U) :
    let prog := evalHashGenProg
      (mkHashParams w w₀ R c_tab d b_char M_out, ((hBase, salt.val), u.val))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (evalSalted U w₀ R c_tab d b_char M_out s_max θ (salt, u)).val ∧
    memoryCost prog s = 1 + 2 * d * (c_tab + 2) ∧
    ValidWhpProg w F s prog := by
  dsimp only
  have hsp_pos := BitPackedDoubleTabulation.space_pos w c_tab d b_char M_out
  have hs1 := stage1RedGenProg_spec (R := R) hw₀ (by omega : hBase < F) hrep u
  have hol_vp := validWhpProg_outerLoop henv hw (salt.isLt.trans_le hs_max) hseg
    (rKey := (Memory.spec 0).clientResult s
      (stage1RedGenProg (mkHashParams w w₀ R c_tab d b_char M_out, (hBase, u.val))))
    d 0 0 s (Nat.zero_add _).le
  have hvp : ValidWhpProg w F s
      (evalHashGenProg (mkHashParams w w₀ R c_tab d b_char M_out, ((hBase, salt.val), u.val))) := by
    unfold evalHashGenProg
    simp only [pure_bind, hpD_mk]
    refine validWhpProg_bind hs1.2.2.2 ?_
    rw [hs1.1]
    refine validWhpProg_bind hol_vp ?_
    exact validWhpProg_pure _
  rw [evalHashGenProg_eq_evalGenProg] at hvp ⊢
  have heq : BitPackedDoubleTabulation.evalGenProg
      (mkHashParams w w₀ R c_tab d b_char M_out, ((hBase, salt.val), u.val)) =
      BitPackedDoubleTabulation.evalProg w w₀ R c_tab d b_char M_out
        ((hBase, salt.val), u.val) := rfl
  obtain ⟨hres, hst⟩ := BitPackedDoubleTabulation.evalProg_spec (R := R) hw₀ hs_max hrep salt u
  have hmc := BitPackedDoubleTabulation.memoryCost_evalProg w w₀ R c_tab d b_char M_out
    ((hBase, salt.val), u.val) s
  rw [heq] at hvp ⊢
  exact ⟨hst, hres, hmc, hvp⟩

/-! ## Section 2: Compact 38-Word Hash Runtime Parameter Bundle (`HashRt`) -/

/-- Compact 38-word runtime parameter bundle `(hp₁, hp₂, base, U, bWhp, maskBkt, sMax, offHashFp)`.
-/
abbrev HashRt : Type :=
  (HashParams × HashParams) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))

@[expose] def hrHpBkt (hrt : HashRt) : HashParams := hrt.1.1
@[expose] def hrHpFp (hrt : HashRt) : HashParams := hrt.1.2
@[expose] def hrBase (hrt : HashRt) : ℕ := hrt.2.1.1
@[expose] def hrULim (hrt : HashRt) : ℕ := hrt.2.1.2
@[expose] def hrBBits (hrt : HashRt) : ℕ := hrt.2.2.1.1
@[expose] def hrMaskBkt (hrt : HashRt) : ℕ := hrt.2.2.1.2
@[expose] def hrSMax (hrt : HashRt) : ℕ := hrt.2.2.2.1
@[expose] def hrOffFp (hrt : HashRt) : ℕ := hrt.2.2.2.2

/-- Pure constructor for `HashRt` in the large regime. -/
@[expose] def mkHashRt (c U w n_max base : ℕ) : HashRt :=
  ((mkHashParams w (w0Whp U) (rRedWhp c n_max)
      (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max),
    mkHashParams w (w0Whp U) (rRedWhp c n_max)
      (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)),
   ((base, U), ((bWhp n_max, numBucketsWhp n_max - 1), (sMaxWhp c n_max, offHashFp c w n_max))))

/-- Runtime envelope for `hrt : HashRt` coupled with `SeedWhpMemRep`. -/
@[expose] def HashRtEnv (w : ℕ) (hrt : HashRt) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w (hrBase hrt) ∧
    hrt = mkHashRt c U w₀ n_max (hrBase hrt) ∧
    SeedWhpMemRep (hrBase hrt) c U w₀ n_max θ s.mem

/-- Extract `HashRt` from `(wp, base) : WhpParams × ℕ` in 0 memory operations. -/
@[irreducible] def mkHashRtGenProg (d : WhpParams × ℕ) : Memory.Prog HashRt := do
  let cp := d.1.1
  let uLim ← pure (wpU cp)
  let bBits ← pure (wpBWhp cp)
  let maskBkt ← pure (wpMaskBkt cp)
  let sMax ← pure (wpSMax cp)
  let offFp ← pure (wpOffHashFp cp)
  pure (d.1.2, ((d.2, uLim), ((bBits, maskBkt), (sMax, offFp))))

theorem realizes_mkHashRtGen :
    Realizes .exact mkHashRtGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := HashRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold mkHashRtGenProg
  realize

theorem mkHashRtGenProg_spec {c U V w n_max base : ℕ} (hth : whpThreshold c ≤ n_max)
    (s : Memory.State) :
    let prog := mkHashRtGenProg (mkWhpParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkHashRt c U w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkHashRtGenProg
  simp only [pure_bind]
  have hwp : mkWhpParams c U V w n_max =
      (mkWhpCoreParams c U V w n_max,
       (mkHashParams w (w0Whp U) (rRedWhp c n_max)
          (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max),
        mkHashParams w (w0Whp U) (rRedWhp c n_max)
          (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))) := by
    unfold mkWhpParams; exact ite_eq_right (Nat.not_lt.mpr hth)
  rw [hwp, wp_large_U hth, wp_large_bWhp hth, wp_large_maskBkt hth, wp_large_sMax hth,
    wp_large_offHashFp hth]
  exact ⟨rfl, rfl, rfl, validWhpProg_pure _⟩

private theorem hashRt_segments_le {c U V w n_max base : ℕ} :
    base + offHashBkt +
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offHashFp c w n_max +
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
        (fpBitsWhp n_max) ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offHashFp c w n_max < base + largeSpaceWhp c U V w n_max := by
  have hsp2 := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max)
  have hend := largeOffsets_eq c U V w n_max
  have h1 : offHashBkt = 32 := rfl
  have h2 : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have h3 : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
  have h4 : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have h5 : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have h6 : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
  have h7 : offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
  have h8 : offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
  have h9 : offBackPtr c U V w n_max =
      offFbStart c U V w n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w := rfl
  have h10 : offBackAux c U V w n_max =
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
  have h11 : offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w := rfl
  have h12 : offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have h13 : offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have h14 : offBtKeys c U V w n_max =
      offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w := rfl
  have h15 : offBtVals c U V w n_max =
      offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w := rfl
  have h16 : offTrieChild0 c U V w n_max =
      offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w := rfl
  have h17 : offTrieChild1 c U V w n_max =
      offTrieChild0 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have h18 : offTrieMeta0 c U V w n_max =
      offTrieChild1 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have h19 : offTrieMeta1 c U V w n_max =
      offTrieMeta0 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have h20 : offTrieItems0 c U V w n_max =
      offTrieMeta1 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have h21 : offTrieItems1 c U V w n_max =
      offTrieItems0 c U V w n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  unfold bktHashWords at h2
  unfold fpHashWords at h3
  exact ⟨by omega, by omega, by omega⟩

/-! ## Section 3: Certified `bktHash`, Feistel Split/Reconstruct, `fpReducedKey`, `fpOfSalt` -/

/-- Compute `bktHash c U n_max θ.1 q` (`d = (hrt, q)`, works for any `q : ℕ`). -/
@[irreducible] def bktHashRtProg (d : HashRt × ℕ) : Memory.Prog ℕ := do
  let hrt := d.1
  let q ← pure d.2
  let uLim ← pure (hrULim hrt)
  if q < uLim then
    let off32 ← pure 32
    let hBaseBkt ← pure (hrBase hrt + off32)
    let zero_v ← pure 0
    evalHashGenProg (hrHpBkt hrt, ((hBaseBkt, zero_v), q))
  else
    pure 0

theorem realizes_bktHashRt :
    Realizes .exact bktHashRtProg
      (WordEncoding.encode (α := HashRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => HashRtEnv w d.1 s)
      (fun _ _ => 0) := by
  unfold bktHashRtProg
  have heh := realizes_evalHashGen
  realize
  all_goals (
    rcases d with ⟨hrt, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hth := henv.2.2.2.1
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hU_eq : hrULim hrt = U := by rw [heq_hrt]; rfl
    have hHp_eq : hrHpBkt hrt = mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) := by rw [heq_hrt]; rfl
    obtain ⟨henv1, _⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
    dsimp only [hrBase] at *
    try exact henv.fits_const (by decide)
  )
  · refine henv.fits_largeSpace.of_le ?_
    have hseg1 := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
      (base := hrt.2.1.1)).1
    have hsp1 := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (bWhp n_max)
    dsimp only [offHashBkt, hdrWordsWhp] at hseg1
    omega
  · dsimp only [EvalHashPre]
    rw [hHp_eq]
    dsimp only [offHashBkt, hdrWordsWhp] at henv1
    refine ⟨henv1, ?_, by simp [hpPowB_mk], ?_⟩
    · dsimp only [hpMaskM_mk]
      change s.mem (hrt.2.1.1 + offHashBkt) ≤ _
      rw [hseed.1.1]
      have := θ.1.1.isLt; omega
    · dsimp only [hpMaskM_mk]
      rw [Nat.shiftLeft_eq, pow_one]
      have hw0 := w0Whp_pos U
      have hpow : 2 * 2 ^ (w0Whp U - 1) = 2 ^ w0Whp U := by
        rw [← pow_succ', Nat.sub_add_cancel hw0]
      have : 1 ≤ 2 ^ (w0Whp U - 1) := Nat.one_le_two_pow
      have hqU : q < 2 ^ w0Whp U := (by rwa [← hU_eq] : q < U).trans_le (le_two_pow_w0Whp U)
      omega

theorem bktHashRtProg_spec {c U V w n_max base q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := bktHashRtProg (mkHashRt c U w n_max base, q)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = bktHash c U n_max θ.1 q ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨henv1, _⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
  have hseg1 := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
    (base := base)).1
  dsimp only
  unfold bktHashRtProg bktHash
  simp only [pure_bind]
  have hULim : hrULim (mkHashRt c U w n_max base) = U := rfl
  have hBase : hrBase (mkHashRt c U w n_max base) = base := rfl
  have hHpBkt : hrHpBkt (mkHashRt c U w n_max base) =
      mkHashParams w (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (bWhp n_max) := rfl
  rw [hULim, hBase, hHpBkt]
  by_cases hq : q < U
  · rw [ite_eq_left hq, dite_eq_left hq]
    have hev := evalHashGenProg_spec henv1 hw (w0Whp_pos U) (le_two_pow_w0Whp U)
      Nat.one_le_two_pow hseg1 hseed.1 ⟨0, Nat.zero_lt_one⟩ ⟨q, hq⟩
    dsimp only [offHashBkt, hdrWordsWhp] at hev
    exact ⟨hev.1, hev.2.1, hev.2.2.1.le, hev.2.2.2⟩
  · rw [ite_eq_right hq, dite_eq_right hq]
    exact ⟨rfl, rfl, Nat.zero_le _, validWhpProg_pure 0⟩

/-- Split any `u_val : ℕ` into `(feistelBucket, keyQuotient)`. -/
@[irreducible] def feistelSplitRtProg (d : HashRt × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let hrt := d.1
  let u_val ← pure d.2
  let q ← pure (u_val >>> hrBBits hrt)
  let low ← pure (u_val &&& hrMaskBkt hrt)
  let h ← bktHashRtProg (hrt, q)
  let h_low ← pure (h &&& hrMaskBkt hrt)
  let b ← pure (h_low ^^^ low)
  pure (b, q)

theorem realizes_feistelSplitRt :
    Realizes .exact feistelSplitRtProg
      (WordEncoding.encode (α := HashRt × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d s => HashRtEnv w d.1 s)
      (fun _ _ => 0) := by
  unfold feistelSplitRtProg
  have hbh := realizes_bktHashRt
  realize
  all_goals (
    rcases d with ⟨hrt, u_val⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hM_lt : numBucketsWhp n_max < 2 ^ w :=
      henv.numBuckets_le_n_max.trans_lt (henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1)
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed⟩
    | (rw [heq_hrt]; dsimp only [mkHashRt, hrMaskBkt, numBucketsWhp]
       rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
       exact (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
         (Nat.mod_lt _ (Nat.two_pow_pos _))).trans hM_lt)
  )

theorem feistelSplitRtProg_spec {c U V w n_max base u_val : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := feistelSplitRtProg (mkHashRt c U w n_max base, u_val)
    let q := keyQuotient (bWhp n_max) u_val
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (b, q) ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  set q := u_val >>> bWhp n_max
  obtain ⟨hst, hres, hmc, hvp⟩ := bktHashRtProg_spec (q := q) henv hseed (s := s)
  have hq_eq : q = keyQuotient (bWhp n_max) u_val := Nat.shiftRight_eq_div_pow u_val (bWhp n_max)
  dsimp only
  unfold feistelSplitRtProg
  simp only [pure_bind]
  have hBBits : hrBBits (mkHashRt c U w n_max base) = bWhp n_max := rfl
  have hMask : hrMaskBkt (mkHashRt c U w n_max base) = numBucketsWhp n_max - 1 := rfl
  rw [hBBits, hMask]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hst]; rfl
  · rw [StateTransitionSpec.clientResult_bind, hst, hres, StateTransitionSpec.clientResult_pure]
    apply Prod.ext
    · unfold feistelBucket keyLow numBucketsWhp
      rw [← hq_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    · exact hq_eq
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst, memoryCost_pure, Nat.add_zero]
    exact hmc
  · refine validWhpProg_bind hvp ?_
    rw [hst]
    exact validWhpProg_pure _

/-- Reconstruct key `feistelReconstruct (bWhp n_max) (bktHash ...) b q` (`d = ((hrt, b), q)` with
`q < 2 ^ quotBitsWhp U n_max`). -/
@[irreducible] def feistelReconstructRtProg (d : (HashRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let hrt := d.1.1
  let b ← pure d.1.2
  let q ← pure d.2
  let h ← bktHashRtProg (hrt, q)
  let h_low ← pure (h &&& hrMaskBkt hrt)
  let b_low ← pure (b &&& hrMaskBkt hrt)
  let low ← pure (h_low ^^^ b_low)
  let hi ← pure (q <<< hrBBits hrt)
  pure (hi + low)

/-- Precondition for subroutines taking a stored quotient `q < 2 ^ quotBitsWhp U n_max`. -/
@[expose] def QuotHashRtEnv (w : ℕ) (hrt : HashRt) (q : ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w (hrBase hrt) ∧
    hrt = mkHashRt c U w₀ n_max (hrBase hrt) ∧
    SeedWhpMemRep (hrBase hrt) c U w₀ n_max θ s.mem ∧
    q < 2 ^ quotBitsWhp U n_max

theorem realizes_feistelReconstructRt :
    Realizes .exact feistelReconstructRtProg
      (WordEncoding.encode (α := (HashRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => QuotHashRtEnv w d.1.1 d.2 s)
      (fun _ _ => 0) := by
  unfold feistelReconstructRtProg
  have hbh := realizes_bktHashRt
  realize
  all_goals (
    rcases d with ⟨⟨hrt, b⟩, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hnU := henv.2.2.2.2.1
    have hU := henv.2.2.2.2.2.1
    have hM_lt : numBucketsWhp n_max < 2 ^ w :=
      henv.numBuckets_le_n_max.trans_lt (hnU.trans_lt hU)
    have hkb_w : 2 ^ keyBits U ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (keyBits_le_w hU)
    have hsplit := quotBitsWhp_add_bWhp hnU
    have hhi_add_lt : ∀ low < 2 ^ bWhp n_max, q * 2 ^ bWhp n_max + low < 2 ^ w := by
      intro low hlow
      calc q * 2 ^ bWhp n_max + low
          < q * 2 ^ bWhp n_max + 2 ^ bWhp n_max := Nat.add_lt_add_left hlow _
        _ = (q + 1) * 2 ^ bWhp n_max := by ring
        _ ≤ 2 ^ quotBitsWhp U n_max * 2 ^ bWhp n_max := Nat.mul_le_mul_right _ hq_lt
        _ = 2 ^ keyBits U := by rw [← Nat.pow_add, hsplit]
        _ ≤ 2 ^ w := hkb_w
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed⟩
    | (rw [heq_hrt]; dsimp only [mkHashRt, hrMaskBkt, hrBBits, numBucketsWhp, Fits]
       first
       | (rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
          exact (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.mod_lt _ (Nat.two_pow_pos _))).trans hM_lt)
       | (rw [Nat.shiftLeft_eq]
          exact (Nat.le_add_right _ 0).trans_lt (hhi_add_lt 0 (Nat.two_pow_pos _)))
       | (rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
          exact hhi_add_lt _ (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.mod_lt _ (Nat.two_pow_pos _)))))
  )

theorem feistelReconstructRtProg_spec {c U V w n_max base b q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := feistelReconstructRtProg ((mkHashRt c U w n_max base, b), q)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst, hres, hmc, hvp⟩ := bktHashRtProg_spec (q := q) henv hseed (s := s)
  dsimp only
  unfold feistelReconstructRtProg
  simp only [pure_bind]
  have hMask : hrMaskBkt (mkHashRt c U w n_max base) = numBucketsWhp n_max - 1 := rfl
  have hBBits : hrBBits (mkHashRt c U w n_max base) = bWhp n_max := rfl
  rw [hMask, hBBits]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hst]; rfl
  · rw [StateTransitionSpec.clientResult_bind, hst, hres, StateTransitionSpec.clientResult_pure]
    unfold feistelReconstruct numBucketsWhp
    rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst, memoryCost_pure, Nat.add_zero]
    exact hmc
  · refine validWhpProg_bind hvp ?_
    rw [hst]
    exact validWhpProg_pure _

/-- Compute `if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0` (`d = (hrt, kv)`). -/
@[irreducible] def fpReducedKeyOptRtProg (d : HashRt × ℕ) : Memory.Prog ℕ := do
  let hrt := d.1
  let kv ← pure d.2
  let uLim ← pure (hrULim hrt)
  if kv < uLim then
    let hBaseFp ← pure (hrBase hrt + hrOffFp hrt)
    stage1RedGenProg (hrHpFp hrt, (hBaseFp, kv))
  else
    pure 0

theorem realizes_fpReducedKeyOptRt :
    Realizes .exact fpReducedKeyOptRtProg
      (WordEncoding.encode (α := HashRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => HashRtEnv w d.1 s)
      (fun _ _ => 0) := by
  unfold fpReducedKeyOptRtProg
  have hs1 := realizes_stage1RedGen
  realize
  all_goals (
    rcases d with ⟨hrt, kv⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hth := henv.2.2.2.1
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hU_eq : hrULim hrt = U := by rw [heq_hrt]; rfl
    have hOff_eq : hrOffFp hrt = offHashFp c w n_max := by rw [heq_hrt]; rfl
    have hHp_eq : hrHpFp hrt = mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) := by rw [heq_hrt]; rfl
    obtain ⟨_, henv2⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
    dsimp only [hrBase] at *
  )
  · rw [hOff_eq]
    exact henv.fits_largeSpace.of_le (hashRt_segments_le (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := hrt.2.1.1)).2.2.le
  · dsimp only [Stage1RedPre]
    rw [hOff_eq, hHp_eq]
    refine ⟨henv2, ?_, ?_⟩
    · dsimp only [hpMaskM_mk]
      rw [hseed.2.1]
      have := θ.2.1.isLt; omega
    · dsimp only [hpMaskM_mk]
      rw [Nat.shiftLeft_eq, pow_one]
      have hw0 := w0Whp_pos U
      have hpow : 2 * 2 ^ (w0Whp U - 1) = 2 ^ w0Whp U := by
        rw [← pow_succ', Nat.sub_add_cancel hw0]
      have : 1 ≤ 2 ^ (w0Whp U - 1) := Nat.one_le_two_pow
      have hkvU : kv < 2 ^ w0Whp U := (by rwa [← hU_eq] : kv < U).trans_le (le_two_pow_w0Whp U)
      omega

theorem fpReducedKeyOptRtProg_spec {c U V w n_max base kv : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := fpReducedKeyOptRtProg (mkHashRt c U w n_max base, kv)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) ∧
    memoryCost prog s ≤ 1 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hh_lt := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
    (base := base)).2.2
  dsimp only
  unfold fpReducedKeyOptRtProg
  simp only [pure_bind]
  have hULim : hrULim (mkHashRt c U w n_max base) = U := rfl
  have hBase : hrBase (mkHashRt c U w n_max base) = base := rfl
  have hOffFp : hrOffFp (mkHashRt c U w n_max base) = offHashFp c w n_max := rfl
  have hHpFp : hrHpFp (mkHashRt c U w n_max base) =
      mkHashParams w (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (fpBitsWhp n_max) := rfl
  rw [hULim, hBase, hOffFp, hHpFp]
  by_cases hkv : kv < U
  · rw [ite_eq_left hkv, dite_eq_left hkv]
    have hs1 := stage1RedGenProg_spec (R := rRedWhp c n_max) (w0Whp_pos U) hh_lt hseed.2 ⟨kv, hkv⟩
    exact ⟨hs1.1, hs1.2.1, hs1.2.2.1.le, hs1.2.2.2⟩
  · rw [ite_eq_right hkv, dite_eq_right hkv]
    exact ⟨rfl, rfl, Nat.zero_le 1, validWhpProg_pure 0⟩

/-- Compute `if hs : salt < sMaxWhp then if hu : kv < U then fpHash θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
else 0` (`d = ((hrt, salt), kv)`). -/
@[irreducible] def fpOfSaltOptRtProg (d : (HashRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let hrt := d.1.1
  let salt ← pure d.1.2
  let kv ← pure d.2
  let sMax ← pure (hrSMax hrt)
  if salt < sMax then
    let uLim ← pure (hrULim hrt)
    if kv < uLim then
      let hBaseFp ← pure (hrBase hrt + hrOffFp hrt)
      evalHashGenProg (hrHpFp hrt, ((hBaseFp, salt), kv))
    else
      pure 0
  else
    pure 0

theorem realizes_fpOfSaltOptRt :
    Realizes .exact fpOfSaltOptRtProg
      (WordEncoding.encode (α := (HashRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => HashRtEnv w d.1.1 s)
      (fun _ _ => 0) := by
  unfold fpOfSaltOptRtProg
  have heh := realizes_evalHashGen
  realize
  all_goals (
    rcases d with ⟨⟨hrt, salt⟩, kv⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hth := henv.2.2.2.1
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hU_eq : hrULim hrt = U := by rw [heq_hrt]; rfl
    have hS_eq : hrSMax hrt = sMaxWhp c n_max := by rw [heq_hrt]; rfl
    have hOff_eq : hrOffFp hrt = offHashFp c w n_max := by rw [heq_hrt]; rfl
    have hHp_eq : hrHpFp hrt = mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) := by rw [heq_hrt]; rfl
    obtain ⟨_, henv2⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
    dsimp only [hrBase] at *
  )
  · rw [hOff_eq]
    exact henv.fits_largeSpace.of_le (hashRt_segments_le (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := hrt.2.1.1)).2.2.le
  · dsimp only [EvalHashPre]
    rw [hOff_eq, hHp_eq]
    refine ⟨henv2, ?_, ?_, ?_⟩
    · dsimp only [hpMaskM_mk]
      rw [hseed.2.1]
      have := θ.2.1.isLt; omega
    · dsimp only [hpPowB_mk]
      exact (by rwa [← hS_eq] : salt < sMaxWhp c n_max).trans_le (sMaxWhp_le_pow_bChar hth)
    · dsimp only [hpMaskM_mk]
      rw [Nat.shiftLeft_eq, pow_one]
      have hw0 := w0Whp_pos U
      have hpow : 2 * 2 ^ (w0Whp U - 1) = 2 ^ w0Whp U := by
        rw [← pow_succ', Nat.sub_add_cancel hw0]
      have : 1 ≤ 2 ^ (w0Whp U - 1) := Nat.one_le_two_pow
      have hkvU : kv < 2 ^ w0Whp U := (by rwa [← hU_eq] : kv < U).trans_le (le_two_pow_w0Whp U)
      omega

theorem fpOfSaltOptRtProg_spec {c U V w n_max base salt kv : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := fpOfSaltOptRtProg ((mkHashRt c U w n_max base, salt), kv)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
       else 0) ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨_, henv2⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
  have hseg2 := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
    (base := base)).2.1
  dsimp only
  unfold fpOfSaltOptRtProg
  simp only [pure_bind]
  have hSMax : hrSMax (mkHashRt c U w n_max base) = sMaxWhp c n_max := rfl
  have hULim : hrULim (mkHashRt c U w n_max base) = U := rfl
  have hBase : hrBase (mkHashRt c U w n_max base) = base := rfl
  have hOffFp : hrOffFp (mkHashRt c U w n_max base) = offHashFp c w n_max := rfl
  have hHpFp : hrHpFp (mkHashRt c U w n_max base) =
      mkHashParams w (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (fpBitsWhp n_max) := rfl
  rw [hSMax, hULim, hBase, hOffFp, hHpFp]
  by_cases hs : salt < sMaxWhp c n_max
  · rw [ite_eq_left hs, dite_eq_left hs]
    by_cases hu : kv < U
    · rw [ite_eq_left hu, dite_eq_left hu]
      have hev := evalHashGenProg_spec henv2 hw (w0Whp_pos U) (le_two_pow_w0Whp U)
        (sMaxWhp_le_pow_bChar hth) hseg2 hseed.2 ⟨salt, hs⟩ ⟨kv, hu⟩
      exact ⟨hev.1, hev.2.1, hev.2.2.1.le, hev.2.2.2⟩
    · rw [ite_eq_right hu, dite_eq_right hu]
      exact ⟨rfl, rfl, Nat.zero_le _, validWhpProg_pure 0⟩
  · rw [ite_eq_right hs, dite_eq_right hs]
    exact ⟨rfl, rfl, Nat.zero_le _, validWhpProg_pure 0⟩

/-- Composite `rKey` from `(b, q)` (`d = ((hrt, b), q)` with `q < 2 ^ quotBitsWhp U n_max`),
matching `FastState.rKeyAt` when `q = fs.quotArr (fs.physSlot n_max b loc)`. -/
@[irreducible] def rKeyOfQuotRtProg (d : (HashRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let kv ← feistelReconstructRtProg d
  fpReducedKeyOptRtProg (d.1.1, kv)

theorem realizes_rKeyOfQuotRt :
    Realizes .exact rKeyOfQuotRtProg
      (WordEncoding.encode (α := (HashRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => QuotHashRtEnv w d.1.1 d.2 s)
      (fun _ _ => 0) := by
  unfold rKeyOfQuotRtProg
  have hfr := realizes_feistelReconstructRt
  have hrk := realizes_fpReducedKeyOptRt
  realize
  all_goals (
    rcases d with ⟨⟨hrt, b⟩, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
  )
  · exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩
  · have hst : (Memory.spec 0).clientState s (feistelReconstructRtProg ((hrt, b), q)) = s := by
      rw [heq_hrt] at henv hseed ⊢
      exact (feistelReconstructRtProg_spec henv hseed).1
    rw [hst]
    exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed⟩

theorem rKeyOfQuotRtProg_spec {c U V w n_max base b q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := rKeyOfQuotRtProg ((mkHashRt c U w n_max base, b), q)
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 1 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst1, hres1, hmc1, hvp1⟩ :=
    feistelReconstructRtProg_spec (b := b) (q := q) henv hseed (s := s)
  set kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
  obtain ⟨hst2, hres2, hmc2, hvp2⟩ :=
    fpReducedKeyOptRtProg_spec (kv := kv) henv hseed (s := s)
  dsimp only
  unfold rKeyOfQuotRtProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst2]
  · rw [StateTransitionSpec.clientResult_bind, hst1, hres1, hres2]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst1, hres1]
    exact Nat.add_le_add hmc1 hmc2
  · refine validWhpProg_bind hvp1 ?_
    rw [hst1, hres1]
    exact hvp2

/-- Composite salted fingerprint from `(((hrt, salt), b), q)` (`q < 2 ^ quotBitsWhp U n_max`),
matching `FastState.fpAt` when `q = fs.quotArr (fs.physSlot n_max b loc)`. -/
@[irreducible] def fpOfQuotRtProg (d : ((HashRt × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let kv ← feistelReconstructRtProg ((d.1.1.1, d.1.2), d.2)
  fpOfSaltOptRtProg (d.1.1, kv)

theorem realizes_fpOfQuotRt :
    Realizes .exact fpOfQuotRtProg
      (WordEncoding.encode (α := ((HashRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => QuotHashRtEnv w d.1.1.1 d.2 s)
      (fun _ _ => 0) := by
  unfold fpOfQuotRtProg
  have hfr := realizes_feistelReconstructRt
  have hfp := realizes_fpOfSaltOptRt
  realize
  all_goals (
    rcases d with ⟨⟨⟨hrt, salt⟩, b⟩, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
  )
  · exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩
  · have hst : (Memory.spec 0).clientState s (feistelReconstructRtProg ((hrt, b), q)) = s := by
      rw [heq_hrt] at henv hseed ⊢
      exact (feistelReconstructRtProg_spec henv hseed).1
    rw [hst]
    exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed⟩

theorem fpOfQuotRtProg_spec {c U V w n_max base salt b q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := fpOfQuotRtProg (((mkHashRt c U w n_max base, salt), b), q)
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
       else 0) ∧
    memoryCost prog s ≤ 2 * hashEvalCostWhp c ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst1, hres1, hmc1, hvp1⟩ :=
    feistelReconstructRtProg_spec (b := b) (q := q) henv hseed (s := s)
  set kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
  obtain ⟨hst2, hres2, hmc2, hvp2⟩ :=
    fpOfSaltOptRtProg_spec (salt := salt) (kv := kv) henv hseed (s := s)
  dsimp only
  unfold fpOfQuotRtProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst2]
  · rw [StateTransitionSpec.clientResult_bind, hst1, hres1, hres2]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst1, hres1, Nat.two_mul]
    exact Nat.add_le_add hmc1 hmc2
  · refine validWhpProg_bind hvp1 ?_
    rw [hst1, hres1]
    exact hvp2

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
