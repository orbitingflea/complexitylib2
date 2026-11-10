/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.SuccinctWhpModelStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Insertion, Global Epoch Ticks, and Sequence Refinement for the Pure WHP Succinct Dictionary

This module completes the deterministic step-correctness proofs for `SuccinctWhpModel`
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]):

* `ValidFastState.fastInsert_spec`: fast-mode insertion / overwrite refines
  `Dynamic.step dict (.insert u v)` and yields `CoreFastInv`, `OvermarsBucketInv`, and
  `ValidEpochStage` whenever `fastInsert` returns `some fs'`.
* `epochTick_spec`: global `O_c(1)` deamortization across Stages `0 .. 5` and epoch rollover
  restores full `ValidFastState` from `CoreFastInv` + `OvermarsBucketInv` +
  `ValidEpochStagePreTick` whenever `epochTick` returns `some fs'`.
* `ValidFastState.fastStepPure_spec`, `whpStepPure_spec`, `whpRunFrom_spec`, `whpRunPure_spec`:
  exact `Dynamic.step` / `Dynamic.run` refinement for **every** static seed `θ` across all modes
  (`.small`, `.fast`, `.fallback`, and seamless `fastToCsr` / `trySelfHeal` transitions).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 1: Backyard pool allocation & `ValidFastState.fastInsert_spec` -/

private theorem fpAt_lt' {c U n_max : ℕ} (θ : SeedWhp c U n_max) (fs : FastState)
    (salt b loc : ℕ) : fs.fpAt c U n_max θ salt b loc < 2 ^ fpBitsWhp n_max := by
  dsimp only [FastState.fpAt]
  split_ifs with hs hu
  · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨_, hu⟩
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

private theorem fpOfSalt_lt {c U n_max : ℕ} (θ₂ : FpSeed c U n_max) (salt : ℕ) (u : Fin U) :
    fpOfSalt c U n_max θ₂ salt u < 2 ^ fpBitsWhp n_max := by
  dsimp only [fpOfSalt]
  split_ifs with hs
  · exact fpHash_lt c U n_max θ₂ ⟨salt, hs⟩ u
  · exact Nat.two_pow_pos _

private theorem valLane_pow_eq' (n_max : ℕ) :
    2 ^ valLaneBitsWhp n_max = 256 * (scaleWhp n_max) ^ 12 := by
  have hsc : scaleWhp n_max = 2 ^ ellWhp n_max := rfl
  unfold valLaneBitsWhp
  rw [hsc, Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm _ 12]
  ring

private theorem quot_lt_pow {U n_max : ℕ} (hnU : n_max ≤ U) (u : Fin U) :
    keyQuotient (bWhp n_max) u.val < 2 ^ quotBitsWhp U n_max := by
  have hsplit := (quotBitsWhp_add_bWhp hnU).symm
  have hu_pow : u.val < 2 ^ keyBits U :=
    u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)
  unfold keyQuotient
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, ← hsplit]
  exact hu_pow

private theorem oldEp_or' {fs : FastState} (h : fs.curEp = 0 ∨ fs.curEp = 1) :
    fs.oldEp = 0 ∨ fs.oldEp = 1 := by
  rcases h with hc | hc <;> simp [FastState.oldEp, hc]

private theorem curEp_ne_oldEp {fs : FastState} (h : fs.curEp = 0 ∨ fs.curEp = 1) :
    fs.curEp ≠ fs.oldEp := by
  rcases h with hc | hc <;> simp [FastState.oldEp, hc]

private theorem BufMapRel.insert_skip {M tag b₀ : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hst_new : locSt' b₀ (bktCnt b₀) ≠ tag)
    (hst_pres : ∀ b < M, ∀ loc < bktCnt b, locSt' b loc = locSt b loc)
    (hrk_pres : ∀ b < M, ∀ loc < bktCnt b, rKeyOf' b loc = rKeyOf b loc) :
    BufMapRel M tag (Function.update bktCnt b₀ (bktCnt b₀ + 1)) locSt' rKeyOf' m := by
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  rw [hrel.2 rk b loc]
  refine ⟨fun ⟨hb, hloc, hst0, hrk0⟩ => ?_, fun ⟨hb, hloc_upd, hst', hrk'⟩ => ?_⟩
  · refine ⟨hb, ?_, (hst_pres b hb loc hloc).trans hst0, (hrk_pres b hb loc hloc).trans hrk0⟩
    by_cases hbb : b = b₀
    · subst hbb; rw [Function.update_self]; exact Nat.lt_succ_of_lt hloc
    · rwa [Function.update_of_ne hbb]
  · by_cases hbb : b = b₀
    · subst hbb
      rw [Function.update_self] at hloc_upd
      rcases Nat.lt_succ_iff_lt_or_eq.mp hloc_upd with hlt | rfl
      · exact ⟨hb, hlt, (hst_pres b hb loc hlt).symm.trans hst',
          (hrk_pres b hb loc hlt).symm.trans hrk'⟩
      · exact absurd hst' hst_new
    · rw [Function.update_of_ne hbb] at hloc_upd
      exact ⟨hb, hloc_upd, (hst_pres b hb loc hloc_upd).symm.trans hst',
        (hrk_pres b hb loc hloc_upd).symm.trans hrk'⟩

/-- Allocating coordinate `X = fs.bktCount b` (`X < totalLocalCoordsWhp n_max`, with
`0 < fs.poolFreeTop` whenever `capFrontWhp n_max ≤ X`) preserves all backyard-pool invariants,
preserves `physSlot` on all existing active coordinates `loc < fs.bktCount b'`, and yields a fresh
physical slot `fs'.physSlot n_max b X` disjoint from all existing active slots. -/
private theorem pool_alloc_new {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hX_lt : fs.bktCount b < totalLocalCoordsWhp n_max)
    (htop_pos : capFrontWhp n_max ≤ fs.bktCount b → 0 < fs.poolFreeTop)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b (fs.bktCount b + 1))
    (hstk' : fs'.poolFreeStack = fs.poolFreeStack)
    (htop' : fs'.poolFreeTop =
      if capFrontWhp n_max ≤ fs.bktCount b then fs.poolFreeTop - 1 else fs.poolFreeTop)
    (hbp' : fs'.backPtr =
      if capFrontWhp n_max ≤ fs.bktCount b then
        Function.update fs.backPtr b
          (Function.update (fs.backPtr b) (fs.bktCount b - capFrontWhp n_max)
            (fs.poolFreeStack (fs.poolFreeTop - 1)))
      else fs.backPtr)
    (hown' : fs'.poolOwner =
      if capFrontWhp n_max ≤ fs.bktCount b then
        Function.update fs.poolOwner (fs.poolFreeStack (fs.poolFreeTop - 1))
          (b * capBackWhp n_max + (fs.bktCount b - capFrontWhp n_max))
      else fs.poolOwner) :
    (∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fs'.physSlot n_max b' loc = fs.physSlot n_max b' loc ∧
      fs'.physSlot n_max b' loc ≠ fs'.physSlot n_max b (fs.bktCount b)) ∧
    fs'.poolFreeTop ≤ poolSizeWhp n_max ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
      fs'.backPtr b' k < poolSizeWhp n_max ∧
      fs'.poolOwner (fs'.backPtr b' k) = b' * capBackWhp n_max + k) ∧
    (∀ j < fs'.poolFreeTop, fs'.poolFreeStack j < poolSizeWhp n_max) ∧
    (∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fs'.bktCount b₁ - capFrontWhp n_max,
     ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fs'.bktCount b₂ - capFrontWhp n_max,
       fs'.backPtr b₁ k₁ = fs'.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂) ∧
    (∀ j₁ < fs'.poolFreeTop, ∀ j₂ < fs'.poolFreeTop,
      fs'.poolFreeStack j₁ = fs'.poolFreeStack j₂ → j₁ = j₂) ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
     ∀ j < fs'.poolFreeTop, fs'.backPtr b' k ≠ fs'.poolFreeStack j) ∧
    fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max := by
  set X := fs.bktCount b
  let cf := capFrontWhp n_max
  have hbp_pres : ∀ b' < numBucketsWhp n_max, ∀ k < fs.bktCount b' - cf,
      fs'.backPtr b' k = fs.backPtr b' k := by
    intro b' _ k hk
    rw [hbp']
    split_ifs with hcf
    · by_cases hbb : b' = b
      · subst hbb
        rw [Function.update_self, Function.update_of_ne (by omega)]
      · rw [Function.update_of_ne hbb]
    · rfl
  have hphys_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fs'.physSlot n_max b' loc = fs.physSlot n_max b' loc := by
    intro b' hb' loc hloc
    dsimp only [FastState.physSlot]
    split_ifs with hlt
    · rfl
    · rw [hbp_pres b' hb' (loc - cf) (by omega)]
  have hphys_ne : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fs'.physSlot n_max b' loc ≠ fs'.physSlot n_max b X := by
    intro b' hb' loc hloc
    rw [hphys_pres b' hb' loc hloc]
    dsimp only [FastState.physSlot]
    change (if loc < cf then b' * cf + loc
        else numBucketsWhp n_max * cf + fs.backPtr b' (loc - cf)) ≠
      (if X < cf then b * cf + X else numBucketsWhp n_max * cf + fs'.backPtr b (X - cf))
    by_cases hcf : cf ≤ X
    · have hp : ¬(X < cf) := by omega
      have htop0 := htop_pos hcf
      rw [ite_eq_right hp, hbp', ite_eq_left hcf, Function.update_self, Function.update_self]
      split_ifs with hlt
      · have : b' * cf + loc < numBucketsWhp n_max * cf := by
          calc b' * cf + loc < b' * cf + cf := by omega
            _ = (b' + 1) * cf := by ring
            _ ≤ numBucketsWhp n_max * cf := Nat.mul_le_mul_right cf hb'
        omega
      · intro heq
        have hbp_eq : fs.backPtr b' (loc - cf) = fs.poolFreeStack (fs.poolFreeTop - 1) := by omega
        exact hc.back_free_disj b' hb' (loc - cf) (by omega) (fs.poolFreeTop - 1) (by omega) hbp_eq
    · have hp : X < cf := by omega
      rw [ite_eq_left hp]
      split_ifs with hlt
      · intro heq
        have hcf_pos : 0 < cf := by omega
        have h1 : (b' * cf + loc) / cf = b' := by
          rw [Nat.mul_comm b' cf, Nat.mul_add_div hcf_pos, Nat.div_eq_of_lt hlt, add_zero]
        have h2 : (b * cf + X) / cf = b := by
          rw [Nat.mul_comm b cf, Nat.mul_add_div hcf_pos, Nat.div_eq_of_lt hp, add_zero]
        have hbb : b' = b := by rw [← h1, heq, h2]
        subst hbb
        omega
      · have : b * cf + X < numBucketsWhp n_max * cf := by
          calc b * cf + X < b * cf + cf := by omega
            _ = (b + 1) * cf := by ring
            _ ≤ numBucketsWhp n_max * cf := Nat.mul_le_mul_right cf hb
        omega
  have hsum_split_old := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs.bktCount b' - cf) (Finset.mem_range.mpr hb)
  have hsum_split_new := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs'.bktCount b' - cf) (Finset.mem_range.mpr hb)
  have herase_eq :
      ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs'.bktCount x - cf) =
        ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs.bktCount x - cf) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hbkt', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  have hcons : fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - cf) = poolSizeWhp n_max := by
    have hpc := hc.pool_conservation
    rw [← hsum_split_old] at hpc
    rw [← hsum_split_new, herase_eq, hbkt', Function.update_self, htop']
    split_ifs with hcf
    · have := htop_pos hcf; omega
    · omega
  refine ⟨fun b' hb' loc hloc => ⟨hphys_pres b' hb' loc hloc, hphys_ne b' hb' loc hloc⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, hcons⟩
  · rw [htop']; have := hc.poolFreeTop_le; split_ifs <;> omega
  · intro b' hb' k hk
    rw [hbkt'] at hk
    by_cases hcf : cf ≤ X
    · have htop0 := htop_pos hcf
      set pSlot := fs.poolFreeStack (fs.poolFreeTop - 1)
      have hp_lt : pSlot < poolSizeWhp n_max := hc.freeStack_lt _ (by omega)
      rw [hbp', hown', ite_eq_left hcf, ite_eq_left hcf]
      by_cases hbk : b' = b ∧ k = X - cf
      · rcases hbk with ⟨rfl, rfl⟩
        rw [Function.update_self, Function.update_self, Function.update_self]
        exact ⟨hp_lt, rfl⟩
      · have hk_old : k < fs.bktCount b' - cf := by
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hk
            have : k ≠ X - cf := fun h => hbk ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hbb] at hk
        have hbp_eq : Function.update fs.backPtr b
            (Function.update (fs.backPtr b) (X - cf) pSlot) b' k = fs.backPtr b' k := by
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self, Function.update_of_ne (fun h => hbk ⟨rfl, h⟩)]
          · rw [Function.update_of_ne hbb]
        rw [hbp_eq]
        have hne_ps : fs.backPtr b' k ≠ pSlot :=
          hc.back_free_disj b' hb' k hk_old (fs.poolFreeTop - 1) (by omega)
        rw [Function.update_of_ne hne_ps]
        exact hc.backPtr_valid b' hb' k hk_old
    · rw [hbp', hown', ite_eq_right hcf, ite_eq_right hcf]
      have hk_old : k < fs.bktCount b' - cf := by
        by_cases hbb : b' = b
        · subst hbb; rw [Function.update_self] at hk; omega
        · rwa [Function.update_of_ne hbb] at hk
      exact hc.backPtr_valid b' hb' k hk_old
  · intro j hj
    rw [htop'] at hj; rw [hstk']
    exact hc.freeStack_lt j (by split_ifs at hj <;> omega)
  · intro b₁ hb₁ k₁ hk₁ b₂ hb₂ k₂ hk₂ heq
    rw [hbkt'] at hk₁ hk₂
    by_cases hcf : cf ≤ X
    · have htop0 := htop_pos hcf
      set pSlot := fs.poolFreeStack (fs.poolFreeTop - 1)
      have eval_bp : ∀ b' < numBucketsWhp n_max,
          ∀ k < Function.update fs.bktCount b (X + 1) b' - cf,
          (b' = b ∧ k = X - cf ∧ fs'.backPtr b' k = pSlot) ∨
          (¬(b' = b ∧ k = X - cf) ∧ k < fs.bktCount b' - cf ∧
            fs'.backPtr b' k = fs.backPtr b' k) := by
        intro b' _ k hk
        by_cases hbk : b' = b ∧ k = X - cf
        · rcases hbk with ⟨rfl, rfl⟩
          left; refine ⟨rfl, rfl, ?_⟩
          rw [hbp', ite_eq_left hcf, Function.update_self, Function.update_self]
        · right
          have hk0 : k < fs.bktCount b' - cf := by
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hk
              have : k ≠ X - cf := fun h => hbk ⟨rfl, h⟩
              omega
            · rwa [Function.update_of_ne hbb] at hk
          exact ⟨hbk, hk0, hbp_pres b' ‹_› k hk0⟩
      rcases eval_bp b₁ hb₁ k₁ hk₁ with ⟨rfl, rfl, he1⟩ | ⟨_, hk1_0, he1⟩ <;>
        rcases eval_bp b₂ hb₂ k₂ hk₂ with ⟨rfl, rfl, he2⟩ | ⟨_, hk2_0, he2⟩
      · exact ⟨rfl, rfl⟩
      · rw [he1, he2] at heq
        exact absurd heq.symm (hc.back_free_disj b₂ hb₂ k₂ hk2_0 _ (by omega))
      · rw [he1, he2] at heq
        exact absurd heq (hc.back_free_disj b₁ hb₁ k₁ hk1_0 _ (by omega))
      · rw [he1, he2] at heq
        exact hc.backPtr_inj b₁ hb₁ k₁ hk1_0 b₂ hb₂ k₂ hk2_0 heq
    · have hk1_0 : k₁ < fs.bktCount b₁ - cf := by
        by_cases hbb : b₁ = b
        · subst hbb; rw [Function.update_self] at hk₁; omega
        · rwa [Function.update_of_ne hbb] at hk₁
      have hk2_0 : k₂ < fs.bktCount b₂ - cf := by
        by_cases hbb : b₂ = b
        · subst hbb; rw [Function.update_self] at hk₂; omega
        · rwa [Function.update_of_ne hbb] at hk₂
      rw [hbp', ite_eq_right hcf] at heq
      exact hc.backPtr_inj b₁ hb₁ k₁ hk1_0 b₂ hb₂ k₂ hk2_0 heq
  · intro j₁ hj₁ j₂ hj₂ heq
    rw [htop'] at hj₁ hj₂; rw [hstk'] at heq
    exact hc.freeStack_inj j₁ (by split_ifs at hj₁ <;> omega)
      j₂ (by split_ifs at hj₂ <;> omega) heq
  · intro b' hb' k hk j hj
    rw [hbkt'] at hk; rw [htop'] at hj; rw [hstk']
    by_cases hcf : cf ≤ X
    · rw [ite_eq_left hcf] at hj
      have htop0 := htop_pos hcf
      by_cases hbk : b' = b ∧ k = X - cf
      · rcases hbk with ⟨rfl, rfl⟩
        rw [hbp', ite_eq_left hcf, Function.update_self, Function.update_self]
        intro heq
        have := hc.freeStack_inj (fs.poolFreeTop - 1) (by omega) j (by omega) heq
        omega
      · have hk0 : k < fs.bktCount b' - cf := by
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hk
            have : k ≠ X - cf := fun h => hbk ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hbb] at hk
        rw [hbp_pres b' hb' k hk0]
        exact hc.back_free_disj b' hb' k hk0 j (by omega)
    · rw [ite_eq_right hcf] at hj
      have hk0 : k < fs.bktCount b' - cf := by
        by_cases hbb : b' = b
        · subst hbb; rw [Function.update_self] at hk; omega
        · rwa [Function.update_of_ne hbb] at hk
      rw [hbp_pres b' hb' k hk0]
      exact hc.back_free_disj b' hb' k hk0 j hj

private theorem inLiveTree_curEp_eq_false {fs : FastState} (hc : fs.curEp = 0 ∨ fs.curEp = 1)
    (doneB : ℕ) :
    inLiveTree fs.rebStage fs.oldEp doneB (2 + fs.curEp) = false := by
  rcases hc with h | h <;> simp [inLiveTree, FastState.oldEp, h]

private theorem liveInsCount_le_eight {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hom : OvermarsBucketInv c U n_max θ fs b) :
    fs.liveInsCount b ≤ 8 * (scaleWhp n_max) ^ 12 := by
  have hcnt3 : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12 :=
    (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  rcases hom with ⟨_, hlt⟩ | ⟨_, _, hcur, hlin, _, _⟩ <;> omega

private def fastInsertAlloc (n_max b X : ℕ) (fs : FastState) : FastState :=
  let cf := capFrontWhp n_max
  let allocTriple :=
    if cf ≤ X then
      let k := X - cf
      let top' := fs.poolFreeTop - 1
      let pSlot := fs.poolFreeStack top'
      (Function.update fs.backPtr b (Function.update (fs.backPtr b) k pSlot),
       (top',
        Function.update fs.poolOwner pSlot (b * capBackWhp n_max + k)))
    else
      (fs.backPtr, (fs.poolFreeTop, fs.poolOwner))
  { fs with
    backPtr := allocTriple.1
    poolFreeTop := allocTriple.2.1
    poolOwner := allocTriple.2.2 }

private def fastInsertFresh (c n_max b X q_val v rKey fp lIdx : ℕ)
    (hasFpCollision : Bool) (fsAlloc : FastState) : FastState :=
  let p_new := fsAlloc.physSlot n_max b X
  let qArr' := Function.update fsAlloc.quotArr p_new q_val
  let vArr' := Function.update fsAlloc.valArr p_new v
  if hasFpCollision then
    let ep := fsAlloc.curEp
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fsAlloc.buf ep) rKey b X
    { fsAlloc with
      quotArr := qArr'
      valArr := vArr'
      bktCount := Function.update fsAlloc.bktCount b (X + 1)
      locState := Function.update fsAlloc.locState b
        (Function.update (fsAlloc.locState b) X (2 + ep))
      buf := Function.update fsAlloc.buf ep tr' }
  else
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fsAlloc.slices lIdx) fp X
    { fsAlloc with
      quotArr := qArr'
      valArr := vArr'
      bktCount := Function.update fsAlloc.bktCount b (X + 1)
      locState := Function.update fsAlloc.locState b
        (Function.update (fsAlloc.locState b) X 1)
      slices := Function.update fsAlloc.slices lIdx sl'
      liveInsCount := Function.update fsAlloc.liveInsCount b (fsAlloc.liveInsCount b + 1) }

/-- Whenever `fastInsert` succeeds (`= some fs'`), `fs'` refines `Dynamic.step dict (.insert u v)`
and preserves `CoreFastInv`, `OvermarsBucketInv` on all buckets, and `ValidEpochStage` (hence also
`ValidEpochStagePreTick`). -/
theorem ValidFastState.fastInsert_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) {u : Fin U} {v : ℕ}
    (hvalid : Dynamic.valid V n_max dict (.insert u v))
    (hins : fastInsert c U n_max θ fs u v = some fs') :
    CoreFastInv c U V n_max θ fs' (Dynamic.step dict (.insert u v)).1 ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    ValidEpochStage c U n_max θ fs' ∧
    fs'.epochClock = fs.epochClock := by
  have hv_lt : v < V := hvalid.2
  have hv_max : v < max V 1 := hv_lt.trans_le (le_max_left V 1)
  have hfl := hv.fastFindLoc_spec u
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  dsimp only [fastInsert, Dynamic.step] at hins ⊢
  cases hfind : fastFindLoc c U n_max θ fs u with
  | some loc =>
    rw [hfind] at hins hfl
    simp only [Option.some.injEq] at hins
    obtain ⟨hloc_lt, hq_loc⟩ := hfl
    obtain ⟨_, hphys_inj⟩ := hv.physSlot_lt_and_inj
    set p := fs.physSlot n_max b loc
    set fs_ov : FastState := { fs with valArr := Function.update fs.valArr p v }
    have hc_ov : CoreFastInv c U V n_max θ fs_ov (Function.update dict u (some v)) :=
      { hth := hv.hth
        curEp_or := hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := fun p' => by
          dsimp only [fs_ov]
          by_cases hp : p' = p
          · subst hp; rw [Function.update_self]; exact ⟨(hv.qv_global _).1, hv_max⟩
          · rw [Function.update_of_ne hp]; exact hv.qv_global p'
        bktCount_le := hv.bktCount_le
        bktCount_ge_zero := hv.bktCount_ge_zero
        locState_active := hv.locState_active
        locState_inactive := hv.locState_inactive
        active_item := fun b' hb' l' hl' => by
          obtain ⟨h1', h2', h3', h4'⟩ := hv.active_item b' hb' l' hl'
          refine ⟨h1', h2', h3', ?_⟩
          have hp_eq : fs_ov.physSlot n_max b' l' = fs.physSlot n_max b' l' := rfl
          rw [hp_eq]
          dsimp only [fs_ov]
          by_cases hp : fs.physSlot n_max b' l' = p
          · rw [hp, Function.update_self]; exact hv_lt
          · rw [Function.update_of_ne hp]; exact h4'
        quot_inj := hv.quot_inj
        dict_map := fun u' => by
          dsimp only
          have hp_eq : fs_ov.physSlot n_max = fs.physSlot n_max := rfl
          rw [hp_eq]
          dsimp only [fs_ov]
          set b' := feistelBucket (bWhp n_max) h1 u'.val
          set q' := keyQuotient (bWhp n_max) u'.val
          have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
          by_cases hu' : u' = u
          · subst hu'
            have hb'_eq : b' = b := rfl
            have hq'_eq : q' = q_val := rfl
            rw [Function.update_self, hb'_eq, hq'_eq]
            refine ⟨⟨fun h => (by cases h), fun hall => absurd hq_loc (hall loc hloc_lt)⟩,
              fun v' => ⟨fun h => ?_, fun ⟨l', hl', hql, hvl⟩ => ?_⟩⟩
            · injection h with hv_eq; subst hv_eq
              exact ⟨loc, hloc_lt, hq_loc, Function.update_self _ _ _⟩
            · have hl_eq : l' = loc := hv.quot_inj b hb l' hl' loc hloc_lt (hql.trans hq_loc.symm)
              subst hl_eq
              rw [Function.update_self] at hvl
              exact congrArg some hvl
          · rw [Function.update_of_ne hu']
            obtain ⟨hn_iff, hs_iff⟩ := hv.dict_map u'
            refine ⟨hn_iff, fun v' => ?_⟩
            rw [hs_iff v']
            have hne_p_of : ∀ l' < fs.bktCount b',
                fs.quotArr (fs.physSlot n_max b' l') = q' → fs.physSlot n_max b' l' ≠ p := by
              intro l' hl' hql heq
              obtain ⟨hbb, hll⟩ := hphys_inj b' hb' l' hl' b hb loc hloc_lt heq
              have hqq : q' = q_val := by
                rw [← hql, hbb, hll, hq_loc]
              have huv : u'.val = u.val := by
                rw [← feistelReconstruct_feistelBucket (bWhp n_max) h1 u'.val,
                  ← feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val]
                change feistelReconstruct (bWhp n_max) h1 b' q' =
                  feistelReconstruct (bWhp n_max) h1 b q_val
                rw [hbb, hqq]
              exact hu' (Fin.ext huv)
            refine ⟨fun ⟨l', hl', hql, hvl⟩ => ⟨l', hl', hql, ?_⟩,
              fun ⟨l', hl', hql, hvl⟩ => ⟨l', hl', hql, ?_⟩⟩
            · rwa [Function.update_of_ne (hne_p_of l' hl' hql)]
            · rwa [Function.update_of_ne (hne_p_of l' hl' hql)] at hvl
        poolFreeTop_le := hv.poolFreeTop_le
        backPtr_valid := hv.backPtr_valid
        freeStack_lt := hv.freeStack_lt
        backPtr_inj := hv.backPtr_inj
        freeStack_inj := hv.freeStack_inj
        back_free_disj := hv.back_free_disj
        pool_conservation := hv.pool_conservation
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := hv.live_fp_inj
        live_valid := hv.live_valid
        rKey_buf_inj := hv.rKey_buf_inj
        bufCur_valid := hv.bufCur_valid
        bufOld_valid := hv.bufOld_valid }
    have hom_ov : ∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs_ov b' :=
      fun b' hb' => hv.overmars_valid b' hb'
    have hst_ov : ValidEpochStage c U n_max θ fs_ov := hv.stage_valid
    rw [← hins]
    obtain ⟨hc', hom', hst', _, _, hclk', _, _⟩ :=
      overmarsStep_spec hc_ov hb (fun b' hb' _ => hom_ov b' hb') (hom_ov b hb).toPre
    exact ⟨hc', hom', hst' hst_ov, hclk'⟩
  | none =>
    rw [hfind] at hins hfl
    have hno_q : ∀ loc < fs.bktCount b, fs.quotArr (fs.physSlot n_max b loc) ≠ q_val :=
      (hv.dict_map u).1.mp hfl
    set X := fs.bktCount b
    set cf := capFrontWhp n_max
    by_cases hg1 : totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0)
    · rw [ite_eq_left hg1] at hins; cases hins
    rw [ite_eq_right hg1] at hins
    have hX_lt : X < totalLocalCoordsWhp n_max := by omega
    have htop_pos : cf ≤ X → 0 < fs.poolFreeTop := by omega
    set rKey := fpReducedKey c U n_max θ.2 u
    have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
    by_cases hg2 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome)
    · rw [ite_eq_left hg2] at hins; cases hins
    rw [ite_eq_right hg2] at hins
    have hcur_lk_none : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = none := by
      cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey with
      | none => rfl
      | some _ => exact absurd (Or.inl (by simp [hlk])) hg2
    have hold_lk_none : fs.rebStage ≤ 3 →
        bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey = none := by
      intro hle3
      cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
      | none => rfl
      | some _ => exact absurd (Or.inr ⟨hle3, by simp [hlk]⟩) hg2
    set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    set lIdx := fs.liveSliceIdx b
    set hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp).isSome
    by_cases hg3 : hasFpCollision ∧
        !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
        2 * rIndepWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
    · rw [ite_eq_left hg3] at hins; cases hins
    rw [ite_eq_right hg3] at hins
    set fsAlloc := fastInsertAlloc n_max b X fs
    set fsIns := fastInsertFresh c n_max b X q_val v rKey fp lIdx hasFpCollision fsAlloc
    have hins_eq : overmarsStep c U n_max θ b fsIns = fs' := Option.some.inj hins
    rw [← hins_eq]
    -- Common facts about `fsIns` (holding in both `hasFpCollision = true` and `false` branches)
    have hfsIns_bkt : fsIns.bktCount = Function.update fs.bktCount b (X + 1) := by
      dsimp only [fsIns, fastInsertFresh, fsAlloc, fastInsertAlloc]; split_ifs <;> rfl
    have hfsIns_stk : fsIns.poolFreeStack = fs.poolFreeStack := by
      dsimp only [fsIns, fastInsertFresh, fsAlloc, fastInsertAlloc]; split_ifs <;> rfl
    have hfsIns_top : fsIns.poolFreeTop =
        if cf ≤ X then fs.poolFreeTop - 1 else fs.poolFreeTop := by
      dsimp only [fsIns, fastInsertFresh, fsAlloc, fastInsertAlloc]; split_ifs <;> rfl
    have hfsIns_bp : fsIns.backPtr =
        if cf ≤ X then
          Function.update fs.backPtr b
            (Function.update (fs.backPtr b) (X - cf) (fs.poolFreeStack (fs.poolFreeTop - 1)))
        else fs.backPtr := by
      dsimp only [fsIns, fastInsertFresh, fsAlloc, fastInsertAlloc]; split_ifs <;> rfl
    have hfsIns_own : fsIns.poolOwner =
        if cf ≤ X then
          Function.update fs.poolOwner (fs.poolFreeStack (fs.poolFreeTop - 1))
            (b * capBackWhp n_max + (X - cf))
        else fs.poolOwner := by
      dsimp only [fsIns, fastInsertFresh, fsAlloc, fastInsertAlloc]; split_ifs <;> rfl
    obtain ⟨hphys_pair, hpoolTop', hbp_val', hfree_lt', hbp_inj', hfree_inj', hdisj', hcons'⟩ :=
      pool_alloc_new hv.toCore hb hX_lt htop_pos hfsIns_bkt hfsIns_stk hfsIns_top hfsIns_bp
        hfsIns_own
    set p_new := fsAlloc.physSlot n_max b X
    have hp_new_eq : fsIns.physSlot n_max b X = p_new := by
      dsimp only [fsIns, fastInsertFresh, p_new, FastState.physSlot]; split_ifs <;> rfl
    have hfsIns_q : fsIns.quotArr = Function.update fs.quotArr p_new q_val := by
      have hqa : fsAlloc.quotArr = fs.quotArr := rfl
      dsimp only [fsIns, fastInsertFresh]; rw [hqa]; split_ifs <;> rfl
    have hfsIns_v : fsIns.valArr = Function.update fs.valArr p_new v := by
      have hva : fsAlloc.valArr = fs.valArr := rfl
      dsimp only [fsIns, fastInsertFresh]; rw [hva]; split_ifs <;> rfl
    have hqv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
        fsIns.quotArr (fsIns.physSlot n_max b' loc) = fs.quotArr (fs.physSlot n_max b' loc) ∧
        fsIns.valArr (fsIns.physSlot n_max b' loc) = fs.valArr (fs.physSlot n_max b' loc) := by
      intro b' hb' loc hloc
      obtain ⟨hp_eq, hp_ne⟩ := hphys_pair b' hb' loc hloc
      rw [hp_new_eq] at hp_ne
      rw [hp_eq] at hp_ne ⊢
      rw [hfsIns_q, hfsIns_v, Function.update_of_ne hp_ne, Function.update_of_ne hp_ne]
      exact ⟨rfl, rfl⟩
    have hkv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
        fsIns.keyValAt c U n_max θ.1 b' loc = fs.keyValAt c U n_max θ.1 b' loc := by
      intro b' hb' loc hloc
      dsimp only [FastState.keyValAt]
      rw [(hqv_pres b' hb' loc hloc).1]
    have hfp_pres : ∀ salt, ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
        fsIns.fpAt c U n_max θ salt b' loc = fs.fpAt c U n_max θ salt b' loc := by
      intro salt b' hb' loc hloc
      dsimp only [FastState.fpAt]
      rw [hkv_pres b' hb' loc hloc]
    have hrk_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
        fsIns.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc := by
      intro b' hb' loc hloc
      dsimp only [FastState.rKeyAt]
      rw [hkv_pres b' hb' loc hloc]
    have hkv_new : fsIns.keyValAt c U n_max θ.1 b X = u.val := by
      dsimp only [FastState.keyValAt]
      rw [hp_new_eq, hfsIns_q, Function.update_self]
      exact feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
    have hfp_new : ∀ salt, fsIns.fpAt c U n_max θ salt b X = fpOfSalt c U n_max θ.2 salt u := by
      intro salt
      dsimp only [FastState.fpAt, fpOfSalt]
      rw [hkv_new]
      split_ifs with hs hu
      · rfl
      · exact absurd u.isLt hu
      · rfl
    have hrk_new : fsIns.rKeyAt c U n_max θ b X = rKey := by
      dsimp only [FastState.rKeyAt, rKey]
      rw [hkv_new]
      simp [u.isLt]
    -- `rKey` does not collide with any existing buffered item (`2 ≤ fs.locState b' l'`)
    obtain ⟨hia_cur, hna_cur, curMap, hv_cur, hrel_cur⟩ := hv.bufCur_valid
    have hcur_map_none : curMap rKey = none := (hv_cur.2.2.2.1 rKey hrk_lt).trans hcur_lk_none
    have hno_rk_cur : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
        fs.locState b' l' = 2 + fs.curEp → fs.rKeyAt c U n_max θ b' l' ≠ rKey :=
      (hrel_cur.1 rKey).mp hcur_map_none
    have hno_rk_old : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
        fs.locState b' l' = 2 + fs.oldEp → fs.rKeyAt c U n_max θ b' l' ≠ rKey := by
      have hbo := hv.bufOld_valid
      by_cases hle3 : fs.rebStage ≤ 3
      · rw [ite_eq_left hle3] at hbo
        obtain ⟨_, _, oldMap, hv_old, hrel_old⟩ := hbo
        have hm_none : oldMap rKey = none :=
          (hv_old.2.2.2.1 rKey hrk_lt).trans (hold_lk_none hle3)
        exact (hrel_old.1 rKey).mp hm_none
      · rw [ite_eq_right hle3] at hbo
        by_cases heq4 : fs.rebStage = 4
        · rw [ite_eq_left heq4] at hbo
          exact fun b' hb' l' hl' hst => absurd hst (hbo.1 b' hb' l' hl')
        · rw [ite_eq_right heq4] at hbo
          exact fun b' hb' l' hl' hst => absurd hst (hbo.1 b' hb' l' hl')
    have hno_rk_any : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
        2 ≤ fs.locState b' l' → fs.rKeyAt c U n_max θ b' l' ≠ rKey := by
      intro b' hb' l' hl' h2
      have hact := hv.locState_active b' hb' l' hl'
      have hst_or : fs.locState b' l' = 2 + fs.curEp ∨ fs.locState b' l' = 2 + fs.oldEp := by
        rcases hv.curEp_or with hc | hc <;> (simp only [FastState.oldEp, hc]; omega)
      rcases hst_or with hsc | hso
      · exact hno_rk_cur b' hb' l' hl' hsc
      · exact hno_rk_old b' hb' l' hl' hso
    -- Common dictionary-map, active-item, and quotient-injectivity proofs for `fsIns`
    have hqv_glob' : ∀ p, fsIns.quotArr p < 2 ^ quotBitsWhp U n_max ∧
        fsIns.valArr p < max V 1 := by
      intro p
      rw [hfsIns_q, hfsIns_v]
      by_cases hp : p = p_new
      · subst hp
        rw [Function.update_self, Function.update_self]
        exact ⟨quot_lt_pow hnU u, hv_max⟩
      · rw [Function.update_of_ne hp, Function.update_of_ne hp]
        exact hv.qv_global p
    have hbkt_le' : ∀ b' < numBucketsWhp n_max, fsIns.bktCount b' ≤ totalLocalCoordsWhp n_max := by
      intro b' hb'
      rw [hfsIns_bkt]
      by_cases hbb : b' = b
      · subst hbb; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hbb]; exact hv.bktCount_le b' hb'
    have hbkt_ge0' : ∀ b', numBucketsWhp n_max ≤ b' → fsIns.bktCount b' = 0 := by
      intro b' hb'
      rw [hfsIns_bkt, Function.update_of_ne (by omega)]
      exact hv.bktCount_ge_zero b' hb'
    have hact_item' : ∀ b' < numBucketsWhp n_max, ∀ l' < fsIns.bktCount b',
        let kv := fsIns.keyValAt c U n_max θ.1 b' l'
        kv < U ∧ feistelBucket (bWhp n_max) h1 kv = b' ∧
        keyQuotient (bWhp n_max) kv = fsIns.quotArr (fsIns.physSlot n_max b' l') ∧
        fsIns.valArr (fsIns.physSlot n_max b' l') < V := by
      intro b' hb' l' hl'
      rw [hfsIns_bkt] at hl'
      by_cases hbb : b' = b
      · subst hbb
        rw [Function.update_self] at hl'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
        · dsimp only
          rw [hkv_pres b hb l' hlt, (hqv_pres b hb l' hlt).1, (hqv_pres b hb l' hlt).2]
          exact hv.active_item b hb l' hlt
        · dsimp only
          rw [hkv_new, hp_new_eq, hfsIns_q, hfsIns_v, Function.update_self, Function.update_self]
          exact ⟨u.isLt, rfl, rfl, hv_lt⟩
      · rw [Function.update_of_ne hbb] at hl'
        dsimp only
        rw [hkv_pres b' hb' l' hl', (hqv_pres b' hb' l' hl').1, (hqv_pres b' hb' l' hl').2]
        exact hv.active_item b' hb' l' hl'
    have hquot_inj' : ∀ b' < numBucketsWhp n_max, ∀ l₁ < fsIns.bktCount b',
        ∀ l₂ < fsIns.bktCount b',
        fsIns.quotArr (fsIns.physSlot n_max b' l₁) = fsIns.quotArr (fsIns.physSlot n_max b' l₂) →
        l₁ = l₂ := by
      intro b' hb' l₁ hl₁ l₂ hl₂ heq
      rw [hfsIns_bkt] at hl₁ hl₂
      by_cases hbb : b' = b
      · subst hbb
        rw [Function.update_self] at hl₁ hl₂
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with hl₁' | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with hl₂' | rfl
        · rw [(hqv_pres b hb l₁ hl₁').1, (hqv_pres b hb l₂ hl₂').1] at heq
          exact hv.quot_inj b hb l₁ hl₁' l₂ hl₂' heq
        · rw [(hqv_pres b hb l₁ hl₁').1, hp_new_eq, hfsIns_q, Function.update_self] at heq
          exact absurd heq (hno_q l₁ hl₁')
        · rw [(hqv_pres b hb l₂ hl₂').1, hp_new_eq, hfsIns_q, Function.update_self] at heq
          exact absurd heq.symm (hno_q l₂ hl₂')
        · rfl
      · rw [Function.update_of_ne hbb] at hl₁ hl₂
        rw [(hqv_pres b' hb' l₁ hl₁).1, (hqv_pres b' hb' l₂ hl₂).1] at heq
        exact hv.quot_inj b' hb' l₁ hl₁ l₂ hl₂ heq
    have hdict_map' : ∀ u' : Fin U,
        let b' := feistelBucket (bWhp n_max) h1 u'.val
        let q' := keyQuotient (bWhp n_max) u'.val
        (Function.update dict u (some v) u' = none ↔
          ∀ loc < fsIns.bktCount b', fsIns.quotArr (fsIns.physSlot n_max b' loc) ≠ q') ∧
        (∀ v', Function.update dict u (some v) u' = some v' ↔
          ∃ loc < fsIns.bktCount b',
            fsIns.quotArr (fsIns.physSlot n_max b' loc) = q' ∧
            fsIns.valArr (fsIns.physSlot n_max b' loc) = v') := by
      intro u'
      dsimp only
      set b' := feistelBucket (bWhp n_max) h1 u'.val
      set q' := keyQuotient (bWhp n_max) u'.val
      have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
      by_cases hu' : u' = u
      · subst hu'
        have hb'_eq : b' = b := rfl
        have hq'_eq : q' = q_val := rfl
        rw [Function.update_self, hb'_eq, hq'_eq, hfsIns_bkt, Function.update_self]
        have hqX : fsIns.quotArr (fsIns.physSlot n_max b X) = q_val := by
          rw [hp_new_eq, hfsIns_q, Function.update_self]
        have hvX : fsIns.valArr (fsIns.physSlot n_max b X) = v := by
          rw [hp_new_eq, hfsIns_v, Function.update_self]
        refine ⟨⟨fun h => (by cases h), fun hall => absurd hqX (hall X (Nat.lt_succ_self X))⟩,
          fun v' => ⟨fun h => ?_, fun ⟨l', hl', hql, hvl⟩ => ?_⟩⟩
        · injection h with hv_eq; subst hv_eq
          exact ⟨X, Nat.lt_succ_self X, hqX, hvX⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
          · rw [(hqv_pres b hb l' hlt).1] at hql
            exact absurd hql (hno_q l' hlt)
          · rw [hvX] at hvl
            exact congrArg some hvl
      · rw [Function.update_of_ne hu']
        obtain ⟨hn_iff, hs_iff⟩ := hv.dict_map u'
        change (dict u' = none ↔ ∀ loc < fs.bktCount b',
          fs.quotArr (fs.physSlot n_max b' loc) ≠ q') at hn_iff
        have hs_iff' : ∀ v', dict u' = some v' ↔ ∃ loc < fs.bktCount b',
            fs.quotArr (fs.physSlot n_max b' loc) = q' ∧
            fs.valArr (fs.physSlot n_max b' loc) = v' := hs_iff
        have hnot_bq : ¬(b' = b ∧ q' = q_val) := by
          rintro ⟨hbb, hqq⟩
          apply hu'; apply Fin.ext
          rw [← feistelReconstruct_feistelBucket (bWhp n_max) h1 u'.val,
            ← feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val]
          change feistelReconstruct (bWhp n_max) h1 b' q' =
            feistelReconstruct (bWhp n_max) h1 b q_val
          rw [hbb, hqq]
        refine ⟨hn_iff.trans ?_, fun v' => (hs_iff' v').trans ?_⟩
        · exact ⟨fun hall loc hloc => by
            rw [hfsIns_bkt] at hloc
            by_cases hbb : b' = b
            · rw [hbb, Function.update_self] at hloc
              rcases Nat.lt_succ_iff_lt_or_eq.mp hloc with hlt | rfl
              · rw [hbb, (hqv_pres b hb loc hlt).1]
                have hloc0 : loc < fs.bktCount b' := by rwa [hbb]
                have hne0 := hall loc hloc0
                rwa [hbb] at hne0
              · rw [hbb, hp_new_eq, hfsIns_q, Function.update_self]
                exact fun heq => hnot_bq ⟨hbb, heq.symm⟩
            · rw [Function.update_of_ne hbb] at hloc
              rw [(hqv_pres b' hb' loc hloc).1]; exact hall loc hloc,
            fun hall loc hloc => by
              have hloc' : loc < fsIns.bktCount b' := by
                rw [hfsIns_bkt]
                by_cases hbb : b' = b
                · rw [hbb] at hloc ⊢; rw [Function.update_self]; exact Nat.lt_succ_of_lt hloc
                · rwa [Function.update_of_ne hbb]
              have := hall loc hloc'
              rwa [(hqv_pres b' hb' loc hloc).1] at this⟩
        · exact ⟨fun ⟨loc, hloc, hql, hvl⟩ => by
            refine ⟨loc, ?_, ?_, ?_⟩
            · rw [hfsIns_bkt]
              by_cases hbb : b' = b
              · rw [hbb] at hloc ⊢; rw [Function.update_self]; exact Nat.lt_succ_of_lt hloc
              · rwa [Function.update_of_ne hbb]
            · rw [(hqv_pres b' hb' loc hloc).1]; exact hql
            · rw [(hqv_pres b' hb' loc hloc).2]; exact hvl,
            fun ⟨loc, hloc, hql, hvl⟩ => by
              rw [hfsIns_bkt] at hloc
              by_cases hbb : b' = b
              · rw [hbb, Function.update_self] at hloc
                rcases Nat.lt_succ_iff_lt_or_eq.mp hloc with hlt | rfl
                · rw [hbb, (hqv_pres b hb loc hlt).1] at hql
                  rw [hbb, (hqv_pres b hb loc hlt).2] at hvl
                  have hlt' : loc < fs.bktCount b' := by rwa [hbb]
                  have hql' : fs.quotArr (fs.physSlot n_max b' loc) = q' := by rwa [hbb]
                  have hvl' : fs.valArr (fs.physSlot n_max b' loc) = v' := by rwa [hbb]
                  exact ⟨loc, hlt', hql', hvl'⟩
                · rw [hbb, hp_new_eq, hfsIns_q, Function.update_self] at hql
                  exact absurd ⟨hbb, hql.symm⟩ hnot_bq
              · rw [Function.update_of_ne hbb] at hloc
                rw [(hqv_pres b' hb' loc hloc).1] at hql
                rw [(hqv_pres b' hb' loc hloc).2] at hvl
                exact ⟨loc, hloc, hql, hvl⟩⟩
    -- Now establish `(hc_ins, hom_other, hom_b, hst_ins)` across the two `hasFpCollision` branches
    suffices hsplit :
        CoreFastInv c U V n_max θ fsIns (Function.update dict u (some v)) ∧
        (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsIns b') ∧
        PreOvermarsBucketInv c U n_max θ fsIns b ∧
        ValidEpochStage c U n_max θ fsIns ∧
        fsIns.epochClock = fs.epochClock by
      obtain ⟨hc_ins, hom_other, hom_b, hst_ins, hclk_ins⟩ := hsplit
      obtain ⟨hc', hom', hst', _, _, hclk', _, _⟩ :=
        overmarsStep_spec hc_ins hb hom_other hom_b
      exact ⟨hc', hom', hst' hst_ins, hclk'.trans hclk_ins⟩
    by_cases hfp_coll : hasFpCollision = true
    · -- Subcase A: `hasFpCollision = true` (inserted into `buf curEp` with `locState = 2 + curEp`)
      have hfsIns_eq : fsIns =
          { fsAlloc with
            quotArr := Function.update fsAlloc.quotArr p_new q_val
            valArr := Function.update fsAlloc.valArr p_new v
            bktCount := Function.update fsAlloc.bktCount b (X + 1)
            locState := Function.update fsAlloc.locState b
              (Function.update (fsAlloc.locState b) X (2 + fsAlloc.curEp))
            buf := Function.update fsAlloc.buf fsAlloc.curEp
              (bufInsert (cTabWhp c) (bCharWhp n_max) (fsAlloc.buf fsAlloc.curEp) rKey b X) } := by
        dsimp only [fsIns, fastInsertFresh]; rw [ite_eq_left hfp_coll]
      have hcur_eq : fsIns.curEp = fs.curEp := by rw [hfsIns_eq]; rfl
      have hold_eq : fsIns.oldEp = fs.oldEp := by rw [hfsIns_eq]; rfl
      have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
          fsIns.locState b' l' = fs.locState b' l' := by
        intro b' _ l' hl'
        rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
        by_cases hbb : b' = b
        · subst hbb; rw [Function.update_self, Function.update_of_ne (by omega)]
        · rw [Function.update_of_ne hbb]
      have hls_new : fsIns.locState b X = 2 + fs.curEp := by
        rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]; simp
      have hinL_X : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fsIns.locState b X) =
          false := by
        rw [hls_new]; exact inLiveTree_curEp_eq_false hv.curEp_or _
      have hins_cur := hv_cur.insert_spec (b := b) (loc := X) hrk_lt
      set tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b X
      have hia_tr' : tr'.itemAlloc ≤ 2 * rIndepWhp c n_max := by
        by_cases hev : bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = true
        · rw [(hins_cur.2.2.2.2.2.2.1 hev).2]; exact hia_cur
        · have hevf : bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = false :=
            Bool.eq_false_iff.mpr hev
          have hlt_cap : (fs.buf fs.curEp).itemAlloc < 2 * rIndepWhp c n_max := by
            by_contra hge
            exact hg3 ⟨hfp_coll, by simp [hevf], Nat.not_lt.mp hge⟩
          have := hins_cur.2.2.2.2.1
          omega
      have hna_tr' : tr'.nodeAlloc ≤ 1 + cTabWhp c * tr'.itemAlloc :=
        hv_cur.insert_nodeAlloc_le hrk_lt hna_cur
      have hbuf_cur_eq : fsIns.buf fsIns.curEp = tr' := by
        rw [hcur_eq, hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]; simp [tr']
      have hbuf_old_eq : fsIns.buf fsIns.oldEp = fs.buf fs.oldEp := by
        rw [hold_eq, hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
        exact Function.update_of_ne (curEp_ne_oldEp hv.curEp_or).symm _ _
      refine ⟨?_, ?_, ?_, ?_, by rw [hfsIns_eq]; rfl⟩
      · refine
          { hth := hv.hth
            curEp_or := hcur_eq ▸ hv.curEp_or
            epochClock_lt := by rw [hfsIns_eq]; exact hv.epochClock_lt
            rebStage_le := by rw [hfsIns_eq]; exact hv.rebStage_le
            rebCollision_zero := by rw [hfsIns_eq]; exact hv.rebCollision_zero
            qv_global := hqv_glob'
            bktCount_le := hbkt_le'
            bktCount_ge_zero := hbkt_ge0'
            locState_active := fun b' hb' l' hl' => by
              rw [hfsIns_bkt] at hl'
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hl'
                rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
                · rw [hls_pres b hb l' hlt]; exact hv.locState_active b hb l' hlt
                · rw [hls_new]; rcases hv.curEp_or with hc | hc <;> omega
              · rw [Function.update_of_ne hbb] at hl'
                rw [hls_pres b' hb' l' hl']; exact hv.locState_active b' hb' l' hl'
            locState_inactive := fun b' l' hnot => by
              rw [hfsIns_bkt] at hnot
              rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hnot ⊢
                rw [Function.update_of_ne (by omega)]
                exact hv.locState_inactive b l' (by omega)
              · rw [Function.update_of_ne hbb] at hnot ⊢
                exact hv.locState_inactive b' l' hnot
            active_item := hact_item'
            quot_inj := hquot_inj'
            dict_map := hdict_map'
            poolFreeTop_le := hpoolTop'
            backPtr_valid := hbp_val'
            freeStack_lt := hfree_lt'
            backPtr_inj := hbp_inj'
            freeStack_inj := hfree_inj'
            back_free_disj := hdisj'
            pool_conservation := hcons'
            roles_valid := by rw [hfsIns_eq]; exact hv.roles_valid
            bktSalt_lt := by rw [hfsIns_eq]; exact hv.bktSalt_lt
            live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
              have hdf_eq : fsIns.rebDoneFlag = fs.rebDoneFlag := by rw [hfsIns_eq]; rfl
              have hbs_eq : fsIns.bktSalt = fs.bktSalt := by rw [hfsIns_eq]; rfl
              rw [hstg_eq, hold_eq, hdf_eq] at hin₁ hin₂
              rw [hbs_eq] at hfeq
              rw [hfsIns_bkt] at hl₁ hl₂
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hl₁ hl₂
                have hl1_lt : l₁ < X := by
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with h | rfl
                  · exact h
                  · rw [hinL_X] at hin₁; cases hin₁
                have hl2_lt : l₂ < X := by
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with h | rfl
                  · exact h
                  · rw [hinL_X] at hin₂; cases hin₂
                rw [hls_pres b hb l₁ hl1_lt] at hin₁
                rw [hls_pres b hb l₂ hl2_lt] at hin₂
                rw [hfp_pres _ b hb l₁ hl1_lt, hfp_pres _ b hb l₂ hl2_lt] at hfeq
                exact hv.live_fp_inj b hb l₁ hl1_lt l₂ hl2_lt hin₁ hin₂ hfeq
              · rw [Function.update_of_ne hbb] at hl₁ hl₂
                rw [hls_pres b' hb' l₁ hl₁] at hin₁
                rw [hls_pres b' hb' l₂ hl₂] at hin₂
                rw [hfp_pres _ b' hb' l₁ hl₁, hfp_pres _ b' hb' l₂ hl₂] at hfeq
                exact hv.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b' hb' => by
              obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
              have hsl_eq : fsIns.slices = fs.slices := by rw [hfsIns_eq]; rfl
              have hlic_eq : fsIns.liveInsCount = fs.liveInsCount := by rw [hfsIns_eq]; rfl
              have hli_eq : fsIns.liveSliceIdx b' = fs.liveSliceIdx b' := by rw [hfsIns_eq]; rfl
              have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
              have hdf_eq : fsIns.rebDoneFlag = fs.rebDoneFlag := by rw [hfsIns_eq]; rfl
              have hbs_eq : fsIns.bktSalt = fs.bktSalt := by rw [hfsIns_eq]; rfl
              refine ⟨lm, ?_, ?_⟩
              · rwa [hsl_eq, hlic_eq, hli_eq]
              · rw [hstg_eq, hold_eq, hdf_eq, hbs_eq, hfsIns_bkt]
                by_cases hbb : b' = b
                · subst hbb; rw [Function.update_self]
                  have hrl' := hrl.congr (f' := fsIns.fpAt c U n_max θ (fs.bktSalt b) b)
                    (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
                      (fsIns.locState b loc) = true)
                    (fun loc hlt => hfp_pres _ b hb loc hlt)
                    (fun loc hlt => by rw [hls_pres b hb loc hlt])
                  exact hrl'.step_false (by rw [hinL_X]; decide)
                · rw [Function.update_of_ne hbb]
                  exact hrl.congr (fun loc hlt => hfp_pres _ b' hb' loc hlt)
                    (fun loc hlt => by rw [hls_pres b' hb' loc hlt])
            rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h2₁ h2₂ hrkeq => by
              rw [hfsIns_bkt] at hl₁ hl₂
              have hcase : ∀ b' < numBucketsWhp n_max,
                  ∀ l' < Function.update fs.bktCount b (X + 1) b',
                  (b' = b ∧ l' = X) ∨ (l' < fs.bktCount b' ∧ ¬(b' = b ∧ l' = X)) := by
                intro b' _ l' hl'
                by_cases hbb : b' = b
                · subst hbb; rw [Function.update_self] at hl'
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with h | rfl
                  · exact Or.inr ⟨h, fun ⟨_, he⟩ => by omega⟩
                  · exact Or.inl ⟨rfl, rfl⟩
                · rw [Function.update_of_ne hbb] at hl'
                  exact Or.inr ⟨hl', fun ⟨hb0, _⟩ => hbb hb0⟩
              rcases hcase b₁ hb₁ l₁ hl₁ with ⟨rfl, rfl⟩ | ⟨hl1_0, _⟩ <;>
                rcases hcase b₂ hb₂ l₂ hl₂ with ⟨rfl, rfl⟩ | ⟨hl2_0, _⟩
              · exact ⟨rfl, rfl⟩
              · rw [hrk_new, hrk_pres b₂ hb₂ l₂ hl2_0] at hrkeq
                rw [hls_pres b₂ hb₂ l₂ hl2_0] at h2₂
                exact absurd hrkeq.symm (hno_rk_any b₂ hb₂ l₂ hl2_0 h2₂)
              · rw [hrk_pres b₁ hb₁ l₁ hl1_0, hrk_new] at hrkeq
                rw [hls_pres b₁ hb₁ l₁ hl1_0] at h2₁
                exact absurd hrkeq (hno_rk_any b₁ hb₁ l₁ hl1_0 h2₁)
              · rw [hrk_pres b₁ hb₁ l₁ hl1_0, hrk_pres b₂ hb₂ l₂ hl2_0] at hrkeq
                rw [hls_pres b₁ hb₁ l₁ hl1_0] at h2₁
                rw [hls_pres b₂ hb₂ l₂ hl2_0] at h2₂
                exact hv.rKey_buf_inj b₁ hb₁ l₁ hl1_0 b₂ hb₂ l₂ hl2_0 h2₁ h2₂ hrkeq
            bufCur_valid := by
              rw [hbuf_cur_eq, hcur_eq]
              refine ⟨hia_tr', hna_tr', Function.update curMap rKey (some (b, X)), hins_cur.1, ?_⟩
              rw [hfsIns_bkt, ← hrk_new]
              exact hrel_cur.insert_fresh hb hls_new hls_pres hrk_pres
                (fun b' hb' loc hloc hst => hrk_new.symm ▸ hno_rk_cur b' hb' loc hloc hst)
            bufOld_valid := by
              have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
              rw [hstg_eq, hbuf_old_eq, hold_eq]
              have hbo := hv.bufOld_valid
              have hnew_ne_old : fsIns.locState b X ≠ 2 + fs.oldEp := by
                rw [hls_new]; have := curEp_ne_oldEp hv.curEp_or; omega
              by_cases hle3 : fs.rebStage ≤ 3
              · rw [ite_eq_left hle3] at hbo ⊢
                obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
                refine ⟨hia_o, hna_o, oldMap, hv_o, ?_⟩
                rw [hfsIns_bkt]
                exact hrel_o.insert_skip hnew_ne_old hls_pres hrk_pres
              · rw [ite_eq_right hle3] at hbo ⊢
                have hno_old' : ∀ b' < numBucketsWhp n_max, ∀ l' < fsIns.bktCount b',
                    fsIns.locState b' l' ≠ 2 + fs.oldEp := by
                  intro b' hb' l' hl'
                  rw [hfsIns_bkt] at hl'
                  have hno0 : ∀ b'' < numBucketsWhp n_max, ∀ l'' < fs.bktCount b'',
                      fs.locState b'' l'' ≠ 2 + fs.oldEp := by
                    split_ifs at hbo <;> exact hbo.1
                  by_cases hbb : b' = b
                  · subst hbb; rw [Function.update_self] at hl'
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
                    · rw [hls_pres b hb l' hlt]; exact hno0 b hb l' hlt
                    · exact hnew_ne_old
                  · rw [Function.update_of_ne hbb] at hl'
                    rw [hls_pres b' hb' l' hl']; exact hno0 b' hb' l' hl'
                split_ifs at hbo ⊢ <;> exact ⟨hno_old', hbo.2⟩ }
      · intro b' hb' hne
        exact OvermarsBucketInv.of_eq_lt (hv.overmars_valid b' hb')
          (by rw [hfsIns_eq]; rfl) (fun loc hlt => hfp_pres _ b' hb' loc hlt)
          (by rw [hfsIns_eq]; rfl) hcur_eq (by rw [hfsIns_eq]; rfl)
          (fun loc hlt => hls_pres b' hb' loc hlt)
          (by rw [hfsIns_bkt, Function.update_of_ne hne])
          (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl)
          (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl)
      · exact (OvermarsBucketInv.of_eq_lt (hv.overmars_valid b hb)
          (by rw [hfsIns_eq]; rfl) (fun loc hlt => hfp_pres _ b hb loc hlt)
          (by rw [hfsIns_eq]; rfl) hcur_eq (by rw [hfsIns_eq]; rfl)
          (fun loc hlt => hls_pres b hb loc hlt)
          (by rw [hfsIns_bkt, Function.update_self]; omega)
          (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl)
          (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl)).toPre
      · have hstg := hv.stage_valid
        dsimp only [ValidEpochStage] at hstg ⊢
        have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
        have hsc_eq : fsIns.stageCursor = fs.stageCursor := by rw [hfsIns_eq]; rfl
        have hdc_eq : fsIns.dirtyCount = fs.dirtyCount := by rw [hfsIns_eq]; rfl
        have hdb_eq : fsIns.dirtyBuckets = fs.dirtyBuckets := by rw [hfsIns_eq]; rfl
        have hdi_eq : fsIns.dirtyIdx = fs.dirtyIdx := by rw [hfsIns_eq]; rfl
        have hdf_eq : fsIns.rebDoneFlag = fs.rebDoneFlag := by rw [hfsIns_eq]; rfl
        have hrq_eq : fsIns.rebQueued = fs.rebQueued := by rw [hfsIns_eq]; rfl
        have hcs_eq : fsIns.rebCandSalt = fs.rebCandSalt := by rw [hfsIns_eq]; rfl
        have hrc_eq : fsIns.rebScanCursor = fs.rebScanCursor := by rw [hfsIns_eq]; rfl
        have hri_eq : fsIns.rebInsCount = fs.rebInsCount := by rw [hfsIns_eq]; rfl
        have hsl_eq : fsIns.slices = fs.slices := by rw [hfsIns_eq]; rfl
        have hrbi_eq : ∀ bc, fsIns.rebSliceIdx bc = fs.rebSliceIdx bc := fun _ => by
          rw [hfsIns_eq]; rfl
        rw [hbuf_old_eq, hold_eq, hstg_eq, hsc_eq, hdc_eq, hdb_eq, hdi_eq, hdf_eq, hrq_eq,
          hcs_eq, hrc_eq, hri_eq, hsl_eq]
        split_ifs at hstg ⊢ with hs0 hs1 hs2 hs3
        · exact hstg
        · exact hstg
        · rcases hstg with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
          refine ⟨hd1, hd2, hd3, hd4, hd5, ?_, fun hlt_s => ?_⟩
          · intro b' hb' l' hl' hst'
            rw [hfsIns_bkt] at hl'
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hl'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
              · rw [hls_pres b hb l' hlt] at hst'; exact hd6 b hb l' hlt hst'
              · rw [hls_new] at hst'
                exact absurd (by omega : fs.curEp = fs.oldEp) (curEp_ne_oldEp hv.curEp_or)
            · rw [Function.update_of_ne hbb] at hl'
              rw [hls_pres b' hb' l' hl'] at hst'; exact hd6 b' hb' l' hl' hst'
          · obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt_s
            set bc := fs.dirtyBuckets fs.dirtyIdx
            have hbc : bc < numBucketsWhp n_max := hd3 _ hd2
            have hbkt_ge : fs.bktCount bc ≤ fsIns.bktCount bc := by
              rw [hfsIns_bkt]
              by_cases hbb : bc = b
              · rw [hbb, Function.update_self]; omega
              · rw [Function.update_of_ne hbb]
            have hmin_eq : min (fsIns.bktCount bc) fs.rebScanCursor =
                min (fs.bktCount bc) fs.rebScanCursor := by
              rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩
              · simp [hc0]
              · rw [Nat.min_eq_right (hc_lt.le.trans hbkt_ge), Nat.min_eq_right hc_lt.le]
            have hmin_le : min (fs.bktCount bc) fs.rebScanCursor ≤ fs.bktCount bc :=
              Nat.min_le_left _ _
            rw [hmin_eq, hrbi_eq bc]
            refine ⟨?_, ?_, rm, hvr, ?_⟩
            · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins_r⟩
              · exact Or.inl ⟨hc0, hi0⟩
              · exact Or.inr ⟨h16, hc_lt.trans_le hbkt_ge, hins_r⟩
            · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
              have hl1_b := hl₁.trans_le hmin_le
              have hl2_b := hl₂.trans_le hmin_le
              rw [hls_pres bc hbc l₁ hl1_b] at hp₁
              rw [hls_pres bc hbc l₂ hl2_b] at hp₂
              rw [hfp_pres _ bc hbc l₁ hl1_b, hfp_pres _ bc hbc l₂ hl2_b] at hfeq
              exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            · exact hrr.congr (fun loc hlt => hfp_pres _ bc hbc loc (hlt.trans_le hmin_le))
                (fun loc hlt => by rw [hls_pres bc hbc loc (hlt.trans_le hmin_le)])
        · exact hstg
    · -- Subcase B: `hasFpCollision = false` (inserted into `slices lIdx` with `locState = 1`)
      have hfp_false : hasFpCollision = false := Bool.eq_false_iff.mpr hfp_coll
      have hfsIns_eq : fsIns =
          { fsAlloc with
            quotArr := Function.update fsAlloc.quotArr p_new q_val
            valArr := Function.update fsAlloc.valArr p_new v
            bktCount := Function.update fsAlloc.bktCount b (X + 1)
            locState := Function.update fsAlloc.locState b
              (Function.update (fsAlloc.locState b) X 1)
            slices := Function.update fsAlloc.slices lIdx
              (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                (fsAlloc.slices lIdx) fp X)
            liveInsCount := Function.update fsAlloc.liveInsCount b
              (fsAlloc.liveInsCount b + 1) } := by
        dsimp only [fsIns, fastInsertFresh]; rw [ite_eq_right hfp_coll]
      have hcur_eq : fsIns.curEp = fs.curEp := by rw [hfsIns_eq]; rfl
      have hold_eq : fsIns.oldEp = fs.oldEp := by rw [hfsIns_eq]; rfl
      have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
          fsIns.locState b' l' = fs.locState b' l' := by
        intro b' _ l' hl'
        rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
        by_cases hbb : b' = b
        · subst hbb; rw [Function.update_self, Function.update_of_ne (by omega)]
        · rw [Function.update_of_ne hbb]
      have hls_new : fsIns.locState b X = 1 := by
        rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]; simp
      have hinL_X : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fsIns.locState b X) =
          true := by
        rw [hls_new]; simp [inLiveTree]
      obtain ⟨liveMap0, hv_live0, hrel_live0⟩ := hv.live_valid b hb
      have hlic_le8 : fs.liveInsCount b ≤ 8 * (scaleWhp n_max) ^ 12 :=
        liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
      have hfp_lt : fp < 2 ^ fpBitsWhp n_max := fpOfSalt_lt θ.2 _ u
      have hX_val : X < 2 ^ valLaneBitsWhp n_max := by
        have hX3 : X < 3 * (scaleWhp n_max) ^ 12 :=
          hX_lt.trans_le totalLocalCoordsWhp_le_three_mul
        rw [valLane_pow_eq' n_max]; omega
      have hlk_live_none :
          btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices lIdx) fp = none := by
        cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices lIdx) fp with
        | none => rfl
        | some _ => exact absurd (by simp [hasFpCollision, hlk]) hfp_coll
      have hlm0_none : liveMap0 fp = none :=
        (hv_live0.lookup_eq hv.hth hlic_le8 hfp_lt).symm.trans hlk_live_none
      have hno_fp_coll : ∀ loc < X,
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true →
          fs.fpAt c U n_max θ (fs.bktSalt b) b loc ≠ fp :=
        (hrel_live0.1 fp).mp hlm0_none
      have hins_live := (hv_live0.insert_spec hv.hth hlic_le8 hfp_lt hX_val).2
      obtain ⟨hlr_b, hor_b, hro_ne_b⟩ := hv.roles_valid b hb
      have hne_om_all : ∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b' ≠ lIdx := by
        intro b' hb'
        by_cases hbb : b' = b
        · subst hbb; dsimp only [FastState.overmarsSliceIdx, lIdx, FastState.liveSliceIdx]; omega
        · dsimp only [FastState.overmarsSliceIdx, lIdx, FastState.liveSliceIdx]
          intro heq
          exact hbb (sliceIdx_inj (hv.roles_valid b' hb').2.1 hlr_b heq).1
      have hne_reb_all : ∀ b' < numBucketsWhp n_max, fs.rebSliceIdx b' ≠ lIdx := by
        intro b' hb'
        obtain ⟨hlr', hor', hne'⟩ := hv.roles_valid b' hb'
        have hrr' : fs.rebRole b' < 3 ∧ fs.rebRole b' ≠ fs.liveRole b' := by
          dsimp only [FastState.rebRole]; omega
        by_cases hbb : b' = b
        · subst hbb; dsimp only [FastState.rebSliceIdx, lIdx, FastState.liveSliceIdx]; omega
        · dsimp only [FastState.rebSliceIdx, lIdx, FastState.liveSliceIdx]
          intro heq
          exact hbb (sliceIdx_inj hrr'.1 hlr_b heq).1
      refine ⟨?_, ?_, ?_, ?_, by rw [hfsIns_eq]; rfl⟩
      · refine
          { hth := hv.hth
            curEp_or := hcur_eq ▸ hv.curEp_or
            epochClock_lt := by rw [hfsIns_eq]; exact hv.epochClock_lt
            rebStage_le := by rw [hfsIns_eq]; exact hv.rebStage_le
            rebCollision_zero := by rw [hfsIns_eq]; exact hv.rebCollision_zero
            qv_global := hqv_glob'
            bktCount_le := hbkt_le'
            bktCount_ge_zero := hbkt_ge0'
            locState_active := fun b' hb' l' hl' => by
              rw [hfsIns_bkt] at hl'
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hl'
                rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
                · rw [hls_pres b hb l' hlt]; exact hv.locState_active b hb l' hlt
                · rw [hls_new]; omega
              · rw [Function.update_of_ne hbb] at hl'
                rw [hls_pres b' hb' l' hl']; exact hv.locState_active b' hb' l' hl'
            locState_inactive := fun b' l' hnot => by
              rw [hfsIns_bkt] at hnot
              rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hnot ⊢
                rw [Function.update_of_ne (by omega)]
                exact hv.locState_inactive b l' (by omega)
              · rw [Function.update_of_ne hbb] at hnot ⊢
                exact hv.locState_inactive b' l' hnot
            active_item := hact_item'
            quot_inj := hquot_inj'
            dict_map := hdict_map'
            poolFreeTop_le := hpoolTop'
            backPtr_valid := hbp_val'
            freeStack_lt := hfree_lt'
            backPtr_inj := hbp_inj'
            freeStack_inj := hfree_inj'
            back_free_disj := hdisj'
            pool_conservation := hcons'
            roles_valid := by rw [hfsIns_eq]; exact hv.roles_valid
            bktSalt_lt := by rw [hfsIns_eq]; exact hv.bktSalt_lt
            live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
              have hdf_eq : fsIns.rebDoneFlag = fs.rebDoneFlag := by rw [hfsIns_eq]; rfl
              have hbs_eq : fsIns.bktSalt = fs.bktSalt := by rw [hfsIns_eq]; rfl
              rw [hstg_eq, hold_eq, hdf_eq] at hin₁ hin₂
              rw [hbs_eq] at hfeq
              rw [hfsIns_bkt] at hl₁ hl₂
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hl₁ hl₂
                rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with hl1_lt | rfl <;>
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with hl2_lt | rfl
                · rw [hls_pres b hb l₁ hl1_lt] at hin₁
                  rw [hls_pres b hb l₂ hl2_lt] at hin₂
                  rw [hfp_pres _ b hb l₁ hl1_lt, hfp_pres _ b hb l₂ hl2_lt] at hfeq
                  exact hv.live_fp_inj b hb l₁ hl1_lt l₂ hl2_lt hin₁ hin₂ hfeq
                · rw [hls_pres b hb l₁ hl1_lt] at hin₁
                  rw [hfp_pres _ b hb l₁ hl1_lt, hfp_new] at hfeq
                  exact absurd hfeq (hno_fp_coll l₁ hl1_lt hin₁)
                · rw [hls_pres b hb l₂ hl2_lt] at hin₂
                  rw [hfp_new, hfp_pres _ b hb l₂ hl2_lt] at hfeq
                  exact absurd hfeq.symm (hno_fp_coll l₂ hl2_lt hin₂)
                · rfl
              · rw [Function.update_of_ne hbb] at hl₁ hl₂
                rw [hls_pres b' hb' l₁ hl₁] at hin₁
                rw [hls_pres b' hb' l₂ hl₂] at hin₂
                rw [hfp_pres _ b' hb' l₁ hl₁, hfp_pres _ b' hb' l₂ hl₂] at hfeq
                exact hv.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b' hb' => by
              have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
              have hdf_eq : fsIns.rebDoneFlag = fs.rebDoneFlag := by rw [hfsIns_eq]; rfl
              have hbs_eq : fsIns.bktSalt = fs.bktSalt := by rw [hfsIns_eq]; rfl
              have hli_eq : fsIns.liveSliceIdx b' = fs.liveSliceIdx b' := by rw [hfsIns_eq]; rfl
              rw [hstg_eq, hold_eq, hdf_eq, hbs_eq, hli_eq, hfsIns_bkt]
              by_cases hbb : b' = b
              · subst hbb
                rw [Function.update_self]
                refine ⟨Function.update liveMap0 fp (some X), ?_, ?_⟩
                · rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc, lIdx]
                  simp only [Function.update_self]
                  exact hins_live
                · have hrl' := hrel_live0.congr
                    (f' := fsIns.fpAt c U n_max θ (fs.bktSalt b) b)
                    (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
                      (fsIns.locState b loc) = true)
                    (fun loc hlt => hfp_pres _ b hb loc hlt)
                    (fun loc hlt => by rw [hls_pres b hb loc hlt])
                  have hstep := hrl'.step_true hinL_X (fun loc hlt hin => by
                    rw [hfp_pres _ b hb loc hlt, hfp_new]
                    rw [hls_pres b hb loc hlt] at hin
                    exact hno_fp_coll loc hlt hin)
                  rwa [hfp_new] at hstep
              · rw [Function.update_of_ne hbb]
                obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
                have hne_s : fs.liveSliceIdx b' ≠ lIdx := by
                  dsimp only [FastState.liveSliceIdx, lIdx]
                  intro heq
                  exact hbb (sliceIdx_inj (hv.roles_valid b' hb').1 hlr_b heq).1
                refine ⟨lm, ?_, hrl.congr (fun loc hlt => hfp_pres _ b' hb' loc hlt)
                  (fun loc hlt => by rw [hls_pres b' hb' loc hlt])⟩
                rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
                simp only [Function.update_of_ne hbb, Function.update_of_ne hne_s]
                exact hvl
            rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h2₁ h2₂ hrkeq => by
              rw [hfsIns_bkt] at hl₁ hl₂
              have hlt0 : ∀ b' < numBucketsWhp n_max,
                  ∀ l' < Function.update fs.bktCount b (X + 1) b',
                  2 ≤ fsIns.locState b' l' → l' < fs.bktCount b' := by
                intro b' _ l' hl' h2
                by_cases hbb : b' = b
                · subst hbb; rw [Function.update_self] at hl'
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with h | rfl
                  · exact h
                  · rw [hls_new] at h2; omega
                · rwa [Function.update_of_ne hbb] at hl'
              have hl1_0 := hlt0 b₁ hb₁ l₁ hl₁ h2₁
              have hl2_0 := hlt0 b₂ hb₂ l₂ hl₂ h2₂
              rw [hls_pres b₁ hb₁ l₁ hl1_0] at h2₁
              rw [hls_pres b₂ hb₂ l₂ hl2_0] at h2₂
              rw [hrk_pres b₁ hb₁ l₁ hl1_0, hrk_pres b₂ hb₂ l₂ hl2_0] at hrkeq
              exact hv.rKey_buf_inj b₁ hb₁ l₁ hl1_0 b₂ hb₂ l₂ hl2_0 h2₁ h2₂ hrkeq
            bufCur_valid := by
              have hbuf_eq : fsIns.buf = fs.buf := by rw [hfsIns_eq]; rfl
              rw [hbuf_eq, hcur_eq]
              refine ⟨hia_cur, hna_cur, curMap, hv_cur, ?_⟩
              rw [hfsIns_bkt]
              exact hrel_cur.insert_skip
                (by rw [hls_new]; rcases hv.curEp_or with hc | hc <;> omega)
                hls_pres hrk_pres
            bufOld_valid := by
              have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
              have hbuf_eq : fsIns.buf = fs.buf := by rw [hfsIns_eq]; rfl
              rw [hstg_eq, hold_eq, hbuf_eq]
              have hbo := hv.bufOld_valid
              have hnew_ne_old : fsIns.locState b X ≠ 2 + fs.oldEp := by
                rw [hls_new]; omega
              by_cases hle3 : fs.rebStage ≤ 3
              · rw [ite_eq_left hle3] at hbo ⊢
                obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
                refine ⟨hia_o, hna_o, oldMap, hv_o, ?_⟩
                rw [hfsIns_bkt]
                exact hrel_o.insert_skip hnew_ne_old hls_pres hrk_pres
              · rw [ite_eq_right hle3] at hbo ⊢
                have hno_old' : ∀ b' < numBucketsWhp n_max, ∀ l' < fsIns.bktCount b',
                    fsIns.locState b' l' ≠ 2 + fs.oldEp := by
                  intro b' hb' l' hl'
                  rw [hfsIns_bkt] at hl'
                  have hno0 : ∀ b'' < numBucketsWhp n_max, ∀ l'' < fs.bktCount b'',
                      fs.locState b'' l'' ≠ 2 + fs.oldEp := by
                    split_ifs at hbo <;> exact hbo.1
                  by_cases hbb : b' = b
                  · subst hbb; rw [Function.update_self] at hl'
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
                    · rw [hls_pres b hb l' hlt]; exact hno0 b hb l' hlt
                    · exact hnew_ne_old
                  · rw [Function.update_of_ne hbb] at hl'
                    rw [hls_pres b' hb' l' hl']; exact hno0 b' hb' l' hl'
                split_ifs at hbo ⊢ <;> exact ⟨hno_old', hbo.2⟩ }
      · intro b' hb' hne
        exact OvermarsBucketInv.of_eq_lt (hv.overmars_valid b' hb')
          (by rw [hfsIns_eq]; rfl) (fun loc hlt => hfp_pres _ b' hb' loc hlt)
          (by rw [hfsIns_eq]; rfl) hcur_eq (by rw [hfsIns_eq]; rfl)
          (fun loc hlt => hls_pres b' hb' loc hlt)
          (by rw [hfsIns_bkt, Function.update_of_ne hne])
          (by
            rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
            exact Function.update_of_ne hne _ _)
          (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl) (by rw [hfsIns_eq]; rfl)
          (by
            have hoi : fsIns.overmarsSliceIdx b' = fs.overmarsSliceIdx b' := by
              rw [hfsIns_eq]; rfl
            rw [hoi, hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
            exact Function.update_of_ne (hne_om_all b' hb') _ _)
      · have hoa_eq : fsIns.overmarsActive b = fs.overmarsActive b := by rw [hfsIns_eq]; rfl
        have hoc_eq : fsIns.overmarsCursor b = fs.overmarsCursor b := by rw [hfsIns_eq]; rfl
        have hoi_eq : fsIns.overmarsInsCount b = fs.overmarsInsCount b := by rw [hfsIns_eq]; rfl
        have hlic_b : fsIns.liveInsCount b = fs.liveInsCount b + 1 := by
          rw [hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]; simp
        have hom_sl : fsIns.slices (fsIns.overmarsSliceIdx b) =
            fs.slices (fs.overmarsSliceIdx b) := by
          have hoi : fsIns.overmarsSliceIdx b = fs.overmarsSliceIdx b := by rw [hfsIns_eq]; rfl
          rw [hoi, hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
          exact Function.update_of_ne (hne_om_all b hb) _ _
        have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
        have hdf_eq : fsIns.rebDoneFlag b = fs.rebDoneFlag b := by rw [hfsIns_eq]; rfl
        have hbs_eq : fsIns.bktSalt b = fs.bktSalt b := by rw [hfsIns_eq]; rfl
        rcases hv.overmars_valid b hb with
          ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
        · exact Or.inl ⟨hoa_eq.trans ha0, by omega⟩
        · refine Or.inr ⟨hoa_eq.trans ha1, hoc_eq.symm ▸ h16, ?_, ?_, ?_, omM, ?_, ?_⟩
          · rw [hoc_eq, hfsIns_bkt, Function.update_self]; omega
          · rw [hoc_eq, hlic_b]; omega
          · rw [hoc_eq, hoi_eq]; omega
          · rwa [hoi_eq, hom_sl]
          · rw [hbs_eq, hstg_eq, hold_eq, hdf_eq, hoc_eq, hfsIns_bkt, Function.update_self,
              Nat.min_eq_right (by omega : fs.overmarsCursor b ≤ X + 1)]
            exact hrO.congr (fun loc hlt => hfp_pres _ b hb loc (hlt.trans hcur))
              (fun loc hlt => by rw [hls_pres b hb loc (hlt.trans hcur)])
      · have hstg := hv.stage_valid
        dsimp only [ValidEpochStage] at hstg ⊢
        have hbuf_eq : fsIns.buf = fs.buf := by rw [hfsIns_eq]; rfl
        have hstg_eq : fsIns.rebStage = fs.rebStage := by rw [hfsIns_eq]; rfl
        have hsc_eq : fsIns.stageCursor = fs.stageCursor := by rw [hfsIns_eq]; rfl
        have hdc_eq : fsIns.dirtyCount = fs.dirtyCount := by rw [hfsIns_eq]; rfl
        have hdb_eq : fsIns.dirtyBuckets = fs.dirtyBuckets := by rw [hfsIns_eq]; rfl
        have hdi_eq : fsIns.dirtyIdx = fs.dirtyIdx := by rw [hfsIns_eq]; rfl
        have hdf_eq : fsIns.rebDoneFlag = fs.rebDoneFlag := by rw [hfsIns_eq]; rfl
        have hrq_eq : fsIns.rebQueued = fs.rebQueued := by rw [hfsIns_eq]; rfl
        have hcs_eq : fsIns.rebCandSalt = fs.rebCandSalt := by rw [hfsIns_eq]; rfl
        have hrc_eq : fsIns.rebScanCursor = fs.rebScanCursor := by rw [hfsIns_eq]; rfl
        have hri_eq : fsIns.rebInsCount = fs.rebInsCount := by rw [hfsIns_eq]; rfl
        rw [hold_eq, hbuf_eq, hstg_eq, hsc_eq, hdc_eq, hdb_eq, hdi_eq, hdf_eq, hrq_eq,
          hcs_eq, hrc_eq, hri_eq]
        split_ifs at hstg ⊢ with hs0 hs1 hs2 hs3
        · exact hstg
        · exact hstg
        · rcases hstg with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
          refine ⟨hd1, hd2, hd3, hd4, hd5, ?_, fun hlt_s => ?_⟩
          · intro b' hb' l' hl' hst'
            rw [hfsIns_bkt] at hl'
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hl'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
              · rw [hls_pres b hb l' hlt] at hst'; exact hd6 b hb l' hlt hst'
              · rw [hls_new] at hst'; omega
            · rw [Function.update_of_ne hbb] at hl'
              rw [hls_pres b' hb' l' hl'] at hst'; exact hd6 b' hb' l' hl' hst'
          · obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt_s
            set bc := fs.dirtyBuckets fs.dirtyIdx
            have hbc : bc < numBucketsWhp n_max := hd3 _ hd2
            have hbkt_ge : fs.bktCount bc ≤ fsIns.bktCount bc := by
              rw [hfsIns_bkt]
              by_cases hbb : bc = b
              · rw [hbb, Function.update_self]; omega
              · rw [Function.update_of_ne hbb]
            have hmin_eq : min (fsIns.bktCount bc) fs.rebScanCursor =
                min (fs.bktCount bc) fs.rebScanCursor := by
              rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩
              · simp [hc0]
              · rw [Nat.min_eq_right (hc_lt.le.trans hbkt_ge), Nat.min_eq_right hc_lt.le]
            have hmin_le : min (fs.bktCount bc) fs.rebScanCursor ≤ fs.bktCount bc :=
              Nat.min_le_left _ _
            have hrsl_eq : fsIns.slices (fsIns.rebSliceIdx bc) =
                fs.slices (fs.rebSliceIdx bc) := by
              have hri : fsIns.rebSliceIdx bc = fs.rebSliceIdx bc := by rw [hfsIns_eq]; rfl
              rw [hri, hfsIns_eq]; dsimp only [fsAlloc, fastInsertAlloc]
              exact Function.update_of_ne (hne_reb_all bc hbc) _ _
            rw [hmin_eq, hrsl_eq]
            refine ⟨?_, ?_, rm, hvr, ?_⟩
            · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins_r⟩
              · exact Or.inl ⟨hc0, hi0⟩
              · exact Or.inr ⟨h16, hc_lt.trans_le hbkt_ge, hins_r⟩
            · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
              have hl1_b := hl₁.trans_le hmin_le
              have hl2_b := hl₂.trans_le hmin_le
              rw [hls_pres bc hbc l₁ hl1_b] at hp₁
              rw [hls_pres bc hbc l₂ hl2_b] at hp₂
              rw [hfp_pres _ bc hbc l₁ hl1_b, hfp_pres _ bc hbc l₂ hl2_b] at hfeq
              exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            · exact hrr.congr (fun loc hlt => hfp_pres _ bc hbc loc (hlt.trans_le hmin_le))
                (fun loc hlt => by rw [hls_pres bc hbc loc (hlt.trans_le hmin_le)])
        · exact hstg

/-! ## Section 2: `rebScanSteps_spec` and `epochTick_spec` -/

private theorem upd_idem' {α : Type*} {β : α → Sort*} [DecidableEq α]
    (f : (a : α) → β a) (a : α) (v w : β a) :
    Function.update (Function.update f a v) a w = Function.update f a w := by
  funext x
  by_cases hx : x = a
  · subst hx; simp
  · simp [hx]

/-- Transfer `CoreFastInv` and `OvermarsBucketInv` across any metadata/stage transition that leaves
buckets, backyard pool, roles, salts, `curEp`, `bufCur`, `liveSlice`, and `overmarsSlice` untouched
and preserves `inLiveTree` on all active coordinates. -/
private theorem core_and_om_of_inLiveTree_eq {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} (fs' : FastState) {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hep : fs'.curEp = fs.curEp)
    (hclk : fs'.epochClock < qEpochWhp n_max)
    (hstg_le : fs'.rebStage ≤ 5)
    (hcoll0 : fs'.rebCollision = 0)
    (hq : fs'.quotArr = fs.quotArr) (hv_arr : fs'.valArr = fs.valArr)
    (hbkt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hbp : fs'.backPtr = fs.backPtr) (htop : fs'.poolFreeTop = fs.poolFreeTop)
    (hstk : fs'.poolFreeStack = fs.poolFreeStack) (hown : fs'.poolOwner = fs.poolOwner)
    (hlr : fs'.liveRole = fs.liveRole) (hor : fs'.overmarsRole = fs.overmarsRole)
    (hbs : fs'.bktSalt = fs.bktSalt) (hlic : fs'.liveInsCount = fs.liveInsCount)
    (hoa : fs'.overmarsActive = fs.overmarsActive) (hoc : fs'.overmarsCursor = fs.overmarsCursor)
    (hoi : fs'.overmarsInsCount = fs.overmarsInsCount)
    (hbuf_cur : fs'.buf fs'.curEp = fs.buf fs.curEp)
    (hsl_live : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.liveSliceIdx b) = fs.slices (fs.liveSliceIdx b))
    (hsl_om : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b))
    (hinL : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
      inLiveTree fs'.rebStage fs'.oldEp (fs'.rebDoneFlag b) (fs.locState b loc) =
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc))
    (hbo' :
      if fs'.rebStage ≤ 3 then
        (fs'.buf fs'.oldEp).itemAlloc ≤ 2 * rIndepWhp c n_max ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs'.buf fs'.oldEp).itemAlloc ∧
        ∃ oldMap,
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) oldMap ∧
          BufMapRel (numBucketsWhp n_max) (2 + fs'.oldEp) fs'.bktCount fs'.locState
            (fs'.rKeyAt c U n_max θ) oldMap
      else if fs'.rebStage = 4 then
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ClearableBufTrie (fs'.buf fs'.oldEp) ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * rIndepWhp c n_max)
      else
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) (fun _ => none) ∧
        (fs'.buf fs'.oldEp).nodeAlloc = 1 ∧
        (fs'.buf fs'.oldEp).itemAlloc = 0) :
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b) := by
  have hphys : fs'.physSlot n_max = fs.physSlot n_max := by
    funext b loc; dsimp only [FastState.physSlot]; rw [hbp]
  have hkv : fs'.keyValAt c U n_max θ.1 = fs.keyValAt c U n_max θ.1 :=
    keyValAt_eq_of_fields hq hbp
  have hrk : fs'.rKeyAt c U n_max θ = fs.rKeyAt c U n_max θ :=
    rKeyAt_eq_of_fields hq hbp
  have hfp : ∀ salt b, fs'.fpAt c U n_max θ salt b = fs.fpAt c U n_max θ salt b :=
    fun salt b => fpAt_eq_of_fields hq hbp salt b
  refine ⟨?_, fun b hb => ?_⟩
  · exact
      { hth := hc.hth
        curEp_or := hep ▸ hc.curEp_or
        epochClock_lt := hclk
        rebStage_le := hstg_le
        rebCollision_zero := hcoll0
        qv_global := fun p => by rw [hq, hv_arr]; exact hc.qv_global p
        bktCount_le := by rw [hbkt]; exact hc.bktCount_le
        bktCount_ge_zero := by rw [hbkt]; exact hc.bktCount_ge_zero
        locState_active := by rw [hbkt, hls]; exact hc.locState_active
        locState_inactive := by rw [hbkt, hls]; exact hc.locState_inactive
        active_item := fun b hb loc hloc => by
          rw [hbkt] at hloc
          dsimp only; rw [hkv, hq, hv_arr, hphys]
          exact hc.active_item b hb loc hloc
        quot_inj := fun b hb l₁ hl₁ l₂ hl₂ heq => by
          rw [hbkt] at hl₁ hl₂; rw [hq, hphys] at heq
          exact hc.quot_inj b hb l₁ hl₁ l₂ hl₂ heq
        dict_map := fun u => by
          dsimp only; rw [hbkt, hq, hv_arr, hphys]; exact hc.dict_map u
        poolFreeTop_le := htop ▸ hc.poolFreeTop_le
        backPtr_valid := by rw [hbkt, hbp, hown]; exact hc.backPtr_valid
        freeStack_lt := by rw [htop, hstk]; exact hc.freeStack_lt
        backPtr_inj := by rw [hbkt, hbp]; exact hc.backPtr_inj
        freeStack_inj := by rw [htop, hstk]; exact hc.freeStack_inj
        back_free_disj := by rw [hbkt, htop, hbp, hstk]; exact hc.back_free_disj
        pool_conservation := by rw [htop, hbkt]; exact hc.pool_conservation
        roles_valid := by rw [hlr, hor]; exact hc.roles_valid
        bktSalt_lt := by rw [hbs]; exact hc.bktSalt_lt
        live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          rw [hbkt] at hl₁ hl₂
          rw [hls, hinL b hb l₁ hl₁] at hin₁
          rw [hls, hinL b hb l₂ hl₂] at hin₂
          rw [hbs, hfp] at hfeq
          exact hc.live_fp_inj b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
        live_valid := fun b hb => by
          obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b hb
          refine ⟨lm, ?_, ?_⟩
          · rwa [hlic, hsl_live b hb]
          · rw [hbs, hfp, hbkt, hls]
            exact hrl.congr (fun _ _ => rfl) (fun loc hlt => by rw [hinL b hb loc hlt])
        rKey_buf_inj := by rw [hbkt, hls, hrk]; exact hc.rKey_buf_inj
        bufCur_valid := by
          rw [hbuf_cur, hep, hbkt, hls, hrk]; exact hc.bufCur_valid
        bufOld_valid := hbo' }
  · dsimp only [OvermarsBucketInv]
    rcases hom b hb with ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
    · rw [hoa, hlic]; exact Or.inl ⟨ha0, hlt5⟩
    · rw [hoa, hoc, hbkt, hlic, hoi, hsl_om b hb, hbs, hfp, hls]
      exact Or.inr ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO,
        hrO.congr (fun _ _ => rfl) (fun loc hlt => by rw [hinL b hb loc (hlt.trans hcur)])⟩

private theorem step_of_inLiveTree_eq {c U V n_max clk₀ : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hep : fs'.curEp = fs.curEp)
    (hclk : fs'.epochClock < qEpochWhp n_max)
    (hstg_le : fs'.rebStage ≤ 5)
    (hcoll0 : fs'.rebCollision = 0)
    (hq : fs'.quotArr = fs.quotArr) (hv_arr : fs'.valArr = fs.valArr)
    (hbkt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hbp : fs'.backPtr = fs.backPtr) (htop : fs'.poolFreeTop = fs.poolFreeTop)
    (hstk : fs'.poolFreeStack = fs.poolFreeStack) (hown : fs'.poolOwner = fs.poolOwner)
    (hlr : fs'.liveRole = fs.liveRole) (hor : fs'.overmarsRole = fs.overmarsRole)
    (hbs : fs'.bktSalt = fs.bktSalt) (hlic : fs'.liveInsCount = fs.liveInsCount)
    (hoa : fs'.overmarsActive = fs.overmarsActive) (hoc : fs'.overmarsCursor = fs.overmarsCursor)
    (hoi : fs'.overmarsInsCount = fs.overmarsInsCount)
    (hbuf_cur : fs'.buf fs'.curEp = fs.buf fs.curEp)
    (hsl_live : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.liveSliceIdx b) = fs.slices (fs.liveSliceIdx b))
    (hsl_om : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b))
    (hinL : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
      inLiveTree fs'.rebStage fs'.oldEp (fs'.rebDoneFlag b) (fs.locState b loc) =
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc))
    (hbo' :
      if fs'.rebStage ≤ 3 then
        (fs'.buf fs'.oldEp).itemAlloc ≤ 2 * rIndepWhp c n_max ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs'.buf fs'.oldEp).itemAlloc ∧
        ∃ oldMap,
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) oldMap ∧
          BufMapRel (numBucketsWhp n_max) (2 + fs'.oldEp) fs'.bktCount fs'.locState
            (fs'.rKeyAt c U n_max θ) oldMap
      else if fs'.rebStage = 4 then
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ClearableBufTrie (fs'.buf fs'.oldEp) ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * rIndepWhp c n_max)
      else
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) (fun _ => none) ∧
        (fs'.buf fs'.oldEp).nodeAlloc = 1 ∧
        (fs'.buf fs'.oldEp).itemAlloc = 0)
    (hstg_valid : ValidEpochStage c U n_max θ fs')
    (hclk_eq : fs'.epochClock = clk₀) :
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b) ∧
    ValidEpochStage c U n_max θ fs' ∧
    fs'.epochClock = clk₀ := by
  obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq fs' hc hom hep hclk hstg_le hcoll0 hq hv_arr
    hbkt hls hbp htop hstk hown hlr hor hbs hlic hoa hoc hoi hbuf_cur hsl_live hsl_om hinL hbo'
  exact ⟨hc', hom', hstg_valid, hclk_eq⟩

/-- Specification of `rebScanSteps c U n_max θ b rem fs` starting from `fs.rebCollision = 0`. -/
private theorem rebScanSteps_spec {c U n_max b : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (rem : ℕ) (fs : FastState)
    (hcoll0 : fs.rebCollision = 0)
    (hcnt_le : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12)
    (hins_ub : fs.rebInsCount + rem ≤ 8 * (scaleWhp n_max) ^ 12)
    (hinj0 : ∀ l₁ < min (fs.bktCount b) fs.rebScanCursor,
      ∀ l₂ < min (fs.bktCount b) fs.rebScanCursor,
        (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
        (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
        fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
        l₁ = l₂)
    (hreb0 : ∃ rebMap,
      ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rebMap ∧
      SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) fs.rebScanCursor) rebMap) :
    (∃ sl' cur' ins',
      rebScanSteps c U n_max θ b rem fs =
        { fs with
          slices := Function.update fs.slices (fs.rebSliceIdx b) sl'
          rebScanCursor := cur'
          rebInsCount := ins'
          rebCollision := 1 }) ∨
    (∃ sl' ins' rebMap',
      rebScanSteps c U n_max θ b rem fs =
        { fs with
          slices := Function.update fs.slices (fs.rebSliceIdx b) sl'
          rebScanCursor := fs.rebScanCursor + rem
          rebInsCount := ins' } ∧
      ins' ≤ fs.rebInsCount + rem ∧
      (∀ l₁ < min (fs.bktCount b) (fs.rebScanCursor + rem),
       ∀ l₂ < min (fs.bktCount b) (fs.rebScanCursor + rem),
        (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
        (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
        fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
        l₁ = l₂) ∧
      ValidWhpSlice n_max ins' sl' rebMap' ∧
      SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) (fs.rebScanCursor + rem)) rebMap') := by
  induction rem generalizing fs with
  | zero =>
    obtain ⟨rm, hvr, hrr⟩ := hreb0
    right
    refine ⟨fs.slices (fs.rebSliceIdx b), fs.rebInsCount, rm, ?_, le_rfl, ?_, hvr, ?_⟩
    · dsimp only [rebScanSteps]; simp
    · simpa using hinj0
    · simpa using hrr
  | succ rem ih =>
    obtain ⟨rm0, hvr0, hrr0⟩ := hreb0
    dsimp only [rebScanSteps]
    rw [ite_eq_right (by omega : ¬(fs.rebCollision ≠ 0))]
    set cur := fs.rebScanCursor
    set rIdx := fs.rebSliceIdx b
    by_cases hact : cur < fs.bktCount b ∧ (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)
    · rw [ite_eq_left hact]
      set fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
      have hfp_lt : fp < 2 ^ fpBitsWhp n_max := fpAt_lt' θ fs _ b cur
      have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
        rw [valLane_pow_eq' n_max]; omega
      cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp with
      | some _ =>
        dsimp only
        have hstop : ∀ r (s : FastState), s.rebCollision ≠ 0 →
            rebScanSteps c U n_max θ b r s = s := by
          intro r s hs; cases r with
          | zero => rfl
          | succ r' => dsimp only [rebScanSteps]; exact ite_eq_left hs
        rw [hstop rem { fs with rebCollision := 1 } (show (1 : ℕ) ≠ 0 by decide)]
        left
        refine ⟨fs.slices rIdx, cur, fs.rebInsCount, ?_⟩
        dsimp only [cur, rIdx]
        rw [Function.update_eq_self]
      | none =>
        dsimp only
        have hrm0_none : rm0 fp = none :=
          (hvr0.lookup_eq hth (by omega) hfp_lt).symm.trans hlk
        have hmin0 : min (fs.bktCount b) cur = cur := Nat.min_eq_right hact.1.le
        have hmin1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
          Nat.min_eq_right (Nat.succ_le_of_lt hact.1)
        rw [hmin0] at hrr0 hinj0
        have hno_coll : ∀ loc < cur,
            (fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp) →
            fs.fpAt c U n_max θ fs.rebCandSalt b loc ≠ fp :=
          (hrr0.1 fp).mp hrm0_none
        set sl1 := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp cur
        have hv1 := (hvr0.insert_spec hth (by omega) hfp_lt hcur_val).2
        have hr1 := hrr0.step_true hact.2 hno_coll
        have hinj1 : ∀ l₁ < cur + 1, ∀ l₂ < cur + 1,
            (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
            (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
            fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
            l₁ = l₂ := by
          intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with hl1' | rfl <;>
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with hl2' | rfl
          · exact hinj0 l₁ hl1' l₂ hl2' hp₁ hp₂ hfeq
          · exact absurd hfeq (hno_coll l₁ hl1' hp₁)
          · exact absurd hfeq.symm (hno_coll l₂ hl2' hp₂)
          · rfl
        set fs1 : FastState :=
          { fs with
            slices := Function.update fs.slices rIdx sl1
            rebScanCursor := cur + 1
            rebInsCount := fs.rebInsCount + 1 }
        have hfp1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b =
            fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
        have hr1_idx : fs1.rebSliceIdx b = rIdx := rfl
        rcases ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega)
          (by dsimp only [fs1]; rw [hfp1, hmin1]; exact hinj1)
          ⟨Function.update rm0 fp (some cur),
            by rw [hr1_idx]; dsimp only [fs1]; rw [Function.update_self]; exact hv1,
            by dsimp only [fs1]; rw [hfp1, hmin1]; exact hr1⟩ with
          ⟨sl', cur', ins', heq⟩ | ⟨sl', ins', rm', heq, hins', hinj', hv', hr'⟩
        · left
          refine ⟨sl', cur', ins', ?_⟩
          rw [heq, hr1_idx]; dsimp only [fs1]; rw [upd_idem']
        · right
          dsimp only [fs1] at hins' hinj' hr'
          rw [hfp1] at hinj' hr'
          have hadd : cur + 1 + rem = cur + (rem + 1) := by omega
          rw [hadd] at hinj' hr'
          refine ⟨sl', ins', rm', ?_, by omega, hinj', hv', hr'⟩
          rw [heq, hr1_idx]; dsimp only [fs1]
          rw [upd_idem', hadd]
    · rw [ite_eq_right hact]
      set fs1 : FastState := { fs with rebScanCursor := cur + 1 }
      have hfp1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b =
          fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
      have hr1_idx : fs1.rebSliceIdx b = rIdx := rfl
      have hstep_min :
          (∀ l₁ < min (fs.bktCount b) (cur + 1), ∀ l₂ < min (fs.bktCount b) (cur + 1),
            (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
            (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
            fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
            l₁ = l₂) ∧
          SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
            (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
            (min (fs.bktCount b) (cur + 1)) rm0 := by
        by_cases hlt_b : cur < fs.bktCount b
        · have hnp : ¬(fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp) :=
            fun hp => hact ⟨hlt_b, hp⟩
          have hm0 : min (fs.bktCount b) cur = cur := Nat.min_eq_right hlt_b.le
          have hm1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
            Nat.min_eq_right (Nat.succ_le_of_lt hlt_b)
          rw [hm0] at hinj0 hrr0; rw [hm1]
          refine ⟨fun l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq => ?_, hrr0.step_false hnp⟩
          have hl1' : l₁ < cur := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₁)
            (fun h => hnp (h ▸ hp₁))
          have hl2' : l₂ < cur := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₂)
            (fun h => hnp (h ▸ hp₂))
          exact hinj0 l₁ hl1' l₂ hl2' hp₁ hp₂ hfeq
        · have hm0 : min (fs.bktCount b) cur = fs.bktCount b := Nat.min_eq_left (by omega)
          have hm1 : min (fs.bktCount b) (cur + 1) = fs.bktCount b := Nat.min_eq_left (by omega)
          rw [hm0] at hinj0 hrr0; rw [hm1]
          exact ⟨hinj0, hrr0⟩
      rcases ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega)
        (by dsimp only [fs1]; rw [hfp1]; exact hstep_min.1)
        ⟨rm0, hvr0, by dsimp only [fs1]; rw [hfp1]; exact hstep_min.2⟩ with
        ⟨sl', cur', ins', heq⟩ | ⟨sl', ins', rm', heq, hins', hinj', hv', hr'⟩
      · left; rw [heq, hr1_idx]; exact ⟨sl', cur', ins', rfl⟩
      · right
        dsimp only [fs1] at hins' hinj' hr'
        rw [hfp1] at hinj' hr'
        have hadd : cur + 1 + rem = cur + (rem + 1) := by omega
        rw [hadd] at hinj' hr'
        refine ⟨sl', ins', rm', ?_, by omega, hinj', hv', hr'⟩
        rw [heq, hr1_idx]; dsimp only [fs1, cur, rIdx]; rw [hadd]

private def epochTickStage0 (fs : FastState) : FastState :=
  let oldTr := fs.buf fs.oldEp
  if fs.stageCursor < oldTr.itemAlloc then
    match bufCheckSlot oldTr fs.stageCursor with
    | some (b, _) =>
      let nextCur := fs.stageCursor + 1
      let fs' := { fs with
        rebQueued := Function.update fs.rebQueued b 0
        rebDoneFlag := Function.update fs.rebDoneFlag b 0
        stageCursor := nextCur }
      if oldTr.itemAlloc ≤ nextCur then
        { fs' with rebStage := 1, stageCursor := 0, dirtyCount := 0 }
      else fs'
    | none =>
      let nextCur := fs.stageCursor + 1
      if oldTr.itemAlloc ≤ nextCur then
        { fs with rebStage := 1, stageCursor := 0, dirtyCount := 0 }
      else { fs with stageCursor := nextCur }
  else
    { fs with rebStage := 1, stageCursor := 0, dirtyCount := 0 }

private theorem epochTickStage0_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs0 : fs.rebStage = 0)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage0 fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_left hs0] at hpre
  obtain ⟨hsc_le, hzero0⟩ := hpre
  let oldTr := fs.buf fs.oldEp
  have hinL_eq : ∀ stg, (stg = 0 ∨ stg = 1) → ∀ (df : ℕ → ℕ) b,
      inLiveTree stg fs.oldEp (df b) = inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) := by
    intro stg hstg df b; funext st
    rcases hstg with rfl | rfl <;> simp [inLiveTree, hs0]
  have hbo_01 : ∀ stg, stg ≤ 3 →
      (if stg ≤ 3 then
        oldTr.itemAlloc ≤ 2 * rIndepWhp c n_max ∧
        oldTr.nodeAlloc ≤ 1 + cTabWhp c * oldTr.itemAlloc ∧
        ∃ oldMap,
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) oldTr oldMap ∧
          BufMapRel (numBucketsWhp n_max) (2 + fs.oldEp) fs.bktCount fs.locState
            (fs.rKeyAt c U n_max θ) oldMap
      else if stg = 4 then
        (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
        ClearableBufTrie oldTr ∧
        oldTr.nodeAlloc ≤ 1 + cTabWhp c * (2 * rIndepWhp c n_max)
      else
        (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) oldTr (fun _ => none) ∧
        oldTr.nodeAlloc = 1 ∧ oldTr.itemAlloc = 0) := by
    intro stg hle3
    have hbo := hc.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    rw [ite_eq_left hle3]; exact hbo
  dsimp only [epochTickStage0]
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some bloc =>
      rcases bloc with ⟨b₀, loc₀⟩
      dsimp only
      have hzero_next : ∀ id < fs.stageCursor + 1, ∀ b' loc',
          bufCheckSlot oldTr id = some (b', loc') →
          Function.update fs.rebQueued b₀ 0 b' = 0 ∧
          Function.update fs.rebDoneFlag b₀ 0 b' = 0 := by
        intro id hid b' loc' hc'
        by_cases hbb : b' = b₀
        · subst hbb; simp
        · rw [Function.update_of_ne hbb, Function.update_of_ne hbb]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hzero0 id hid' b' loc' hc'
          · rw [hchk] at hc'
            injection hc' with hp; injection hp with hb_eq _
            exact absurd hb_eq.symm hbb
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          (show 1 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b _ loc _ => congrFun (hinL_eq 1 (Or.inr rfl) _ b) _)
          (hbo_01 1 (by decide)) ?_ rfl
        dsimp only [ValidEpochStage]
        simp only [show ¬(1 = 0) by decide, ↓reduceIte]
        exact ⟨Nat.zero_le _, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _),
          fun _ h => absurd h (Nat.not_lt_zero _),
          fun id hid b' loc' hc' => Or.inl (hzero_next id (hid.trans_le hdone) b' loc' hc'),
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · rw [ite_eq_right hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b _ loc _ => congrFun (hinL_eq fs.rebStage (Or.inl hs0) _ b) _)
          (hbo_01 fs.rebStage (by omega)) ?_ rfl
        dsimp only [ValidEpochStage]; rw [ite_eq_left hs0]
        exact ⟨Nat.le_of_lt (Nat.lt_of_not_le hdone), hzero_next⟩
    | none =>
      dsimp only
      have hzero_next : ∀ id < fs.stageCursor + 1, ∀ b' loc',
          bufCheckSlot oldTr id = some (b', loc') →
          fs.rebQueued b' = 0 ∧ fs.rebDoneFlag b' = 0 := by
        intro id hid b' loc' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
        · exact hzero0 id hid' b' loc' hc'
        · rw [hchk] at hc'; cases hc'
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          (show 1 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b _ loc _ => congrFun (hinL_eq 1 (Or.inr rfl) _ b) _)
          (hbo_01 1 (by decide)) ?_ rfl
        dsimp only [ValidEpochStage]
        simp only [show ¬(1 = 0) by decide, ↓reduceIte]
        exact ⟨Nat.zero_le _, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _),
          fun _ h => absurd h (Nat.not_lt_zero _),
          fun id hid b' loc' hc' => Or.inl (hzero_next id (hid.trans_le hdone) b' loc' hc'),
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · rw [ite_eq_right hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ _ _ => rfl) (hbo_01 fs.rebStage (by omega)) ?_ rfl
        dsimp only [ValidEpochStage]; rw [ite_eq_left hs0]
        exact ⟨Nat.le_of_lt (Nat.lt_of_not_le hdone), hzero_next⟩
  · rw [ite_eq_right hlt]
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 1 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b _ loc _ => congrFun (hinL_eq 1 (Or.inr rfl) _ b) _)
      (hbo_01 1 (by decide)) ?_ rfl
    dsimp only [ValidEpochStage]
    simp only [show ¬(1 = 0) by decide, ↓reduceIte]
    exact ⟨Nat.zero_le _, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _),
      fun id hid b' loc' hc' =>
        Or.inl (hzero0 id (hid.trans_le (Nat.le_of_not_lt hlt)) b' loc' hc'),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

private def epochTickStage1Finish (s : FastState) : FastState :=
  if s.dirtyCount = 0 then
    { s with rebStage := 3, stageCursor := 0 }
  else
    let b0 := s.dirtyBuckets 0
    let rIdx0 := s.rebSliceIdx b0
    { s with
      rebStage := 2
      dirtyIdx := 0
      rebCandSalt := 0
      rebScanCursor := 0
      rebInsCount := 0
      rebCollision := 0
      slices := Function.update s.slices rIdx0 (resetBTreeSlice (s.slices rIdx0)) }

private def epochTickStage1 (fs : FastState) : FastState :=
  let oldTr := fs.buf fs.oldEp
  if fs.stageCursor < oldTr.itemAlloc then
    let nextCur := fs.stageCursor + 1
    let fs' :=
      match bufCheckSlot oldTr fs.stageCursor with
      | some (b, _) =>
        if fs.rebQueued b = 0 then
          { fs with
            rebQueued := Function.update fs.rebQueued b 1
            dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
            dirtyCount := fs.dirtyCount + 1
            stageCursor := nextCur }
        else { fs with stageCursor := nextCur }
      | none => { fs with stageCursor := nextCur }
    if oldTr.itemAlloc ≤ nextCur then
      epochTickStage1Finish fs'
    else fs'
  else epochTickStage1Finish fs

private theorem epochTickStage1Finish_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {s : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ s dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ s b)
    (hs1 : s.rebStage = 1)
    (hdc_le : s.dirtyCount ≤ (s.buf s.oldEp).itemAlloc)
    (hd_props : ∀ j < s.dirtyCount,
      s.dirtyBuckets j < numBucketsWhp n_max ∧
      s.rebQueued (s.dirtyBuckets j) = 1 ∧
      s.rebDoneFlag (s.dirtyBuckets j) = 0)
    (hd_inj : ∀ j₁ < s.dirtyCount, ∀ j₂ < s.dirtyCount,
      s.dirtyBuckets j₁ = s.dirtyBuckets j₂ → j₁ = j₂)
    (hall_queued : ∀ id < (s.buf s.oldEp).itemAlloc, ∀ b loc,
      bufCheckSlot (s.buf s.oldEp) id = some (b, loc) →
        ∃ j < s.dirtyCount, s.dirtyBuckets j = b) :
    let fs1 := epochTickStage1Finish s
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = s.epochClock := by
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : s.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
  have hold_dirty : ∀ b < numBucketsWhp n_max, ∀ loc < s.bktCount b,
      s.locState b loc = 2 + s.oldEp → ∃ j < s.dirtyCount, s.dirtyBuckets j = b := by
    intro b hb loc hloc hst
    have hm_some : oldMap (s.rKeyAt c U n_max θ b loc) = some (b, loc) :=
      (hrel_o.2 _ b loc).mpr ⟨hb, hloc, hst, rfl⟩
    obtain ⟨id, hid, hchk⟩ := hv_o.exists_checkSlot_of_map_some hm_some
    exact hall_queued id hid b loc hchk
  dsimp only [epochTickStage1Finish]
  by_cases hdc0 : s.dirtyCount = 0
  · rw [ite_eq_left hdc0]
    have hno_old : ∀ b < numBucketsWhp n_max, ∀ loc < s.bktCount b,
        s.locState b loc ≠ 2 + s.oldEp := by
      intro b hb loc hloc hst
      obtain ⟨j, hj, _⟩ := hold_dirty b hb loc hloc hst
      omega
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 3 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b hb loc hloc => by
        have hne := hno_old b hb loc hloc
        change inLiveTree 3 s.oldEp (s.rebDoneFlag b) (s.locState b loc) =
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc)
        simp [inLiveTree, hs1, hne])
      (by
        dsimp only [FastState.oldEp]
        simp only [show (3 : ℕ) ≤ 3 by decide, ↓reduceIte]
        exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩) ?_ rfl
    dsimp only [ValidEpochStage]
    simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
      ↓reduceIte]
    exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [ite_eq_right hdc0]
    have hdc_pos : 0 < s.dirtyCount := Nat.pos_of_ne_zero hdc0
    set b0 := s.dirtyBuckets 0
    have hb0 : b0 < numBucketsWhp n_max := (hd_props 0 hdc_pos).1
    set rIdx0 := s.rebSliceIdx b0
    obtain ⟨hlr0, hor0, hne0⟩ := hc.roles_valid b0 hb0
    have hrr0 : s.rebRole b0 < 3 ∧ s.rebRole b0 ≠ s.liveRole b0 ∧
        s.rebRole b0 ≠ s.overmarsRole b0 := by
      dsimp only [FastState.rebRole]; omega
    have hne_live : ∀ b < numBucketsWhp n_max, s.liveSliceIdx b ≠ rIdx0 := by
      intro b hb; dsimp only [FastState.liveSliceIdx, rIdx0, FastState.rebSliceIdx]
      by_cases hbb : b = b0
      · subst hbb; omega
      · intro heq; exact hbb (sliceIdx_inj (hc.roles_valid b hb).1 hrr0.1 heq).1
    have hne_om : ∀ b < numBucketsWhp n_max, s.overmarsSliceIdx b ≠ rIdx0 := by
      intro b hb; dsimp only [FastState.overmarsSliceIdx, rIdx0, FastState.rebSliceIdx]
      by_cases hbb : b = b0
      · subst hbb; omega
      · intro heq; exact hbb (sliceIdx_inj (hc.roles_valid b hb).2.1 hrr0.1 heq).1
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 2 ≤ 5 by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
      (fun b hb => Function.update_of_ne (hne_live b hb) _ _)
      (fun b hb => Function.update_of_ne (hne_om b hb) _ _)
      (fun b hb loc hloc => by
        change inLiveTree 2 s.oldEp (s.rebDoneFlag b) (s.locState b loc) =
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc)
        by_cases hst : s.locState b loc = 2 + s.oldEp
        · obtain ⟨j, hj, hdb_eq⟩ := hold_dirty b hb loc hloc hst
          have hdf0 : s.rebDoneFlag b = 0 := hdb_eq ▸ (hd_props j hj).2.2
          simp [inLiveTree, hs1, hst, hdf0]
        · simp [inLiveTree, hs1, hst])
      (by
        dsimp only [FastState.oldEp]
        simp only [show (2 : ℕ) ≤ 3 by decide, ↓reduceIte]
        exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩) ?_ rfl
    dsimp only [ValidEpochStage]
    simp only [show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte]
    refine ⟨hdc_le.trans hia_o, hdc_pos, fun j hj => (hd_props j hj).1, hd_inj,
      fun j hj => ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => (hd_props j hj).2.2⟩,
      hold_dirty, fun _ => ⟨Or.inl ⟨trivial, trivial⟩,
        fun _ hl => absurd (hl.trans_le (Nat.min_le_right _ _)) (Nat.not_lt_zero _),
        fun _ => none, ?_,
        by
          rw [Nat.min_zero]
          exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    change ValidWhpSlice n_max 0
      (Function.update s.slices rIdx0 (resetBTreeSlice (s.slices rIdx0)) rIdx0)
      (fun _ => none)
    rw [Function.update_self]
    exact validSlice_zero _ _ _ 0 _

private theorem epochTickStage1_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs1 : fs.rebStage = 1)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage1 fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)), ite_eq_left hs1] at hpre
  rcases hpre with ⟨hsc_le, hdc_sc, hd_props, hd_inj, hall_or, hlt_sc⟩
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
  let oldTr := fs.buf fs.oldEp
  dsimp only [epochTickStage1]
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    let nextCur := fs.stageCursor + 1
    set fs' : FastState :=
      match bufCheckSlot oldTr fs.stageCursor with
      | some (b, _) =>
        if fs.rebQueued b = 0 then
          { fs with
            rebQueued := Function.update fs.rebQueued b 1
            dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
            dirtyCount := fs.dirtyCount + 1
            stageCursor := nextCur }
        else { fs with stageCursor := nextCur }
      | none => { fs with stageCursor := nextCur }
    have hstep :
        CoreFastInv c U V n_max θ fs' dict ∧
        (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b) ∧
        fs'.rebStage = 1 ∧
        fs'.epochClock = fs.epochClock ∧
        fs'.buf fs'.oldEp = oldTr ∧
        fs'.stageCursor = nextCur ∧
        fs'.dirtyCount ≤ nextCur ∧
        (∀ j < fs'.dirtyCount,
          fs'.dirtyBuckets j < numBucketsWhp n_max ∧
          fs'.rebQueued (fs'.dirtyBuckets j) = 1 ∧
          fs'.rebDoneFlag (fs'.dirtyBuckets j) = 0) ∧
        (∀ j₁ < fs'.dirtyCount, ∀ j₂ < fs'.dirtyCount,
          fs'.dirtyBuckets j₁ = fs'.dirtyBuckets j₂ → j₁ = j₂) ∧
        (∀ id < oldTr.itemAlloc, ∀ b loc,
          bufCheckSlot oldTr id = some (b, loc) →
            (fs'.rebQueued b = 0 ∧ fs'.rebDoneFlag b = 0) ∨
            ∃ j < fs'.dirtyCount, fs'.dirtyBuckets j = b) ∧
        (∀ id < nextCur, ∀ b loc,
          bufCheckSlot oldTr id = some (b, loc) →
            ∃ j < fs'.dirtyCount, fs'.dirtyBuckets j = b) := by
      cases hchk : bufCheckSlot oldTr fs.stageCursor with
      | some bloc =>
        rcases bloc with ⟨b₀, loc₀⟩
        obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
        have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
        by_cases hq0 : fs.rebQueued b₀ = 0
        · have hfs'_eq : fs' =
              { fs with
                rebQueued := Function.update fs.rebQueued b₀ 1
                dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
                dirtyCount := fs.dirtyCount + 1
                stageCursor := nextCur } := by
            dsimp only [fs']; rw [hchk]; exact ite_eq_left hq0
          have hdf₀ : fs.rebDoneFlag b₀ = 0 := by
            rcases hall_or fs.stageCursor hlt b₀ loc₀ hchk with ⟨_, hd⟩ | ⟨j, hj, hdb⟩
            · exact hd
            · have := (hd_props j hj).2.1; rw [hdb, hq0] at this; omega
          have hne_prev : ∀ j < fs.dirtyCount, fs.dirtyBuckets j ≠ b₀ := by
            intro j hj heq
            have := (hd_props j hj).2.1; rw [heq, hq0] at this; omega
          rw [hfs'_eq]
          dsimp only
          obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq
            { fs with
              rebQueued := Function.update fs.rebQueued b₀ 1
              dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
              dirtyCount := fs.dirtyCount + 1
              stageCursor := nextCur }
            hc hom rfl hc.epochClock_lt
            hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
            (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
                exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
          refine ⟨hc', hom', hs1, rfl, rfl, rfl, by omega, ?_, ?_, ?_, ?_⟩
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
            · rw [Function.update_of_ne (by omega : j ≠ fs.dirtyCount),
                Function.update_of_ne (hne_prev j hj')]
              exact hd_props j hj'
            · simp [hb₀, hdf₀]
          · intro j₁ hj₁ j₂ hj₂ heq
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj₁ with hj₁' | rfl <;>
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj₂ with hj₂' | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at heq
              exact hd_inj j₁ hj₁' j₂ hj₂' heq
            · rw [Function.update_of_ne (by omega), Function.update_self] at heq
              exact absurd heq (hne_prev j₁ hj₁')
            · rw [Function.update_self, Function.update_of_ne (by omega)] at heq
              exact absurd heq.symm (hne_prev j₂ hj₂')
            · rfl
          · intro id hid b' loc' hc'
            by_cases hbb : b' = b₀
            · subst hbb; right; exact ⟨fs.dirtyCount, Nat.lt_succ_self _, by simp⟩
            · rw [Function.update_of_ne hbb]
              rcases hall_or id hid b' loc' hc' with hleft | ⟨j, hj, hdb⟩
              · exact Or.inl hleft
              · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, by
                  rw [Function.update_of_ne (by omega)]; exact hdb⟩
          · intro id hid b' loc' hc'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
            · obtain ⟨j, hj, hdb⟩ := hlt_sc id hid' b' loc' hc'
              exact ⟨j, Nat.lt_succ_of_lt hj, by
                rw [Function.update_of_ne (by omega)]; exact hdb⟩
            · rw [hchk] at hc'; injection hc' with hp; injection hp with hbb _
              exact ⟨fs.dirtyCount, Nat.lt_succ_self _, by simp [hbb]⟩
        · have hfs'_eq : fs' = { fs with stageCursor := nextCur } := by
            dsimp only [fs']; rw [hchk]; exact ite_eq_right hq0
          have hex₀ : ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b₀ := by
            rcases hall_or fs.stageCursor hlt b₀ loc₀ hchk with ⟨hq, _⟩ | hex
            · exact absurd hq hq0
            · exact hex
          rw [hfs'_eq]
          dsimp only
          obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq { fs with stageCursor := nextCur }
            hc hom rfl hc.epochClock_lt
            hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
            (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
                exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
          refine ⟨hc', hom', hs1, rfl, rfl, rfl, by omega, hd_props, hd_inj, hall_or, ?_⟩
          intro id hid b' loc' hc'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hlt_sc id hid' b' loc' hc'
          · rw [hchk] at hc'; injection hc' with hp; injection hp with hbb _
            rwa [← hbb]
      | none =>
        have hfs'_eq : fs' = { fs with stageCursor := nextCur } := by
          dsimp only [fs']; rw [hchk]
        rw [hfs'_eq]
        dsimp only
        obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq { fs with stageCursor := nextCur }
          hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
          (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
              exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
        refine ⟨hc', hom', hs1, rfl, rfl, rfl, by omega, hd_props, hd_inj, hall_or, ?_⟩
        intro id hid b' loc' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
        · exact hlt_sc id hid' b' loc' hc'
        · rw [hchk] at hc'; cases hc'
    rcases hstep with ⟨hc', hom', hs1', hclk', hbuf', hsc', hdc', hd_p', hd_i', hall_o', hlt_s'⟩
    by_cases hdone : oldTr.itemAlloc ≤ nextCur
    · rw [ite_eq_left hdone]
      obtain ⟨hcF, homF, hstF, hclkF⟩ := epochTickStage1Finish_spec hc' hom' hs1'
        (by rw [hbuf']; exact hdc'.trans (by omega))
        hd_p' hd_i'
        (fun id hid b loc hchk => hlt_s' id (by rw [hbuf'] at hid; omega) b loc (hbuf' ▸ hchk))
      exact ⟨hcF, homF, hstF, hclkF.trans hclk'⟩
    · rw [ite_eq_right hdone]
      refine ⟨hc', hom', ?_, hclk'⟩
      dsimp only [ValidEpochStage]
      rw [ite_eq_right (by omega : ¬(fs'.rebStage = 0)), ite_eq_left hs1', hbuf', hsc']
      exact ⟨by omega, hdc', hd_p', hd_i', hall_o', hlt_s'⟩
  · rw [ite_eq_right hlt]
    exact epochTickStage1Finish_spec hc hom hs1 (hdc_sc.trans hsc_le) hd_props hd_inj
      (fun id hid b loc hchk => hlt_sc id (hid.trans_le (Nat.le_of_not_lt hlt)) b loc hchk)

private def epochTickStage2Swap (b : ℕ) (fsScan : FastState) : FastState :=
  let oldReb := fsScan.rebRole b
  let omIdx := fsScan.overmarsSliceIdx b
  let nextIdx := fsScan.dirtyIdx + 1
  { fsScan with
    liveRole := Function.update fsScan.liveRole b oldReb
    bktSalt := Function.update fsScan.bktSalt b fsScan.rebCandSalt
    liveInsCount := Function.update fsScan.liveInsCount b fsScan.rebInsCount
    overmarsActive := Function.update fsScan.overmarsActive b 0
    overmarsCursor := Function.update fsScan.overmarsCursor b 0
    overmarsInsCount := Function.update fsScan.overmarsInsCount b 0
    slices := Function.update fsScan.slices omIdx (resetBTreeSlice (fsScan.slices omIdx))
    rebDoneFlag := Function.update fsScan.rebDoneFlag b 1
    dirtyIdx := nextIdx
    rebCandSalt := 0
    rebScanCursor := 0
    rebInsCount := 0
    rebCollision := 0 }

private def epochTickStage2AfterSwap (nextIdx : ℕ) (fsSwapped : FastState) : FastState :=
  if fsSwapped.dirtyCount ≤ nextIdx then
    { fsSwapped with rebStage := 3, stageCursor := 0 }
  else
    let bNext := fsSwapped.dirtyBuckets nextIdx
    let rIdxNext := fsSwapped.rebSliceIdx bNext
    { fsSwapped with
      slices := Function.update fsSwapped.slices rIdxNext
        (resetBTreeSlice (fsSwapped.slices rIdxNext)) }

private def epochTickStage2 (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : FastState :=
  if fs.dirtyIdx < fs.dirtyCount then
    let b := fs.dirtyBuckets fs.dirtyIdx
    if fs.rebCandSalt < sMaxWhp c n_max then
      let fsScan := rebScanSteps c U n_max θ b 16 fs
      if fsScan.rebCollision ≠ 0 then
        let rIdx := fsScan.rebSliceIdx b
        { fsScan with
          rebCandSalt := fsScan.rebCandSalt + 1
          rebScanCursor := 0
          rebInsCount := 0
          rebCollision := 0
          slices := Function.update fsScan.slices rIdx (resetBTreeSlice (fsScan.slices rIdx)) }
      else if fsScan.bktCount b ≤ fsScan.rebScanCursor then
        epochTickStage2AfterSwap (fsScan.dirtyIdx + 1) (epochTickStage2Swap b fsScan)
      else fsScan
    else fs
  else { fs with rebStage := 3, stageCursor := 0 }

private theorem epochTickStage2_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs2 : fs.rebStage = 2)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage2 c U n_max θ fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  have hL2 : 2 ≤ scaleWhp n_max := two_le_scaleWhp n_max
  have hL12 : 4096 ≤ (scaleWhp n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
    ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2] at hpre
  rcases hpre with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  dsimp only [epochTickStage2]
  rw [ite_eq_left hd2]
  set b := fs.dirtyBuckets fs.dirtyIdx
  have hb : b < numBucketsWhp n_max := hd3 _ hd2
  obtain ⟨hlr_b, hor_b, hne_b⟩ := hc.roles_valid b hb
  have hrr_b : fs.rebRole b < 3 ∧ fs.rebRole b ≠ fs.liveRole b ∧
      fs.rebRole b ≠ fs.overmarsRole b := by
    dsimp only [FastState.rebRole]; omega
  set rIdx := fs.rebSliceIdx b
  have hne_live_r : ∀ b' < numBucketsWhp n_max, fs.liveSliceIdx b' ≠ rIdx := by
    intro b' hb'; dsimp only [FastState.liveSliceIdx, rIdx, FastState.rebSliceIdx]
    by_cases hbb : b' = b
    · subst hbb; omega
    · intro heq; exact hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hrr_b.1 heq).1
  have hne_om_r : ∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b' ≠ rIdx := by
    intro b' hb'; dsimp only [FastState.overmarsSliceIdx, rIdx, FastState.rebSliceIdx]
    by_cases hbb : b' = b
    · subst hbb; omega
    · intro heq; exact hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hrr_b.1 heq).1
  by_cases hcs_lt : fs.rebCandSalt < sMaxWhp c n_max
  · rw [ite_eq_left hcs_lt]
    obtain ⟨hcur_r, hinj_r, rm0, hvr0, hrr0⟩ := hreb hcs_lt
    have hcnt_3L : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12 :=
      (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
    have hins_ub : fs.rebInsCount + 16 ≤ 8 * (scaleWhp n_max) ^ 12 := by
      rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hc_le, hins_le⟩ <;> omega
    rcases rebScanSteps_spec hc.hth θ 16 fs hc.rebCollision_zero hcnt_3L hins_ub hinj_r
      ⟨rm0, hvr0, hrr0⟩ with
      ⟨sl_c, cur_c, ins_c, hscan_c⟩ | ⟨sl', ins', rm', hscan_ok, hins_le', hinj', hv', hrr'⟩
    · -- Fingerprint collision detected during the 16-step scan: reset `rIdx` and bump `rebCandSalt`
      rw [hscan_c]
      dsimp only
      rw [ite_eq_left (by decide)]
      refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
        hc.rebStage_le rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun b' hb' => by
          change Function.update (Function.update fs.slices rIdx sl_c) rIdx
            (resetBTreeSlice (Function.update fs.slices rIdx sl_c rIdx))
            (fs.liveSliceIdx b') = fs.slices (fs.liveSliceIdx b')
          rw [upd_idem']
          exact Function.update_of_ne (hne_live_r b' hb') _ _)
        (fun b' hb' => by
          change Function.update (Function.update fs.slices rIdx sl_c) rIdx
            (resetBTreeSlice (Function.update fs.slices rIdx sl_c rIdx))
            (fs.overmarsSliceIdx b') = fs.slices (fs.overmarsSliceIdx b')
          rw [upd_idem']
          exact Function.update_of_ne (hne_om_r b' hb') _ _)
        (fun _ _ _ _ => rfl)
        (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]; exact hbo)
        ?_ rfl
      dsimp only [ValidEpochStage]
      rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
        ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2]
      refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun _ => ⟨Or.inl ⟨rfl, rfl⟩,
        fun _ hl => absurd (hl.trans_le (Nat.min_le_right _ _)) (Nat.not_lt_zero _),
        fun _ => none, ?_,
        by
          rw [Nat.min_zero]
          exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
      change ValidWhpSlice n_max 0
        (Function.update (Function.update fs.slices rIdx sl_c) rIdx
          (resetBTreeSlice (Function.update fs.slices rIdx sl_c rIdx)) rIdx) (fun _ => none)
      rw [upd_idem', Function.update_self, Function.update_self]
      exact validSlice_zero _ _ _ 0 _
    · -- Clean 16-step scan (`rebCollision = 0`)
      rw [hscan_ok]
      dsimp only
      have hc0_scan : ¬(({ fs with
          slices := Function.update fs.slices rIdx sl'
          rebScanCursor := fs.rebScanCursor + 16
          rebInsCount := ins' } : FastState).rebCollision ≠ 0) :=
        fun h => h hc.rebCollision_zero
      rw [ite_eq_right hc0_scan]
      by_cases hdone_b : fs.bktCount b ≤ fs.rebScanCursor + 16
      · -- Bucket `b` finished scanning: swap `rebRole b` into `liveRole b` and advance `dirtyIdx`
        rw [ite_eq_left hdone_b]
        have hmin_full : min (fs.bktCount b) (fs.rebScanCursor + 16) = fs.bktCount b :=
          Nat.min_eq_left hdone_b
        rw [hmin_full] at hinj' hrr'
        have hins'_lt5 : ins' < 5 * (scaleWhp n_max) ^ 12 := by
          rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hc_le, hins_le⟩ <;> omega
        set fsScan : FastState :=
          { fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := fs.rebScanCursor + 16
            rebInsCount := ins' }
        set fsSw : FastState := epochTickStage2Swap b fsScan
        have hinL_sw_b : ∀ st, (inLiveTree 2 fs.oldEp 1 st = true) ↔
            (st = 1 ∨ st = 2 + fs.oldEp) := by
          intro st; simp [inLiveTree]
        have hSw_core : CoreFastInv c U V n_max θ fsSw dict :=
          { hth := hc.hth
            curEp_or := hc.curEp_or
            epochClock_lt := hc.epochClock_lt
            rebStage_le := hc.rebStage_le
            rebCollision_zero := rfl
            qv_global := hc.qv_global
            bktCount_le := hc.bktCount_le
            bktCount_ge_zero := hc.bktCount_ge_zero
            locState_active := hc.locState_active
            locState_inactive := hc.locState_inactive
            active_item := hc.active_item
            quot_inj := hc.quot_inj
            dict_map := hc.dict_map
            poolFreeTop_le := hc.poolFreeTop_le
            backPtr_valid := hc.backPtr_valid
            freeStack_lt := hc.freeStack_lt
            backPtr_inj := hc.backPtr_inj
            freeStack_inj := hc.freeStack_inj
            back_free_disj := hc.back_free_disj
            pool_conservation := hc.pool_conservation
            roles_valid := fun b' hb' => by
              dsimp only [fsSw, epochTickStage2Swap, fsScan]
              by_cases hbb : b' = b
              · subst hbb
                rw [Function.update_self]
                exact ⟨hrr_b.1, hor_b, hrr_b.2.2⟩
              · rw [Function.update_of_ne hbb]
                exact hc.roles_valid b' hb'
            bktSalt_lt := fun b' hb' => by
              dsimp only [fsSw, epochTickStage2Swap, fsScan]
              by_cases hbb : b' = b
              · subst hbb; simp [hcs_lt]
              · simp [hbb, hc.bktSalt_lt b' hb']
            live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              have hst_eq : fsSw.rebStage = 2 := hs2
              have hold_eq : fsSw.oldEp = fs.oldEp := rfl
              have hls_eq : fsSw.locState = fs.locState := rfl
              have hfp_eq : ∀ s, fsSw.fpAt c U n_max θ s = fs.fpAt c U n_max θ s :=
                fun s => by funext b0; exact fpAt_eq_of_fields rfl rfl s b0
              rw [hst_eq, hold_eq, hls_eq] at hin₁ hin₂
              rw [hfp_eq] at hfeq
              by_cases hbb : b' = b
              · subst hbb
                have hdf1 : fsSw.rebDoneFlag b = 1 := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]; simp
                have hbs_b : fsSw.bktSalt b = fs.rebCandSalt := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]; simp
                rw [hdf1] at hin₁ hin₂
                rw [hbs_b] at hfeq
                exact hinj' l₁ hl₁ l₂ hl₂ ((hinL_sw_b _).mp hin₁) ((hinL_sw_b _).mp hin₂) hfeq
              · have hdf_o : fsSw.rebDoneFlag b' = fs.rebDoneFlag b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  exact Function.update_of_ne hbb _ _
                have hbs_o : fsSw.bktSalt b' = fs.bktSalt b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  exact Function.update_of_ne hbb _ _
                rw [hdf_o, ← hs2] at hin₁ hin₂; rw [hbs_o] at hfeq
                exact hc.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b' hb' => by
              have hst_eq : fsSw.rebStage = 2 := hs2
              have hold_eq : fsSw.oldEp = fs.oldEp := rfl
              have hls_eq : fsSw.locState = fs.locState := rfl
              have hbkt_eq : fsSw.bktCount = fs.bktCount := rfl
              have hfp_eq : ∀ s, fsSw.fpAt c U n_max θ s = fs.fpAt c U n_max θ s :=
                fun s => by funext b0; exact fpAt_eq_of_fields rfl rfl s b0
              rw [hst_eq, hold_eq, hls_eq, hbkt_eq, hfp_eq]
              by_cases hbb : b' = b
              · subst hbb
                have hdf1 : fsSw.rebDoneFlag b = 1 := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]; simp
                have hbs_b : fsSw.bktSalt b = fs.rebCandSalt := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]; simp
                have hlic_b : fsSw.liveInsCount b = ins' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]; simp
                have hl_idx : fsSw.liveSliceIdx b = rIdx := by
                  change 3 * b + Function.update fs.liveRole b (fs.rebRole b) b =
                    3 * b + fs.rebRole b
                  rw [Function.update_self]
                have hsl_b : fsSw.slices (fsSw.liveSliceIdx b) = sl' := by
                  rw [hl_idx]
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  have hro_ne : rIdx ≠ fs.overmarsSliceIdx b := (hne_om_r b hb).symm
                  change Function.update (Function.update fs.slices rIdx sl')
                    (fs.overmarsSliceIdx b) _ rIdx = sl'
                  rw [Function.update_of_ne hro_ne, Function.update_self]
                rw [hdf1, hbs_b, hlic_b, hsl_b]
                exact ⟨rm', hv', hrr'.congr (fun _ _ => rfl)
                  (fun loc _ => hinL_sw_b (fs.locState b loc))⟩
              · obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
                have hdf_o : fsSw.rebDoneFlag b' = fs.rebDoneFlag b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  exact Function.update_of_ne hbb _ _
                have hbs_o : fsSw.bktSalt b' = fs.bktSalt b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  exact Function.update_of_ne hbb _ _
                have hlic_o : fsSw.liveInsCount b' = fs.liveInsCount b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  exact Function.update_of_ne hbb _ _
                have hne_om_b : fs.liveSliceIdx b' ≠ fs.overmarsSliceIdx b := by
                  dsimp only [FastState.liveSliceIdx, FastState.overmarsSliceIdx]
                  intro heq
                  exact hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hor_b heq).1
                have hl_idx : fsSw.liveSliceIdx b' = fs.liveSliceIdx b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan, FastState.liveSliceIdx]
                  rw [Function.update_of_ne hbb]
                have hsl_o :
                    fsSw.slices (fsSw.liveSliceIdx b') = fs.slices (fs.liveSliceIdx b') := by
                  rw [hl_idx]
                  change Function.update (Function.update fs.slices rIdx sl')
                    (fs.overmarsSliceIdx b) _ (fs.liveSliceIdx b') = _
                  rw [Function.update_of_ne hne_om_b, Function.update_of_ne (hne_live_r b' hb')]
                rw [hdf_o, hbs_o, hlic_o, hsl_o, ← hs2]
                exact ⟨lm, hvl, hrl⟩
            rKey_buf_inj := hc.rKey_buf_inj
            bufCur_valid := hc.bufCur_valid
            bufOld_valid := by
              have hst_sw : fsSw.rebStage = fs.rebStage := rfl
              rw [hst_sw, ite_eq_left (by omega : fs.rebStage ≤ 3)]
              exact hbo }
        have hSw_om : ∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fsSw b' := by
          intro b' hb'
          by_cases hbb : b' = b
          · subst hbb
            left
            dsimp only [fsSw, epochTickStage2Swap, fsScan]
            simp [hins'_lt5]
          · have hne_om2 : fs.overmarsSliceIdx b' ≠ fs.overmarsSliceIdx b := by
              dsimp only [FastState.overmarsSliceIdx]
              intro heq
              exact hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hor_b heq).1
            have hu_ne : ∀ (f : ℕ → ℕ) v, Function.update f b v b' = f b' :=
              fun _ _ => Function.update_of_ne hbb _ _
            refine (hom b' hb').of_eq_on
              (by dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  rw [Function.update_of_ne hbb]; exact fpAt_eq_of_fields rfl rfl _ _)
              rfl rfl (hu_ne _ _) rfl rfl (hu_ne _ _) (hu_ne _ _) (hu_ne _ _) (hu_ne _ _)
              (by
                have ho_idx : fsSw.overmarsSliceIdx b' = fs.overmarsSliceIdx b' := rfl
                rw [ho_idx]
                change Function.update (Function.update fs.slices rIdx sl')
                  (fs.overmarsSliceIdx b) _ (fs.overmarsSliceIdx b') = _
                rw [Function.update_of_ne hne_om2, Function.update_of_ne (hne_om_r b' hb')])
        have hd5_Sw : ∀ j < fs.dirtyCount,
            (j < fs.dirtyIdx + 1 → fsSw.rebDoneFlag (fs.dirtyBuckets j) = 1) ∧
            (fs.dirtyIdx + 1 ≤ j → fsSw.rebDoneFlag (fs.dirtyBuckets j) = 0) := by
          intro j hj
          dsimp only [fsSw, epochTickStage2Swap, fsScan]
          by_cases hjd : j = fs.dirtyIdx
          · subst hjd
            change (fs.dirtyIdx < fs.dirtyIdx + 1 → Function.update fs.rebDoneFlag b 1 b = 1) ∧
              (fs.dirtyIdx + 1 ≤ fs.dirtyIdx → Function.update fs.rebDoneFlag b 1 b = 0)
            rw [Function.update_self]; exact ⟨fun _ => rfl, fun h => by omega⟩
          · have hdb_ne : fs.dirtyBuckets j ≠ b := fun heq => hjd (hd4 j hj fs.dirtyIdx hd2 heq)
            rw [Function.update_of_ne hdb_ne]
            exact ⟨fun hlt => (hd5 j hj).1 (by omega), fun hge => (hd5 j hj).2 (by omega)⟩
        dsimp only [epochTickStage2AfterSwap]
        have hdc_sw : fsSw.dirtyCount = fs.dirtyCount := rfl
        by_cases hall_done : fsSw.dirtyCount ≤ fs.dirtyIdx + 1
        · rw [ite_eq_left hall_done]
          refine step_of_inLiveTree_eq hSw_core hSw_om rfl hc.epochClock_lt
            (show 3 ≤ 5 by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
            (fun b' hb' loc hloc => by
              have hst_sw : fsSw.rebStage = 2 := hs2
              have hold_sw : fsSw.oldEp = fs.oldEp := rfl
              have hls_sw : fsSw.locState = fs.locState := rfl
              change inLiveTree 3 fsSw.oldEp (fsSw.rebDoneFlag b') (fsSw.locState b' loc) =
                inLiveTree fsSw.rebStage fsSw.oldEp (fsSw.rebDoneFlag b') (fsSw.locState b' loc)
              rw [hst_sw, hold_sw, hls_sw]
              by_cases hst : fs.locState b' loc = 2 + fs.oldEp
              · obtain ⟨j, hj, hdb_j⟩ := hd6 b' hb' loc hloc hst
                have hdf1 : fsSw.rebDoneFlag b' = 1 :=
                  hdb_j ▸ (hd5_Sw j hj).1 (by rw [hdc_sw] at hall_done; omega)
                simp [inLiveTree, hst, hdf1]
              · simp [inLiveTree, beq_false_of_ne hst])
            (by
              dsimp only [FastState.oldEp]
              simp only [show (3 : ℕ) ≤ 3 by decide, ↓reduceIte]
              exact hbo) ?_ rfl
          dsimp only [ValidEpochStage]
          simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
            ↓reduceIte]
          exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        · rw [ite_eq_right hall_done]
          have hnxt_lt : fs.dirtyIdx + 1 < fs.dirtyCount := by rw [hdc_sw] at hall_done; omega
          set bNext := fsSw.dirtyBuckets (fs.dirtyIdx + 1)
          have hbNext : bNext < numBucketsWhp n_max := hd3 _ hnxt_lt
          set rIdxNext := fsSw.rebSliceIdx bNext
          obtain ⟨hlr_n, hor_n, hne_n⟩ := hSw_core.roles_valid bNext hbNext
          have hrr_n : fsSw.rebRole bNext < 3 ∧ fsSw.rebRole bNext ≠ fsSw.liveRole bNext ∧
              fsSw.rebRole bNext ≠ fsSw.overmarsRole bNext := by
            dsimp only [FastState.rebRole]; omega
          have hne_live_n : ∀ b' < numBucketsWhp n_max, fsSw.liveSliceIdx b' ≠ rIdxNext := by
            intro b' hb'; dsimp only [FastState.liveSliceIdx, rIdxNext, FastState.rebSliceIdx]
            by_cases hbb : b' = bNext
            · subst hbb; omega
            · intro heq; exact hbb (sliceIdx_inj (hSw_core.roles_valid b' hb').1 hrr_n.1 heq).1
          have hne_om_n : ∀ b' < numBucketsWhp n_max, fsSw.overmarsSliceIdx b' ≠ rIdxNext := by
            intro b' hb'; dsimp only [FastState.overmarsSliceIdx, rIdxNext, FastState.rebSliceIdx]
            by_cases hbb : b' = bNext
            · subst hbb; omega
            · intro heq; exact hbb (sliceIdx_inj (hSw_core.roles_valid b' hb').2.1 hrr_n.1 heq).1
          refine step_of_inLiveTree_eq hSw_core hSw_om rfl hc.epochClock_lt
            hc.rebStage_le rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            (fun b' hb' => Function.update_of_ne (hne_live_n b' hb') _ _)
            (fun b' hb' => Function.update_of_ne (hne_om_n b' hb') _ _)
            (fun _ _ _ _ => rfl)
            (by
              have hst_sw : ({ fsSw with
                  slices := Function.update fsSw.slices rIdxNext
                    (resetBTreeSlice (fsSw.slices rIdxNext)) } : FastState).rebStage =
                  fs.rebStage := rfl
              rw [hst_sw, ite_eq_left (by omega : fs.rebStage ≤ 3)]
              exact hbo) ?_ rfl
          dsimp only [ValidEpochStage]
          have hs2_sw : fsSw.rebStage = 2 := hs2
          rw [ite_eq_right (by rw [hs2_sw]; decide), ite_eq_right (by rw [hs2_sw]; decide),
            ite_eq_left hs2_sw]
          refine ⟨hd1, hnxt_lt, hd3, hd4, hd5_Sw, hd6, fun _ => ⟨Or.inl ⟨rfl, rfl⟩,
            fun _ hl => absurd (hl.trans_le (Nat.min_le_right _ _)) (Nat.not_lt_zero _),
            fun _ => none, ?_,
            by
              change SliceMapRel _ _ (min _ 0) _
              rw [Nat.min_zero]
              exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
          change ValidWhpSlice n_max 0
            (Function.update fsSw.slices rIdxNext (resetBTreeSlice (fsSw.slices rIdxNext)) rIdxNext)
            (fun _ => none)
          rw [Function.update_self]
          exact validSlice_zero _ _ _ 0 _
      · -- Bucket `b` still scanning (`fs.rebScanCursor + 16 < fs.bktCount b`)
        rw [ite_eq_right hdone_b]
        have hcur_lt_b : fs.rebScanCursor + 16 < fs.bktCount b := Nat.lt_of_not_le hdone_b
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl
          (fun b' hb' => Function.update_of_ne (hne_live_r b' hb') _ _)
          (fun b' hb' => Function.update_of_ne (hne_om_r b' hb') _ _)
          (fun _ _ _ _ => rfl)
          (by
            dsimp only [FastState.oldEp]
            rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
            exact hbo)
          ?_ rfl
        dsimp only [ValidEpochStage]
        rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
          ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2]
        have hfp_eq : ({ fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := fs.rebScanCursor + 16
            rebInsCount := ins' } : FastState).fpAt c U n_max θ fs.rebCandSalt b =
            fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
        refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun _ => ⟨?_, ?_, rm', ?_, ?_⟩⟩
        · right
          refine ⟨by omega, hcur_lt_b, ?_⟩
          rcases hcur_r with ⟨hc0, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
        · rw [hfp_eq]; exact hinj'
        · change ValidWhpSlice n_max ins' (Function.update fs.slices rIdx sl' rIdx) rm'
          rw [Function.update_self]; exact hv'
        · rw [hfp_eq]; exact hrr'
  · -- Exhausted `sMaxWhp`: `epochTickStage2` is a no-op (`fs1 = fs`), vacuous in `ValidEpochStage`
    rw [ite_eq_right hcs_lt]
    refine ⟨hc, hom, ?_, rfl⟩
    dsimp only [ValidEpochStage]
    rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
      ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2]
    exact ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun h => absurd h hcs_lt⟩

private theorem bufDelete_self_checkSlot_none {cTab bChar id rKey : ℕ} {tr : BufTrie}
    (hw : bufWalk bChar tr.trieChild rKey cTab 0 0 = some (tr.itemLeaf id)) :
    bufCheckSlot (bufDelete cTab bChar tr rKey) id = none := by
  dsimp only [bufDelete]
  rw [hw]
  dsimp only
  split_ifs with hcond
  · dsimp only [bufCheckSlot]
    split_ifs with hid hc2
    · rcases hcond with h1 | h2 <;> omega
    · rfl
    · rfl
  · dsimp only [bufCheckSlot]
    by_cases hid : id < tr.itemAlloc
    · simp [hid]
    · exact ite_eq_right hid

private theorem BufMapRel.untag_one {M tag b₀ loc₀ : ℕ} {bktCnt : ℕ → ℕ}
    {locSt rKeyOf : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hb₀ : b₀ < M) (hl₀ : loc₀ < bktCnt b₀) (hst₀ : locSt b₀ loc₀ = tag)
    (hinj : ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag →
      rKeyOf b loc = rKeyOf b₀ loc₀ → b = b₀ ∧ loc = loc₀)
    (hne : 1 ≠ tag) :
    BufMapRel M tag bktCnt
      (Function.update locSt b₀ (Function.update (locSt b₀) loc₀ 1)) rKeyOf
      (Function.update m (rKeyOf b₀ loc₀) none) := by
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  by_cases hrk : rk = rKeyOf b₀ loc₀
  · subst hrk
    simp only [Function.update_self, reduceCtorEq, false_iff]
    rintro ⟨hb, hloc, hst', heq⟩
    by_cases hbl : b = b₀ ∧ loc = loc₀
    · rcases hbl with ⟨rfl, rfl⟩
      rw [Function.update_self, Function.update_self] at hst'
      exact hne hst'
    · have hst_old : locSt b loc = tag := by
        by_cases hbb : b = b₀
        · subst hbb
          have hne_l : loc ≠ loc₀ := fun h => hbl ⟨rfl, h⟩
          rwa [Function.update_self, Function.update_of_ne hne_l] at hst'
        · rwa [Function.update_of_ne hbb] at hst'
      exact hbl (hinj b hb loc hloc hst_old heq)
  · rw [Function.update_of_ne hrk, hrel.2 rk b loc]
    refine ⟨fun ⟨hb, hloc, hst, heq⟩ => ⟨hb, hloc, ?_, heq⟩,
      fun ⟨hb, hloc, hst', heq⟩ => ⟨hb, hloc, ?_, heq⟩⟩
    · by_cases hbb : b = b₀
      · subst hbb
        have hne_l : loc ≠ loc₀ := fun h => hrk (h ▸ heq.symm)
        rw [Function.update_self, Function.update_of_ne hne_l]; exact hst
      · rwa [Function.update_of_ne hbb]
    · by_cases hbb : b = b₀
      · subst hbb
        rw [Function.update_self] at hst'
        by_cases hll : loc = loc₀
        · subst hll; rw [Function.update_self] at hst'; exact absurd hst' hne
        · rwa [Function.update_of_ne hll] at hst'
      · rwa [Function.update_of_ne hbb] at hst'

private def epochTickStage3Finish (s : FastState) : FastState :=
  if (s.buf s.oldEp).itemAlloc ≤ s.stageCursor then
    { s with rebStage := 4 }
  else s

private def epochTickStage3 (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : FastState :=
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  if fs.stageCursor < oldTr.itemAlloc then
    let nextCur := fs.stageCursor + 1
    let fs' :=
      match bufCheckSlot oldTr fs.stageCursor with
      | some (b, loc) =>
        let rKey := fs.rKeyAt c U n_max θ b loc
        let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) oldTr rKey
        { fs with
          buf := Function.update fs.buf oldEp tr'
          locState := Function.update fs.locState b (Function.update (fs.locState b) loc 1)
          stageCursor := nextCur }
      | none =>
        { fs with stageCursor := nextCur }
    if (fs'.buf oldEp).itemAlloc ≤ nextCur then
      { fs' with rebStage := 4 }
    else fs'
  else
    { fs with rebStage := 4 }

private theorem epochTickStage3Finish_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {s : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ s dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ s b)
    (hs3 : s.rebStage = 3)
    (hsc_le : s.stageCursor ≤ (s.buf s.oldEp).itemAlloc)
    (hnone_lt : ∀ id < s.stageCursor, bufCheckSlot (s.buf s.oldEp) id = none) :
    let fs1 := epochTickStage3Finish s
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = s.epochClock := by
  dsimp only [epochTickStage3Finish]
  by_cases hdone : (s.buf s.oldEp).itemAlloc ≤ s.stageCursor
  · rw [ite_eq_left hdone]
    have hbo := hc.bufOld_valid
    rw [ite_eq_left (by omega : s.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
    have hno_old : ∀ b < numBucketsWhp n_max, ∀ loc < s.bktCount b,
        s.locState b loc ≠ 2 + s.oldEp := by
      intro b hb loc hloc hst
      have hms : oldMap (s.rKeyAt c U n_max θ b loc) = some (b, loc) :=
        (hrel_o.2 _ b loc).mpr ⟨hb, hloc, hst, rfl⟩
      obtain ⟨id, hid, hchk⟩ := hv_o.exists_checkSlot_of_map_some hms
      have hn := hnone_lt id (hid.trans_le hdone)
      rw [hn] at hchk; cases hchk
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 4 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b hb loc hloc => by
        have hne := hno_old b hb loc hloc
        change inLiveTree 4 s.oldEp (s.rebDoneFlag b) (s.locState b loc) =
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc)
        simp [inLiveTree, hs3, hne])
      (by
        dsimp only [FastState.oldEp]
        simp only [show ¬((4 : ℕ) ≤ 3) by decide, ↓reduceIte]
        refine ⟨hno_old, hv_o.toClearable, ?_⟩
        exact hna_o.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hia_o) 1))
      ?_ rfl
    dsimp only [ValidEpochStage]
    simp
  · rw [ite_eq_right hdone]
    refine ⟨hc, hom, ?_, rfl⟩
    dsimp only [ValidEpochStage]
    rw [ite_eq_right (by omega : ¬(s.rebStage = 0)),
      ite_eq_right (by omega : ¬(s.rebStage = 1)),
      ite_eq_right (by omega : ¬(s.rebStage = 2)), ite_eq_left hs3]
    exact ⟨hsc_le, hnone_lt⟩

private theorem epochTickStage3_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs3 : fs.rebStage = 3)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage3 c U n_max θ fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
    ite_eq_right (by omega : ¬(fs.rebStage = 1)),
    ite_eq_right (by omega : ¬(fs.rebStage = 2)), ite_eq_left hs3] at hpre
  obtain ⟨hsc_le, hnone0⟩ := hpre
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
  set oldEp := fs.oldEp
  set oldTr := fs.buf oldEp
  dsimp only [epochTickStage3]
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    set nextCur := fs.stageCursor + 1
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some bloc =>
      rcases bloc with ⟨b₀, loc₀⟩
      dsimp only
      obtain ⟨_, k, hk_lt, hwk, hmk⟩ := hv_o.checkSlot_some hchk
      obtain ⟨hb₀, hl₀, hst₀, hrk_k⟩ := (hrel_o.2 k b₀ loc₀).mp hmk
      subst hrk_k
      set rKey := fs.rKeyAt c U n_max θ b₀ loc₀
      set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) oldTr rKey
      obtain ⟨hv_tr', hna_eq, hia_eq, _, hnone_pres⟩ := hv_o.delete_spec hk_lt
      have hself_none : bufCheckSlot tr' fs.stageCursor = none :=
        bufDelete_self_checkSlot_none hwk
      set fs' : FastState :=
        { fs with
          buf := Function.update fs.buf oldEp tr'
          locState := Function.update fs.locState b₀ (Function.update (fs.locState b₀) loc₀ 1)
          stageCursor := nextCur }
      have hinL_pres : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
          inLiveTree 3 oldEp (fs.rebDoneFlag b) (fs'.locState b loc) =
            inLiveTree 3 oldEp (fs.rebDoneFlag b) (fs.locState b loc) := by
        intro b _ loc _
        dsimp only [fs']
        by_cases hbl : b = b₀ ∧ loc = loc₀
        · rcases hbl with ⟨rfl, rfl⟩
          rw [Function.update_self, Function.update_self, hst₀]
          simp [inLiveTree]
        · by_cases hbb : b = b₀
          · subst hbb
            rw [Function.update_self, Function.update_of_ne (fun h => hbl ⟨rfl, h⟩)]
          · rw [Function.update_of_ne hbb]
      have hc' : CoreFastInv c U V n_max θ fs' dict :=
        { hth := hc.hth
          curEp_or := hc.curEp_or
          epochClock_lt := hc.epochClock_lt
          rebStage_le := hc.rebStage_le
          rebCollision_zero := hc.rebCollision_zero
          qv_global := hc.qv_global
          bktCount_le := hc.bktCount_le
          bktCount_ge_zero := hc.bktCount_ge_zero
          locState_active := fun b hb loc hloc => by
            dsimp only [fs']
            by_cases hbl : b = b₀ ∧ loc = loc₀
            · rcases hbl with ⟨rfl, rfl⟩; simp
            · by_cases hbb : b = b₀
              · subst hbb; rw [Function.update_self, Function.update_of_ne (fun h => hbl ⟨rfl, h⟩)]
                exact hc.locState_active b hb loc hloc
              · rw [Function.update_of_ne hbb]; exact hc.locState_active b hb loc hloc
          locState_inactive := fun b loc hnot => by
            dsimp only [fs']
            by_cases hbb : b = b₀
            · subst hbb
              rw [Function.update_self,
                Function.update_of_ne (fun h => hnot ⟨hb₀, by rw [h]; exact hl₀⟩)]
              exact hc.locState_inactive b loc hnot
            · rw [Function.update_of_ne hbb]; exact hc.locState_inactive b loc hnot
          active_item := hc.active_item
          quot_inj := hc.quot_inj
          dict_map := hc.dict_map
          poolFreeTop_le := hc.poolFreeTop_le
          backPtr_valid := hc.backPtr_valid
          freeStack_lt := hc.freeStack_lt
          backPtr_inj := hc.backPtr_inj
          freeStack_inj := hc.freeStack_inj
          back_free_disj := hc.back_free_disj
          pool_conservation := hc.pool_conservation
          roles_valid := hc.roles_valid
          bktSalt_lt := hc.bktSalt_lt
          live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
            have hst_eq : fs'.rebStage = 3 := hs3
            have hold_eq : fs'.oldEp = oldEp := rfl
            rw [hst_eq, hold_eq, hinL_pres b hb l₁ hl₁, ← hs3] at hin₁
            rw [hst_eq, hold_eq, hinL_pres b hb l₂ hl₂, ← hs3] at hin₂
            exact hc.live_fp_inj b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
          live_valid := fun b hb => by
            obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b hb
            refine ⟨lm, hvl, hrl.congr (fun _ _ => rfl) fun loc hloc => ?_⟩
            have hst_eq : fs'.rebStage = 3 := hs3
            have hold_eq : fs'.oldEp = oldEp := rfl
            rw [hst_eq, hold_eq, hinL_pres b hb loc hloc, ← hs3]
          rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h2₁ h2₂ hrkeq => by
            have h2_orig : ∀ b < numBucketsWhp n_max, ∀ l < fs.bktCount b,
                2 ≤ fs'.locState b l → 2 ≤ fs.locState b l := by
              intro b _ l _ h2
              dsimp only [fs'] at h2
              by_cases hbb : b = b₀
              · subst hbb; rw [Function.update_self] at h2
                by_cases hll : l = loc₀
                · subst hll; rw [Function.update_self] at h2; omega
                · rwa [Function.update_of_ne hll] at h2
              · rwa [Function.update_of_ne hbb] at h2
            exact hc.rKey_buf_inj b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂
              (h2_orig b₁ hb₁ l₁ hl₁ h2₁) (h2_orig b₂ hb₂ l₂ hl₂ h2₂) hrkeq
          bufCur_valid := by
            obtain ⟨hi_c, hn_c, cm, hvc, hrc⟩ := hc.bufCur_valid
            have hbuf_c : fs'.buf fs'.curEp = fs.buf fs.curEp :=
              Function.update_of_ne (curEp_ne_oldEp hc.curEp_or) _ _
            rw [hbuf_c]
            refine ⟨hi_c, hn_c, cm, hvc, hrc.congr (fun _ _ => rfl) (fun b _ loc _ => ?_)
              (fun _ _ _ _ => rfl)⟩
            dsimp only [fs']
            by_cases hbl : b = b₀ ∧ loc = loc₀
            · rcases hbl with ⟨rfl, rfl⟩
              rw [Function.update_self, Function.update_self, hst₀]
              have := curEp_ne_oldEp hc.curEp_or; omega
            · by_cases hbb : b = b₀
              · subst hbb; rw [Function.update_self, Function.update_of_ne (fun h => hbl ⟨rfl, h⟩)]
              · rw [Function.update_of_ne hbb]
          bufOld_valid := by
            have hst_eq : fs'.rebStage = 3 := hs3
            have hold_eq : fs'.oldEp = oldEp := rfl
            have hbuf_o : fs'.buf oldEp = tr' := by dsimp only [fs']; simp
            rw [hst_eq, hold_eq, ite_eq_left (by decide : (3 : ℕ) ≤ 3), hbuf_o]
            refine ⟨hia_eq ▸ hia_o, hna_eq.symm ▸ hia_eq.symm ▸ hna_o,
              Function.update oldMap rKey none, hv_tr', ?_⟩
            exact hrel_o.untag_one hb₀ hl₀ hst₀
              (fun b hb loc hloc h1 =>
                hc.rKey_buf_inj b hb loc hloc b₀ hb₀ loc₀ hl₀ (by omega) (by omega))
              (by omega) }
      have hom' : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b := by
        intro b hb
        rcases hom b hb with ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
        · exact Or.inl ⟨ha0, hlt5⟩
        · refine Or.inr ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO,
            hrO.congr (fun _ _ => rfl) fun loc hlt_c => ?_⟩
          have hst_eq : fs'.rebStage = 3 := hs3
          have hold_eq : fs'.oldEp = oldEp := rfl
          rw [hst_eq, hold_eq, hinL_pres b hb loc (hlt_c.trans hcur), ← hs3]
      have hbuf_o' : fs'.buf fs'.oldEp = tr' := by
        change Function.update fs.buf oldEp tr' oldEp = tr'
        exact Function.update_self _ _ _
      have hnone_next : ∀ id < nextCur, bufCheckSlot (fs'.buf fs'.oldEp) id = none := by
        intro id hid
        rw [hbuf_o']
        rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
        · exact hnone_pres id (hnone0 id hid')
        · exact hself_none
      exact epochTickStage3Finish_spec hc' hom' hs3
        (by rw [hbuf_o', hia_eq]; exact Nat.succ_le_of_lt hlt)
        hnone_next
    | none =>
      dsimp only
      set fs' : FastState := { fs with stageCursor := nextCur }
      obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq fs' hc hom rfl hc.epochClock_lt
        hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (by dsimp only [fs', FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
            exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
      exact epochTickStage3Finish_spec hc' hom' hs3 (Nat.succ_le_of_lt hlt)
        (fun id hid => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hnone0 id hid'
          · exact hchk)
  · rw [ite_eq_right hlt]
    have heq_s3 : ({ fs with rebStage := 4 } : FastState) = epochTickStage3Finish fs := by
      dsimp only [epochTickStage3Finish]; rw [ite_eq_left (Nat.not_lt.mp hlt)]
    change (let fs1 : FastState := { fs with rebStage := 4 }; _)
    rw [heq_s3]
    exact epochTickStage3Finish_spec hc hom hs3 hsc_le hnone0

private theorem ClearableBufTrie.clearSteps_pres :
    ∀ (k : ℕ) {tr : BufTrie}, ClearableBufTrie tr →
      ClearableBufTrie (bufClearSteps k tr) ∧ (bufClearSteps k tr).nodeAlloc ≤ max 1 tr.nodeAlloc
  | 0, tr, hc => ⟨hc, le_max_right 1 tr.nodeAlloc⟩
  | k + 1, tr, hc => by
    obtain ⟨hc1, hna1⟩ := hc.clearOne_step
    obtain ⟨hck, hnak⟩ := hc1.clearSteps_pres k
    refine ⟨hck, hnak.trans ?_⟩
    rw [hna1]
    have := hc.1
    omega

private def epochTickStage4 (fs : FastState) : FastState :=
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  let doneClear := decide (oldTr.nodeAlloc ≤ 8)
  let tr' := bufClearSteps 8 oldTr
  { fs with
    buf := Function.update fs.buf oldEp tr'
    rebStage := if doneClear then 5 else 4 }

private theorem epochTickStage4_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs4 : fs.rebStage = 4) :
    let fs1 := epochTickStage4 fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
  obtain ⟨hno_old, hclr, hna_ub⟩ := hbo
  set oldEp := fs.oldEp
  set oldTr := fs.buf oldEp
  dsimp only [epochTickStage4]
  by_cases hle8 : oldTr.nodeAlloc ≤ 8
  · obtain ⟨hv_empty, hna1, hia0⟩ := hclr.clearSteps_spec (cTabWhp c) (bCharWhp n_max) 8 hle8
    have hd_true : decide (oldTr.nodeAlloc ≤ 8) = true := decide_eq_true hle8
    rw [hd_true, ite_eq_left rfl]
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      le_rfl hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Function.update_of_ne (curEp_ne_oldEp hc.curEp_or) _ _)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => by simp [inLiveTree, hs4])
      (by
        simp only [show ¬((5 : ℕ) ≤ 3) by decide, show ¬(5 = 4) by decide, ↓reduceIte]
        change (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + oldEp) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max)
            (Function.update fs.buf oldEp (bufClearSteps 8 oldTr) oldEp) (fun _ => none) ∧
          (Function.update fs.buf oldEp (bufClearSteps 8 oldTr) oldEp).nodeAlloc = 1 ∧
          (Function.update fs.buf oldEp (bufClearSteps 8 oldTr) oldEp).itemAlloc = 0
        rw [Function.update_self]
        exact ⟨hno_old, hv_empty, hna1, hia0⟩)
      (by simp [ValidEpochStage]) rfl
  · obtain ⟨hclr', hna'⟩ := hclr.clearSteps_pres 8
    have h1_le : 1 ≤ oldTr.nodeAlloc := hclr.1
    have hd_false : decide (oldTr.nodeAlloc ≤ 8) = false := decide_eq_false hle8
    rw [hd_false, ite_eq_right Bool.false_ne_true]
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 4 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
      (Function.update_of_ne (curEp_ne_oldEp hc.curEp_or) _ _)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => by simp [inLiveTree, hs4])
      (by
        simp only [show ¬((4 : ℕ) ≤ 3) by decide, ↓reduceIte]
        change (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + oldEp) ∧
          ClearableBufTrie (Function.update fs.buf oldEp (bufClearSteps 8 oldTr) oldEp) ∧
          (Function.update fs.buf oldEp (bufClearSteps 8 oldTr) oldEp).nodeAlloc ≤
            1 + cTabWhp c * (2 * rIndepWhp c n_max)
        rw [Function.update_self]
        exact ⟨hno_old, hclr', hna'.trans ((max_eq_right h1_le).trans_le hna_ub)⟩)
      (by simp [ValidEpochStage]) rfl

private def epochTickStage (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : FastState :=
  if fs.rebStage = 0 then epochTickStage0 fs
  else if fs.rebStage = 1 then epochTickStage1 fs
  else if fs.rebStage = 2 then epochTickStage2 c U n_max θ fs
  else if fs.rebStage = 3 then epochTickStage3 c U n_max θ fs
  else if fs.rebStage = 4 then epochTickStage4 fs
  else fs

private def epochTickRollover (n_max : ℕ) (fs1 : FastState) : Option FastState :=
  let nextClk := fs1.epochClock + 1
  if qEpochWhp n_max ≤ nextClk then
    if fs1.rebStage = 5 then
      some { fs1 with
        curEp := 1 - fs1.curEp
        epochClock := 0
        rebStage := 0
        stageCursor := 0 }
    else none
  else
    some { fs1 with epochClock := nextClk }

private theorem epochTick_eq_stage_rollover (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) :
    epochTick c U n_max θ fs = epochTickRollover n_max (epochTickStage c U n_max θ fs) := by
  dsimp only [epochTick, epochTickStage]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0, ite_eq_left hs0]; rfl
  rw [ite_eq_right hs0, ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1, ite_eq_left hs1]
    dsimp only [epochTickStage1, epochTickStage1Finish]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt, ite_eq_left hlt]; rfl
    · rw [ite_eq_right hlt, ite_eq_right hlt]; rfl
  rw [ite_eq_right hs1, ite_eq_right hs1]
  by_cases hs2 : fs.rebStage = 2
  · rw [ite_eq_left hs2, ite_eq_left hs2]; rfl
  rw [ite_eq_right hs2, ite_eq_right hs2]
  by_cases hs3 : fs.rebStage = 3
  · rw [ite_eq_left hs3, ite_eq_left hs3]; rfl
  rw [ite_eq_right hs3, ite_eq_right hs3]
  by_cases hs4 : fs.rebStage = 4
  · rw [ite_eq_left hs4, ite_eq_left hs4]; rfl
  rw [ite_eq_right hs4, ite_eq_right hs4]; rfl

/-- `epochTick` restores full `ValidFastState` from `CoreFastInv` + `OvermarsBucketInv` +
`ValidEpochStagePreTick` whenever `epochTick` returns `some fs'`. -/
theorem epochTick_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (htick : epochTick c U n_max θ fs = some fs') :
    ValidFastState c U V n_max θ fs' dict := by
  rw [epochTick_eq_stage_rollover] at htick
  set fs1 := epochTickStage c U n_max θ fs
  have hst1 :
      CoreFastInv c U V n_max θ fs1 dict ∧
      (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
      ValidEpochStage c U n_max θ fs1 ∧
      fs1.epochClock = fs.epochClock := by
    dsimp only [fs1, epochTickStage]
    by_cases hs0 : fs.rebStage = 0
    · rw [ite_eq_left hs0]; exact epochTickStage0_spec hc hom hs0 hpre
    rw [ite_eq_right hs0]
    by_cases hs1 : fs.rebStage = 1
    · rw [ite_eq_left hs1]; exact epochTickStage1_spec hc hom hs1 hpre
    rw [ite_eq_right hs1]
    by_cases hs2 : fs.rebStage = 2
    · rw [ite_eq_left hs2]; exact epochTickStage2_spec hc hom hs2 hpre
    rw [ite_eq_right hs2]
    by_cases hs3 : fs.rebStage = 3
    · rw [ite_eq_left hs3]; exact epochTickStage3_spec hc hom hs3 hpre
    rw [ite_eq_right hs3]
    by_cases hs4 : fs.rebStage = 4
    · rw [ite_eq_left hs4]; exact epochTickStage4_spec hc hom hs4
    rw [ite_eq_right hs4]
    have hs5 : fs.rebStage = 5 := by have := hc.rebStage_le; omega
    exact ⟨hc, hom, by simp [ValidEpochStage, hs5], rfl⟩
  obtain ⟨hc1, hom1, hstg1, _⟩ := hst1
  dsimp only [epochTickRollover] at htick
  by_cases hroll : qEpochWhp n_max ≤ fs1.epochClock + 1
  · rw [ite_eq_left hroll] at htick
    by_cases hs5 : fs1.rebStage = 5
    · rw [ite_eq_left hs5] at htick
      injection htick with hfs'
      rw [← hfs']
      have hq_pos : 0 < qEpochWhp n_max := by
        unfold qEpochWhp; have := scaleWhp_pos n_max; positivity
      have hbo1 := hc1.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs1.rebStage ≤ 3)),
        ite_eq_right (by omega : ¬(fs1.rebStage = 4))] at hbo1
      obtain ⟨hno_old1, hv_old1, hna1, hia0⟩ := hbo1
      have hcur'_or : (1 - fs1.curEp) = 0 ∨ (1 - fs1.curEp) = 1 :=
        oldEp_or' hc1.curEp_or
      have hold'_eq : ({ fs1 with
          curEp := 1 - fs1.curEp
          epochClock := 0
          rebStage := 0
          stageCursor := 0 } : FastState).oldEp = fs1.curEp := by
        dsimp only [FastState.oldEp]
        rcases hc1.curEp_or with h | h <;> simp [h]
      have hinL_roll : ∀ (df : ℕ → ℕ) b st,
          inLiveTree 0 fs1.curEp (df b) st = inLiveTree 5 fs1.oldEp (df b) st := by
        intro _ _ _; simp [inLiveTree]
      refine CoreFastInv.toValidFastState ?_ ?_ ?_
      · exact
          { hth := hc1.hth
            curEp_or := hcur'_or
            epochClock_lt := hq_pos
            rebStage_le := Nat.zero_le 5
            rebCollision_zero := hc1.rebCollision_zero
            qv_global := hc1.qv_global
            bktCount_le := hc1.bktCount_le
            bktCount_ge_zero := hc1.bktCount_ge_zero
            locState_active := hc1.locState_active
            locState_inactive := hc1.locState_inactive
            active_item := hc1.active_item
            quot_inj := hc1.quot_inj
            dict_map := hc1.dict_map
            poolFreeTop_le := hc1.poolFreeTop_le
            backPtr_valid := hc1.backPtr_valid
            freeStack_lt := hc1.freeStack_lt
            backPtr_inj := hc1.backPtr_inj
            freeStack_inj := hc1.freeStack_inj
            back_free_disj := hc1.back_free_disj
            pool_conservation := hc1.pool_conservation
            roles_valid := hc1.roles_valid
            bktSalt_lt := hc1.bktSalt_lt
            live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              rw [hold'_eq, hinL_roll, ← hs5] at hin₁ hin₂
              exact hc1.live_fp_inj b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b hb => by
              obtain ⟨lm, hvl, hrl⟩ := hc1.live_valid b hb
              refine ⟨lm, hvl, hrl.congr (fun _ _ => rfl) fun loc _ => ?_⟩
              rw [hold'_eq, hinL_roll, hs5]
            rKey_buf_inj := hc1.rKey_buf_inj
            bufCur_valid := by
              change (fs1.buf fs1.oldEp).itemAlloc ≤ 2 * rIndepWhp c n_max ∧
                (fs1.buf fs1.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs1.buf fs1.oldEp).itemAlloc ∧
                ∃ curMap,
                  ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf fs1.oldEp) curMap ∧
                  BufMapRel (numBucketsWhp n_max) (2 + fs1.oldEp) fs1.bktCount fs1.locState
                    (fs1.rKeyAt c U n_max θ) curMap
              rw [hna1, hia0]
              exact ⟨Nat.zero_le _, by omega, fun _ => none, hv_old1,
                BufMapRel.empty_of_not _ _ _ _ _ hno_old1⟩
            bufOld_valid := by
              rw [hold'_eq, ite_eq_left (Nat.zero_le 3)]
              exact hc1.bufCur_valid }
      · intro b hb
        rcases hom1 b hb with ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
        · exact Or.inl ⟨ha0, hlt5⟩
        · refine Or.inr ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO,
            hrO.congr (fun _ _ => rfl) fun loc _ => ?_⟩
          rw [hold'_eq, hinL_roll, hs5]
      · dsimp only [ValidEpochStage]
        simp only [↓reduceIte]
        exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · rw [ite_eq_right hs5] at htick; cases htick
  · rw [ite_eq_right hroll] at htick
    injection htick with hfs'
    rw [← hfs']
    exact CoreFastInv.toValidFastState
      { hc1 with epochClock_lt := Nat.lt_of_not_le hroll } hom1 hstg1

/-! ## Section 3: `fastStepPure_spec`, `whpStepPure_spec`, `whpRunFrom_spec`, `whpRunPure_spec` -/

/-- Whenever `fastStepPure` returns `some (fs', res)`, `fs'` satisfies `ValidFastState` for
`(Dynamic.step dict op).1` and `res = opResultOpt op (Dynamic.step dict op).2`. -/
theorem ValidFastState.fastStepPure_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {res : Option ℕ}
    (hv : ValidFastState c U V n_max θ fs dict)
    {op : Dynamic.Op U} (hvalid : Dynamic.valid V n_max dict op)
    (hstep : fastStepPure c U n_max θ fs op = some (fs', res)) :
    ValidFastState c U V n_max θ fs' (Dynamic.step dict op).1 ∧
    res = opResultOpt op (Dynamic.step dict op).2 := by
  cases op with
  | query u =>
    dsimp only [fastStepPure] at hstep
    cases ht : epochTick c U n_max θ fs with
    | none => rw [ht] at hstep; cases hstep
    | some fs1 =>
      rw [ht] at hstep; injection hstep with hp; injection hp with hfs1 hres
      rw [← hfs1, ← hres]
      exact ⟨epochTick_spec hv.toCore hv.overmars_valid hv.stage_valid.toPreTick ht,
        hv.fastQuery_spec u⟩
  | delete u =>
    dsimp only [fastStepPure] at hstep
    obtain ⟨hc1, hom1, hpre1, _⟩ := hv.fastDelete_spec u
    cases ht : epochTick c U n_max θ (fastDelete c U n_max θ fs u) with
    | none => rw [ht] at hstep; cases hstep
    | some fs2 =>
      rw [ht] at hstep; injection hstep with hp; injection hp with hfs2 hres
      rw [← hfs2, ← hres]
      exact ⟨epochTick_spec hc1 hom1 hpre1 ht, rfl⟩
  | insert u v =>
    dsimp only [fastStepPure] at hstep
    cases hi : fastInsert c U n_max θ fs u v with
    | none => rw [hi] at hstep; cases hstep
    | some fs1 =>
      rw [hi] at hstep
      dsimp only at hstep
      obtain ⟨hc1, hom1, hst1, _⟩ := hv.fastInsert_spec hnU hvalid hi
      cases ht : epochTick c U n_max θ fs1 with
      | none => rw [ht] at hstep; cases hstep
      | some fs2 =>
        rw [ht] at hstep; injection hstep with hp; injection hp with hfs2 hres
        rw [← hfs2, ← hres]
        exact ⟨epochTick_spec hc1 hom1 hst1.toPreTick ht, rfl⟩

/-- Exact single-step `Dynamic.step` refinement of `whpStepPure` for **every** static seed `θ`
across `.small`, `.fast` (both hit and fallback), and `.fallback` (including `trySelfHeal`). -/
theorem whpStepPure_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    (θ : SeedWhp c U n_max) {st : WhpDictState} {dict : State U}
    (hv : ValidWhpState c U V n_max θ st dict)
    {op : Dynamic.Op U} (hvalid : Dynamic.valid V n_max dict op) :
    let (st', res) := whpStepPure c U n_max θ st op
    ValidWhpState c U V n_max θ st' (Dynamic.step dict op).1 ∧
    res = opResultOpt op (Dynamic.step dict op).2 := by
  cases st with
  | small sm =>
    obtain ⟨hlt, hsm⟩ := hv
    cases op with
    | query u => exact ⟨⟨hlt, hsm⟩, smallQuery_spec hsm u⟩
    | delete u => exact ⟨⟨hlt, smallDelete_spec hsm u⟩, rfl⟩
    | insert u v => exact ⟨⟨hlt, smallInsert_spec hsm hvalid⟩, rfl⟩
  | fast fs =>
    dsimp only [whpStepPure]
    cases hf : fastStepPure c U n_max θ fs op with
    | some p =>
      rcases p with ⟨fs', res⟩
      exact hv.fastStepPure_spec hnU hvalid hf
    | none =>
      dsimp only
      obtain ⟨hcsr0, hqv0⟩ := hv.fastToCsr_spec
      obtain ⟨hcsr1, hres1, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hvalid
      exact ⟨(trySelfHeal_spec hv.hth hcsr1 hqv1).1, hres1⟩
  | fallback csr0 =>
    obtain ⟨hth, hcsr0, hqv0⟩ := hv
    dsimp only [whpStepPure]
    obtain ⟨hcsr1, hres1, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hvalid
    exact ⟨(trySelfHeal_spec hth hcsr1 hqv1).1, hres1⟩

/-- Multi-step sequence refinement from any `ValidWhpState`. -/
theorem whpRunFrom_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    (θ : SeedWhp c U n_max) {st : WhpDictState} {dict : State U}
    (hv : ValidWhpState c U V n_max θ st dict)
    {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V n_max).ValidHistory dict ops) :
    ValidWhpState c U V n_max θ (whpRunFrom c U n_max θ st ops)
      ((Dynamic.spec U V n_max).run dict ops).1 := by
  induction ops generalizing st dict with
  | nil => exact hv
  | cons op rest ih =>
    obtain ⟨hval, hvh_rest⟩ := hvh
    exact ih (whpStepPure_spec hnU θ hv hval).1 hvh_rest

/-- Multi-step sequence refinement starting from `whpInitPure c n_max` (`Dictionary.empty U`). -/
theorem whpRunPure_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    (θ : SeedWhp c U n_max) {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ValidWhpState c U V n_max θ (whpRunPure c U n_max θ ops)
      ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 :=
  whpRunFrom_spec hnU θ (whpInitPure_spec c U V n_max θ) hvh

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
