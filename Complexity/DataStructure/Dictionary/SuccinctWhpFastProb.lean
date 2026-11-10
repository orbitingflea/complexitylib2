/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.SuccinctWhpModelTick
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-Operation Fast-Path Hit Probability for the WHP Succinct Dynamic Dictionary

This module connects the trailing-window hash-seed event `GoodSeedOnWindow` (proved to hold with
probability at least `1 - (max n_max 1)⁻¹ ^ c` in `SuccinctWhpProb`) to the deterministic pure
transition machine `whpRunPure` / `whpStepPure` (`SuccinctWhpModelTick`):

1. **Epoch rebuild potential (`stageWorkRemaining`)**: tracks remaining background ticks across
   Stages `0 .. 5` of `epochTick`. Under `GoodSeedOnWindow`, every dirty bucket admits a
   collision-free salt `< sMaxWhp c n_max`, bounding total rebuild ticks per epoch by
   `stageWorkMax c n_max < qEpochWhp n_max` so `epochTick` never aborts at rollover.
2. **Clean-epoch invariant (`CleanWindowFast`)**: bounds `(fs.buf fs.curEp).itemAlloc` by the
   number of colliding window insertions already encountered (`< 2 * rIndepWhp c n_max`), ensuring
   none of the capacity, backyard-pool, Stage-1 `rKey`, buffer-cap, or rollover guards in
   `fastStepPure` ever fires inside a clean epoch.
3. **Self-healing / rollover burn-in (`HasBurnInBudget`)**: within at most `qEpochWhp n_max`
   operations of entering the trailing window `windowSuffix` (`length = 2 * qEpochWhp n_max + 2`),
   either `trySelfHeal` or an epoch rollover deterministically places `whpRunPure` into
   `CleanWindowFast`, where it remains through the target operation `op`.
4. **Master per-operation fast-path probability theorem (`toOuterMeasure_isFastStepHit_false_le`)**:
   for every `c, U, V, n_max` with `n_max ≤ U` and every admissible oblivious sequence
   `ops_prev ++ [op]`, the probability over `θ ~ seedLawWhp c U n_max` that step `op` fails to take
   the `O_c(1)` fast path (`.small` below `whpThreshold c`, or `.fast` with `fastStepPure = some _`
   at or above `whpThreshold c`) is at most `(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.stageWorkRemaining`, `stageWorkMax`: monotone
  epoch-rebuild remaining-work potential across Stages `0 .. 5`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.IsFastStepHit`: boolean indicator that `whpStepPure`
  takes the `O_c(1)` worst-case branch (`.small` or `.fast` hit).

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.isFastStepHit_of_goodSeedOnWindow`: deterministic
  fast-path hit guarantee whenever `GoodSeedOnWindow c U n_max (ops_prev ++ [op]) θ` holds.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.toOuterMeasure_isFastStepHit_false_le`:
  `(seedLawWhp c U n_max).toOuterMeasure {θ | IsFastStepHit ... = false} ≤ (max n_max 1)⁻¹ ^ c`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Bucket cardinality bijection, collision-free scan, and rebuild work potential -/

/-- In any `CoreFastInv` state, `fs.bktCount b` equals the exact number of keys in
`Dictionary.dom dict` hashing to Feistel bucket `b`. -/
theorem CoreFastInv.bktCount_eq_card_filter {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.bktCount b =
      #((Dictionary.dom dict).filter
        fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b) := by
  classical
  let S := (Dictionary.dom dict).filter
    fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b
  let toKey : (loc : Fin (fs.bktCount b)) → Fin U :=
    fun loc => ⟨fs.keyValAt c U n_max θ.1 b loc.val, (hc.active_item b hb loc.val loc.isLt).1⟩
  have hmem : ∀ loc : Fin (fs.bktCount b), toKey loc ∈ S := by
    intro loc
    obtain ⟨_, hfb, hq_eq, _⟩ := hc.active_item b hb loc.val loc.isLt
    rw [mem_filter, Dictionary.mem_dom_iff]
    refine ⟨⟨fs.valArr (fs.physSlot n_max b loc.val), ?_⟩, hfb⟩
    exact ((hc.dict_map (toKey loc)).2 _).mpr
      ⟨loc.val, hfb.symm ▸ loc.isLt, hfb.symm ▸ hq_eq.symm, hfb.symm ▸ rfl⟩
  have hinj : Function.Injective toKey := by
    intro l₁ l₂ heq
    have hkv : fs.keyValAt c U n_max θ.1 b l₁.val = fs.keyValAt c U n_max θ.1 b l₂.val :=
      congrArg Fin.val heq
    have hq₁ := (hc.active_item b hb l₁.val l₁.isLt).2.2.1
    have hq₂ := (hc.active_item b hb l₂.val l₂.isLt).2.2.1
    exact Fin.ext (hc.quot_inj b hb l₁.val l₁.isLt l₂.val l₂.isLt (hq₁.symm.trans (hkv ▸ hq₂)))
  have hsurj : ∀ u ∈ S, ∃ loc : Fin (fs.bktCount b), toKey loc = u := by
    intro u hu
    rw [mem_filter, Dictionary.mem_dom_iff] at hu
    obtain ⟨⟨v, hv⟩, hfb⟩ := hu
    obtain ⟨loc, hloc, hq_loc, _⟩ := ((hc.dict_map u).2 v).mp hv
    rw [hfb] at hloc hq_loc
    refine ⟨⟨loc, hloc⟩, Fin.ext ?_⟩
    dsimp only [toKey, FastState.keyValAt]
    rw [hq_loc, ← hfb]
    exact feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  symm
  refine (Finset.card_bij (fun (loc : Fin (fs.bktCount b)) _ => toKey loc)
    (fun loc _ => hmem loc) (fun _ _ _ _ h => hinj h)
    (fun u hu => let ⟨loc, hl⟩ := hsurj u hu; ⟨loc, mem_univ loc, hl⟩)).symm.trans ?_
  simp

/-- When `fs.fpAt c U n_max θ fs.rebCandSalt b` is injective on all active Stage-2 coordinates of
bucket `b`, `rebScanSteps` never sets `rebCollision` to non-zero. -/
theorem rebScanSteps_rebCollision_eq_zero_of_inj {c U n_max b : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (rem : ℕ) (fs : FastState)
    (hcoll0 : fs.rebCollision = 0)
    (hcnt_le : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12)
    (hins_ub : fs.rebInsCount + rem ≤ 8 * (scaleWhp n_max) ^ 12)
    (hinj_all : ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
      (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
      (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
      fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
      l₁ = l₂)
    (hreb0 : ∃ rebMap,
      ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rebMap ∧
      SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) fs.rebScanCursor) rebMap) :
    (rebScanSteps c U n_max θ b rem fs).rebCollision = 0 := by
  induction rem generalizing fs with
  | zero => exact hcoll0
  | succ rem ih =>
    obtain ⟨rm0, hvr0, hrr0⟩ := hreb0
    dsimp only [rebScanSteps]
    rw [ite_eq_right (by omega : ¬(fs.rebCollision ≠ 0))]
    set cur := fs.rebScanCursor
    set rIdx := fs.rebSliceIdx b
    by_cases hact : cur < fs.bktCount b ∧ (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)
    · rw [ite_eq_left hact]
      set fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
      have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
        dsimp only [fp, FastState.fpAt]
        split_ifs with hs hu
        · exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ ⟨_, hu⟩
        · exact Nat.two_pow_pos _
        · exact Nat.two_pow_pos _
      cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp with
      | some prev_loc =>
        exfalso
        rw [hvr0.lookup_eq hth (by omega) hfp_lt] at hlk
        obtain ⟨hprev_min, hp_prev, hfp_prev⟩ := (hrr0.2 fp prev_loc).mp hlk
        have hprev_lt_cur : prev_loc < cur := hprev_min.trans_le (Nat.min_le_right _ _)
        have hprev_lt_cnt : prev_loc < fs.bktCount b := hprev_min.trans_le (Nat.min_le_left _ _)
        have heq := hinj_all prev_loc hprev_lt_cnt cur hact.1 hp_prev hact.2 hfp_prev
        omega
      | none =>
        dsimp only
        have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
          have : 2 ^ valLaneBitsWhp n_max = 256 * (scaleWhp n_max) ^ 12 := by
            unfold valLaneBitsWhp scaleWhp slabScale ellWhp
            rw [Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm _ 12]; ring
          omega
        have hins := hvr0.insert_spec hth (by omega) hfp_lt hcur_val
        set sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp cur
        let fs1 : FastState :=
          { fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := cur + 1
            rebInsCount := fs.rebInsCount + 1 }
        have hfp1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b =
            fs.fpAt c U n_max θ fs.rebCandSalt b := rfl
        refine ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega) hinj_all
          ⟨Function.update rm0 fp (some cur), ?_, ?_⟩
        · change ValidWhpSlice n_max (fs.rebInsCount + 1)
            (Function.update fs.slices rIdx sl' rIdx) _
          rw [Function.update_self]; exact hins.2
        · rw [hfp1]
          have hmin_eq : min (fs.bktCount b) (cur + 1) = cur + 1 :=
            Nat.min_eq_right (Nat.succ_le_of_lt hact.1)
          have hmin0 : min (fs.bktCount b) cur = cur :=
            Nat.min_eq_right hact.1.le
          rw [hmin0] at hrr0
          change SliceMapRel _ _ (min (fs.bktCount b) (cur + 1)) _
          rw [hmin_eq]
          exact SliceMapRel.step_true hrr0 hact.2 fun loc hlt hp =>
            fun heq => Nat.ne_of_lt hlt (hinj_all loc (hlt.trans hact.1) cur hact.1 hp hact.2 heq)
    · rw [ite_eq_right hact]
      let fs1 : FastState := { fs with rebScanCursor := cur + 1 }
      refine ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega) hinj_all ⟨rm0, hvr0, ?_⟩
      change SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) (cur + 1)) rm0
      by_cases hlt_cnt : cur < fs.bktCount b
      · have hmin0 : min (fs.bktCount b) cur = cur := Nat.min_eq_right hlt_cnt.le
        have hmin1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
          Nat.min_eq_right (Nat.succ_le_of_lt hlt_cnt)
        rw [hmin0] at hrr0; rw [hmin1]
        exact SliceMapRel.step_false hrr0 fun hp => hact ⟨hlt_cnt, hp⟩
      · have hmin0 : min (fs.bktCount b) cur = fs.bktCount b :=
          Nat.min_eq_left (Nat.le_of_not_lt hlt_cnt)
        have hmin1 : min (fs.bktCount b) (cur + 1) = fs.bktCount b :=
          Nat.min_eq_left (by omega)
        rwa [hmin1, ← hmin0]

/-- `bufClearSteps k` on a `ClearableBufTrie` sets `nodeAlloc = max 1 (tr.nodeAlloc - k)`. -/
theorem ClearableBufTrie.clearSteps_nodeAlloc_eq :
    ∀ (k : ℕ) {tr : BufTrie}, ClearableBufTrie tr →
      (bufClearSteps k tr).nodeAlloc = max 1 (tr.nodeAlloc - k)
  | 0, tr, hc => by
    have := hc.1
    dsimp only [bufClearSteps]
    omega
  | k + 1, tr, hc => by
    obtain ⟨hc1, hna1⟩ := hc.clearOne_step
    dsimp only [bufClearSteps]
    rw [hc1.clearSteps_nodeAlloc_eq k, hna1]
    have := hc.1
    omega

/-- Maximum Stage-4 remaining work `1 + cTabWhp c * (2 * rIndepWhp c n_max)`. -/
@[expose] def stage4Max (c n_max : ℕ) : ℕ :=
  1 + cTabWhp c * (2 * rIndepWhp c n_max)

/-- Maximum Stage-3 remaining work. -/
@[expose] def stage3Max (c n_max : ℕ) : ℕ :=
  (2 * rIndepWhp c n_max + 2) + stage4Max c n_max

/-- Per-dirty-bucket Stage-2 work budget `sMaxWhp c n_max * (3 * L ^ 12 + 1)`. -/
@[expose] def bktWorkUnit (c n_max : ℕ) : ℕ :=
  sMaxWhp c n_max * (3 * (scaleWhp n_max) ^ 12 + 1)

/-- Maximum Stage-2 remaining work across `≤ 2 * rIndepWhp c n_max` dirty buckets. -/
@[expose] def stage2Max (c n_max : ℕ) : ℕ :=
  (2 * rIndepWhp c n_max) * bktWorkUnit c n_max + 1 + stage3Max c n_max

/-- Maximum Stage-1 remaining work. -/
@[expose] def stage1Max (c n_max : ℕ) : ℕ :=
  (2 * rIndepWhp c n_max + 2) + stage2Max c n_max

/-- Maximum Stage-0..4 remaining background rebuild work per epoch. -/
@[expose] def stageWorkMax (c n_max : ℕ) : ℕ :=
  (2 * rIndepWhp c n_max + 2) + stage1Max c n_max

/-- Monotone remaining-work potential for `epochTick` across Stages `0 .. 5`. -/
@[expose] def stageWorkRemaining (c n_max : ℕ) (fs : FastState) : ℕ :=
  let r2 := 2 * rIndepWhp c n_max
  let L12_3 := 3 * (scaleWhp n_max) ^ 12
  if fs.rebStage = 0 then
    (r2 + 1 - min r2 fs.stageCursor) + stage1Max c n_max
  else if fs.rebStage = 1 then
    (r2 + 1 - min r2 fs.stageCursor) + stage2Max c n_max
  else if fs.rebStage = 2 then
    (fs.dirtyCount - 1 - fs.dirtyIdx) * bktWorkUnit c n_max +
    (sMaxWhp c n_max - 1 - fs.rebCandSalt) * (L12_3 + 1) +
    (L12_3 - min L12_3 fs.rebScanCursor) + 1 + stage3Max c n_max
  else if fs.rebStage = 3 then
    (r2 + 1 - min r2 fs.stageCursor) + stage4Max c n_max
  else if fs.rebStage = 4 then
    (fs.buf fs.oldEp).nodeAlloc
  else 0

/-- `stageWorkMax c n_max + 1 ≤ qEpochWhp n_max` whenever `whpThreshold c ≤ n_max`. -/
theorem stageWorkMax_add_one_le_qEpoch {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    stageWorkMax c n_max + 1 ≤ qEpochWhp n_max := by
  set L := scaleWhp n_max
  have hL := cEff_add_four_le_scaleWhp hth
  have hL_big : 6553600 ≤ L := hL.1
  have hL_c : cEff c + 4 ≤ L := hL.2
  have hr_le : rIndepWhp c n_max ≤ L ^ 2 := by
    unfold rIndepWhp; nlinarith
  have hs_le : sMaxWhp c n_max ≤ L ^ 2 := by
    unfold sMaxWhp; nlinarith
  have hcTab_le : cTabWhp c ≤ 9 * L := by
    rw [cTabWhp_eq]; linarith
  have hL4 : stage4Max c n_max ≤ 19 * L ^ 3 := by
    unfold stage4Max
    have hmul : cTabWhp c * (2 * rIndepWhp c n_max) ≤ (9 * L) * (2 * L ^ 2) :=
      Nat.mul_le_mul hcTab_le (Nat.mul_le_mul_left 2 hr_le)
    have h1 : 1 ≤ L ^ 3 := Nat.one_le_pow 3 L (by omega)
    nlinarith
  have hbu : bktWorkUnit c n_max ≤ 4 * L ^ 14 := by
    unfold bktWorkUnit
    have h1 : 1 ≤ L ^ 12 := Nat.one_le_pow 12 L (by omega)
    have hm : sMaxWhp c n_max * (3 * L ^ 12 + 1) ≤ L ^ 2 * (4 * L ^ 12) :=
      Nat.mul_le_mul hs_le (by omega)
    nlinarith
  have h2r_bu : (2 * rIndepWhp c n_max) * bktWorkUnit c n_max ≤ 8 * L ^ 16 := by
    have hm : (2 * rIndepWhp c n_max) * bktWorkUnit c n_max ≤ (2 * L ^ 2) * (4 * L ^ 14) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr_le) hbu
    nlinarith
  have h3_16 : L ^ 3 ≤ L ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2_16 : L ^ 2 ≤ L ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1_16 : 1 ≤ L ^ 16 := Nat.one_le_pow 16 L (by omega)
  have htot_16 : stageWorkMax c n_max + 1 ≤ 40 * L ^ 16 := by
    unfold stageWorkMax stage1Max stage2Max stage3Max
    nlinarith
  calc stageWorkMax c n_max + 1
      ≤ 40 * L ^ 16 := htot_16
    _ ≤ L ^ 2 * L ^ 16 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = qEpochWhp n_max := by unfold qEpochWhp; ring

/-- Every valid `FastState` has `stageWorkRemaining c n_max fs ≤ stageWorkMax c n_max`. -/
theorem stageWorkRemaining_le_max {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hstg : ValidEpochStage c U n_max θ fs) :
    stageWorkRemaining c n_max fs ≤ stageWorkMax c n_max := by
  dsimp only [stageWorkRemaining]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0]; unfold stageWorkMax; omega
  rw [ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1]; unfold stageWorkMax stage1Max; omega
  rw [ite_eq_right hs1]
  by_cases hs2 : fs.rebStage = 2
  · rw [ite_eq_left hs2]
    dsimp only [ValidEpochStage] at hstg
    rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2] at hstg
    obtain ⟨hdc_le, hdi_lt, _⟩ := hstg
    have hs_pos : 0 < sMaxWhp c n_max := sMaxWhp_pos c n_max
    have hcur_le :
        (sMaxWhp c n_max - 1 - fs.rebCandSalt) * (3 * (scaleWhp n_max) ^ 12 + 1) +
        (3 * (scaleWhp n_max) ^ 12 - min (3 * (scaleWhp n_max) ^ 12) fs.rebScanCursor) + 1 ≤
        bktWorkUnit c n_max := by
      have h1 : sMaxWhp c n_max - 1 - fs.rebCandSalt ≤ sMaxWhp c n_max - 1 := Nat.sub_le _ _
      have hmul : (sMaxWhp c n_max - 1 - fs.rebCandSalt) * (3 * (scaleWhp n_max) ^ 12 + 1) ≤
          (sMaxWhp c n_max - 1) * (3 * (scaleWhp n_max) ^ 12 + 1) :=
        Nat.mul_le_mul_right _ h1
      have h2 : 3 * (scaleWhp n_max) ^ 12 -
          min (3 * (scaleWhp n_max) ^ 12) fs.rebScanCursor ≤ 3 * (scaleWhp n_max) ^ 12 :=
        Nat.sub_le _ _
      have hb_eq : bktWorkUnit c n_max =
          (sMaxWhp c n_max - 1) * (3 * (scaleWhp n_max) ^ 12 + 1) +
            (3 * (scaleWhp n_max) ^ 12 + 1) := by
        unfold bktWorkUnit
        cases hsm : sMaxWhp c n_max with
        | zero => omega
        | succ k => simp [Nat.succ_mul]
      omega
    have hrem_le : fs.dirtyCount - 1 - fs.dirtyIdx + 1 ≤ 2 * rIndepWhp c n_max := by omega
    have htot_bkt :
        (fs.dirtyCount - 1 - fs.dirtyIdx) * bktWorkUnit c n_max + bktWorkUnit c n_max ≤
        (2 * rIndepWhp c n_max) * bktWorkUnit c n_max := by
      calc (fs.dirtyCount - 1 - fs.dirtyIdx) * bktWorkUnit c n_max + bktWorkUnit c n_max
          = (fs.dirtyCount - 1 - fs.dirtyIdx + 1) * bktWorkUnit c n_max := by ring
        _ ≤ (2 * rIndepWhp c n_max) * bktWorkUnit c n_max :=
            Nat.mul_le_mul_right _ hrem_le
    unfold stageWorkMax stage1Max stage2Max
    omega
  rw [ite_eq_right hs2]
  by_cases hs3 : fs.rebStage = 3
  · rw [ite_eq_left hs3]; unfold stageWorkMax stage1Max stage2Max stage3Max; omega
  rw [ite_eq_right hs3]
  by_cases hs4 : fs.rebStage = 4
  · rw [ite_eq_left hs4]
    have hbo := hc.bufOld_valid
    rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
    have hna : (fs.buf fs.oldEp).nodeAlloc ≤ stage4Max c n_max := hbo.2.2
    unfold stageWorkMax stage1Max stage2Max stage3Max
    omega
  rw [ite_eq_right hs4]
  exact Nat.zero_le _

/-- Helper: every active coordinate `(b, loc)` (`b < M`, `loc < fs.bktCount b`) in `CoreFastInv`
yields a key `u : Fin U` in `Dictionary.dom dict` with bucket `b` and quotient
`fs.quotArr (fs.physSlot n_max b loc)`. -/
private theorem CoreFastInv.mem_dom_of_loc {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    {b loc : ℕ} (hb : b < numBucketsWhp n_max) (hloc : loc < fs.bktCount b) :
    let u : Fin U := ⟨fs.keyValAt c U n_max θ.1 b loc, (hc.active_item b hb loc hloc).1⟩
    u ∈ Dictionary.dom dict ∧
    feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b := by
  obtain ⟨hkv_lt, hfb, hq_eq, _⟩ := hc.active_item b hb loc hloc
  let u : Fin U := ⟨fs.keyValAt c U n_max θ.1 b loc, hkv_lt⟩
  refine ⟨Dictionary.mem_dom_iff.mpr ⟨fs.valArr (fs.physSlot n_max b loc), ?_⟩, hfb⟩
  exact ((hc.dict_map u).2 _).mpr ⟨loc, hfb.symm ▸ hloc, hfb.symm ▸ hq_eq.symm, hfb.symm ▸ rfl⟩

private def tickStage0 (fs : FastState) : FastState :=
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

private def tickStage1Fin (s : FastState) : FastState :=
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

private def tickStage1 (fs : FastState) : FastState :=
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
    if oldTr.itemAlloc ≤ nextCur then tickStage1Fin fs' else fs'
  else tickStage1Fin fs

private def tickStage2Swap (b : ℕ) (fsScan : FastState) : FastState :=
  let oldReb := fsScan.rebRole b
  let omIdx := fsScan.overmarsSliceIdx b
  let nextIdx := fsScan.dirtyIdx + 1
  let fsSw : FastState :=
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
  if fsSw.dirtyCount ≤ nextIdx then
    { fsSw with rebStage := 3, stageCursor := 0 }
  else
    let bNext := fsSw.dirtyBuckets nextIdx
    let rIdxNext := fsSw.rebSliceIdx bNext
    { fsSw with
      slices := Function.update fsSw.slices rIdxNext (resetBTreeSlice (fsSw.slices rIdxNext)) }

private def tickStage2 (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) : FastState :=
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
        tickStage2Swap b fsScan
      else fsScan
    else fs
  else { fs with rebStage := 3, stageCursor := 0 }

private def tickStage3 (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) : FastState :=
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
      | none => { fs with stageCursor := nextCur }
    if (fs'.buf oldEp).itemAlloc ≤ nextCur then { fs' with rebStage := 4 } else fs'
  else { fs with rebStage := 4 }

private def tickStage4 (fs : FastState) : FastState :=
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  let doneClear := decide (oldTr.nodeAlloc ≤ 8)
  let tr' := bufClearSteps 8 oldTr
  { fs with
    buf := Function.update fs.buf oldEp tr'
    rebStage := if doneClear then 5 else 4 }

private def tickStage (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) : FastState :=
  if fs.rebStage = 0 then tickStage0 fs
  else if fs.rebStage = 1 then tickStage1 fs
  else if fs.rebStage = 2 then tickStage2 c U n_max θ fs
  else if fs.rebStage = 3 then tickStage3 c U n_max θ fs
  else if fs.rebStage = 4 then tickStage4 fs
  else fs

private def tickRollover (n_max : ℕ) (fs1 : FastState) : Option FastState :=
  let nextClk := fs1.epochClock + 1
  if qEpochWhp n_max ≤ nextClk then
    if fs1.rebStage = 5 then
      some { fs1 with curEp := 1 - fs1.curEp, epochClock := 0, rebStage := 0, stageCursor := 0 }
    else none
  else some { fs1 with epochClock := nextClk }

private theorem epochTick_eq_tickStage (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) :
    epochTick c U n_max θ fs = tickRollover n_max (tickStage c U n_max θ fs) := by
  dsimp only [epochTick, tickStage]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0, ite_eq_left hs0]; rfl
  rw [ite_eq_right hs0, ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1, ite_eq_left hs1]
    dsimp only [tickStage1, tickStage1Fin]
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

/-- Active Stage-2 salt search bound: candidate salt has not yet passed the collision-free salt. -/
@[expose] def SaltBoundAt (c U n_max : ℕ) (θ : SeedWhp c U n_max) (W_keys : Finset (Fin U))
    (fs : FastState) : Prop :=
  fs.rebStage = 2 → fs.dirtyIdx < fs.dirtyCount →
    ∃ s_opt : Fin (sMaxWhp c n_max),
      Set.InjOn (fpHash c U n_max θ.2 s_opt)
        (W_keys.filter (fun u =>
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val =
            fs.dirtyBuckets fs.dirtyIdx) : Set (Fin U)) ∧
      fs.rebCandSalt ≤ s_opt.val

private theorem rebScanSteps_meta (c U n_max b : ℕ) (θ : SeedWhp c U n_max) :
    ∀ (k : ℕ) (s : FastState),
      (rebScanSteps c U n_max θ b k s).epochClock = s.epochClock ∧
      (rebScanSteps c U n_max θ b k s).curEp = s.curEp ∧
      (rebScanSteps c U n_max θ b k s).buf = s.buf ∧
      (rebScanSteps c U n_max θ b k s).rebStage = s.rebStage ∧
      (rebScanSteps c U n_max θ b k s).dirtyCount = s.dirtyCount ∧
      (rebScanSteps c U n_max θ b k s).dirtyIdx = s.dirtyIdx ∧
      (rebScanSteps c U n_max θ b k s).dirtyBuckets = s.dirtyBuckets ∧
      (rebScanSteps c U n_max θ b k s).rebCandSalt = s.rebCandSalt ∧
      (rebScanSteps c U n_max θ b k s).bktCount = s.bktCount := by
  intro k; induction k with
  | zero => intro s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro s; dsimp only [rebScanSteps]
    split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (s.slices (s.rebSliceIdx b))
        (s.fpAt c U n_max θ s.rebCandSalt b s.rebScanCursor) <;> exact ih _
    · exact ih _

private theorem rebScanSteps_cursor_of_zero (c U n_max b : ℕ) (θ : SeedWhp c U n_max) :
    ∀ (k : ℕ) (s : FastState),
      (rebScanSteps c U n_max θ b k s).rebCollision = 0 →
      (rebScanSteps c U n_max θ b k s).rebScanCursor = s.rebScanCursor + k := by
  intro k; induction k with
  | zero => intro s _; simp [rebScanSteps]
  | succ k ih =>
    intro s hcz; dsimp only [rebScanSteps] at hcz ⊢
    by_cases hsnz : s.rebCollision ≠ 0
    · rw [ite_eq_left hsnz] at hcz; exact absurd hcz hsnz
    rw [ite_eq_right hsnz] at hcz ⊢
    split_ifs at hcz ⊢
    · cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (s.slices (s.rebSliceIdx b))
        (s.fpAt c U n_max θ s.rebCandSalt b s.rebScanCursor)
      · rw [hlk] at hcz; dsimp only at hcz ⊢
        have h := ih _ hcz; dsimp only at h; omega
      · rw [hlk] at hcz; dsimp only at hcz
        have h1 : ∀ m (t : FastState), t.rebCollision = 1 →
            (rebScanSteps c U n_max θ b m t).rebCollision = 1 := by
          intro m; induction m <;> intro t ht
          · exact ht
          · dsimp only [rebScanSteps]; rw [ite_eq_left (by omega)]; exact ht
        have := h1 k { s with rebCollision := 1 } rfl; rw [hcz] at this; cases this
    · have h := ih _ hcz; dsimp only at h; omega

private theorem tickStage0_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs0 : fs.rebStage = 0) :
    let fs1 := tickStage0 fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  have hia_le : (fs.buf fs.oldEp).itemAlloc ≤ 2 * rIndepWhp c n_max := hbo.1
  dsimp only [tickStage0]
  by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
  · rw [ite_eq_left hlt]
    cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩; dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, show ¬(1 = 0) by decide, ↓reduceIte, Nat.min_zero]
        unfold stage1Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs0] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, ↓reduceIte]; omega
    | none =>
      dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, show ¬(1 = 0) by decide, ↓reduceIte, Nat.min_zero]
        unfold stage1Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs0] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, ↓reduceIte]; omega
  · rw [ite_eq_right hlt]
    refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [hs0, show ¬(1 = 0) by decide, ↓reduceIte, Nat.min_zero]
    unfold stage1Max; omega

private theorem tickStage1Fin_props {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} (s : FastState) (sc₀ : ℕ)
    (hdc_le : s.dirtyCount ≤ 2 * rIndepWhp c n_max)
    (hd_lt : ∀ j < s.dirtyCount, s.dirtyBuckets j < numBucketsWhp n_max)
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))) :
    let f := tickStage1Fin s
    f.epochClock = s.epochClock ∧
    f.buf f.curEp = s.buf s.curEp ∧
    stageWorkRemaining c n_max f <
      (2 * rIndepWhp c n_max + 1 - min (2 * rIndepWhp c n_max) sc₀) + stage2Max c n_max ∧
    SaltBoundAt c U n_max θ W_keys f := by
  dsimp only [tickStage1Fin]
  by_cases hdc0 : s.dirtyCount = 0
  · rw [ite_eq_left hdc0]
    refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
      ↓reduceIte, Nat.min_zero]
    unfold stage2Max stage3Max; omega
  · rw [ite_eq_right hdc0]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · dsimp only [stageWorkRemaining]
      simp only [show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte,
        Nat.sub_zero, Nat.min_zero]
      have hs_pos : 0 < sMaxWhp c n_max := sMaxWhp_pos c n_max
      have hb_eq : (sMaxWhp c n_max - 1) * (3 * (scaleWhp n_max) ^ 12 + 1) +
          3 * (scaleWhp n_max) ^ 12 + 1 = bktWorkUnit c n_max := by
        unfold bktWorkUnit
        cases hsm : sMaxWhp c n_max with
        | zero => omega
        | succ k => simp [Nat.succ_mul]; omega
      have htot_dc : (s.dirtyCount - 1) * bktWorkUnit c n_max + bktWorkUnit c n_max ≤
          (2 * rIndepWhp c n_max) * bktWorkUnit c n_max := by
        calc (s.dirtyCount - 1) * bktWorkUnit c n_max + bktWorkUnit c n_max
            = s.dirtyCount * bktWorkUnit c n_max := by
                cases hdc_eq : s.dirtyCount with
                | zero => exact absurd hdc_eq hdc0
                | succ d => simp [Nat.succ_mul]
          _ ≤ (2 * rIndepWhp c n_max) * bktWorkUnit c n_max := Nat.mul_le_mul_right _ hdc_le
      unfold stage2Max; omega
    · intro _ hdi
      obtain ⟨s_opt, hs_opt⟩ := hsalt_all ⟨s.dirtyBuckets 0, hd_lt 0 hdi⟩
      exact ⟨s_opt, hs_opt, Nat.zero_le _⟩

private theorem tickStage1_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs1 : fs.rebStage = 1)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))) :
    let fs1 := tickStage1 fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_le, _, oldMap, hv_o, hrel_o⟩ := hbo
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right hs0, ite_eq_left hs1] at hpre
  obtain ⟨hsc_le, hdc_sc, hd_props, _, _, _⟩ := hpre
  have hrem_eq : stageWorkRemaining c n_max fs =
      (2 * rIndepWhp c n_max + 1 - min (2 * rIndepWhp c n_max) fs.stageCursor) +
        stage2Max c n_max := by
    dsimp only [stageWorkRemaining]; rw [ite_eq_right hs0, ite_eq_left hs1]
  rw [hrem_eq]
  dsimp only [tickStage1]
  by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
  · rw [ite_eq_left hlt]
    cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩; dsimp only
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
      by_cases hq0 : fs.rebQueued b₀ = 0
      · rw [ite_eq_left hq0]
        by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
        · rw [ite_eq_left hdone]
          refine tickStage1Fin_props _ fs.stageCursor (by dsimp only; omega) (fun j hj => ?_)
            hsalt_all
          dsimp only at hj ⊢
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · rw [Function.update_of_ne (by omega)]; exact (hd_props j hj').1
          · simp [hb₀]
        · rw [ite_eq_right hdone]
          refine ⟨rfl, rfl, ?_, by intro h; rw [hs1] at h; cases h⟩
          dsimp only [stageWorkRemaining]
          rw [ite_eq_right hs0, ite_eq_left hs1]; omega
      · rw [ite_eq_right hq0]
        by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
        · rw [ite_eq_left hdone]
          exact tickStage1Fin_props _ fs.stageCursor (by dsimp only; omega)
            (fun j hj => (hd_props j hj).1) hsalt_all
        · rw [ite_eq_right hdone]
          refine ⟨rfl, rfl, ?_, by intro h; rw [hs1] at h; cases h⟩
          dsimp only [stageWorkRemaining]
          rw [ite_eq_right hs0, ite_eq_left hs1]; omega
    | none =>
      dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        exact tickStage1Fin_props _ fs.stageCursor (by dsimp only; omega)
          (fun j hj => (hd_props j hj).1) hsalt_all
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs1] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        rw [ite_eq_right hs0, ite_eq_left hs1]; omega
  · rw [ite_eq_right hlt]
    exact tickStage1Fin_props fs fs.stageCursor (hdc_sc.trans (hsc_le.trans hia_le))
      (fun j hj => (hd_props j hj).1) hsalt_all

private theorem tickStage2_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs2 : fs.rebStage = 2)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U)))
    (hsalt_cur : SaltBoundAt c U n_max θ W_keys fs) :
    let fs1 := tickStage2 c U n_max θ fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hs1 : ¬(fs.rebStage = 1) := by omega
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2] at hpre
  obtain ⟨_, hd2, hd3, _, _, _, hreb⟩ := hpre
  set b := fs.dirtyBuckets fs.dirtyIdx
  have hb : b < numBucketsWhp n_max := hd3 _ hd2
  obtain ⟨s_opt, hs_opt_inj, hc_le_s_opt⟩ := hsalt_cur hs2 hd2
  have hcs_lt : fs.rebCandSalt < sMaxWhp c n_max := hc_le_s_opt.trans_lt s_opt.isLt
  obtain ⟨hcur_r, _, rm0, hvr0, hrr0⟩ := hreb hcs_lt
  have hcnt_3L : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12 :=
    (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  have hrem_fs : stageWorkRemaining c n_max fs =
      (fs.dirtyCount - 1 - fs.dirtyIdx) * bktWorkUnit c n_max +
      (sMaxWhp c n_max - 1 - fs.rebCandSalt) * (3 * (scaleWhp n_max) ^ 12 + 1) +
      (3 * (scaleWhp n_max) ^ 12 - min (3 * (scaleWhp n_max) ^ 12) fs.rebScanCursor) +
      1 + stage3Max c n_max := by
    dsimp only [stageWorkRemaining]; rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2]
  rw [hrem_fs]
  dsimp only [tickStage2]
  rw [ite_eq_left hd2, ite_eq_left hcs_lt]
  set fsScan := rebScanSteps c U n_max θ b 16 fs
  obtain ⟨hm_clk, hm_ep, hm_buf, hm_stg, hm_dc, hm_di, hm_db, hm_cs, hm_cnt⟩ :=
    rebScanSteps_meta c U n_max b θ 16 fs
  by_cases hcoll_nz : fsScan.rebCollision ≠ 0
  · rw [ite_eq_left hcoll_nz]
    have hne_s_opt : fs.rebCandSalt ≠ s_opt.val := by
      intro heq_s; apply hcoll_nz
      have hins_ub : fs.rebInsCount + 16 ≤ 8 * (scaleWhp n_max) ^ 12 := by
        have hL2 := two_le_scaleWhp n_max
        have : 4096 ≤ (scaleWhp n_max) ^ 12 := by
          calc 4096 = 2 ^ 12 := by norm_num
            _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
        rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hc_le, hins_le⟩ <;> omega
      refine rebScanSteps_rebCollision_eq_zero_of_inj hc.hth θ 16 fs hc.rebCollision_zero
        hcnt_3L hins_ub (fun l₁ hl₁ l₂ hl₂ _ _ hfp_eq => ?_) ⟨rm0, hvr0, hrr0⟩
      obtain ⟨hm₁, hfb₁⟩ := hc.mem_dom_of_loc hb hl₁
      obtain ⟨hm₂, hfb₂⟩ := hc.mem_dom_of_loc hb hl₂
      let u₁ : Fin U := ⟨fs.keyValAt c U n_max θ.1 b l₁, (hc.active_item b hb l₁ hl₁).1⟩
      let u₂ : Fin U := ⟨fs.keyValAt c U n_max θ.1 b l₂, (hc.active_item b hb l₂ hl₂).1⟩
      have hw₁ : u₁ ∈ W_keys.filter
          (fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b) :=
        mem_filter.mpr ⟨hdom_sub hm₁, hfb₁⟩
      have hw₂ : u₂ ∈ W_keys.filter
          (fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b) :=
        mem_filter.mpr ⟨hdom_sub hm₂, hfb₂⟩
      have hf₁ : fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fpHash c U n_max θ.2 s_opt u₁ := by
        dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₁.isLt, u₁]
      have hf₂ : fs.fpAt c U n_max θ fs.rebCandSalt b l₂ = fpHash c U n_max θ.2 s_opt u₂ := by
        dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₂.isLt, u₂]
      have hu_eq : u₁ = u₂ := hs_opt_inj hw₁ hw₂ (hf₁.symm.trans (hfp_eq.trans hf₂))
      have hkv_eq : fs.keyValAt c U n_max θ.1 b l₁ = fs.keyValAt c U n_max θ.1 b l₂ :=
        congrArg Fin.val hu_eq
      have hq₁ := (hc.active_item b hb l₁ hl₁).2.2.1
      have hq₂ := (hc.active_item b hb l₂ hl₂).2.2.1
      exact hc.quot_inj b hb l₁ hl₁ l₂ hl₂ (hq₁.symm.trans (hkv_eq ▸ hq₂))
    have hlt_s_opt : fs.rebCandSalt < s_opt.val := Nat.lt_of_le_of_ne hc_le_s_opt hne_s_opt
    refine ⟨hm_clk, by dsimp only; rw [hm_buf, hm_ep], ?_, ?_⟩
    · dsimp only [stageWorkRemaining]
      rw [hm_stg, hm_dc, hm_di, hm_cs, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2,
        Nat.min_zero]
      have hs_lt_max : fs.rebCandSalt + 1 ≤ sMaxWhp c n_max - 1 := by have := s_opt.isLt; omega
      have hsub1 : sMaxWhp c n_max - 1 - fs.rebCandSalt =
          (sMaxWhp c n_max - 1 - (fs.rebCandSalt + 1)) + 1 := by omega
      rw [hsub1, Nat.add_mul, one_mul]; omega
    · intro _ _
      refine ⟨s_opt, ?_, ?_⟩
      · dsimp only; rw [hm_db, hm_di]; exact hs_opt_inj
      · dsimp only; rw [hm_cs]; omega
  · rw [ite_eq_right hcoll_nz]
    have hm_cur := rebScanSteps_cursor_of_zero c U n_max b θ 16 fs
      (Classical.not_not.mp hcoll_nz)
    by_cases hdone_b : fsScan.bktCount b ≤ fsScan.rebScanCursor
    · rw [ite_eq_left hdone_b]
      dsimp only [tickStage2Swap]
      by_cases hall_done : fsScan.dirtyCount ≤ fsScan.dirtyIdx + 1
      · rw [ite_eq_left hall_done]
        refine ⟨hm_clk, by dsimp only; rw [hm_buf, hm_ep], ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
          ↓reduceIte, Nat.min_zero]
        unfold stage3Max; omega
      · rw [ite_eq_right hall_done]
        refine ⟨hm_clk, by dsimp only; rw [hm_buf, hm_ep], ?_, ?_⟩
        · dsimp only [stageWorkRemaining]
          rw [hm_stg, hm_dc, hm_di, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2,
            Nat.min_zero]
          have hnxt_lt : fs.dirtyIdx + 1 < fs.dirtyCount := by rw [hm_dc, hm_di] at hall_done; omega
          have hsub_d : fs.dirtyCount - 1 - fs.dirtyIdx =
              (fs.dirtyCount - 1 - (fs.dirtyIdx + 1)) + 1 := by omega
          have hb_eq : (sMaxWhp c n_max - 1 - 0) * (3 * (scaleWhp n_max) ^ 12 + 1) +
              (3 * (scaleWhp n_max) ^ 12 - 0) + 1 = bktWorkUnit c n_max := by
            have := sMaxWhp_pos c n_max; unfold bktWorkUnit
            cases hsm : sMaxWhp c n_max with
            | zero => omega
            | succ k => simp [Nat.succ_mul]; omega
          rw [hsub_d, Nat.add_mul, one_mul]; omega
        · intro _ hdi'
          dsimp only at hdi' ⊢
          rw [hm_db, hm_di]; rw [hm_dc, hm_di] at hdi'
          obtain ⟨s_opt', hs_opt'⟩ := hsalt_all ⟨fs.dirtyBuckets (fs.dirtyIdx + 1), hd3 _ hdi'⟩
          exact ⟨s_opt', hs_opt', Nat.zero_le _⟩
    · rw [ite_eq_right hdone_b]
      refine ⟨hm_clk, by rw [hm_buf, hm_ep], ?_, ?_⟩
      · dsimp only [stageWorkRemaining]
        rw [hm_stg, hm_dc, hm_di, hm_cs, hm_cur, ite_eq_right hs0, ite_eq_right hs1,
          ite_eq_left hs2]
        have hlt_3L : fs.rebScanCursor + 16 < 3 * (scaleWhp n_max) ^ 12 := by
          rw [hm_cnt, hm_cur] at hdone_b; omega
        omega
      · intro _ _; rw [hm_db, hm_di, hm_cs]; exact ⟨s_opt, hs_opt_inj, hc_le_s_opt⟩

private theorem tickStage3_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs3 : fs.rebStage = 3) :
    let fs1 := tickStage3 c U n_max θ fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hs1 : ¬(fs.rebStage = 1) := by omega
  have hs2 : ¬(fs.rebStage = 2) := by omega
  have hne_ep : fs.curEp ≠ fs.oldEp := by
    dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_le, hna_le, _, hv_o, _⟩ := hbo
  have hmul_le : cTabWhp c * (fs.buf fs.oldEp).itemAlloc ≤ cTabWhp c * (2 * rIndepWhp c n_max) :=
    Nat.mul_le_mul_left _ hia_le
  have hrem_fs : stageWorkRemaining c n_max fs =
      (2 * rIndepWhp c n_max + 1 - min (2 * rIndepWhp c n_max) fs.stageCursor) +
        stage4Max c n_max := by
    dsimp only [stageWorkRemaining]
    rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]
  rw [hrem_fs]
  dsimp only [tickStage3]
  by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
  · rw [ite_eq_left hlt]
    cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩; dsimp only
      obtain ⟨_, hna_eq, hia_eq, _, _⟩ :=
        hv_o.delete_spec (rKey := fs.rKeyAt c U n_max θ b₀ loc₀)
          (by
            dsimp only [FastState.rKeyAt]
            split_ifs with hu
            · exact fpReducedKey_lt c U n_max θ.2 ⟨_, hu⟩
            · exact Nat.two_pow_pos _)
      set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp)
        (fs.rKeyAt c U n_max θ b₀ loc₀)
      have hbuf_o' : Function.update fs.buf fs.oldEp tr' fs.oldEp = tr' :=
        Function.update_self _ _ _
      by_cases hdone : (Function.update fs.buf fs.oldEp tr' fs.oldEp).itemAlloc ≤
          fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
          show ¬(4 = 3) by decide, ↓reduceIte]
        change (Function.update fs.buf fs.oldEp tr' fs.oldEp).nodeAlloc < _
        rw [hbuf_o', hna_eq]; unfold stage4Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; rw [hs3] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]
        rw [hbuf_o', hia_eq] at hdone; omega
    | none =>
      dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
          show ¬(4 = 3) by decide, ↓reduceIte]
        change (fs.buf fs.oldEp).nodeAlloc < _
        unfold stage4Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs3] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]; omega
  · rw [ite_eq_right hlt]
    refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
      show ¬(4 = 3) by decide, ↓reduceIte]
    change (fs.buf fs.oldEp).nodeAlloc < _
    unfold stage4Max; omega

private theorem tickStage4_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs4 : fs.rebStage = 4) :
    let fs1 := tickStage4 fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hs1 : ¬(fs.rebStage = 1) := by omega
  have hs2 : ¬(fs.rebStage = 2) := by omega
  have hs3 : ¬(fs.rebStage = 3) := by omega
  have hne_ep : fs.curEp ≠ fs.oldEp := by
    dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
  obtain ⟨_, hclr, _⟩ := hbo
  have h1_le : 1 ≤ (fs.buf fs.oldEp).nodeAlloc := hclr.1
  have hrem_fs : stageWorkRemaining c n_max fs = (fs.buf fs.oldEp).nodeAlloc := by
    dsimp only [stageWorkRemaining]
    rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_right hs3, ite_eq_left hs4]
  rw [hrem_fs]
  dsimp only [tickStage4]
  by_cases hle8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
  · rw [decide_eq_true hle8, ite_eq_left rfl]
    refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(5 = 0) by decide, show ¬(5 = 1) by decide, show ¬(5 = 2) by decide,
      show ¬(5 = 3) by decide, show ¬(5 = 4) by decide, ↓reduceIte]
    omega
  · rw [decide_eq_false hle8, ite_eq_right Bool.false_ne_true]
    refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
      show ¬(4 = 3) by decide, ↓reduceIte]
    change (Function.update fs.buf fs.oldEp (bufClearSteps 8 (fs.buf fs.oldEp)) fs.oldEp).nodeAlloc
      < _
    rw [Function.update_self, hclr.clearSteps_nodeAlloc_eq 8]; omega

/-- Under bounded remaining rebuild work and collision-free window salts `< sMaxWhp c n_max`,
`epochTick` always returns `some fs'`, preserves the work bound and Stage-2 salt invariant, and
either leaves `fs'.buf fs'.curEp` untouched or rolls over to `itemAlloc = 0`. -/
theorem epochTick_some_of_work_bound {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U)))
    (hsalt_cur : SaltBoundAt c U n_max θ W_keys fs)
    (hwork : fs.epochClock + stageWorkRemaining c n_max fs + 1 ≤ qEpochWhp n_max) :
    ∃ fs',
      epochTick c U n_max θ fs = some fs' ∧
      ValidFastState c U V n_max θ fs' dict ∧
      fs'.epochClock + stageWorkRemaining c n_max fs' + 1 ≤ qEpochWhp n_max ∧
      SaltBoundAt c U n_max θ W_keys fs' ∧
      (fs'.buf fs'.curEp = fs.buf fs.curEp ∨ (fs'.buf fs'.curEp).itemAlloc = 0) := by
  set fs1 := tickStage c U n_max θ fs
  have h1 :
      (fs.rebStage < 5 ∧ fs1.epochClock = fs.epochClock ∧ fs1.buf fs1.curEp = fs.buf fs.curEp ∧
       stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
       SaltBoundAt c U n_max θ W_keys fs1) ∨
      (fs.rebStage = 5 ∧ fs1 = fs) := by
    dsimp only [fs1, tickStage]
    by_cases hs0 : fs.rebStage = 0
    · rw [ite_eq_left hs0]; exact Or.inl ⟨by omega, tickStage0_props hc hs0⟩
    rw [ite_eq_right hs0]
    by_cases hs1 : fs.rebStage = 1
    · rw [ite_eq_left hs1]; exact Or.inl ⟨by omega, tickStage1_props hc hs1 hpre hsalt_all⟩
    rw [ite_eq_right hs1]
    by_cases hs2 : fs.rebStage = 2
    · rw [ite_eq_left hs2]
      exact Or.inl ⟨by omega, tickStage2_props hc hs2 hpre hdom_sub hsalt_all hsalt_cur⟩
    rw [ite_eq_right hs2]
    by_cases hs3 : fs.rebStage = 3
    · rw [ite_eq_left hs3]; exact Or.inl ⟨by omega, tickStage3_props hc hs3⟩
    rw [ite_eq_right hs3]
    by_cases hs4 : fs.rebStage = 4
    · rw [ite_eq_left hs4]; exact Or.inl ⟨by omega, tickStage4_props hc hs4⟩
    rw [ite_eq_right hs4]
    exact Or.inr ⟨by have := hc.rebStage_le; omega, rfl⟩
  rcases h1 with ⟨_, hclk1, hbuf1, hw_lt, hsalt1⟩ | ⟨hs5, hfs1_eq⟩
  · have hno_roll : ¬(qEpochWhp n_max ≤ fs1.epochClock + 1) := by omega
    have htick_some :
        epochTick c U n_max θ fs = some { fs1 with epochClock := fs1.epochClock + 1 } := by
      rw [epochTick_eq_tickStage]; dsimp only [tickRollover]; exact ite_eq_right hno_roll
    have hv' := epochTick_spec hc hom hpre htick_some
    refine ⟨{ fs1 with epochClock := fs1.epochClock + 1 }, htick_some, hv', ?_, hsalt1,
      Or.inl hbuf1⟩
    have hw_eq : stageWorkRemaining c n_max { fs1 with epochClock := fs1.epochClock + 1 } =
        stageWorkRemaining c n_max fs1 := rfl
    rw [hw_eq]; dsimp only; omega
  · have hw0 : stageWorkRemaining c n_max fs = 0 := by
      dsimp only [stageWorkRemaining]; simp [hs5]
    change tickStage c U n_max θ fs = fs at hfs1_eq
    by_cases hroll : qEpochWhp n_max ≤ fs.epochClock + 1
    · have htick_some : epochTick c U n_max θ fs =
          some { fs with
            curEp := 1 - fs.curEp, epochClock := 0, rebStage := 0, stageCursor := 0 } := by
        rw [epochTick_eq_tickStage, hfs1_eq]; dsimp only [tickRollover]
        rw [ite_eq_left hroll, ite_eq_left hs5]
      have hv' := epochTick_spec hc hom hpre htick_some
      set fs' : FastState :=
        { fs with curEp := 1 - fs.curEp, epochClock := 0, rebStage := 0, stageCursor := 0 }
      have hbo5 := hc.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)),
        ite_eq_right (by omega : ¬(fs.rebStage = 4))] at hbo5
      refine ⟨fs', htick_some, hv', ?_, (fun h => by cases h),
        Or.inr hbo5.2.2.2⟩
      have hw_le := stageWorkRemaining_le_max hv'.toCore hv'.stage_valid
      have hmax_le := stageWorkMax_add_one_le_qEpoch hc.hth
      have hclk0 : fs'.epochClock = 0 := rfl
      omega
    · have htick_some :
          epochTick c U n_max θ fs = some { fs with epochClock := fs.epochClock + 1 } := by
        rw [epochTick_eq_tickStage, hfs1_eq]; dsimp only [tickRollover]; exact ite_eq_right hroll
      have hv' := epochTick_spec hc hom hpre htick_some
      refine ⟨{ fs with epochClock := fs.epochClock + 1 }, htick_some, hv', ?_, hsalt_cur,
        Or.inl rfl⟩
      have hw_eq : stageWorkRemaining c n_max { fs with epochClock := fs.epochClock + 1 } = 0 := hw0
      rw [hw_eq]; dsimp only; omega


/-! ## Section 2: `CleanWindowFast` invariant and deterministic `fastStepPure` success -/

private theorem overmarsScanSteps_meta (c U n_max b : ℕ) (θ : SeedWhp c U n_max) :
    ∀ (k : ℕ) (s : FastState),
      (overmarsScanSteps c U n_max θ b k s).epochClock = s.epochClock ∧
      (overmarsScanSteps c U n_max θ b k s).curEp = s.curEp ∧
      (overmarsScanSteps c U n_max θ b k s).buf = s.buf ∧
      (overmarsScanSteps c U n_max θ b k s).rebStage = s.rebStage ∧
      (overmarsScanSteps c U n_max θ b k s).stageCursor = s.stageCursor ∧
      (overmarsScanSteps c U n_max θ b k s).dirtyCount = s.dirtyCount ∧
      (overmarsScanSteps c U n_max θ b k s).dirtyIdx = s.dirtyIdx ∧
      (overmarsScanSteps c U n_max θ b k s).dirtyBuckets = s.dirtyBuckets ∧
      (overmarsScanSteps c U n_max θ b k s).rebCandSalt = s.rebCandSalt ∧
      (overmarsScanSteps c U n_max θ b k s).rebScanCursor = s.rebScanCursor := by
  intro k; induction k with
  | zero => intro s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro s; dsimp only [overmarsScanSteps]; split_ifs <;> exact ih _

private theorem overmarsStep_meta (c U n_max b : ℕ) (θ : SeedWhp c U n_max) (s : FastState) :
    (overmarsStep c U n_max θ b s).epochClock = s.epochClock ∧
    (overmarsStep c U n_max θ b s).curEp = s.curEp ∧
    (overmarsStep c U n_max θ b s).buf = s.buf ∧
    (overmarsStep c U n_max θ b s).rebStage = s.rebStage ∧
    (overmarsStep c U n_max θ b s).stageCursor = s.stageCursor ∧
    (overmarsStep c U n_max θ b s).dirtyCount = s.dirtyCount ∧
    (overmarsStep c U n_max θ b s).dirtyIdx = s.dirtyIdx ∧
    (overmarsStep c U n_max θ b s).dirtyBuckets = s.dirtyBuckets ∧
    (overmarsStep c U n_max θ b s).rebCandSalt = s.rebCandSalt ∧
    (overmarsStep c U n_max θ b s).rebScanCursor = s.rebScanCursor := by
  have hfin : ∀ fs1 : FastState,
      fs1.epochClock = s.epochClock ∧ fs1.curEp = s.curEp ∧ fs1.buf = s.buf ∧
      fs1.rebStage = s.rebStage ∧ fs1.stageCursor = s.stageCursor ∧
      fs1.dirtyCount = s.dirtyCount ∧ fs1.dirtyIdx = s.dirtyIdx ∧
      fs1.dirtyBuckets = s.dirtyBuckets ∧ fs1.rebCandSalt = s.rebCandSalt ∧
      fs1.rebScanCursor = s.rebScanCursor →
      let r : FastState :=
        if fs1.bktCount b ≤ fs1.overmarsCursor b then
          { fs1 with
            liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
            overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
            liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
            overmarsActive := Function.update fs1.overmarsActive b 0
            overmarsCursor := Function.update fs1.overmarsCursor b 0
            overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
        else fs1
      r.epochClock = s.epochClock ∧ r.curEp = s.curEp ∧ r.buf = s.buf ∧
      r.rebStage = s.rebStage ∧ r.stageCursor = s.stageCursor ∧
      r.dirtyCount = s.dirtyCount ∧ r.dirtyIdx = s.dirtyIdx ∧
      r.dirtyBuckets = s.dirtyBuckets ∧ r.rebCandSalt = s.rebCandSalt ∧
      r.rebScanCursor = s.rebScanCursor := by
    intro fs1 hm
    by_cases hd : fs1.bktCount b ≤ fs1.overmarsCursor b
    · dsimp only; rw [ite_eq_left hd]; exact hm
    · dsimp only; rw [ite_eq_right hd]; exact hm
  have hgo : ∀ t : FastState,
      t.epochClock = s.epochClock ∧ t.curEp = s.curEp ∧ t.buf = s.buf ∧
      t.rebStage = s.rebStage ∧ t.stageCursor = s.stageCursor ∧
      t.dirtyCount = s.dirtyCount ∧ t.dirtyIdx = s.dirtyIdx ∧
      t.dirtyBuckets = s.dirtyBuckets ∧ t.rebCandSalt = s.rebCandSalt ∧
      t.rebScanCursor = s.rebScanCursor →
      let r : FastState :=
        if t.overmarsActive b = 1 then
          let fs1 := overmarsScanSteps c U n_max θ b 16 t
          if fs1.bktCount b ≤ fs1.overmarsCursor b then
            { fs1 with
              liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
              overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
              liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
              overmarsActive := Function.update fs1.overmarsActive b 0
              overmarsCursor := Function.update fs1.overmarsCursor b 0
              overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
          else fs1
        else t
      r.epochClock = s.epochClock ∧ r.curEp = s.curEp ∧ r.buf = s.buf ∧
      r.rebStage = s.rebStage ∧ r.stageCursor = s.stageCursor ∧
      r.dirtyCount = s.dirtyCount ∧ r.dirtyIdx = s.dirtyIdx ∧
      r.dirtyBuckets = s.dirtyBuckets ∧ r.rebCandSalt = s.rebCandSalt ∧
      r.rebScanCursor = s.rebScanCursor := by
    intro t ht
    by_cases ha : t.overmarsActive b = 1
    · dsimp only; rw [ite_eq_left ha]
      have hm := overmarsScanSteps_meta c U n_max b θ 16 t
      exact hfin (overmarsScanSteps c U n_max θ b 16 t)
        ⟨hm.1.trans ht.1, hm.2.1.trans ht.2.1, hm.2.2.1.trans ht.2.2.1,
         hm.2.2.2.1.trans ht.2.2.2.1, hm.2.2.2.2.1.trans ht.2.2.2.2.1,
         hm.2.2.2.2.2.1.trans ht.2.2.2.2.2.1, hm.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.1,
         hm.2.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.2.1,
         hm.2.2.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.2.2.1,
         hm.2.2.2.2.2.2.2.2.2.trans ht.2.2.2.2.2.2.2.2.2⟩
    · dsimp only; rw [ite_eq_right ha]; exact ht
  dsimp only [overmarsStep]
  by_cases hc0 : s.overmarsActive b = 0 ∧ 5 * (scaleWhp n_max) ^ 12 ≤ s.liveInsCount b
  · rw [ite_eq_left hc0]
    exact hgo _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [ite_eq_right hc0]
    exact hgo s ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem stageWorkRemaining_eq_of_meta (c n_max : ℕ) {s₁ s₂ : FastState}
    (h1 : s₁.rebStage = s₂.rebStage) (h2 : s₁.stageCursor = s₂.stageCursor)
    (h3 : s₁.dirtyCount = s₂.dirtyCount) (h4 : s₁.dirtyIdx = s₂.dirtyIdx)
    (h5 : s₁.rebCandSalt = s₂.rebCandSalt) (h6 : s₁.rebScanCursor = s₂.rebScanCursor)
    (h7 : (s₁.buf s₁.oldEp).nodeAlloc = (s₂.buf s₂.oldEp).nodeAlloc) :
    stageWorkRemaining c n_max s₁ = stageWorkRemaining c n_max s₂ := by
  dsimp only [stageWorkRemaining]
  rw [h1, h2, h3, h4, h5, h6, h7]

private theorem bufDelete_everPresent (cTab bChar : ℕ) (tr : BufTrie) (rKey k : ℕ) :
    bufEverPresent cTab bChar (bufDelete cTab bChar tr rKey) k =
      bufEverPresent cTab bChar tr k := by
  dsimp only [bufDelete]
  cases bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => rfl
  | some leaf => dsimp only; split_ifs <;> rfl


private theorem ValidBufTrie.everPresent_of_map_some {cTab bChar k b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : k < 2 ^ (cTab * bChar)) (hm : mapFn k = some (b, loc)) :
    bufEverPresent cTab bChar tr k = true := by
  have hlk : bufLookup cTab bChar tr k = some (b, loc) := (hv.2.2.2.1 k hk).symm.trans hm
  dsimp only [bufLookup, bufEverPresent] at hlk ⊢
  cases hw : bufWalk bChar tr.trieChild k cTab 0 0 with
  | none => rw [hw] at hlk; cases hlk
  | some leaf =>
    rw [hw] at hlk; dsimp only at hlk
    by_cases hz : tr.nodeLeafItem leaf = 0
    · simp [hz] at hlk
    · simp [hz]

/-- Clean-epoch fast-mode invariant along the trailing window `(W_keys, BadIns)`. -/
structure CleanWindowFast (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (W_keys BadIns : Finset (Fin U)) (fs : FastState) (dict : State U) : Prop where
  valid : ValidFastState c U V n_max θ fs dict
  buf_alloc :
    (fs.buf fs.curEp).itemAlloc ≤
      #(BadIns.filter fun u =>
        bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
          (fpReducedKey c U n_max θ.2 u))
  work_le : fs.epochClock + stageWorkRemaining c n_max fs + 1 ≤ qEpochWhp n_max
  salt_bound : SaltBoundAt c U n_max θ W_keys fs

theorem CleanWindowFast.of_clean_fast {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys BadIns : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict)
    (hia0 : (fs.buf fs.curEp).itemAlloc = 0)
    (hclk0 : fs.epochClock = 0)
    (hno2 : fs.rebStage ≠ 2) :
    CleanWindowFast c U V n_max θ W_keys BadIns fs dict :=
  { valid := hv
    buf_alloc := by rw [hia0]; exact Nat.zero_le _
    work_le := by
      have hw := stageWorkRemaining_le_max hv.toCore hv.stage_valid
      have hm := stageWorkMax_add_one_le_qEpoch hv.hth
      omega
    salt_bound := fun hs2 => absurd hs2 hno2 }

private theorem fastDeleteMoveSlices_rebSliceIdx (n_max b loc_del loc_last fp : ℕ)
    (s : FastState)
    (hroles : s.liveRole b < 3 ∧ s.overmarsRole b < 3 ∧ s.liveRole b ≠ s.overmarsRole b) :
    (fastDeleteMoveSlices n_max b loc_del loc_last fp s).1 (s.rebSliceIdx b) =
      s.slices (s.rebSliceIdx b) := by
  have hne1 : s.rebSliceIdx b ≠ s.liveSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.liveSliceIdx, FastState.rebRole]; omega
  have hne2 : s.rebSliceIdx b ≠ s.overmarsSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.overmarsSliceIdx, FastState.rebRole]; omega
  dsimp only [fastDeleteMoveSlices]
  have h1 : ∀ (f : ℕ → BTreeSlice),
      f (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) →
      (if s.overmarsActive b = 1 ∧
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_last) then
        if loc_last < s.overmarsCursor b then
          (Function.update f (s.overmarsSliceIdx b)
            (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (f (s.overmarsSliceIdx b)) fp loc_del), s.overmarsInsCount)
        else if loc_del < s.overmarsCursor b then
          (Function.update f (s.overmarsSliceIdx b)
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (f (s.overmarsSliceIdx b)) fp loc_del),
           Function.update s.overmarsInsCount b (s.overmarsInsCount b + 1))
        else (f, s.overmarsInsCount)
      else (f, s.overmarsInsCount)).1 (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) := by
    intro f hf
    by_cases hc1 : s.overmarsActive b = 1 ∧
        inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_last)
    · rw [ite_eq_left hc1]
      by_cases hc2 : loc_last < s.overmarsCursor b
      · rw [ite_eq_left hc2]; dsimp only; rw [Function.update_of_ne hne2]; exact hf
      · rw [ite_eq_right hc2]
        by_cases hc3 : loc_del < s.overmarsCursor b
        · rw [ite_eq_left hc3]; dsimp only; rw [Function.update_of_ne hne2]; exact hf
        · rw [ite_eq_right hc3]; exact hf
    · rw [ite_eq_right hc1]; exact hf
  apply h1
  by_cases hc0 : inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_last)
  · rw [ite_eq_left hc0, Function.update_of_ne hne1]
  · rw [ite_eq_right hc0]

private theorem fastDeleteErase_rebSliceIdx (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (s : FastState) (u : Fin U) (b loc_del : ℕ)
    (hroles : s.liveRole b < 3 ∧ s.overmarsRole b < 3 ∧ s.liveRole b ≠ s.overmarsRole b) :
    (fastDeleteErase c U n_max θ s u b loc_del).slices (s.rebSliceIdx b) =
      if (decide (s.rebStage = 2 ∧ s.dirtyIdx < s.dirtyCount ∧
            s.dirtyBuckets s.dirtyIdx = b ∧ s.rebCandSalt < sMaxWhp c n_max ∧
            s.rebCollision = 0) &&
          decide (loc_del < s.rebScanCursor ∧
            (s.locState b loc_del = 1 ∨ s.locState b loc_del = 2 + s.oldEp))) = true then
        btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (s.slices (s.rebSliceIdx b)) (fpOfSalt c U n_max θ.2 s.rebCandSalt u)
      else s.slices (s.rebSliceIdx b) := by
  have hne1 : s.rebSliceIdx b ≠ s.liveSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.liveSliceIdx, FastState.rebRole]; omega
  have hne2 : s.rebSliceIdx b ≠ s.overmarsSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.overmarsSliceIdx, FastState.rebRole]; omega
  dsimp only [fastDeleteErase]
  have hs2 : ∀ (f : ℕ → BTreeSlice),
      f (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) →
      (if s.overmarsActive b = 1 ∧ loc_del < s.overmarsCursor b ∧
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del) then
        Function.update f (s.overmarsSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (f (s.overmarsSliceIdx b)) (fpOfSalt c U n_max θ.2 (s.bktSalt b) u))
      else f) (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) := by
    intro f hf
    by_cases hc2 : s.overmarsActive b = 1 ∧ loc_del < s.overmarsCursor b ∧
        inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del)
    · rw [ite_eq_left hc2, Function.update_of_ne hne2]; exact hf
    · rw [ite_eq_right hc2]; exact hf
  have hs1 : (if inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del) then
      Function.update s.slices (s.liveSliceIdx b)
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (s.slices (s.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (s.bktSalt b) u))
    else s.slices) (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) := by
    by_cases hc1 : inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del)
    · rw [ite_eq_left hc1, Function.update_of_ne hne1]
    · rw [ite_eq_right hc1]
  have hmid := hs2 _ hs1
  by_cases hc3 : (decide (s.rebStage = 2 ∧ s.dirtyIdx < s.dirtyCount ∧
        s.dirtyBuckets s.dirtyIdx = b ∧ s.rebCandSalt < sMaxWhp c n_max ∧
        s.rebCollision = 0) &&
      decide (loc_del < s.rebScanCursor ∧
        (s.locState b loc_del = 1 ∨ s.locState b loc_del = 2 + s.oldEp))) = true
  · rw [ite_eq_left hc3, ite_eq_left hc3, Function.update_self, hmid]
  · rw [ite_eq_right hc3, ite_eq_right hc3, hmid]

private theorem fastDelete_clean_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hsalt_cur : SaltBoundAt c U n_max θ W_keys fs) (u : Fin U) :
    let fs' := fastDelete c U n_max θ fs u
    fs'.epochClock = fs.epochClock ∧
    fs'.curEp = fs.curEp ∧
    (fs'.buf fs'.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
    (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
      bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.curEp) k =
        bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) ∧
    stageWorkRemaining c n_max fs' ≤ stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs' := by
  have hc := hv.toCore
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) _ u.val
  dsimp only [fastDelete]
  have hom_m := fun s => overmarsStep_meta c U n_max b θ s
  cases hfl : fastFindLoc c U n_max θ fs u with
  | none =>
    dsimp only
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hom_m fs
    have hw_eq := stageWorkRemaining_eq_of_meta c n_max h4 h5 h6 h7 h9 h10
      (by dsimp only [FastState.oldEp]; rw [h3, h2])
    refine ⟨h1, h2, by rw [h3, h2], fun k _ => by rw [h3, h2], hw_eq.le, ?_⟩
    intro hs2 hdi; rw [h4] at hs2; rw [h7, h6] at hdi
    rw [h8, h7, h9]; exact hsalt_cur hs2 hdi
  | some loc_del =>
    dsimp only
    have hfl_sp := hv.fastFindLoc_spec u
    dsimp only at hfl_sp; rw [hfl] at hfl_sp
    have hloc_del : loc_del < fs.bktCount b := hfl_sp.1
    set loc_last := fs.bktCount b - 1
    have hloc_last : loc_last < fs.bktCount b := by omega
    set rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    set fs1 := fastDeleteErase c U n_max θ fs u b loc_del
    set fs2 := if loc_del < loc_last then
      fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1 else fs1
    set fs3 := fastDeleteShrink n_max b loc_last fs2
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hom_m fs3
    have hclk_eq : fs3.epochClock = fs.epochClock := by
      dsimp only [fs3, fastDeleteShrink, fs2, fastDeleteMoveLast, fs1, fastDeleteErase]
      by_cases hlt : loc_del < loc_last <;> [rw [ite_eq_left hlt]; rw [ite_eq_right hlt]]
    have hep_eq : fs3.curEp = fs.curEp := by
      dsimp only [fs3, fastDeleteShrink, fs2, fastDeleteMoveLast, fs1, fastDeleteErase]
      by_cases hlt : loc_del < loc_last <;> [rw [ite_eq_left hlt]; rw [ite_eq_right hlt]]
    -- Buffer `curEp` preservation across `fs1` and `fs2`:
    obtain ⟨_, _, curMap, hv_c, hrel_c⟩ := hc.bufCur_valid
    have hrk_u_lt : fpReducedKey c U n_max θ.2 u < 2 ^ (cTabWhp c * bCharWhp n_max) :=
      fpReducedKey_lt c U n_max θ.2 u
    have hbuf1_c :
        (∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf fs.curEp) m1 ∧
          ∀ rk b' l', l' ≠ loc_del → curMap rk = some (b', l') → m1 rk = some (b', l')) ∧
        (fs1.buf fs.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
        (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs1.buf fs.curEp) k =
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) := by
      dsimp only [fs1, fastDeleteErase]
      rcases hc.curEp_or with hcep | hcep
      · rw [hcep] at hv_c hrel_c ⊢
        by_cases hst2 : fs.locState b loc_del = 2
        · rw [ite_eq_left hst2, Function.update_self]
          obtain ⟨hv_d, _, hia_d, _, _⟩ := hv_c.delete_spec hrk_u_lt
          refine ⟨⟨_, hv_d, fun rk b' l' hne hm => ?_⟩, hia_d,
            fun k _ => bufDelete_everPresent _ _ _ _ k⟩
          have hrk_ne : rk ≠ fpReducedKey c U n_max θ.2 u := by
            intro heq; subst heq
            obtain ⟨hb', hl', hst', hrk'⟩ := (hrel_c.2 _ b' l').mp hm
            have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
              dsimp only [FastState.keyValAt]
              rw [hfl_sp.2, feistelReconstruct_feistelBucket (bWhp n_max) _ u.val]
            have hrk_del : fs.rKeyAt c U n_max θ b loc_del = fpReducedKey c U n_max θ.2 u := by
              dsimp only [FastState.rKeyAt]; simp [hkv_del, u.isLt]
            have hbl := hc.rKey_buf_inj b' hb' l' hl' b hb loc_del hloc_del
              (by omega) (by omega) (hrk'.trans hrk_del.symm)
            exact hne hbl.2
          rwa [Function.update_of_ne hrk_ne]
        · rw [ite_eq_right hst2]
          by_cases hst3 : fs.locState b loc_del = 3
          · rw [ite_eq_left hst3, Function.update_of_ne (by decide)]
            exact ⟨⟨curMap, hv_c, fun _ _ _ _ h => h⟩, rfl, fun _ _ => rfl⟩
          · rw [ite_eq_right hst3]
            exact ⟨⟨curMap, hv_c, fun _ _ _ _ h => h⟩, rfl, fun _ _ => rfl⟩
      · rw [hcep] at hv_c hrel_c ⊢
        by_cases hst2 : fs.locState b loc_del = 2
        · rw [ite_eq_left hst2, Function.update_of_ne (by decide)]
          exact ⟨⟨curMap, hv_c, fun _ _ _ _ h => h⟩, rfl, fun _ _ => rfl⟩
        · rw [ite_eq_right hst2]
          by_cases hst3 : fs.locState b loc_del = 3
          · rw [ite_eq_left hst3, Function.update_self]
            obtain ⟨hv_d, _, hia_d, _, _⟩ := hv_c.delete_spec hrk_u_lt
            refine ⟨⟨_, hv_d, fun rk b' l' hne hm => ?_⟩, hia_d,
              fun k _ => bufDelete_everPresent _ _ _ _ k⟩
            have hrk_ne : rk ≠ fpReducedKey c U n_max θ.2 u := by
              intro heq; subst heq
              obtain ⟨hb', hl', hst', hrk'⟩ := (hrel_c.2 _ b' l').mp hm
              have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
                dsimp only [FastState.keyValAt]
                rw [hfl_sp.2, feistelReconstruct_feistelBucket (bWhp n_max) _ u.val]
              have hrk_del : fs.rKeyAt c U n_max θ b loc_del = fpReducedKey c U n_max θ.2 u := by
                dsimp only [FastState.rKeyAt]; simp [hkv_del, u.isLt]
              have hbl := hc.rKey_buf_inj b' hb' l' hl' b hb loc_del hloc_del
                (by omega) (by omega) (hrk'.trans hrk_del.symm)
              exact hne hbl.2
            rwa [Function.update_of_ne hrk_ne]
          · rw [ite_eq_right hst3]
            exact ⟨⟨curMap, hv_c, fun _ _ _ _ h => h⟩, rfl, fun _ _ => rfl⟩
    obtain ⟨⟨m1, hv_m1, hm1_pres⟩, hia1, hev1⟩ := hbuf1_c
    have hbuf2_c :
        (fs2.buf fs.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
        (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs2.buf fs.curEp) k =
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) := by
      dsimp only [fs2]
      by_cases hlt_dl : loc_del < loc_last
      · rw [ite_eq_left hlt_dl]
        dsimp only [fastDeleteMoveLast]
        have hls1 : fs1.locState = fs.locState := rfl
        have hrk1 : fs1.rKeyAt c U n_max θ b loc_last = fs.rKeyAt c U n_max θ b loc_last := rfl
        rw [hls1, hrk1]
        have hrk_last_lt : fs.rKeyAt c U n_max θ b loc_last < 2 ^ (cTabWhp c * bCharWhp n_max) := by
          dsimp only [FastState.rKeyAt]
          split_ifs with hu
          · exact fpReducedKey_lt c U n_max θ.2 ⟨_, hu⟩
          · exact Nat.two_pow_pos _
        rcases hc.curEp_or with hcep | hcep
        · rw [hcep] at hrel_c hv_m1 hia1 hev1 ⊢
          by_cases hsl2 : fs.locState b loc_last = 2
          · rw [ite_eq_left hsl2, Function.update_self]
            have hm_last : curMap (fs.rKeyAt c U n_max θ b loc_last) = some (b, loc_last) :=
              (hrel_c.2 _ b loc_last).mpr ⟨hb, hloc_last, by omega, rfl⟩
            have hm1_last := hm1_pres _ b loc_last (by omega) hm_last
            have hev_last := hv_m1.everPresent_of_map_some hrk_last_lt hm1_last
            have hins := hv_m1.insert_spec (b := b) (loc := loc_del) hrk_last_lt
            refine ⟨(hins.2.2.2.2.2.2.1 hev_last).2.trans hia1, fun k hk => ?_⟩
            rw [hins.2.2.2.2.2.1 k hk]
            by_cases hkr : k = fs.rKeyAt c U n_max θ b loc_last
            · subst hkr; rw [ite_eq_left rfl, ← hev1 _ hrk_last_lt, hev_last]
            · rw [ite_eq_right hkr]; exact hev1 k hk
          · rw [ite_eq_right hsl2]
            by_cases hsl3 : fs.locState b loc_last = 3
            · rw [ite_eq_left hsl3, Function.update_of_ne (by decide)]; exact ⟨hia1, hev1⟩
            · rw [ite_eq_right hsl3]; exact ⟨hia1, hev1⟩
        · rw [hcep] at hrel_c hv_m1 hia1 hev1 ⊢
          by_cases hsl2 : fs.locState b loc_last = 2
          · rw [ite_eq_left hsl2, Function.update_of_ne (by decide)]; exact ⟨hia1, hev1⟩
          · rw [ite_eq_right hsl2]
            by_cases hsl3 : fs.locState b loc_last = 3
            · rw [ite_eq_left hsl3, Function.update_self]
              have hm_last : curMap (fs.rKeyAt c U n_max θ b loc_last) = some (b, loc_last) :=
                (hrel_c.2 _ b loc_last).mpr ⟨hb, hloc_last, by omega, rfl⟩
              have hm1_last := hm1_pres _ b loc_last (by omega) hm_last
              have hev_last := hv_m1.everPresent_of_map_some hrk_last_lt hm1_last
              have hins := hv_m1.insert_spec (b := b) (loc := loc_del) hrk_last_lt
              refine ⟨(hins.2.2.2.2.2.2.1 hev_last).2.trans hia1, fun k hk => ?_⟩
              rw [hins.2.2.2.2.2.1 k hk]
              by_cases hkr : k = fs.rKeyAt c U n_max θ b loc_last
              · subst hkr; rw [ite_eq_left rfl, ← hev1 _ hrk_last_lt, hev_last]
              · rw [ite_eq_right hkr]; exact hev1 k hk
            · rw [ite_eq_right hsl3]; exact ⟨hia1, hev1⟩
      · rw [ite_eq_right hlt_dl]; exact ⟨hia1, hev1⟩
    have hbuf3_eq : fs3.buf = fs2.buf := rfl
    refine ⟨h1.trans hclk_eq, h2.trans hep_eq,
      by rw [h3, hbuf3_eq, h2, hep_eq]; exact hbuf2_c.1,
      fun k hk => by rw [h3, hbuf3_eq, h2, hep_eq]; exact hbuf2_c.2 k hk, ?_, ?_⟩
    · -- `stageWorkRemaining` across `fastDelete` (`≤`)
      have hw_om : stageWorkRemaining c n_max (overmarsStep c U n_max θ b fs3) =
          stageWorkRemaining c n_max fs3 :=
        stageWorkRemaining_eq_of_meta c n_max h4 h5 h6 h7 h9 h10
          (by dsimp only [FastState.oldEp]; rw [h3, h2])
      rw [hw_om]
      have hw32 : stageWorkRemaining c n_max fs3 = stageWorkRemaining c n_max fs2 :=
        stageWorkRemaining_eq_of_meta c n_max rfl rfl rfl rfl rfl rfl rfl
      rw [hw32]
      have hold4_na : fs.rebStage = 4 →
          (fs2.buf fs2.oldEp).nodeAlloc = (fs.buf fs.oldEp).nodeAlloc := by
        intro hs4
        have hbo := hc.bufOld_valid
        rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
        have hno_old := hbo.1
        have h1_na : fs1.buf fs.oldEp = fs.buf fs.oldEp := by
          dsimp only [fs1, fastDeleteErase]
          have hne_d := hno_old b hb loc_del hloc_del
          rcases hc.curEp_or with hcep | hcep
          · have ho : fs.oldEp = 1 := by dsimp [FastState.oldEp]; omega
            rw [ho] at hne_d ⊢
            by_cases h2 : fs.locState b loc_del = 2
            · rw [ite_eq_left h2, Function.update_of_ne (by decide)]
            · rw [ite_eq_right h2]
              by_cases h3 : fs.locState b loc_del = 3
              · omega
              · rw [ite_eq_right h3]
          · have ho : fs.oldEp = 0 := by dsimp [FastState.oldEp]; omega
            rw [ho] at hne_d ⊢
            by_cases h2 : fs.locState b loc_del = 2
            · omega
            · rw [ite_eq_right h2]
              by_cases h3 : fs.locState b loc_del = 3
              · rw [ite_eq_left h3, Function.update_of_ne (by decide)]
              · rw [ite_eq_right h3]
        dsimp only [fs2]
        by_cases hlt_dl : loc_del < loc_last
        · rw [ite_eq_left hlt_dl]
          have hold2 : (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1).oldEp =
              fs.oldEp := rfl
          rw [hold2]; dsimp only [fastDeleteMoveLast]
          have hls1 : fs1.locState = fs.locState := rfl; rw [hls1]
          have hne_l := hno_old b hb loc_last hloc_last
          rcases hc.curEp_or with hcep | hcep
          · have ho : fs.oldEp = 1 := by dsimp [FastState.oldEp]; omega
            rw [ho] at hne_l h1_na ⊢
            by_cases h2 : fs.locState b loc_last = 2
            · rw [ite_eq_left h2, Function.update_of_ne (by decide), h1_na]
            · rw [ite_eq_right h2]
              by_cases h3 : fs.locState b loc_last = 3
              · omega
              · rw [ite_eq_right h3, h1_na]
          · have ho : fs.oldEp = 0 := by dsimp [FastState.oldEp]; omega
            rw [ho] at hne_l h1_na ⊢
            by_cases h2 : fs.locState b loc_last = 2
            · omega
            · rw [ite_eq_right h2]
              by_cases h3 : fs.locState b loc_last = 3
              · rw [ite_eq_left h3, Function.update_of_ne (by decide), h1_na]
              · rw [ite_eq_right h3, h1_na]
        · rw [ite_eq_right hlt_dl]
          have hold1 : fs1.oldEp = fs.oldEp := rfl; rw [hold1, h1_na]
      dsimp only [fs2]
      by_cases hlt_dl : loc_del < loc_last
      · rw [ite_eq_left hlt_dl]
        by_cases hs4 : fs.rebStage = 4
        · have hw_eq : stageWorkRemaining c n_max
              (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1) =
              stageWorkRemaining c n_max fs := by
            dsimp only [stageWorkRemaining]
            have hst_mv :
                (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1).rebStage =
                  fs.rebStage := rfl
            simp only [hst_mv, hs4, show ¬(4 = 0) by decide, show ¬(4 = 1) by decide,
              show ¬(4 = 2) by decide, show ¬(4 = 3) by decide, ↓reduceIte]
            have h := hold4_na hs4
            dsimp only [fs2] at h; rw [ite_eq_left hlt_dl] at h; exact h
          exact hw_eq.le
        · -- `fs.rebStage ≠ 4`: check whether `rebCandSalt` bumped in `fastDeleteMoveLast`
          dsimp only [fastDeleteMoveLast]
          have h1_meta : fs1.rebStage = fs.rebStage ∧ fs1.stageCursor = fs.stageCursor ∧
              fs1.dirtyCount = fs.dirtyCount ∧ fs1.dirtyIdx = fs.dirtyIdx ∧
              fs1.rebCandSalt = fs.rebCandSalt ∧ fs1.rebScanCursor = fs.rebScanCursor :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          by_cases hreb_act : (rebActiveB && decide (fs1.locState b loc_last = 1 ∨
              fs1.locState b loc_last = 2 + fs1.oldEp)) = true
          · simp only [hreb_act, ↓reduceIte]
            obtain ⟨hra_t, hst_last_ok⟩ := Bool.and_eq_true_iff.mp hreb_act
            rw [decide_eq_true_iff] at hra_t hst_last_ok
            obtain ⟨hs2, hd2, hdb_eq, hcs_lt, _⟩ := hra_t
            by_cases hll_sc : loc_last < fs1.rebScanCursor
            · simp only [hll_sc, ↓reduceIte]
              dsimp only [stageWorkRemaining]
              rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
                h1_meta.2.2.2.2.2]
              simp only [hs4, ↓reduceIte]; exact le_rfl
            · simp only [hll_sc, ↓reduceIte]
              by_cases hld_sc : loc_del < fs1.rebScanCursor
              · simp only [hld_sc, ↓reduceIte]
                cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                    ((fastDeleteMoveSlices n_max b loc_del loc_last
                      (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last) fs1).1
                      (fs1.rebSliceIdx b))
                    (fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last) with
                | none =>
                  dsimp only [stageWorkRemaining]
                  rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
                    h1_meta.2.2.2.2.2]
                  simp only [hs4, ↓reduceIte]; exact le_rfl
                | some prev_loc =>
                  obtain ⟨s_opt, hs_opt_inj, hc_le_s⟩ := hsalt_cur hs2 hd2
                  have hne_s : fs.rebCandSalt ≠ s_opt.val := by
                    intro heq_s
                    have hstg := hv.stage_valid
                    dsimp only [ValidEpochStage] at hstg
                    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hs2] at hstg
                    obtain ⟨_, _, _, _, _, _, hreb⟩ := hstg
                    rw [hdb_eq] at hreb
                    obtain ⟨hcur_r, _, rm0, hvr0, hrr0⟩ := hreb hcs_lt
                    have hroles1 : fs1.liveRole b < 3 ∧ fs1.overmarsRole b < 3 ∧
                        fs1.liveRole b ≠ fs1.overmarsRole b := hc.roles_valid b hb
                    rw [fastDeleteMoveSlices_rebSliceIdx n_max b loc_del loc_last _ fs1 hroles1]
                      at hlk
                    have hr_eq1 : fs1.rebSliceIdx b = fs.rebSliceIdx b := rfl
                    have hfp_eq1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last =
                        fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := rfl
                    rw [hr_eq1, hfp_eq1] at hlk
                    have hins_le8 : fs.rebInsCount ≤ 8 * (scaleWhp n_max) ^ 12 := by
                      have hcnt3 := (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
                      have hL2 := two_le_scaleWhp n_max
                      have : 4096 ≤ (scaleWhp n_max) ^ 12 := by
                        calc 4096 = 2 ^ 12 := by norm_num
                          _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
                      rcases hcur_r with ⟨_, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
                    have hfp_cl_lt : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last <
                        2 ^ fpBitsWhp n_max := by
                      dsimp only [FastState.fpAt]
                      by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
                      · rw [dite_eq_left hs]
                        by_cases hu : fs.keyValAt c U n_max θ.1 b loc_last < U
                        · rw [dite_eq_left hu]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ ⟨_, hu⟩
                        · rw [dite_eq_right hu]; exact Nat.two_pow_pos _
                      · rw [dite_eq_right hs]; exact Nat.two_pow_pos _
                    have hrm_prev : rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) =
                        some prev_loc := by
                      dsimp only [fs1] at hlk
                      rw [fastDeleteErase_rebSliceIdx _ _ _ _ _ _ _ _ (hc.roles_valid b hb)] at hlk
                      split_ifs at hlk
                      · have hfp_d_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u <
                            2 ^ fpBitsWhp n_max := by
                          dsimp only [fpOfSalt]
                          by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
                          · rw [dite_eq_left hs]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
                          · rw [dite_eq_right hs]; exact Nat.two_pow_pos _
                        have hvd := hvr0.delete_spec hc.hth hins_le8 hfp_d_lt
                        rw [hvd.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
                        by_cases heq_fp : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last =
                            fpOfSalt c U n_max θ.2 fs.rebCandSalt u
                        · change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
                            (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
                          rw [heq_fp, Function.update_self] at hlk; cases hlk
                        · change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
                            (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
                          rwa [Function.update_of_ne heq_fp] at hlk
                      · rwa [hvr0.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
                    obtain ⟨hprev_min, _, hfp_prev⟩ := (hrr0.2 _ prev_loc).mp hrm_prev
                    have hprev_lt_sc : prev_loc < fs.rebScanCursor :=
                      hprev_min.trans_le (Nat.min_le_right _ _)
                    have hprev_lt_cnt : prev_loc < fs.bktCount b :=
                      hprev_min.trans_le (Nat.min_le_left _ _)
                    obtain ⟨hm₁, hfb₁⟩ := hc.mem_dom_of_loc hb hprev_lt_cnt
                    obtain ⟨hm₂, hfb₂⟩ := hc.mem_dom_of_loc hb hloc_last
                    let u₁ : Fin U :=
                      ⟨fs.keyValAt c U n_max θ.1 b prev_loc,
                       (hc.active_item b hb prev_loc hprev_lt_cnt).1⟩
                    let u₂ : Fin U :=
                      ⟨fs.keyValAt c U n_max θ.1 b loc_last,
                       (hc.active_item b hb loc_last hloc_last).1⟩
                    have hw₁ : u₁ ∈ W_keys.filter (fun w =>
                        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
                          fs.dirtyBuckets fs.dirtyIdx) :=
                      mem_filter.mpr ⟨hdom_sub hm₁, hfb₁.trans hdb_eq.symm⟩
                    have hw₂ : u₂ ∈ W_keys.filter (fun w =>
                        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
                          fs.dirtyBuckets fs.dirtyIdx) :=
                      mem_filter.mpr ⟨hdom_sub hm₂, hfb₂.trans hdb_eq.symm⟩
                    have hf₁ : fs.fpAt c U n_max θ fs.rebCandSalt b prev_loc =
                        fpHash c U n_max θ.2 s_opt u₁ := by
                      dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₁.isLt, u₁]
                    have hf₂ : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last =
                        fpHash c U n_max θ.2 s_opt u₂ := by
                      dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₂.isLt, u₂]
                    have hu_eq : u₁ = u₂ := hs_opt_inj hw₁ hw₂ (hf₁.symm.trans (hfp_prev.trans hf₂))
                    have hkv_eq : fs.keyValAt c U n_max θ.1 b prev_loc =
                        fs.keyValAt c U n_max θ.1 b loc_last := congrArg Fin.val hu_eq
                    have hq₁ := (hc.active_item b hb prev_loc hprev_lt_cnt).2.2.1
                    have hq₂ := (hc.active_item b hb loc_last hloc_last).2.2.1
                    have hl_eq := hc.quot_inj b hb prev_loc hprev_lt_cnt loc_last hloc_last
                      (hq₁.symm.trans (hkv_eq ▸ hq₂))
                    change loc_del < fs.rebScanCursor at hld_sc
                    change ¬(loc_last < fs.rebScanCursor) at hll_sc
                    omega
                  dsimp only [stageWorkRemaining]
                  simp only [h1_meta.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1, hs2,
                    show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte, Nat.min_zero]
                  have hs_lt_max : fs.rebCandSalt + 1 ≤ sMaxWhp c n_max - 1 := by
                    have := s_opt.isLt; omega
                  have hsub1 : sMaxWhp c n_max - 1 - fs.rebCandSalt =
                      (sMaxWhp c n_max - 1 - (fs.rebCandSalt + 1)) + 1 := by omega
                  rw [hsub1, Nat.add_mul, one_mul]; omega
              · simp only [hld_sc, ↓reduceIte]
                dsimp only [stageWorkRemaining]
                rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
                  h1_meta.2.2.2.2.2]
                simp only [hs4, ↓reduceIte]; exact le_rfl
          · simp only [hreb_act, Bool.false_eq_true, ↓reduceIte]
            dsimp only [stageWorkRemaining]
            rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
              h1_meta.2.2.2.2.2]
            simp only [hs4, ↓reduceIte]; exact le_rfl
      · rw [ite_eq_right hlt_dl]
        by_cases hs4 : fs.rebStage = 4
        · have h := hold4_na hs4; dsimp only [fs2] at h; rw [ite_eq_right hlt_dl] at h
          exact (stageWorkRemaining_eq_of_meta (s₁ := fs1) (s₂ := fs) c n_max
            rfl rfl rfl rfl rfl rfl h).le
        · dsimp only [stageWorkRemaining]
          have hst1 : fs1.rebStage = fs.rebStage := rfl
          rw [hst1]; simp only [hs4, ↓reduceIte]; exact le_rfl
    · -- `SaltBoundAt` across `fastDelete`: prove directly from `hsalt_cur`.
      have h3_meta : fs3.rebStage = fs.rebStage ∧ fs3.dirtyCount = fs.dirtyCount ∧
          fs3.dirtyIdx = fs.dirtyIdx ∧ fs3.dirtyBuckets = fs.dirtyBuckets ∧
          fs3.rebCandSalt = fs2.rebCandSalt := by
        dsimp only [fs3, fastDeleteShrink, fs2, fastDeleteMoveLast, fs1, fastDeleteErase]
        by_cases hlt_dl : loc_del < loc_last
        · rw [ite_eq_left hlt_dl]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · rw [ite_eq_right hlt_dl]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      intro hs2' hdi'
      rw [h4, h3_meta.1] at hs2'
      rw [h7, h6, h3_meta.2.2.1, h3_meta.2.1] at hdi'
      rw [h8, h7, h9, h3_meta.2.2.2.1, h3_meta.2.2.1, h3_meta.2.2.2.2]
      obtain ⟨s_opt, hs_opt_inj, hc_le_s⟩ := hsalt_cur hs2' hdi'
      have hs2 : fs.rebStage = 2 := hs2'
      refine ⟨s_opt, hs_opt_inj, ?_⟩
      dsimp only [fs2]
      by_cases hlt_dl : loc_del < loc_last
      · rw [ite_eq_left hlt_dl]; dsimp only [fastDeleteMoveLast]
        split_ifs with hreb_act hll_sc hld_sc
        · exact hc_le_s
        · cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              ((fastDeleteMoveSlices n_max b loc_del loc_last
                (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last) fs1).1
                (fs1.rebSliceIdx b))
              (fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last) with
          | none => exact hc_le_s
          | some prev_loc =>
            dsimp only
            by_contra hgt
            push Not at hgt
            have heq_s : fs.rebCandSalt = s_opt.val := by
              change s_opt.val < fs.rebCandSalt + 1 at hgt; omega
            obtain ⟨hra_t, _⟩ := Bool.and_eq_true_iff.mp hreb_act
            rw [decide_eq_true_iff] at hra_t
            obtain ⟨_, _, hdb_eq, hcs_lt, _⟩ := hra_t
            have hstg := hv.stage_valid
            dsimp only [ValidEpochStage] at hstg
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hs2] at hstg
            obtain ⟨_, _, _, _, _, _, hreb⟩ := hstg
            rw [hdb_eq] at hreb
            obtain ⟨hcur_r, _, rm0, hvr0, hrr0⟩ := hreb hcs_lt
            have hroles1 : fs1.liveRole b < 3 ∧ fs1.overmarsRole b < 3 ∧
                fs1.liveRole b ≠ fs1.overmarsRole b := hc.roles_valid b hb
            rw [fastDeleteMoveSlices_rebSliceIdx n_max b loc_del loc_last _ fs1 hroles1] at hlk
            have hr_eq1 : fs1.rebSliceIdx b = fs.rebSliceIdx b := rfl
            have hfp_eq1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last =
                fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := rfl
            rw [hr_eq1, hfp_eq1] at hlk
            have hins_le8 : fs.rebInsCount ≤ 8 * (scaleWhp n_max) ^ 12 := by
              have hcnt3 := (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
              have hL2 := two_le_scaleWhp n_max
              have : 4096 ≤ (scaleWhp n_max) ^ 12 := by
                calc 4096 = 2 ^ 12 := by norm_num
                  _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
              rcases hcur_r with ⟨_, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
            have hfp_cl_lt : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last <
                2 ^ fpBitsWhp n_max := by
              dsimp only [FastState.fpAt]
              by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
              · rw [dite_eq_left hs]
                by_cases hu : fs.keyValAt c U n_max θ.1 b loc_last < U
                · rw [dite_eq_left hu]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ ⟨_, hu⟩
                · rw [dite_eq_right hu]; exact Nat.two_pow_pos _
              · rw [dite_eq_right hs]; exact Nat.two_pow_pos _
            have hrm_prev : rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) =
                some prev_loc := by
              dsimp only [fs1] at hlk
              rw [fastDeleteErase_rebSliceIdx _ _ _ _ _ _ _ _ (hc.roles_valid b hb)] at hlk
              split_ifs at hlk
              · have hfp_d_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u < 2 ^ fpBitsWhp n_max := by
                  dsimp only [fpOfSalt]
                  by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
                  · rw [dite_eq_left hs]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
                  · rw [dite_eq_right hs]; exact Nat.two_pow_pos _
                have hvd := hvr0.delete_spec hc.hth hins_le8 hfp_d_lt
                rw [hvd.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
                by_cases heq_fp : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last =
                    fpOfSalt c U n_max θ.2 fs.rebCandSalt u
                · change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
                    (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
                  rw [heq_fp, Function.update_self] at hlk; cases hlk
                · change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
                    (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
                  rwa [Function.update_of_ne heq_fp] at hlk
              · rwa [hvr0.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
            obtain ⟨hprev_min, _, hfp_prev⟩ := (hrr0.2 _ prev_loc).mp hrm_prev
            have hprev_lt_sc : prev_loc < fs.rebScanCursor :=
              hprev_min.trans_le (Nat.min_le_right _ _)
            have hprev_lt_cnt : prev_loc < fs.bktCount b :=
              hprev_min.trans_le (Nat.min_le_left _ _)
            obtain ⟨hm₁, hfb₁⟩ := hc.mem_dom_of_loc hb hprev_lt_cnt
            obtain ⟨hm₂, hfb₂⟩ := hc.mem_dom_of_loc hb hloc_last
            let u₁ : Fin U :=
              ⟨fs.keyValAt c U n_max θ.1 b prev_loc,
               (hc.active_item b hb prev_loc hprev_lt_cnt).1⟩
            let u₂ : Fin U :=
              ⟨fs.keyValAt c U n_max θ.1 b loc_last,
               (hc.active_item b hb loc_last hloc_last).1⟩
            have hw₁ : u₁ ∈ W_keys.filter (fun w =>
                feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
                  fs.dirtyBuckets fs.dirtyIdx) :=
              mem_filter.mpr ⟨hdom_sub hm₁, hfb₁.trans hdb_eq.symm⟩
            have hw₂ : u₂ ∈ W_keys.filter (fun w =>
                feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
                  fs.dirtyBuckets fs.dirtyIdx) :=
              mem_filter.mpr ⟨hdom_sub hm₂, hfb₂.trans hdb_eq.symm⟩
            have hf₁ : fs.fpAt c U n_max θ fs.rebCandSalt b prev_loc =
                fpHash c U n_max θ.2 s_opt u₁ := by
              dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₁.isLt, u₁]
            have hf₂ : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last =
                fpHash c U n_max θ.2 s_opt u₂ := by
              dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₂.isLt, u₂]
            have hu_eq : u₁ = u₂ := hs_opt_inj hw₁ hw₂ (hf₁.symm.trans (hfp_prev.trans hf₂))
            have hkv_eq : fs.keyValAt c U n_max θ.1 b prev_loc =
                fs.keyValAt c U n_max θ.1 b loc_last := congrArg Fin.val hu_eq
            have hq₁ := (hc.active_item b hb prev_loc hprev_lt_cnt).2.2.1
            have hq₂ := (hc.active_item b hb loc_last hloc_last).2.2.1
            have hl_eq := hc.quot_inj b hb prev_loc hprev_lt_cnt loc_last hloc_last
              (hq₁.symm.trans (hkv_eq ▸ hq₂))
            change loc_del < fs.rebScanCursor at hld_sc
            change ¬(loc_last < fs.rebScanCursor) at hll_sc
            omega
        · exact hc_le_s
        · exact hc_le_s
      · rw [ite_eq_right hlt_dl]; exact hc_le_s

private theorem fastInsert_some_and_clean_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys W_ins BadIns : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hcw : CleanWindowFast c U V n_max θ W_keys BadIns fs dict)
    {u : Fin U} {v : ℕ} (hval : Dynamic.valid V n_max dict (.insert u v))
    (hu_ins : u ∈ W_ins)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hu_W : u ∈ W_keys)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    (hbal_nxt : BalancedBuckets U n_max (bktHash c U n_max θ.1)
      (Dictionary.dom (Dynamic.step dict (.insert u v)).1))
    (hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * rIndepWhp c n_max) :
    ∃ fs1,
      fastInsert c U n_max θ fs u v = some fs1 ∧
      fs1.epochClock = fs.epochClock ∧
      (fs1.buf fs1.curEp).itemAlloc ≤
        #(BadIns.filter fun x =>
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs1.buf fs1.curEp)
            (fpReducedKey c U n_max θ.2 x)) ∧
      stageWorkRemaining c n_max fs1 = stageWorkRemaining c n_max fs ∧
      SaltBoundAt c U n_max θ W_keys fs1 := by
  have hv := hcw.valid
  have hc := hv.toCore
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) h1 u.val
  have hom_m := fun s => overmarsStep_meta c U n_max b θ s
  dsimp only [fastInsert]
  cases hfl : fastFindLoc c U n_max θ fs u with
  | some loc =>
    dsimp only
    set fs' : FastState :=
      { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v }
    obtain ⟨h1m, h2m, h3m, h4m, h5m, h6m, h7m, h8m, h9m, h10m⟩ := hom_m fs'
    refine ⟨overmarsStep c U n_max θ b fs', rfl, h1m, ?_, ?_, ?_⟩
    · rw [h3m, h2m]; exact hcw.buf_alloc
    · exact stageWorkRemaining_eq_of_meta c n_max h4m h5m h6m h7m h9m h10m
        (by dsimp only [FastState.oldEp]; rw [h3m, h2m])
    · intro hs2 hdi; rw [h4m] at hs2; rw [h7m, h6m] at hdi
      rw [h8m, h7m, h9m]; exact hcw.salt_bound hs2 hdi
  | none =>
    dsimp only
    have hfl_sp := hv.fastFindLoc_spec u
    dsimp only at hfl_sp; rw [hfl] at hfl_sp
    have hu_ndom : u ∉ Dictionary.dom dict := Dictionary.notMem_dom_iff.mpr hfl_sp
    -- 1. Guard 1 (`totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0)`) is false:
    have hg1 : ¬(totalLocalCoordsWhp n_max ≤ fs.bktCount b ∨
        (capFrontWhp n_max ≤ fs.bktCount b ∧ fs.poolFreeTop = 0)) := by
      set dict' := (Dynamic.step dict (.insert u v)).1
      have hdom' : Dictionary.dom dict' = insert u (Dictionary.dom dict) := by
        ext x
        by_cases hx : x = u
        · subst hx; simp [dict', Dictionary.dom]
        · simp [dict', Dictionary.dom, hx]
      have hcard_dom' : #(Dictionary.dom dict') ≤ n_max := by
        rw [hdom', Finset.card_insert_of_notMem hu_ndom]
        rcases hval.1 with hlt | hsome
        · omega
        · rw [hfl_sp] at hsome; cases hsome
      let X' : Fin (numBucketsWhp n_max) → ℕ :=
        fun b' => #((Dictionary.dom dict').filter fun w =>
          feistelBucket (bWhp n_max) h1 w.val = b'.val)
      have hX'_eq : ∀ b' : Fin (numBucketsWhp n_max),
          X' b' = if b'.val = b then fs.bktCount b + 1 else fs.bktCount b'.val := by
        intro b'
        dsimp only [X', h1]
        rw [hdom', Finset.filter_insert]
        by_cases hbb : b = b'.val
        · have heq : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b'.val := hbb
          rw [ite_eq_left heq, Finset.card_insert_of_notMem
            (fun hm => hu_ndom (mem_filter.mp hm).1), ite_eq_left hbb.symm, ← hbb,
            hc.bktCount_eq_card_filter hb]
        · have hne : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val ≠ b'.val := hbb
          rw [ite_eq_right hne, ite_eq_right (Ne.symm hbb), hc.bktCount_eq_card_filter b'.isLt]
      have hsum_X' : ∑ b', X' b' = #(Dictionary.dom dict') := by
        have h1_sum : ∀ w ∈ Dictionary.dom dict', (1 : ℕ) =
            ∑ b' : Fin (numBucketsWhp n_max),
              if feistelBucket (bWhp n_max) h1 w.val = b'.val then 1 else 0 := by
          intro w _
          let bw : Fin (numBucketsWhp n_max) :=
            ⟨feistelBucket (bWhp n_max) h1 w.val, feistelBucket_lt (bWhp n_max) h1 w.val⟩
          rw [Fintype.sum_eq_single bw]
          · simp [bw]
          · intro b' hb'; simp [show feistelBucket (bWhp n_max) h1 w.val ≠ b'.val from
              fun h => hb' (Fin.ext h.symm)]
        calc ∑ b' : Fin (numBucketsWhp n_max), X' b'
            = ∑ b' : Fin (numBucketsWhp n_max), ∑ w ∈ Dictionary.dom dict',
                if feistelBucket (bWhp n_max) h1 w.val = b'.val then 1 else 0 :=
              Fintype.sum_congr _ _ fun b' => by dsimp only [X']; rw [Finset.card_filter]
          _ = ∑ w ∈ Dictionary.dom dict', ∑ b' : Fin (numBucketsWhp n_max),
                if feistelBucket (bWhp n_max) h1 w.val = b'.val then 1 else 0 := Finset.sum_comm
          _ = ∑ _w ∈ Dictionary.dom dict', 1 := Finset.sum_congr rfl fun w hw => (h1_sum w hw).symm
          _ = #(Dictionary.dom dict') := by simp
      obtain ⟨hcb_lt, _, hpool_le⟩ := sum_sub_capFront_le_poolSize hc.hth X'
        (hsum_X'.trans_le hcard_dom')
        (fun b' => by rw [hsum_X']; exact (hbal_nxt b').1)
        (fun b' => by rw [hsum_X']; exact (hbal_nxt b').2)
      have hb_cb := hcb_lt ⟨b, hb⟩
      rw [hX'_eq ⟨b, hb⟩, ite_eq_left rfl] at hb_cb
      have hcb_pos : 0 < capBackWhp n_max := by
        unfold capBackWhp; have := scaleWhp_pos n_max; positivity
      have hX_lt_tot : fs.bktCount b < totalLocalCoordsWhp n_max := by
        unfold totalLocalCoordsWhp; omega
      rintro (hge | ⟨hcf_le, htop0⟩)
      · omega
      · have hsum_add1 :
            (∑ b' ∈ range (numBucketsWhp n_max), (fs.bktCount b' - capFrontWhp n_max)) + 1 =
              ∑ b' : Fin (numBucketsWhp n_max), (X' b' - capFrontWhp n_max) := by
          rw [← Fin.sum_univ_eq_sum_range]
          have hpt : ∀ b' : Fin (numBucketsWhp n_max),
              X' b' - capFrontWhp n_max =
                (fs.bktCount b'.val - capFrontWhp n_max) + (if b' = ⟨b, hb⟩ then 1 else 0) := by
            intro b'; rw [hX'_eq b']
            by_cases hbb : b' = ⟨b, hb⟩
            · subst hbb; simp; omega
            · have hv_ne : b'.val ≠ b := fun h => hbb (Fin.ext h)
              simp [hbb, hv_ne]
          simp_rw [hpt]
          rw [Finset.sum_add_distrib]
          simp
        have hcons := hc.pool_conservation
        omega
    rw [ite_eq_right hg1]
    -- 2. Guard 2 (Stage-1 `rKey` collision in `buf curEp` or `buf oldEp`) is false:
    set rKey := fpReducedKey c U n_max θ.2 u
    have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
    have hg2 : ¬((bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome = true ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome = true)) := by
      rintro (hcur_some | ⟨hs3, hold_some⟩)
      · obtain ⟨_, _, cm, hvc, hrc⟩ := hc.bufCur_valid
        cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey with
        | none => rw [hlk] at hcur_some; cases hcur_some
        | some bp0 =>
          rcases bp0 with ⟨b', l'⟩
          rw [← hvc.2.2.2.1 _ hrk_lt] at hlk
          obtain ⟨hb', hl', _, hrk_eq⟩ := (hrc.2 _ b' l').mp hlk
          obtain ⟨hm', _⟩ := hc.mem_dom_of_loc hb' hl'
          let u' : Fin U := ⟨fs.keyValAt c U n_max θ.1 b' l', (hc.active_item b' hb' l' hl').1⟩
          have hrk_u' : fpReducedKey c U n_max θ.2 u' = rKey := by
            dsimp only [FastState.rKeyAt] at hrk_eq
            simpa [u'.isLt, u'] using hrk_eq
          have hu_eq : u' = u := hinj_rkey (hdom_sub hm') hu_W hrk_u'
          exact hu_ndom (hu_eq ▸ hm')
      · have hbo := hc.bufOld_valid; rw [ite_eq_left hs3] at hbo
        obtain ⟨_, _, om, hvo, hro⟩ := hbo
        cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
        | none => rw [hlk] at hold_some; cases hold_some
        | some bp0 =>
          rcases bp0 with ⟨b', l'⟩
          rw [← hvo.2.2.2.1 _ hrk_lt] at hlk
          obtain ⟨hb', hl', _, hrk_eq⟩ := (hro.2 _ b' l').mp hlk
          obtain ⟨hm', _⟩ := hc.mem_dom_of_loc hb' hl'
          let u' : Fin U := ⟨fs.keyValAt c U n_max θ.1 b' l', (hc.active_item b' hb' l' hl').1⟩
          have hrk_u' : fpReducedKey c U n_max θ.2 u' = rKey := by
            dsimp only [FastState.rKeyAt] at hrk_eq
            simpa [u'.isLt, u'] using hrk_eq
          have hu_eq : u' = u := hinj_rkey (hdom_sub hm') hu_W hrk_u'
          exact hu_ndom (hu_eq ▸ hm')
    rw [ite_eq_right hg2]
    -- 3. Guard 3 (`2 * rIndepWhp ≤ itemAlloc`) is false since `itemAlloc ≤ #BadIns`:
    have hia_lt : (fs.buf fs.curEp).itemAlloc < 2 * rIndepWhp c n_max :=
      hcw.buf_alloc.trans_lt ((Finset.card_filter_le _ _).trans_lt hbad_lt)
    have hg3 : ¬((btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true ∧
        (!bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey) = true ∧
        2 * rIndepWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc) := by
      rintro ⟨_, _, hge⟩; omega
    rw [ite_eq_right hg3]
    -- Now `fastInsert` returns `some (overmarsStep ... fsInserted)`!
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · exact (hom_m _).1.trans (by
        by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
        · rw [ite_eq_left hfpc]
        · rw [ite_eq_right hfpc])
    · -- Check `(fs1.buf fs1.curEp).itemAlloc ≤ #(AllocBadKeys)`!
      rw [(hom_m _).2.2.1, (hom_m _).2.1]
      by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
      · rw [ite_eq_left hfpc]
        change (Function.update fs.buf fs.curEp
            (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b (fs.bktCount b))
            fs.curEp).itemAlloc ≤
          #(BadIns.filter fun x =>
            bufEverPresent (cTabWhp c) (bCharWhp n_max)
              (Function.update fs.buf fs.curEp
                (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b (fs.bktCount b))
                fs.curEp)
              (fpReducedKey c U n_max θ.2 x))
        rw [Function.update_self]
        -- Show `u ∈ BadIns` from `hfpc`!
        have hu_bad : u ∈ BadIns := by
          obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b hb
          have hs_b := hc.bktSalt_lt b hb
          have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
            dsimp only [fpOfSalt]; simp [hs_b, fpHash_lt]
          cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u) with
          | none => rw [hlk] at hfpc; cases hfpc
          | some loc_v =>
            rw [hvl.lookup_eq hc.hth (hv.liveInsCount_le hb) hfp_lt] at hlk
            obtain ⟨hlv, _, hfp_v⟩ := (hrl.2 _ loc_v).mp hlk
            obtain ⟨hm_v, hfb_v⟩ := hc.mem_dom_of_loc hb hlv
            let y : Fin U := ⟨fs.keyValAt c U n_max θ.1 b loc_v, (hc.active_item b hb loc_v hlv).1⟩
            have hy_ne : u ≠ y := fun h => hu_ndom (h ▸ hm_v)
            refine hbad_def u hu_ins ⟨y, mem_filter.mpr ⟨hdom_sub hm_v, hfb_v⟩, hy_ne,
              ⟨fs.bktSalt b, hs_b⟩, ?_⟩
            have h1_fp : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u =
                fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs_b⟩ u := by
              dsimp only [fpOfSalt]; simp [hs_b]
            have h2_fp : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_v =
                fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs_b⟩ y := by
              dsimp only [FastState.fpAt]; simp [hs_b, y.isLt, y]
            exact h1_fp.symm.trans (hfp_v.symm.trans h2_fp)
        obtain ⟨_, _, _, hvc, _⟩ := hc.bufCur_valid
        have hins := hvc.insert_spec (b := b) (loc := fs.bktCount b) hrk_lt
        set tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b (fs.bktCount b)
        have hsub_ev : BadIns.filter (fun x =>
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
              (fpReducedKey c U n_max θ.2 x)) ⊆
            BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) tr'
                (fpReducedKey c U n_max θ.2 x)) := by
          intro x hx
          rw [mem_filter] at hx ⊢
          refine ⟨hx.1, ?_⟩
          rw [hins.2.2.2.2.2.1 _ (fpReducedKey_lt c U n_max θ.2 x)]
          split_ifs
          · rfl
          · exact hx.2
        by_cases hev : bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = true
        · rw [(hins.2.2.2.2.2.2.1 hev).2]
          exact hcw.buf_alloc.trans (Finset.card_le_card hsub_ev)
        · have hu_nin : u ∉ BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                (fpReducedKey c U n_max θ.2 x)) := by
            rw [mem_filter]; rintro ⟨_, ht⟩; exact hev ht
          have hu_in' : u ∈ BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) tr'
                (fpReducedKey c U n_max θ.2 x)) := by
            rw [mem_filter]; refine ⟨hu_bad, ?_⟩
            rw [hins.2.2.2.2.2.1 _ hrk_lt, ite_eq_left rfl]
          have hins_sub : insert u (BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                (fpReducedKey c U n_max θ.2 x))) ⊆
              BadIns.filter (fun x =>
                bufEverPresent (cTabWhp c) (bCharWhp n_max) tr'
                  (fpReducedKey c U n_max θ.2 x)) :=
            Finset.insert_subset_iff.mpr ⟨hu_in', hsub_ev⟩
          calc tr'.itemAlloc
              ≤ (fs.buf fs.curEp).itemAlloc + 1 := hins.2.2.2.2.1
            _ ≤ #(BadIns.filter fun x =>
                  bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                    (fpReducedKey c U n_max θ.2 x)) + 1 := Nat.add_le_add_right hcw.buf_alloc 1
            _ = #(insert u (BadIns.filter fun x =>
                  bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                    (fpReducedKey c U n_max θ.2 x))) :=
                (Finset.card_insert_of_notMem hu_nin).symm
            _ ≤ _ := Finset.card_le_card hins_sub
      · rw [ite_eq_right hfpc]
        exact hcw.buf_alloc
    · have hne_ep : fs.oldEp ≠ fs.curEp := by
        dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
      have hwk_i : ∀ (s_i : FastState),
          s_i.rebStage = fs.rebStage → s_i.stageCursor = fs.stageCursor →
          s_i.dirtyCount = fs.dirtyCount → s_i.dirtyIdx = fs.dirtyIdx →
          s_i.rebCandSalt = fs.rebCandSalt → s_i.rebScanCursor = fs.rebScanCursor →
          (s_i.buf s_i.oldEp).nodeAlloc = (fs.buf fs.oldEp).nodeAlloc →
          stageWorkRemaining c n_max (overmarsStep c U n_max θ b s_i) =
            stageWorkRemaining c n_max fs := by
        intro s_i r1 r2 r3 r4 r5 r6 r7
        obtain ⟨_, q2, q3, q4, q5, q6, q7, _, q9, q10⟩ := hom_m s_i
        refine stageWorkRemaining_eq_of_meta c n_max (q4.trans r1) (q5.trans r2)
          (q6.trans r3) (q7.trans r4) (q9.trans r5) (q10.trans r6) ?_
        have hold_eq : (overmarsStep c U n_max θ b s_i).oldEp = s_i.oldEp := by
          dsimp only [FastState.oldEp]; rw [q2]
        rw [hold_eq, q3]; exact r7
      by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
      · rw [ite_eq_left hfpc]
        refine hwk_i _ rfl rfl rfl rfl rfl rfl ?_
        change (Function.update fs.buf fs.curEp _ fs.oldEp).nodeAlloc = _
        rw [Function.update_of_ne hne_ep]
      · rw [ite_eq_right hfpc]
        exact hwk_i _ rfl rfl rfl rfl rfl rfl rfl
    · have hst_i : ∀ (s_i : FastState),
          s_i.rebStage = fs.rebStage → s_i.dirtyCount = fs.dirtyCount →
          s_i.dirtyIdx = fs.dirtyIdx → s_i.dirtyBuckets = fs.dirtyBuckets →
          s_i.rebCandSalt = fs.rebCandSalt →
          SaltBoundAt c U n_max θ W_keys (overmarsStep c U n_max θ b s_i) := by
        intro s_i r1 r2 r3 r4 r5
        obtain ⟨_, _, _, q4, _, q6, q7, q8, q9, _⟩ := hom_m s_i
        intro hs2 hdi
        rw [q4, r1] at hs2; rw [q7, q6, r3, r2] at hdi
        rw [q8, q7, q9, r4, r3, r5]
        exact hcw.salt_bound hs2 hdi
      by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
      · rw [ite_eq_left hfpc]; exact hst_i _ rfl rfl rfl rfl rfl
      · rw [ite_eq_right hfpc]; exact hst_i _ rfl rfl rfl rfl rfl

/-- Inside the trailing window under `GoodSeedOnWindow`, every admissible operation `op` from a
`CleanWindowFast` state succeeds with `fastStepPure = some (fs', res)` and preserves
`CleanWindowFast`. -/
theorem CleanWindowFast.step {c U V n_max : ℕ} (hnU : n_max ≤ U) {θ : SeedWhp c U n_max}
    {W_keys W_ins BadIns : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hcw : CleanWindowFast c U V n_max θ W_keys BadIns fs dict)
    {op : Dynamic.Op U} (hval : Dynamic.valid V n_max dict op)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hdom_nxt : (Dictionary.dom (Dynamic.step dict op).1 : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hop_ins : ∀ u v, op = .insert u v → u ∈ W_ins ∧ u ∈ W_keys)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    (hbal_nxt : BalancedBuckets U n_max (bktHash c U n_max θ.1)
      (Dictionary.dom (Dynamic.step dict op).1))
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U)))
    (hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * rIndepWhp c n_max) :
    ∃ fs' res,
      fastStepPure c U n_max θ fs op = some (fs', res) ∧
      CleanWindowFast c U V n_max θ W_keys BadIns fs' (Dynamic.step dict op).1 := by
  have hv := hcw.valid
  cases op with
  | query u =>
    obtain ⟨fs', htick, hv', hw', hs', hbuf_or⟩ :=
      epochTick_some_of_work_bound hv.toCore hv.overmars_valid hv.stage_valid.toPreTick
        hdom_sub hsalt_all hcw.salt_bound hcw.work_le
    refine ⟨fs', fastQuery c U n_max θ fs u, ?_, ⟨hv', ?_, hw', hs'⟩⟩
    · dsimp only [fastStepPure]; rw [htick]
    · rcases hbuf_or with hbeq | hia0
      · rw [hbeq]; exact hcw.buf_alloc
      · rw [hia0]; exact Nat.zero_le _
  | delete u =>
    obtain ⟨hc1, hom1, hpre1, _⟩ := hv.fastDelete_spec u
    obtain ⟨hclk1, hep1, hia1, hev1, hw1_le, hs1⟩ :=
      fastDelete_clean_props hv hdom_sub hcw.salt_bound u
    obtain ⟨fs', htick, hv', hw', hs', hbuf_or⟩ :=
      epochTick_some_of_work_bound hc1 hom1 hpre1 hdom_nxt hsalt_all hs1
        (by have := hcw.work_le; omega)
    refine ⟨fs', none, ?_, ⟨hv', ?_, hw', hs'⟩⟩
    · dsimp only [fastStepPure]; rw [htick]
    · rcases hbuf_or with hbeq | hia0
      · rw [hbeq, hia1]
        refine hcw.buf_alloc.trans (le_of_eq ?_)
        congr 1; ext x; rw [mem_filter, mem_filter]
        exact and_congr_right fun _ => by rw [← hev1 _ (fpReducedKey_lt c U n_max θ.2 x)]
      · rw [hia0]; exact Nat.zero_le _
  | insert u v =>
    obtain ⟨hu_ins, hu_W⟩ := hop_ins u v rfl
    obtain ⟨fs1, hins, hclk1, hba1, hw1_eq, hs1⟩ :=
      fastInsert_some_and_clean_props hcw hval hu_ins hdom_sub hu_W hinj_rkey hbal_nxt
        hbad_def hbad_lt
    obtain ⟨hc1, hom1, hst1, _⟩ := hv.fastInsert_spec hnU hval hins
    obtain ⟨fs', htick, hv', hw', hs', hbuf_or⟩ :=
      epochTick_some_of_work_bound hc1 hom1 hst1.toPreTick hdom_nxt hsalt_all hs1
        (by rw [hclk1, hw1_eq]; exact hcw.work_le)
    refine ⟨fs', none, ?_, ⟨hv', ?_, hw', hs'⟩⟩
    · dsimp only [fastStepPure]; rw [hins]; dsimp only; rw [htick]
    · rcases hbuf_or with hbeq | hia0
      · rw [hbeq]; exact hba1
      · rw [hia0]; exact Nat.zero_le _

/-! ## Section 3: Burn-in budget (`HasBurnInBudget`) and fast-path probability theorem -/

private def HasBurnInBudget (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (W_keys BadIns : Finset (Fin U)) (st : WhpDictState) (dict : State U) (b : ℕ) : Prop :=
  (∃ fs, st = .fast fs ∧ CleanWindowFast c U V n_max θ W_keys BadIns fs dict) ∨
  (1 ≤ b ∧ ValidWhpState c U V n_max θ st dict ∧
    match st with
    | .small _ => False
    | .fallback _ => True
    | .fast fs => qEpochWhp n_max - fs.epochClock ≤ b)

private theorem HasBurnInBudget.of_validWhpState {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) {θ : SeedWhp c U n_max}
    {W_keys BadIns : Finset (Fin U)} {st : WhpDictState} {dict : State U}
    (hv : ValidWhpState c U V n_max θ st dict) :
    HasBurnInBudget c U V n_max θ W_keys BadIns st dict (qEpochWhp n_max) := by
  have hq_pos : 1 ≤ qEpochWhp n_max := by
    unfold qEpochWhp; exact Nat.one_le_pow 18 _ (scaleWhp_pos n_max)
  right
  refine ⟨hq_pos, hv, ?_⟩
  cases st with
  | small sm => exact absurd hv.1 (not_lt.mpr hth)
  | fallback _ => trivial
  | fast fs => exact Nat.sub_le _ _


private theorem tickStage_epochClock (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) :
    (tickStage c U n_max θ fs).epochClock = fs.epochClock := by
  dsimp only [tickStage]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0]; dsimp only [tickStage0]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt]
      cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · dsimp only; split_ifs <;> rfl
      · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
    · rw [ite_eq_right hlt]
  rw [ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1]; dsimp only [tickStage1, tickStage1Fin]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt]
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · dsimp only; split_ifs <;> rfl
        · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
      · rw [ite_eq_right hdone]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · rfl
        · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
    · rw [ite_eq_right hlt]; split_ifs <;> rfl
  rw [ite_eq_right hs1]
  by_cases hs2 : fs.rebStage = 2
  · rw [ite_eq_left hs2]; dsimp only [tickStage2, tickStage2Swap]
    by_cases hd : fs.dirtyIdx < fs.dirtyCount
    · rw [ite_eq_left hd]
      by_cases hcs : fs.rebCandSalt < sMaxWhp c n_max
      · rw [ite_eq_left hcs]
        have hm := (rebScanSteps_meta c U n_max (fs.dirtyBuckets fs.dirtyIdx) θ 16 fs).1
        split_ifs <;> exact hm
      · rw [ite_eq_right hcs]
    · rw [ite_eq_right hd]
  rw [ite_eq_right hs2]
  by_cases hs3 : fs.rebStage = 3
  · rw [ite_eq_left hs3]; dsimp only [tickStage3]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt]
      cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · dsimp only; split_ifs <;> rfl
      · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
    · rw [ite_eq_right hlt]
  rw [ite_eq_right hs3]
  by_cases hs4 : fs.rebStage = 4
  · rw [ite_eq_left hs4]; rfl
  rw [ite_eq_right hs4]

private theorem tickStage_rollover_itemAlloc_zero {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hs5 : (tickStage c U n_max θ fs).rebStage = 5) :
    let fs1 := tickStage c U n_max θ fs
    (fs1.buf (1 - fs1.curEp)).itemAlloc = 0 := by
  dsimp only [tickStage] at hs5 ⊢
  by_cases h0 : fs.rebStage = 0
  · rw [ite_eq_left h0] at hs5; dsimp only [tickStage0] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt] at hs5
      cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
      · rename_i p; rcases p with ⟨_, _⟩
        rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
    · rw [ite_eq_right hlt] at hs5; cases hs5
  rw [ite_eq_right h0] at hs5 ⊢
  by_cases h1 : fs.rebStage = 1
  · rw [ite_eq_left h1] at hs5; dsimp only [tickStage1, tickStage1Fin] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt] at hs5
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone] at hs5
        cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · rw [hchk] at hs5; dsimp only at hs5; split_ifs at hs5 <;> cases hs5
        · rename_i p; rcases p with ⟨_, _⟩
          rw [hchk] at hs5; dsimp only at hs5; split_ifs at hs5 <;> cases hs5
      · rw [ite_eq_right hdone] at hs5
        cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · rw [hchk] at hs5; exact absurd hs5 hne5
        · rename_i p; rcases p with ⟨_, _⟩
          rw [hchk] at hs5; dsimp only at hs5
          split_ifs at hs5 <;> exact absurd hs5 hne5
    · rw [ite_eq_right hlt] at hs5; split_ifs at hs5 <;> cases hs5
  rw [ite_eq_right h1] at hs5 ⊢
  by_cases h2 : fs.rebStage = 2
  · rw [ite_eq_left h2] at hs5; dsimp only [tickStage2, tickStage2Swap] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hd : fs.dirtyIdx < fs.dirtyCount
    · rw [ite_eq_left hd] at hs5
      by_cases hcs : fs.rebCandSalt < sMaxWhp c n_max
      · rw [ite_eq_left hcs] at hs5
        have hm := (rebScanSteps_meta c U n_max (fs.dirtyBuckets fs.dirtyIdx) θ 16 fs).2.2.2.1
        have hne5' :
            (rebScanSteps c U n_max θ (fs.dirtyBuckets fs.dirtyIdx) 16 fs).rebStage ≠ 5 := by
          omega
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5'
      · rw [ite_eq_right hcs] at hs5; exact absurd hs5 hne5
    · rw [ite_eq_right hd] at hs5; cases hs5
  rw [ite_eq_right h2] at hs5 ⊢
  by_cases h3 : fs.rebStage = 3
  · rw [ite_eq_left h3] at hs5; dsimp only [tickStage3] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt] at hs5
      cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
      · rename_i p; rcases p with ⟨_, _⟩
        rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
    · rw [ite_eq_right hlt] at hs5; cases hs5
  rw [ite_eq_right h3] at hs5 ⊢
  by_cases h4 : fs.rebStage = 4
  · rw [ite_eq_left h4] at hs5 ⊢; dsimp only [tickStage4] at hs5 ⊢
    by_cases hle8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
    · have hbo := hc.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left h4] at hbo
      have hia0 := (hbo.2.1.clearSteps_spec (cTabWhp c) (bCharWhp n_max) 8 hle8).2.2
      change (Function.update fs.buf fs.oldEp (bufClearSteps 8 (fs.buf fs.oldEp))
        fs.oldEp).itemAlloc = 0
      rw [Function.update_self]; exact hia0
    · rw [decide_eq_false hle8, ite_eq_right Bool.false_ne_true] at hs5; cases hs5
  rw [ite_eq_right h4] at hs5 ⊢
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_right h4] at hbo
  exact hbo.2.2.2

private theorem epochTick_clean_or_clock {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys BadIns : Finset (Fin U)} {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hv' : ValidFastState c U V n_max θ fs' dict)
    (htick : epochTick c U n_max θ fs = some fs') :
    CleanWindowFast c U V n_max θ W_keys BadIns fs' dict ∨
    (fs'.epochClock = fs.epochClock + 1 ∧ fs.epochClock + 1 < qEpochWhp n_max) := by
  rw [epochTick_eq_tickStage] at htick
  set fs1 := tickStage c U n_max θ fs
  have hclk1 : fs1.epochClock = fs.epochClock := tickStage_epochClock c U n_max θ fs
  dsimp only [tickRollover] at htick
  by_cases hroll : qEpochWhp n_max ≤ fs1.epochClock + 1
  · rw [ite_eq_left hroll] at htick
    by_cases hs5 : fs1.rebStage = 5
    · rw [ite_eq_left hs5] at htick
      injection htick with hfs'
      rw [← hfs'] at hv' ⊢
      exact Or.inl (CleanWindowFast.of_clean_fast hv'
        (tickStage_rollover_itemAlloc_zero hc hs5) rfl (fun h => by cases h))
    · rw [ite_eq_right hs5] at htick; cases htick
  · rw [ite_eq_right hroll] at htick
    injection htick with hfs'
    rw [← hfs']
    exact Or.inr ⟨congrArg (· + 1) hclk1, by omega⟩

private theorem fastDelete_epochClock (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (u : Fin U) :
    (fastDelete c U n_max θ fs u).epochClock = fs.epochClock := by
  dsimp only [fastDelete]
  refine (overmarsStep_meta c U n_max _ θ _).1.trans ?_
  cases fastFindLoc c U n_max θ fs u with
  | none => rfl
  | some loc_del =>
    dsimp only [fastDeleteShrink, fastDeleteMoveLast, fastDeleteErase]
    by_cases hlt : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
        - 1 <;> [rw [ite_eq_left hlt]; rw [ite_eq_right hlt]]

private theorem fastInsert_epochClock {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs1 : FastState} {u : Fin U} {v : ℕ}
    (hins : fastInsert c U n_max θ fs u v = some fs1) :
    fs1.epochClock = fs.epochClock := by
  dsimp only [fastInsert] at hins
  cases hfl : fastFindLoc c U n_max θ fs u with
  | some loc =>
    rw [hfl] at hins; dsimp only at hins
    injection hins with h1; rw [← h1]
    exact (overmarsStep_meta c U n_max _ θ _).1
  | none =>
    rw [hfl] at hins; dsimp only at hins
    set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    by_cases hg1 : totalLocalCoordsWhp n_max ≤ fs.bktCount b ∨
        (capFrontWhp n_max ≤ fs.bktCount b ∧ fs.poolFreeTop = 0)
    · rw [ite_eq_left hg1] at hins; cases hins
    rw [ite_eq_right hg1] at hins
    by_cases hg2 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
          (fpReducedKey c U n_max θ.2 u)).isSome = true ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp)
            (fpReducedKey c U n_max θ.2 u)).isSome = true)
    · rw [ite_eq_left hg2] at hins; cases hins
    rw [ite_eq_right hg2] at hins
    by_cases hg3 : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true ∧
        (!bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
          (fpReducedKey c U n_max θ.2 u)) = true ∧
        2 * rIndepWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
    · rw [ite_eq_left hg3] at hins; cases hins
    rw [ite_eq_right hg3] at hins
    injection hins with h1; rw [← h1]
    refine (overmarsStep_meta c U n_max _ θ _).1.trans ?_
    by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
    · rw [ite_eq_left hfpc]
    · rw [ite_eq_right hfpc]

private theorem trySelfHeal_clean {c U V n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    {θ : SeedWhp c U n_max} {W_keys BadIns : Finset (Fin U)}
    {csr : CsrState} {dict : State U}
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    (hgood : GoodSeedOnState c U n_max θ dict) :
    ∃ fs', trySelfHeal c U n_max θ csr = .fast fs' ∧
      CleanWindowFast c U V n_max θ W_keys BadIns fs' dict := by
  obtain ⟨hv, hclean⟩ := trySelfHeal_spec hth hcsr hqv
  obtain ⟨fs', hst', hb0, _, hep0, hclk0, hstg5⟩ := hclean hgood
  rw [hst'] at hv
  refine ⟨fs', hst', CleanWindowFast.of_clean_fast hv ?_ hclk0 (by omega)⟩
  rw [hep0, hb0]; rfl

private theorem HasBurnInBudget.step {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {W_keys W_ins BadIns : Finset (Fin U)}
    {st : WhpDictState} {dict : State U} {b : ℕ}
    (hbud : HasBurnInBudget c U V n_max θ W_keys BadIns st dict b)
    {op : Dynamic.Op U} (hval : Dynamic.valid V n_max dict op)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hdom_nxt : (Dictionary.dom (Dynamic.step dict op).1 : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hop_ins : ∀ u v, op = .insert u v → u ∈ W_ins ∧ u ∈ W_keys)
    (hgood_nxt : GoodSeedOnState c U n_max θ (Dynamic.step dict op).1)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    (hbal_nxt : BalancedBuckets U n_max (bktHash c U n_max θ.1)
      (Dictionary.dom (Dynamic.step dict op).1))
    (hsalt_all : ∀ bk : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = bk.val) : Set (Fin U)))
    (hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * rIndepWhp c n_max) :
    HasBurnInBudget c U V n_max θ W_keys BadIns
      (whpStepPure c U n_max θ st op).1 (Dynamic.step dict op).1 (b - 1) := by
  rcases hbud with ⟨fs, rfl, hcw⟩ | ⟨hb_pos, hv, hrem⟩
  · obtain ⟨fs', res, hf, hcw'⟩ := CleanWindowFast.step hnU hcw hval hdom_sub hdom_nxt hop_ins
      hinj_rkey hbal_nxt hsalt_all hbad_def hbad_lt
    left
    refine ⟨fs', ?_, hcw'⟩
    dsimp only [whpStepPure]; rw [hf]
  · cases st with
    | small _ => exact absurd hrem id
    | fallback csr0 =>
      obtain ⟨hth, hcsr0, hqv0⟩ := hv
      dsimp only [whpStepPure]
      obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hval
      obtain ⟨fs', hsh, hcw'⟩ := trySelfHeal_clean hth hcsr1 hqv1 hgood_nxt
      exact Or.inl ⟨fs', hsh, hcw'⟩
    | fast fs =>
      change qEpochWhp n_max - fs.epochClock ≤ b at hrem
      dsimp only [whpStepPure]
      cases hf : fastStepPure c U n_max θ fs op with
      | none =>
        dsimp only
        obtain ⟨hcsr0, hqv0⟩ := hv.fastToCsr_spec
        obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hval
        obtain ⟨fs', hsh, hcw'⟩ := trySelfHeal_clean hv.hth hcsr1 hqv1 hgood_nxt
        exact Or.inl ⟨fs', hsh, hcw'⟩
      | some p =>
        rcases p with ⟨fs', res⟩
        dsimp only
        have hv' := (hv.fastStepPure_spec hnU hval hf).1
        have hor : CleanWindowFast c U V n_max θ W_keys BadIns fs' (Dynamic.step dict op).1 ∨
            (fs'.epochClock = fs.epochClock + 1 ∧ fs.epochClock + 1 < qEpochWhp n_max) := by
          cases op with
          | query u =>
            dsimp only [fastStepPure] at hf
            cases ht : epochTick c U n_max θ fs with
            | none => rw [ht] at hf; cases hf
            | some fs2 =>
              rw [ht] at hf; injection hf with hp; injection hp with hfs2 _
              rw [← hfs2] at hv' ⊢
              exact epochTick_clean_or_clock hv.toCore hv' ht
          | delete u =>
            dsimp only [fastStepPure] at hf
            have hc1 := (hv.fastDelete_spec u).1
            have hclk1 := fastDelete_epochClock c U n_max θ fs u
            cases ht : epochTick c U n_max θ (fastDelete c U n_max θ fs u) with
            | none => rw [ht] at hf; cases hf
            | some fs2 =>
              rw [ht] at hf; injection hf with hp; injection hp with hfs2 _
              rw [← hfs2] at hv' ⊢
              rcases epochTick_clean_or_clock hc1 hv' ht with hcw' | ⟨hc2, hlt2⟩
              · exact Or.inl hcw'
              · rw [hclk1] at hc2 hlt2; exact Or.inr ⟨hc2, hlt2⟩
          | insert u v =>
            dsimp only [fastStepPure] at hf
            cases hi : fastInsert c U n_max θ fs u v with
            | none => rw [hi] at hf; cases hf
            | some fs1 =>
              rw [hi] at hf; dsimp only at hf
              have hc1 := (hv.fastInsert_spec hnU hval hi).1
              have hclk1 := fastInsert_epochClock hi
              cases ht : epochTick c U n_max θ fs1 with
              | none => rw [ht] at hf; cases hf
              | some fs2 =>
                rw [ht] at hf; injection hf with hp; injection hp with hfs2 _
                rw [← hfs2] at hv' ⊢
                rcases epochTick_clean_or_clock hc1 hv' ht with hcw' | ⟨hc2, hlt2⟩
                · exact Or.inl hcw'
                · rw [hclk1] at hc2 hlt2; exact Or.inr ⟨hc2, hlt2⟩
        rcases hor with hcw' | ⟨hclk', hlt_q⟩
        · exact Or.inl ⟨fs', rfl, hcw'⟩
        · exact Or.inr ⟨by omega, hv', by dsimp only; omega⟩

private theorem spec_run_fst_eq_runOps {U V n_max : ℕ} (s : State U)
    (ops : List (Dynamic.Op U)) :
    ((Dynamic.spec U V n_max).run s ops).1 = runOps s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons o rest ih => exact ih (Dynamic.step s o).1

private theorem validOpSeq_of_validHistory {U V n_max : ℕ} {s : State U}
    {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V n_max).ValidHistory s ops) :
    ValidOpSeq V n_max s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons o rest ih => exact ⟨hvh.1, ih hvh.2⟩

private theorem validHistory_take {U V n_max : ℕ} {s : State U}
    {ops : List (Dynamic.Op U)} (k : ℕ)
    (hvh : (Dynamic.spec U V n_max).ValidHistory s ops) :
    (Dynamic.spec U V n_max).ValidHistory s (ops.take k) := by
  induction ops generalizing s k with
  | nil => simp
  | cons o rest ih =>
    cases k with
    | zero => trivial
    | succ k => exact ⟨hvh.1, ih k hvh.2⟩

private theorem mem_stateSeq_append_left {U : ℕ} (s₀ : State U)
    (l₁ l₂ : List (Dynamic.Op U)) :
    ∀ s ∈ stateSeq s₀ l₁, s ∈ stateSeq s₀ (l₁ ++ l₂) := by
  induction l₁ generalizing s₀ with
  | nil =>
    intro s hs
    simp only [stateSeq, List.mem_singleton] at hs
    subst hs; exact self_mem_stateSeq _ _
  | cons o rest ih =>
    intro s hs
    simp only [stateSeq, List.cons_append, List.mem_cons] at hs ⊢
    exact hs.imp id (ih (Dynamic.step s₀ o).1 s)

private theorem opInsKeys_append {U : ℕ} (l₁ l₂ : List (Dynamic.Op U)) :
    opInsKeys (l₁ ++ l₂) = opInsKeys l₁ ∪ opInsKeys l₂ := by
  induction l₁ with
  | nil => simp [opInsKeys]
  | cons o rest ih =>
    cases o <;> simp [opInsKeys, ih, insert_union]

private theorem HasBurnInBudget.run {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {ops : List (Dynamic.Op U)} {θ : SeedWhp c U n_max}
    (hg : GoodSeedOnWindow c U n_max ops θ)
    {BadIns : Finset (Fin U)}
    (hbad_def : ∀ x ∈ opInsKeys (windowSuffix U n_max ops),
      (∃ y ∈ (Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops)).filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * rIndepWhp c n_max) :
    ∀ (l : List (Dynamic.Op U)) {st : WhpDictState} {dict : State U} {b : ℕ},
      HasBurnInBudget c U V n_max θ
        (Dictionary.dom (windowStartState U n_max ops) ∪ opInsKeys (windowSuffix U n_max ops))
        BadIns st dict b →
      ValidOpSeq V n_max dict l →
      (∀ s ∈ stateSeq dict l,
        s ∈ stateSeq (windowStartState U n_max ops) (windowSuffix U n_max ops)) →
      opInsKeys l ⊆ opInsKeys (windowSuffix U n_max ops) →
      HasBurnInBudget c U V n_max θ
        (Dictionary.dom (windowStartState U n_max ops) ∪ opInsKeys (windowSuffix U n_max ops))
        BadIns (whpRunFrom c U n_max θ st l) (runOps dict l) (b - l.length) := by
  intro l
  induction l with
  | nil =>
    intro st dict b hbud _ _ _
    simpa [whpRunFrom, runOps] using hbud
  | cons o rest ih =>
    intro st dict b hbud hv_l hseq_sub hins_sub
    have hdict_mem := hseq_sub dict (self_mem_stateSeq dict (o :: rest))
    have hnxt_mem := hseq_sub (Dynamic.step dict o).1
      (List.mem_cons_of_mem dict (self_mem_stateSeq _ rest))
    have hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆
        ((Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops) : Finset (Fin U)) : Set (Fin U)) := by
      exact_mod_cast dom_subset_union_opInsKeys _ _ dict hdict_mem
    have hdom_nxt : (Dictionary.dom (Dynamic.step dict o).1 : Set (Fin U)) ⊆
        ((Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops) : Finset (Fin U)) : Set (Fin U)) := by
      exact_mod_cast dom_subset_union_opInsKeys _ _ _ hnxt_mem
    have hop_ins : ∀ u v, o = .insert u v →
        u ∈ opInsKeys (windowSuffix U n_max ops) ∧
        u ∈ Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops) := by
      rintro u v rfl
      have hu : u ∈ opInsKeys (windowSuffix U n_max ops) :=
        hins_sub (mem_insert_self u _)
      exact ⟨hu, mem_union_right _ hu⟩
    have hstep := HasBurnInBudget.step hnU hbud hv_l.1 hdom_sub hdom_nxt hop_ins
      (hg.goodSeedOnState_of_mem hnxt_mem) hg.1 (hg.2.1 _ hnxt_mem) hg.2.2.2.1 hbad_def hbad_lt
    have hins_rest : opInsKeys rest ⊆ opInsKeys (windowSuffix U n_max ops) := by
      refine Subset.trans ?_ hins_sub
      cases o with
      | insert u _ => exact subset_insert u _
      | query _ => exact Subset.rfl
      | delete _ => exact Subset.rfl
    have hres := ih hstep hv_l.2
      (fun s hs => hseq_sub s (List.mem_cons_of_mem dict hs)) hins_rest
    simpa only [whpRunFrom, runOps, List.length_cons, Nat.add_comm, Nat.sub_sub] using hres

private theorem whpRunFrom_small {c U n_max : ℕ} (θ : SeedWhp c U n_max) :
    ∀ (ops : List (Dynamic.Op U)) (sm : SmallDictState),
      ∃ sm', whpRunFrom c U n_max θ (.small sm) ops = .small sm' := by
  intro ops
  induction ops with
  | nil => intro sm; exact ⟨sm, rfl⟩
  | cons o rest ih =>
    intro sm
    cases o <;> exact ih _

/-- Predicate stating that on seed `θ` after history `ops_prev`, executing `op` takes the
`O_c(1)` worst-case time path (either `.small` mode when `n_max < whpThreshold c`, or `.fast` mode
with `fastStepPure = some _` when `whpThreshold c ≤ n_max`). -/
@[expose] def IsFastStepHit (c U n_max : ℕ) (ops_prev : List (Dynamic.Op U))
    (op : Dynamic.Op U) (θ : SeedWhp c U n_max) : Prop :=
  match whpRunPure c U n_max θ ops_prev with
  | .small _ => True
  | .fast fs => (fastStepPure c U n_max θ fs op).isSome = true
  | .fallback _ => False

/-- Deterministic bridge: for every `whpThreshold c ≤ n_max`, if `θ` satisfies `GoodSeedOnWindow`
on `ops_prev ++ [op]`, then `whpRunPure` reaches `.fast fs` after `ops_prev` and `fastStepPure`
succeeds (`some _`) on `op`. -/
theorem isFastStepHit_of_goodSeedOnWindow {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (hnU : n_max ≤ U)
    {ops_prev : List (Dynamic.Op U)} {op : Dynamic.Op U}
    (hvh : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (ops_prev ++ [op]))
    {θ : SeedWhp c U n_max}
    (hg : GoodSeedOnWindow c U n_max (ops_prev ++ [op]) θ) :
    IsFastStepHit c U n_max ops_prev op θ := by
  classical
  set ops := ops_prev ++ [op]
  set s_start := windowStartState U n_max ops
  set suf := windowSuffix U n_max ops
  set W_ins := opInsKeys suf
  set W_keys := Dictionary.dom s_start ∪ W_ins
  let BadIns : Finset (Fin U) := W_ins.filter fun u =>
    ∃ v ∈ W_keys.filter (fun w =>
      feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val),
      u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
        fpHash c U n_max θ.2 salt u = fpHash c U n_max θ.2 salt v
  have hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns := fun _ hx hex => mem_filter.mpr ⟨hx, hex⟩
  have hbad_lt : #BadIns < 2 * rIndepWhp c n_max := hg.2.2.2.2
  have hv_ops : ValidOpSeq V n_max (Dictionary.empty U) (ops_prev ++ [op]) :=
    validOpSeq_of_validHistory hvh
  obtain ⟨hv_prev, hv_op_singleton⟩ := (ValidOpSeq.append_iff _ ops_prev [op]).mp hv_ops
  have hval_op : Dynamic.valid V n_max (runOps (Dictionary.empty U) ops_prev) op :=
    hv_op_singleton.1
  have hclean_prev :
      ∃ fs, whpRunPure c U n_max θ ops_prev = .fast fs ∧
        CleanWindowFast c U V n_max θ W_keys BadIns fs
          (runOps (Dictionary.empty U) ops_prev) ∧
        ∃ l, suf = l ++ [op] ∧ runOps s_start l = runOps (Dictionary.empty U) ops_prev := by
    by_cases hle : ops.length ≤ windowLenWhp n_max
    · have hsub0 : ops.length - windowLenWhp n_max = 0 := Nat.sub_eq_zero_of_le hle
      have hs_eq : s_start = Dictionary.empty U := by
        dsimp only [s_start, windowStartState]; rw [hsub0]; rfl
      have hsuf_eq : suf = ops_prev ++ [op] := by
        dsimp only [suf, windowSuffix]; rw [hsub0]; rfl
      have hinit_eq : whpInitPure c n_max = .fast (emptyFastState n_max) := by
        unfold whpInitPure; exact ite_eq_right (not_lt.mpr hth)
      have hcw0 : CleanWindowFast c U V n_max θ W_keys BadIns
          (emptyFastState n_max) (Dictionary.empty U) :=
        CleanWindowFast.of_clean_fast (validFastState_empty hth θ) rfl rfl
          (fun h => by cases h)
      have hbud0 : HasBurnInBudget c U V n_max θ W_keys BadIns
          (whpInitPure c n_max) (Dictionary.empty U) 0 :=
        Or.inl ⟨emptyFastState n_max, hinit_eq, hcw0⟩
      have hbud_end := HasBurnInBudget.run hnU hg hbad_def hbad_lt ops_prev hbud0 hv_prev
        (fun s hs => by
          change s ∈ stateSeq s_start suf
          rw [hs_eq, hsuf_eq]; exact mem_stateSeq_append_left _ _ _ s hs)
        (by
          change opInsKeys ops_prev ⊆ W_ins
          dsimp only [W_ins]; rw [hsuf_eq, opInsKeys_append]; exact subset_union_left)
      rw [Nat.zero_sub] at hbud_end
      rcases hbud_end with ⟨fs, hfs, hcw_fs⟩ | ⟨h10, _⟩
      · exact ⟨fs, hfs, hcw_fs, ops_prev, hsuf_eq, by rw [hs_eq]⟩
      · omega
    · set k := ops.length - windowLenWhp n_max
      have hk_le : k ≤ ops_prev.length := by
        dsimp only [k, ops, windowLenWhp] at hle ⊢
        rw [List.length_append, List.length_singleton] at hle ⊢
        omega
      have htake_eq : ops.take k = ops_prev.take k :=
        List.take_append_of_le_length hk_le
      have hsuf_eq : suf = ops_prev.drop k ++ [op] := by
        dsimp only [suf, windowSuffix, ops]
        exact List.drop_append_of_le_length hk_le
      have hs_eq : s_start = runOps (Dictionary.empty U) (ops_prev.take k) := by
        dsimp only [s_start, windowStartState]; rw [htake_eq]
      have hvh_take : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U)
          (ops_prev.take k) := by
        rw [← htake_eq]; exact validHistory_take k hvh
      have hv_st0 : ValidWhpState c U V n_max θ
          (whpRunPure c U n_max θ (ops_prev.take k)) s_start := by
        rw [hs_eq, ← spec_run_fst_eq_runOps (V := V) (n_max := n_max)]
        exact whpRunPure_spec hnU θ hvh_take
      have hbud0 := HasBurnInBudget.of_validWhpState (W_keys := W_keys) (BadIns := BadIns)
        hth hv_st0
      have hv_split : ValidOpSeq V n_max (Dictionary.empty U)
          (ops_prev.take k ++ ops_prev.drop k) := by
        rwa [List.take_append_drop]
      have hv_drop : ValidOpSeq V n_max s_start (ops_prev.drop k) := by
        rw [hs_eq]; exact ((ValidOpSeq.append_iff _ _ _).mp hv_split).2
      have hbud_end := HasBurnInBudget.run hnU hg hbad_def hbad_lt (ops_prev.drop k) hbud0 hv_drop
        (fun s hs => by
          change s ∈ stateSeq s_start suf
          rw [hsuf_eq]; exact mem_stateSeq_append_left _ _ _ s hs)
        (by
          change opInsKeys (ops_prev.drop k) ⊆ W_ins
          dsimp only [W_ins]; rw [hsuf_eq, opInsKeys_append]; exact subset_union_left)
      have hq_sub : qEpochWhp n_max - (ops_prev.drop k).length = 0 := by
        rw [List.length_drop]
        dsimp only [k, ops, windowLenWhp] at hle ⊢
        rw [List.length_append, List.length_singleton] at hle ⊢
        omega
      rw [hq_sub] at hbud_end
      have hrun_eq : whpRunFrom c U n_max θ
          (whpRunPure c U n_max θ (ops_prev.take k)) (ops_prev.drop k) =
          whpRunPure c U n_max θ ops_prev := by
        dsimp only [whpRunPure]
        rw [← whpRunFrom_append, List.take_append_drop]
      have hdict_eq : runOps s_start (ops_prev.drop k) =
          runOps (Dictionary.empty U) ops_prev := by
        rw [hs_eq, ← runOps_append, List.take_append_drop]
      rw [hrun_eq, hdict_eq] at hbud_end
      rcases hbud_end with ⟨fs, hfs, hcw_fs⟩ | ⟨h10, _⟩
      · exact ⟨fs, hfs, hcw_fs, ops_prev.drop k, hsuf_eq, hdict_eq⟩
      · omega
  obtain ⟨fs, hfs, hcw, l, hsuf_l, hdict_l⟩ := hclean_prev
  have hprev_mem : runOps (Dictionary.empty U) ops_prev ∈ stateSeq s_start suf := by
    rw [← hdict_l, hsuf_l]
    exact mem_stateSeq_append_left _ _ _ _ (runOps_mem_stateSeq s_start l)
  have hnxt_mem : (Dynamic.step (runOps (Dictionary.empty U) ops_prev) op).1 ∈
      stateSeq s_start suf := by
    have heq : (Dynamic.step (runOps (Dictionary.empty U) ops_prev) op).1 =
        runOps s_start suf := by
      rw [hsuf_l, runOps_append, hdict_l]; rfl
    rw [heq]; exact runOps_mem_stateSeq s_start suf
  have hdom_prev : (Dictionary.dom (runOps (Dictionary.empty U) ops_prev) : Set (Fin U)) ⊆
      (W_keys : Set (Fin U)) := by
    exact_mod_cast dom_subset_union_opInsKeys s_start suf _ hprev_mem
  have hdom_nxt :
      (Dictionary.dom (Dynamic.step (runOps (Dictionary.empty U) ops_prev) op).1 : Set (Fin U)) ⊆
      (W_keys : Set (Fin U)) := by
    exact_mod_cast dom_subset_union_opInsKeys s_start suf _ hnxt_mem
  have hop_ins : ∀ u v, op = .insert u v → u ∈ W_ins ∧ u ∈ W_keys := by
    rintro u v rfl
    have hu : u ∈ W_ins := by
      dsimp only [W_ins]; rw [hsuf_l, opInsKeys_append]
      exact mem_union_right _ (mem_insert_self u ∅)
    exact ⟨hu, mem_union_right _ hu⟩
  obtain ⟨fs', res, hf, _⟩ := CleanWindowFast.step hnU hcw hval_op hdom_prev hdom_nxt hop_ins
    hg.1 (hg.2.1 _ hnxt_mem) hg.2.2.2.1 hbad_def hbad_lt
  dsimp only [IsFastStepHit]
  rw [hfs]; dsimp only; rw [hf]; rfl

/-- **Master per-operation slow-fallback probability bound**:
Across **all** capacities `n_max ≤ U` (both `< whpThreshold c` and `≥ whpThreshold c`), on any
admissible oblivious operation history `ops_prev ++ [op]`, the probability over `θ ~ seedLawWhp`
that `op` fails to take the `O_c(1)` fast path (`IsFastStepHit`) is at most
`(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`. -/
theorem toOuterMeasure_not_isFastStepHit_le {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {ops_prev : List (Dynamic.Op U)} {op : Dynamic.Op U}
    (hvh : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (ops_prev ++ [op])) :
    (seedLawWhp c U n_max).toOuterMeasure
      {θ | ¬ IsFastStepHit c U n_max ops_prev op θ} ≤
      (max n_max 1 : ℝ≥0∞)⁻¹ ^ c := by
  by_cases hth : whpThreshold c ≤ n_max
  · have hsub : {θ | ¬ IsFastStepHit c U n_max ops_prev op θ} ⊆
        {θ | ¬ GoodSeedOnWindow c U n_max (ops_prev ++ [op]) θ} :=
      fun _ hnot hg => hnot (isFastStepHit_of_goodSeedOnWindow hth hnU hvh hg)
    exact (MeasureTheory.measure_mono hsub).trans
      (toOuterMeasure_not_goodSeedOnWindow_le hth (validOpSeq_of_validHistory hvh))
  · have hemp : {θ | ¬ IsFastStepHit c U n_max ops_prev op θ} = ∅ := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      dsimp only [IsFastStepHit, whpRunPure]
      have hinit : whpInitPure c n_max = .small emptySmallState :=
        ite_eq_left (Nat.lt_of_not_ge hth)
      rw [hinit]
      obtain ⟨sm', hsm'⟩ := whpRunFrom_small θ ops_prev emptySmallState
      rw [hsm']; trivial
    simp only [hemp, MeasureTheory.measure_empty, zero_le]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
