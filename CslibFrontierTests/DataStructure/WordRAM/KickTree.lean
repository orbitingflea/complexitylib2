/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.KickTree.Layout
public import CslibFrontier.DataStructure.Dictionary.WordRAM.KickTree.Prog

/-!
# Concrete Tests for KickTree Bit-Packed Word-RAM Layout and `Memory.Prog` Subroutines

This module tests the parameterized bit-packed Word-RAM layout, pure array extraction/update laws,
sequential `Memory.Prog` execution, and uniform width-free `Realizes .exact` (`¬ReadsWidth`)
certificates for `k`-kick tree slot tables ([BenderFarachColtonKuszmaulKuszmaulLiu2022]):

1. **Layout & Space Bounds**: verifies concrete layout constants (`metaBits`, `kickLimit`,
   `totalSpace`), `totalSpace_le_kickTreeWords`, and `kickTreeWords_le_succinctWords` at `k = 1`.
2. **Pure Extraction & Range Bounds**: verifies zero-initialization and bit-width bounds for all
   five bit-packed arrays (`quotAt`, `valAt`, `occAt`, `elevAt`, `metaAt`).
3. **Sequential `_spec`, `ValidHistory`, & `memoryCost` Caller Tests**: allocates separate hashed
   (`base = 0`) and unindexed tail-cubby (`tailBase`) tables via `allocKickTableProg_spec`,
   exercises sparse `SlotMeta` via `writeMetaProg_spec`/`readMetaProg_spec`, runs `kickLoopProg`
   via the parametric `kickLoopProg_spec` (`Realization.iterate_spec`) preserving the local
   adaptation's 1-bit `elevAt` under displacement, vacates hashed slot `3` via `clearSlotProg_spec`,
   compacts contiguous `[0, 2)` tail slots (`0` from `1` and self-pop `0` from `0`) via
   `popUnindexedSlotProg_spec`, re-inserts the popped item into `base = 0` via `kickLoopProg_spec`,
   and checks `ValidHistory` and `memoryCost` bounds across all eight subroutines.
4. **Width-Freedom, Safety Satisfiability, & Non-Vacuous Native Execution**:
   extracts concrete emitted `WordRAM.Code` for all eight `Realizes .exact` certificates, checks
   `¬ReadsWidth`, instantiates `KickEnvGen`, `KickStepSafe`, and `iterationSafe` at `w = 64` via
   `validHistory_kickLoopProg`, and proves non-trivial native `ExecWithin 64` execution for
   `allocKickTableGenProg`, `querySlotGenProg` (`some 42`), and `clearSlotGenProg` (`y ≠ x`,
   rejecting `.halt`) using `BitPackedArray.writePacked_lt_two_pow` and `fits_encode_*`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022],
  STOC 2022, pp. 1284–1297 (`arXiv:2111.00602v2`).
-/

public section

namespace CslibFrontierTests.DataStructure.WordRAM.KickTree

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.KickTree
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.KickTree

/-! ### 1. Concrete Layout and Space Bound Tests -/

/-- Concrete test parameters: 64-bit machine words, capacity 1000, universe `10^6`, values `10^6`,
0-indexed kick parameter `k = 2` (`kickLimit = 3`), header space `hSpace = 16`, metadata
multiplicity `cMeta = 2`. -/
@[expose] def testParams : KickTreeParams :=
  mkKickTreeParams 64 1000 1000000 1000000 2 16 2

/-- Small concrete test parameters (`w = 16, nMax = 8, k = 1`, so `kickLimit = 2`). -/
@[expose] def smallParams : KickTreeParams :=
  mkKickTreeParams 16 8 64 64 1 2 2

/-- Unindexed tail-cubby test parameters with full `keyBits 64 = 6`-bit keys and `cMeta = 0`. -/
@[expose] def tailParams : KickTreeParams :=
  mkKickTreeParams 16 8 64 64 1 2 0 (quotiented := false)

/-- Word width of `testParams` is positive. -/
theorem test_hw : 0 < testParams.w := by decide

/-- Concrete computational checks on layout offsets, `kickLimit`, `metaBits`, and word
footprints. -/
theorem test_concrete_layout_values :
    testParams.kickLimit = 3 ∧
      smallParams.kickLimit = 2 ∧
      offQuot testParams = 16 ∧
      1 ≤ metaBits testParams ∧
      metaBits testParams ≤ testParams.w ∧
      0 < totalSpace testParams ∧
      totalSpace testParams ≤
        kickTreeWords (testParams.cMeta + 7) (testParams.hSpace + 14)
          testParams.U testParams.V testParams.w testParams.k testParams.nMax ∧
      kickTreeWords 9 30 testParams.U testParams.V testParams.w 1 testParams.nMax ≤
        Dynamic.succinctWords 9 30 testParams.U testParams.V testParams.w testParams.nMax := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    totalSpace_le_kickTreeWords testParams (by decide),
    kickTreeWords_le_succinctWords 9 30 testParams.U testParams.V testParams.w testParams.nMax⟩

/-! ### 2. Pure Extraction and Range Tests -/

/-- Zero memory function. -/
def zeroMem : ℕ → ℕ := fun _ => 0

/-- All five bit-packed logical arrays extract as identically zero on `zeroMem`. -/
theorem test_zero_of_init :
    quotAt 0 testParams zeroMem = (fun _ => 0) ∧
      valAt 0 testParams zeroMem = (fun _ => 0) ∧
      occAt 0 testParams zeroMem = (fun _ => 0) ∧
      elevAt 0 testParams zeroMem = (fun _ => 0) ∧
      metaAt 0 testParams zeroMem = (fun _ => 0) :=
  ⟨quotAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   valAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   occAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   elevAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   metaAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)⟩

/-- Bit-width range bounds hold on arbitrary memory contents across all five arrays. -/
theorem test_range_bounds (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt 0 testParams mem idx < 2 ^ fullQuotBits testParams.U testParams.nMax ∧
      valAt 0 testParams mem idx < 2 ^ valBits testParams.V ∧
      occAt 0 testParams mem idx < 2 ^ 1 ∧
      elevAt 0 testParams mem idx < 2 ^ 1 ∧
      metaAt 0 testParams mem idx < 2 ^ metaBits testParams :=
  ⟨quotAt_lt 0 testParams mem idx,
   valAt_lt 0 testParams mem idx,
   occAt_lt 0 testParams mem idx,
   elevAt_lt 0 testParams mem idx,
   metaAt_lt 0 testParams mem idx⟩

/-! ### 3. End-to-End Sequential `_spec` Caller Tests -/

/-- Representative caller chaining `allocKickTableProg_spec`, `writeMetaProg_spec`,
`readMetaProg_spec`, `kickLoopProg_spec` (`Realization.iterate_spec`), `querySlotProg_spec`,
`clearSlotProg_spec`, and `popUnindexedSlotProg_spec`:
1. Allocates hashed kick-tree table at `base = 0` (`smallParams`, `p.kickLimit = 2`) and separate
   unindexed tail-cubby table at `tailBase = totalSpace smallParams` (`tailParams`, `cMeta = 0`),
   then dirty-allocates `[totalSpace smallParams + totalSpace tailParams, ... + 200)` so switching-
   path words `[200..205]` lie below `frontier` while remaining framed across allocations.
2. Writes and reads sparse `SlotMeta[7] = 1` in `base = 0` (`writeMetaProg` / `readMetaProg`).
3. Populates contiguous unindexed slots `0` (`(quot = 4, val = 11)`) and `1` (`(quot = 6,
   val = 13)`) in `tailBase`.
4. Inserts `(quot = 0, val = 0, elevated = 0)` along `[200, 201] = [3, 5]` in `base = 0`, then
   inserts elevated item `(quot = 7, val = 9, elevated = 1)` along `[200, 201] = [3, 5]`,
   displacing `(0, 0, 0)` from slot `3` to slot `5` while preserving `elevAt ... 3 = 1`,
   `elevAt ... 5 = 0`, and `SlotMeta[7] = 1`.
5. Vacates hashed slot `3` via `clearSlotProg`, pops contiguous unindexed slot `0` compacted from
   `lastSlot = 1` in `tailBase` via `popUnindexedSlotProg` (yielding `((4, 11), 0)` and moving
   `(6, 13)` into `tailBase` slot `0`), re-inserts `(4, 11)` into `base = 0` along `[202, 203] =
   [3, 6]` via `kickLoopProg_spec`, and self-pops `slot = 0, lastSlot = 0` in `tailBase`. -/
theorem test_sequential_caller_specs :
    let mInit : ℕ → ℕ := fun a =>
      if a = 200 then 3 else if a = 201 then 5
      else if a = 202 then 3 else if a = 203 then 6
      else if a = 204 then 0 else if a = 205 then 1 else 0
    let s₀ : Memory.State := ⟨mInit, 0⟩
    let s₁ := (Memory.spec 0).clientState s₀ (allocKickTableProg smallParams)
    let tailBase := (Memory.spec 0).clientResult s₁ (allocKickTableProg tailParams)
    let s₁' := (Memory.spec 0).clientState s₁ (allocKickTableProg tailParams)
    let s₁'' := (Memory.spec 0).clientState s₁' (Memory.allocDirty 200)
    let sM := (Memory.spec 0).clientState s₁'' (writeMetaProg smallParams 0 7 1)
    let sT₁ :=
      (Memory.spec 0).clientState sM (kickStepProg tailParams tailBase 204 ⟨0, 4, 11, 0, 1⟩)
    let sT₂ :=
      (Memory.spec 0).clientState sT₁ (kickStepProg tailParams tailBase 205 ⟨0, 6, 13, 0, 1⟩)
    let r₂ := (Memory.spec 0).clientResult sT₂ (kickLoopProg smallParams 0 200 0 0 0)
    let s₂ := (Memory.spec 0).clientState sT₂ (kickLoopProg smallParams 0 200 0 0 0)
    let r₄ := (Memory.spec 0).clientResult s₂ (kickLoopProg smallParams 0 200 7 9 1)
    let s₄ := (Memory.spec 0).clientState s₂ (kickLoopProg smallParams 0 200 7 9 1)
    let s₅ := (Memory.spec 0).clientState s₄ (clearSlotProg smallParams 0 3)
    let popped := (Memory.spec 0).clientResult s₅ (popUnindexedSlotProg tailParams tailBase 0 1)
    let sPop := (Memory.spec 0).clientState s₅ (popUnindexedSlotProg tailParams tailBase 0 1)
    let sReins := (Memory.spec 0).clientState sPop (kickLoopProg smallParams 0 202 4 11 0)
    let sSelf := (Memory.spec 0).clientState sReins (popUnindexedSlotProg tailParams tailBase 0 0)
    r₂ = ⟨1, 0, 0, 0, 0⟩ ∧
      r₄ = ⟨2, 0, 0, 0, 0⟩ ∧
      (Memory.spec 0).clientResult s₄ (readMetaProg smallParams 0 7) = 1 ∧
      elevAt 0 smallParams s₄.mem 3 = 1 ∧
      elevAt 0 smallParams s₄.mem 5 = 0 ∧
      (Memory.spec 0).clientResult s₄ (querySlotProg smallParams 0 3 7) = some 9 ∧
      (Memory.spec 0).clientResult s₄ (querySlotProg smallParams 0 3 8) = none ∧
      (Memory.spec 0).clientResult s₄ (querySlotProg smallParams 0 5 0) = some 0 ∧
      (Memory.spec 0).clientResult s₅ (querySlotProg smallParams 0 3 7) = none ∧
      (Memory.spec 0).clientResult s₅ (querySlotProg smallParams 0 5 0) = some 0 ∧
      popped = ((4, 11), 0) ∧
      (Memory.spec 0).clientResult sPop (querySlotProg tailParams tailBase 0 6) = some 13 ∧
      (Memory.spec 0).clientResult sPop (querySlotProg tailParams tailBase 1 6) = none ∧
      (Memory.spec 0).clientResult sReins (querySlotProg smallParams 0 3 4) = some 11 ∧
      (Memory.spec 0).clientResult sReins (querySlotProg smallParams 0 5 0) = some 0 ∧
      (Memory.spec 0).clientResult sSelf (querySlotProg tailParams tailBase 0 6) = none := by
  intro mInit s₀ s₁ tailBase s₁' s₁'' sM sT₁ sT₂ r₂ s₂ r₄ s₄ s₅ popped sPop sReins sSelf
  have shw : 0 < smallParams.w := by decide
  have thw : 0 < tailParams.w := by decide
  have henvS : KickEnv smallParams 16 0 :=
    ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
  have htot1 : totalSpace smallParams ≤ 50 := by decide
  have htot2 : totalSpace smallParams + totalSpace tailParams ≤ 100 := by decide
  have hpos1 : 10 ≤ totalSpace smallParams := by decide
  have hwf_of {α : Type} {s : Memory.State} {p : Memory.Prog α}
      (hwf : Memory.WellFormed 16 s)
      (hv : (Memory.spec 16).ValidHistory s ((Memory.spec 16).clientHistory s p)) :
      Memory.WellFormed 16 ((Memory.spec 0).clientState s p) := by
    rw [← clientState_width 16, ← StateTransitionSpec.run_runClient]
    exact hwf.run hv
  have hwf0 : Memory.WellFormed 16 s₀ :=
    ⟨by decide, fun a => by dsimp only [s₀, mInit]; split_ifs <;> decide⟩
  obtain ⟨hb0, hfr1, _, hout_a1, hq_a1, hv_a1, ho_a1, he_a1, hm_a1⟩ :=
    allocKickTableProg_spec smallParams shw s₀
  have hwf1 : Memory.WellFormed 16 s₁ :=
    hwf_of hwf0 (validHistory_allocKickTableProg smallParams (by decide))
  have hbase0 : (Memory.spec 0).clientResult s₀ (allocKickTableProg smallParams) = 0 := hb0
  rw [hbase0] at hout_a1 hq_a1 hv_a1 ho_a1 he_a1 hm_a1
  obtain ⟨htb, hfr1', _, hout_a2, hq_t0, hv_t0, ho_t0, he_t0, _⟩ :=
    allocKickTableProg_spec tailParams thw s₁
  have htb_eq : tailBase = totalSpace smallParams := htb.trans hfr1
  have henvT : KickEnv tailParams 16 tailBase := by
    rw [htb_eq]; exact ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
  have hwf1' : Memory.WellFormed 16 s₁' :=
    hwf_of hwf1 (validHistory_allocKickTableProg tailParams (by rw [hfr1]; decide))
  have hfr1'' : s₁''.frontier = totalSpace smallParams + totalSpace tailParams + 200 := by
    change s₁'.frontier + 200 = _; rw [hfr1', hfr1, zero_add]
  have hmem1'' : s₁''.mem = s₁'.mem := rfl
  have hwf1'' : Memory.WellFormed 16 s₁'' :=
    ⟨by rw [hfr1'']; decide, by rw [hmem1'']; exact hwf1'.2⟩
  have h1'_eq_on : ∀ a, 0 + smallParams.hSpace ≤ a → a < 0 + totalSpace smallParams →
      s₁''.mem a = s₁.mem a := fun a _ ha2 => by
    rw [hmem1'']; exact hout_a2 a (by rw [htb, hfr1]; omega)
  obtain ⟨hq_1', hv_1', ho_1', he_1', hm_1'⟩ := arrays_congr_of_eq_on smallParams shw h1'_eq_on
  rw [hq_a1] at hq_1'; rw [hv_a1] at hv_1'; rw [ho_a1] at ho_1'
  rw [he_a1] at he_1'; rw [hm_a1] at hm_1'
  obtain ⟨hfrM, hout_m, hq_m, hv_m, ho_m, he_m, hm_m⟩ :=
    writeMetaProg_spec smallParams shw (base := 0) (by decide : 7 < metaLen smallParams)
      (by decide : 1 < 2 ^ metaBits smallParams) s₁''
  change sM.frontier = s₁''.frontier at hfrM
  have hwfM : Memory.WellFormed 16 sM :=
    hwf_of hwf1'' (validHistory_writeMetaProg smallParams henvS (by decide) hwf1''
      (by rw [hfr1'']; omega))
  rw [hq_1'] at hq_m; rw [hv_1'] at hv_m; rw [ho_1'] at ho_m
  rw [he_1'] at he_m; rw [hm_1'] at hm_m
  have hm_eq_t : ∀ a, tailBase + tailParams.hSpace ≤ a → a < tailBase + totalSpace tailParams →
      sM.mem a = s₁'.mem a := fun a ha1 _ => by
    rw [← hmem1'']; exact hout_m a (by rw [htb_eq] at ha1; omega)
  obtain ⟨hq_tm, hv_tm, ho_tm, he_tm, _⟩ := arrays_congr_of_eq_on tailParams thw hm_eq_t
  rw [hq_t0] at hq_tm; rw [hv_t0] at hv_tm; rw [ho_t0] at ho_tm; rw [he_t0] at he_tm
  have hpath_sM : ∀ a, 200 ≤ a → sM.mem a = mInit a := fun a ha => by
    refine (hout_m a (by omega)).trans ?_
    rw [hmem1'']
    refine (hout_a2 a ?_).trans (hout_a1 a (by omega))
    rw [htb, hfr1]; omega
  have hp204 : sM.mem (204 + 0) = 0 := hpath_sM 204 (by omega)
  have ht1_spec := kickStepProg_vacant_spec tailParams thw (base := tailBase) (pathBase := 204)
    (st := ⟨0, 4, 11, 0, 1⟩) (s := sM) (by decide) (by rw [hp204]; decide)
    (by decide) (by decide) (by decide) (by rw [ho_tm])
  dsimp only at ht1_spec; rw [hp204] at ht1_spec
  obtain ⟨_, hfr_t1, hout_t1, hq_t1, hv_t1, he_t1, ho_t1, _⟩ := ht1_spec
  change sT₁.frontier = sM.frontier at hfr_t1
  have hwfT1 : Memory.WellFormed 16 sT₁ :=
    hwf_of hwfM (validHistory_kickStepProg tailParams henvT hwfM
      (by rw [hfrM, hfr1'', htb_eq]; omega)
      (fun _ => ⟨by dsimp only; rw [hfrM, hfr1'']; omega, by rw [hp204]; decide⟩))
  have hp205 : sT₁.mem (205 + 0) = 1 :=
    (hout_t1 205 (by rw [htb_eq]; omega)).trans (hpath_sM 205 (by omega))
  have ht2_spec := kickStepProg_vacant_spec tailParams thw (base := tailBase) (pathBase := 205)
    (st := ⟨0, 6, 13, 0, 1⟩) (s := sT₁) (by decide) (by rw [hp205]; decide)
    (by decide) (by decide) (by decide)
    (by rw [hp205, ho_t1, ho_tm, Function.update_of_ne (by decide)])
  dsimp only at ht2_spec; rw [hp205] at ht2_spec
  obtain ⟨_, hfr_t2, hout_t2, hq_t2, hv_t2, he_t2, ho_t2, _⟩ := ht2_spec
  change sT₂.frontier = sT₁.frontier at hfr_t2
  have hwfT2 : Memory.WellFormed 16 sT₂ :=
    hwf_of hwfT1 (validHistory_kickStepProg tailParams henvT hwfT1
      (by rw [hfr_t1, hfrM, hfr1'', htb_eq]; omega)
      (fun _ => ⟨by dsimp only; rw [hfr_t1, hfrM, hfr1'']; omega, by rw [hp205]; decide⟩))
  have hfrT2 : sT₂.frontier = totalSpace smallParams + totalSpace tailParams + 200 := by
    rw [hfr_t2, hfr_t1, hfrM, hfr1'']
  have ht2_eq_0 : ∀ a, 0 + smallParams.hSpace ≤ a → a < 0 + totalSpace smallParams →
      sT₂.mem a = sM.mem a := fun a _ ha2 =>
    (hout_t2 a (by rw [htb_eq]; omega)).trans (hout_t1 a (by rw [htb_eq]; omega))
  obtain ⟨hq_0, hv_0, ho_0, he_0, hm_0⟩ := arrays_congr_of_eq_on smallParams shw ht2_eq_0
  rw [hq_m] at hq_0; rw [hv_m] at hv_0; rw [ho_m] at ho_0
  rw [he_m] at he_0; rw [hm_m] at hm_0
  have hpath_sT2 : ∀ a, 200 ≤ a → sT₂.mem a = mInit a := fun a ha =>
    (hout_t2 a (by rw [htb_eq]; omega)).trans
      ((hout_t1 a (by rw [htb_eq]; omega)).trans (hpath_sM a ha))
  have hp200_t2 : sT₂.mem (200 + 0) = 3 := hpath_sT2 200 (by omega)
  have hp201_t2 : sT₂.mem (200 + 1) = 5 := hpath_sT2 201 (by omega)
  have hs1a := kickStepProg_vacant_spec smallParams shw (base := 0) (pathBase := 200)
    (st := ⟨0, 0, 0, 0, 1⟩) (s := sT₂) (by decide) (by rw [hp200_t2]; decide)
    (by decide) (by decide) (by decide) (by rw [ho_0])
  dsimp only at hs1a; rw [hp200_t2] at hs1a
  obtain ⟨hr1a, _, hout1a, hq2, hv2, he2, ho2, hm2⟩ := hs1a
  set s₁_step := (Memory.spec 0).clientState sT₂ (kickStepProg smallParams 0 200 ⟨0, 0, 0, 0, 1⟩)
  have hloop1 := kickLoopProg_spec smallParams henvS
    (st₀ := ⟨0, 0, 0, 0, 1⟩) (fuel := smallParams.kickLimit)
    (fun i st s => if i = 0 then st = ⟨0, 0, 0, 0, 1⟩ ∧ s = sT₂
      else st = ⟨1, 0, 0, 0, 0⟩ ∧ s = s₁_step)
    hwfT2 (by rw [hfrT2]; omega)
    (by
      change 200 + 0 + smallParams.kickLimit ≤ _
      rw [hfrT2]; have : smallParams.kickLimit = 2 := rfl; omega)
    (fun i hi => by
      have : smallParams.kickLimit = 2 := rfl
      change ¬(_ ≤ 200 + (0 + i) ∧ _); omega)
    (fun i hi => by
      have : smallParams.kickLimit = 2 := rfl
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · change sT₂.mem (200 + 0) < _; rw [hp200_t2]; decide
      · change sT₂.mem (200 + 1) < _; rw [hp201_t2]; decide)
    ⟨rfl, rfl⟩
    (fun i _ st s _ _ hinv => by
      rcases i with _ | i
      · rcases hinv with ⟨rfl, rfl⟩; exact ⟨hr1a, rfl⟩
      · rcases hinv with ⟨rfl, rfl⟩
        exact kickStepProg_inactive_spec smallParams rfl s₁_step)
  obtain ⟨_, hv_l1, _, hfr2, _, hr2_eq, hs2_eq⟩ := hloop1
  have hwf2 : Memory.WellFormed 16 s₂ := hwf_of hwfT2 hv_l1
  rw [← hs2_eq] at hout1a hq2 hv2 he2 ho2 hm2
  have hp200_s2 : s₂.mem (200 + 0) = 3 := (hout1a 200 (by omega)).trans hp200_t2
  have hp201_s2 : s₂.mem 201 = 5 := (hout1a 201 (by omega)).trans (hpath_sT2 201 (by omega))
  set s₃ := (Memory.spec 0).clientState s₂ (kickStepProg smallParams 0 200 ⟨0, 7, 9, 1, 1⟩)
  set st₃ := (Memory.spec 0).clientResult s₂ (kickStepProg smallParams 0 200 ⟨0, 7, 9, 1, 1⟩)
  have hs3_spec := kickStepProg_displace_spec smallParams shw (base := 0) (pathBase := 200)
    (st := ⟨0, 7, 9, 1, 1⟩) (s := s₂) (by decide) (by rw [hp200_s2]; decide)
    (by decide) (by decide) (by decide)
    (by rw [hp200_s2, ho2, Function.update_self]; decide)
  dsimp only at hs3_spec; rw [hp200_s2] at hs3_spec
  obtain ⟨hst3, _, hout3, hq3, hv3, he3, ho3, hm3⟩ := hs3_spec
  have hst3_eq : st₃ = ⟨1, 0, 0, 0, 1⟩ := by
    change (Memory.spec 0).clientResult s₂ _ = _
    rw [hst3, hq2, hv2, he2, Function.update_self, Function.update_self, Function.update_self]
  have hp201_s3 : s₃.mem (200 + st₃.stepIdx) = 5 := by
    rw [hst3_eq]; exact (hout3 201 (by omega)).trans hp201_s2
  have hs4_spec := kickStepProg_vacant_spec smallParams shw (base := 0) (pathBase := 200)
    (st := st₃) (s := s₃) (by rw [hst3_eq]; decide) (by rw [hp201_s3]; decide)
    (by rw [hst3_eq]; decide) (by rw [hst3_eq]; decide) (by rw [hst3_eq]; decide)
    (by rw [hp201_s3, ho3, ho2, ho_0, Function.update_of_ne (by decide)])
  dsimp only at hs4_spec; rw [hp201_s3, hst3_eq] at hs4_spec; dsimp only at hs4_spec
  obtain ⟨hr4a, _, hout4, hq4, hv4, he4, ho4, hm4⟩ := hs4_spec
  set s₄_step := (Memory.spec 0).clientState s₃ (kickStepProg smallParams 0 200 ⟨1, 0, 0, 0, 1⟩)
  have hloop2 := kickLoopProg_spec smallParams henvS
    (st₀ := ⟨0, 7, 9, 1, 1⟩) (fuel := smallParams.kickLimit)
    (fun i st s => if i = 0 then st = ⟨0, 7, 9, 1, 1⟩ ∧ s = s₂
      else if i = 1 then st = ⟨1, 0, 0, 0, 1⟩ ∧ s = s₃
      else st = ⟨2, 0, 0, 0, 0⟩ ∧ s = s₄_step)
    hwf2 (by rw [hfr2, hfrT2]; omega)
    (by
      change 200 + 0 + smallParams.kickLimit ≤ _
      rw [hfr2, hfrT2]; have : smallParams.kickLimit = 2 := rfl; omega)
    (fun i hi => by
      have : smallParams.kickLimit = 2 := rfl
      change ¬(_ ≤ 200 + (0 + i) ∧ _); omega)
    (fun i hi => by
      have : smallParams.kickLimit = 2 := rfl
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · change s₂.mem (200 + 0) < _; rw [hp200_s2]; decide
      · change s₂.mem 201 < _; rw [hp201_s2]; decide)
    ⟨rfl, rfl⟩
    (fun i _ st s _ _ hinv => by
      rcases i with _ | _ | i
      · rcases hinv with ⟨rfl, rfl⟩; exact ⟨hst3_eq, rfl⟩
      · rcases hinv with ⟨rfl, rfl⟩; exact ⟨hr4a, rfl⟩
      · rcases hinv with ⟨rfl, rfl⟩
        exact kickStepProg_inactive_spec smallParams rfl s₄_step)
  obtain ⟨_, hv_l2, _, hfr4, _, hr4_eq, hs4_eq⟩ := hloop2
  have hwf4 : Memory.WellFormed 16 s₄ := hwf_of hwf2 hv_l2
  rw [← hs4_eq] at hout4 hq4 hv4 he4 ho4 hm4
  obtain ⟨hfr5, hout5, hq5, hv5, he5, ho5, _⟩ :=
    clearSlotProg_spec smallParams shw (base := 0) (by decide : 3 < smallParams.nMax) s₄
  have hwf5 : Memory.WellFormed 16 s₅ :=
    hwf_of hwf4 (validHistory_clearSlotProg smallParams henvS (by decide) hwf4
      (by rw [hfr4, hfr2, hfrT2]; omega))
  have hs5_eq_tail : ∀ a, tailBase + tailParams.hSpace ≤ a → a < tailBase + totalSpace tailParams →
      s₅.mem a = sT₂.mem a := fun a ha1 _ => by
    have hnot : ¬(0 + smallParams.hSpace ≤ a ∧ a < 0 + totalSpace smallParams) := by
      rw [htb_eq] at ha1; omega
    exact (hout5 a hnot).trans ((hout4 a hnot).trans ((hout3 a hnot).trans (hout1a a hnot)))
  obtain ⟨hq_t5, hv_t5, ho_t5, he_t5, _⟩ := arrays_congr_of_eq_on tailParams thw hs5_eq_tail
  rw [hq_t2, hq_t1, hq_tm] at hq_t5
  rw [hv_t2, hv_t1, hv_tm] at hv_t5
  rw [ho_t2, ho_t1, ho_tm] at ho_t5
  rw [he_t2, he_t1, he_tm] at he_t5
  obtain ⟨hpop_res, hfrP, houtP, hqP, hvP, heP, hoP, _⟩ :=
    popUnindexedSlotProg_spec tailParams thw (base := tailBase)
      (by decide : 0 < tailParams.nMax) (by decide : 1 < tailParams.nMax) s₅
  have hwfPop : Memory.WellFormed 16 sPop :=
    hwf_of hwf5 (validHistory_popUnindexedSlotProg tailParams henvT (by decide) (by decide) hwf5
      (by rw [hfr5, hfr4, hfr2, hfrT2, htb_eq]; omega))
  have hsPop_eq_0 : ∀ a, 0 + smallParams.hSpace ≤ a → a < 0 + totalSpace smallParams →
      sPop.mem a = s₅.mem a := fun a _ ha2 =>
    houtP a (by rw [htb_eq]; omega)
  obtain ⟨hq_p0, hv_p0, ho_p0, he_p0, _⟩ := arrays_congr_of_eq_on smallParams shw hsPop_eq_0
  have hp202_pop : sPop.mem (202 + 0) = 3 := by
    have hnot0 : ¬(0 + smallParams.hSpace ≤ 202 ∧ 202 < 0 + totalSpace smallParams) := by omega
    refine (houtP 202 (by rw [htb_eq]; omega)).trans ?_
    exact (hout5 202 hnot0).trans ((hout4 202 hnot0).trans
      ((hout3 202 hnot0).trans ((hout1a 202 hnot0).trans (hpath_sT2 202 (by omega)))))
  have hp203_pop : sPop.mem (202 + 1) = 6 := by
    have hnot0 : ¬(0 + smallParams.hSpace ≤ 203 ∧ 203 < 0 + totalSpace smallParams) := by omega
    refine (houtP 203 (by rw [htb_eq]; omega)).trans ?_
    exact (hout5 203 hnot0).trans ((hout4 203 hnot0).trans
      ((hout3 203 hnot0).trans ((hout1a 203 hnot0).trans (hpath_sT2 203 (by omega)))))
  have hreins1 := kickStepProg_vacant_spec smallParams shw (base := 0) (pathBase := 202)
    (st := ⟨0, 4, 11, 0, 1⟩) (s := sPop) (by decide) (by rw [hp202_pop]; decide)
    (by decide) (by decide) (by decide)
    (by rw [hp202_pop, ho_p0, ho5, Function.update_self])
  dsimp only at hreins1; rw [hp202_pop] at hreins1
  obtain ⟨hrr1, _, houtR1, hqR, hvR, _, hoR, _⟩ := hreins1
  set sR_step := (Memory.spec 0).clientState sPop (kickStepProg smallParams 0 202 ⟨0, 4, 11, 0, 1⟩)
  have hloop3 := kickLoopProg_spec smallParams henvS
    (st₀ := ⟨0, 4, 11, 0, 1⟩) (fuel := smallParams.kickLimit)
    (fun i st s => if i = 0 then st = ⟨0, 4, 11, 0, 1⟩ ∧ s = sPop
      else st = ⟨1, 0, 0, 0, 0⟩ ∧ s = sR_step)
    hwfPop (by rw [hfrP, hfr5, hfr4, hfr2, hfrT2]; omega)
    (by
      change 202 + 0 + smallParams.kickLimit ≤ _
      rw [hfrP, hfr5, hfr4, hfr2, hfrT2]; have : smallParams.kickLimit = 2 := rfl; omega)
    (fun i hi => by
      have : smallParams.kickLimit = 2 := rfl
      change ¬(_ ≤ 202 + (0 + i) ∧ _); omega)
    (fun i hi => by
      have : smallParams.kickLimit = 2 := rfl
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · change sPop.mem (202 + 0) < _; rw [hp202_pop]; decide
      · change sPop.mem (202 + 1) < _; rw [hp203_pop]; decide)
    ⟨rfl, rfl⟩
    (fun i _ st s _ _ hinv => by
      rcases i with _ | i
      · rcases hinv with ⟨rfl, rfl⟩; exact ⟨hrr1, rfl⟩
      · rcases hinv with ⟨rfl, rfl⟩
        exact kickStepProg_inactive_spec smallParams rfl sR_step)
  obtain ⟨_, _, _, _, _, _, hsReins_eq⟩ := hloop3
  rw [← hsReins_eq] at houtR1 hqR hvR hoR
  obtain ⟨_, _, _, _, _, _, hoS, _⟩ :=
    popUnindexedSlotProg_spec tailParams thw (base := tailBase)
      (by decide : 0 < tailParams.nMax) (by decide : 0 < tailParams.nMax) sReins
  refine ⟨hr2_eq, hr4_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(readMetaProg_spec smallParams (by decide : 7 < metaLen smallParams) s₄).2,
      hm4, hm3, hm2, hm_0]; decide
  · rw [he4, he3, he2, he_0]; decide
  · rw [he4]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₄).2, ho4, ho3, ho2, hq4, hq3, hv4, hv3]
    decide
  · rw [(querySlotProg_spec smallParams (by decide) s₄).2, ho4, ho3, ho2, hq4, hq3]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₄).2, ho4, hq4, hv4]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₅).2, ho5]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₅).2, ho5, ho4, hq5, hq4, hv5, hv4]; decide
  · change (Memory.spec 0).clientResult s₅ _ = _
    rw [hpop_res, hq_t5, hv_t5, he_t5]; decide
  · rw [(querySlotProg_spec tailParams (by decide) sPop).2, hoP, hqP, hvP, ho_t5, hq_t5, hv_t5]
    decide
  · rw [(querySlotProg_spec tailParams (by decide) sPop).2, hoP]; decide
  · rw [(querySlotProg_spec smallParams (by decide) sReins).2, hoR, hqR, hvR]; decide
  · rw [(querySlotProg_spec smallParams (by decide) sReins).2, hoR, ho_p0, ho5, ho4,
      hqR, hq_p0, hq5, hq4, hvR, hv_p0, hv5, hv4]; decide
  · rw [(querySlotProg_spec tailParams (by decide) sSelf).2, hoS]; decide

/-! ### 4. Width-Freedom (`¬ReadsWidth`), Envelope Satisfiability, and Native Execution Tests -/

/-- Simulation and width-freedom contract for an emitted native `Code` realizing `prog`. -/
def EmittedSubroutine (B : Basis) {k l : ℕ} {δ α : Type}
    (prog : δ → Memory.Prog α) (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) : Prop :=
  ∃ (r C : ℕ) (frontier : Fin r) (src : Fin k → Fin r) (res : Fin l → Fin r) (c : Code B r),
    ¬c.ReadsWidth ∧ k ≤ frontier.1 ∧ (∀ i : Fin k, (src i).1 = i.1) ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (prog d)) →
      ∃ y, ExecWithin w c x y
          (C * (memoryCost (prog d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
        memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (prog d) ∧
        ∀ i : Fin l, y.regs (res i) =
          output ((Memory.spec w).clientResult (memoryState frontier x) (prog d)) i

/-- Instantiate any `Realizes` certificate on a concrete disjoint register bank to witness emitted
`WordRAM.Code` satisfying `¬ReadsWidth` alongside its native `ExecWithin` contract. -/
theorem exists_emitted_not_readsWidth {B : Basis} {k l : ℕ} {δ α : Type}
    {prog : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    (h : Realizes B prog input output safe work) :
    EmittedSubroutine B prog input output safe work := by
  obtain ⟨n, C, emit, hspec⟩ := h
  let r := k + (l + n + 1) + 1
  let frontier : Fin r := ⟨k + (l + n + 1), by omega⟩
  let src : Fin k → Fin r := fun i => ⟨i.1, by omega⟩
  let tmp : Fin (l + n + 1) → Fin r := fun j => ⟨k + j.1, by omega⟩
  have hinj : Function.Injective tmp := fun j₁ j₂ heq =>
    Fin.ext (by have := congrArg Fin.val heq; dsimp [tmp] at this; omega)
  have hdisj : ∀ i j, src i ≠ tmp j := fun i j heq => by
    have := congrArg Fin.val heq; dsimp [src, tmp] at this; omega
  have htf : ∀ j, tmp j ≠ frontier := fun j heq => by
    have := congrArg Fin.val heq; dsimp [tmp, frontier] at this; omega
  have hsf : ∀ i, src i ≠ frontier := fun i heq => by
    have := congrArg Fin.val heq; dsimp [src, frontier] at this; omega
  obtain ⟨hnw, hrun⟩ := hspec frontier src tmp hinj hdisj htf hsf
  refine ⟨r, C, frontier, src, fun i => tmp (Fin.castAdd (n + 1) i),
    emit frontier src tmp, hnw, by dsimp [frontier]; omega, fun _ => rfl,
    fun w d x hx hin hs hv => ?_⟩
  obtain ⟨y, hy, hm, hout, _⟩ := hrun w d x hx hin hs hv
  exact ⟨y, hy, hm, hout⟩

/-- Emitted `Code` for all eight `Realizes .exact` certificates satisfies `¬ReadsWidth` and
preserves the native subroutine execution contracts. -/
theorem test_all_eight_not_readsWidth :
    EmittedSubroutine .exact allocKickTableGenProg
      (WordEncoding.encode (α := KickRuntimeParams))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True)
      (fun _ _ => 0) ∧
    EmittedSubroutine .exact querySlotGenProg
      (WordEncoding.encode (α := KickQueryInput))
      (WordEncoding.encode (α := Option ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax)
      (fun _ _ => 0) ∧
    EmittedSubroutine .exact readMetaGenProg
      (WordEncoding.encode (α := KickMetaReadInput))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.idx < d.rp.metaLen)
      (fun _ _ => 0) ∧
    EmittedSubroutine .exact writeMetaGenProg
      (WordEncoding.encode (α := KickMetaWriteInput))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.idx < d.rp.metaLen)
      (fun _ _ => 0) ∧
    EmittedSubroutine .exact kickStepGenProg
      (WordEncoding.encode (α := KickStepEnv × KickStepState))
      (WordEncoding.encode (α := KickStepState))
      KickStepSafe
      (fun _ _ => 0) ∧
    EmittedSubroutine .exact kickLoopIterGenProg
      (WordEncoding.encode (α := (KickStepEnv × KickStepState) × ℕ))
      (WordEncoding.encode (α := KickStepState))
      (fun w ((env, st), fuel) s =>
        iterationSafe kickStepGenProg KickStepSafe w env fuel st s)
      (fun ((env, st), fuel) s =>
        iterationWork kickStepGenProg (fun _ _ => 0) env fuel st s) ∧
    EmittedSubroutine .exact clearSlotGenProg
      (WordEncoding.encode (α := KickClearInput))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax)
      (fun _ _ => 0) ∧
    EmittedSubroutine .exact popUnindexedSlotGenProg
      (WordEncoding.encode (α := KickPopInput))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax ∧ d.lastSlot < d.rp.nMax)
      (fun _ _ => 0) := ⟨
  exists_emitted_not_readsWidth realizes_allocKickTableGen,
  exists_emitted_not_readsWidth realizes_querySlotGen,
  exists_emitted_not_readsWidth realizes_readMetaGen,
  exists_emitted_not_readsWidth realizes_writeMetaGen,
  exists_emitted_not_readsWidth realizes_kickStepGen,
  exists_emitted_not_readsWidth realizes_kickLoopGen,
  exists_emitted_not_readsWidth realizes_clearSlotGen,
  exists_emitted_not_readsWidth realizes_popUnindexedSlotGen
⟩

/-- Concrete 64-bit `KickEnv` and `KickEnvGen` witness on `testParams` at `base = 0`. -/
theorem test_kickEnvGen_64 :
    KickEnv testParams 64 0 ∧ KickEnvGen 64 (mkKickRuntimeParams testParams) 0 := by
  have henv : KickEnv testParams 64 0 :=
    ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
  exact ⟨henv, ⟨testParams, rfl, henv⟩⟩

/-- Concrete check of `memoryCost` bounds and `ValidHistory` certificates across all eight
subroutines. -/
theorem test_memoryCost_and_validHistory :
    let s : Memory.State := ⟨zeroMem, 3000⟩
    memoryCost (allocKickTableProg testParams) s = totalSpace testParams + 1 ∧
      memoryCost (querySlotProg testParams 0 0 7) s ≤ 6 ∧
      memoryCost (readMetaProg testParams 0 0) s = 2 ∧
      memoryCost (writeMetaProg testParams 0 0 1) s = 4 ∧
      memoryCost (kickStepProg testParams 0 2000 ⟨0, 7, 42, 0, 1⟩) s ≤ 21 ∧
      memoryCost (kickLoopProg testParams 0 2000 7 42 0) s ≤ 21 * testParams.kickLimit ∧
      memoryCost (clearSlotProg testParams 0 0) s = 16 ∧
      memoryCost (popUnindexedSlotProg testParams 0 0 1) s = 46 ∧
      (Memory.spec 64).ValidHistory s
        ((Memory.spec 64).clientHistory s (readMetaProg testParams 0 0)) ∧
      (Memory.spec 64).ValidHistory s
        ((Memory.spec 64).clientHistory s (writeMetaProg testParams 0 0 1)) := by
  intro s
  have henv := test_kickEnvGen_64.1
  have hwf : Memory.WellFormed 64 s := ⟨by decide, fun _ => Nat.two_pow_pos 64⟩
  exact ⟨memoryCost_allocKickTableProg testParams s,
    memoryCost_querySlotProg_le testParams 0 0 7 s,
    memoryCost_readMetaProg testParams 0 0 s,
    memoryCost_writeMetaProg testParams 0 0 1 s,
    memoryCost_kickStepProg_le testParams 0 2000 ⟨0, 7, 42, 0, 1⟩ s,
    memoryCost_kickLoopProg_le testParams 0 2000 ⟨0, 7, 42, 0, 1⟩ testParams.kickLimit s,
    memoryCost_clearSlotProg testParams 0 0 s,
    memoryCost_popUnindexedSlotProg testParams 0 0 1 s,
    validHistory_readMetaProg testParams rfl test_hw (by decide) (by dsimp [s]; decide),
    validHistory_writeMetaProg testParams henv (by decide) hwf (by dsimp [s]; decide)⟩

/-- Concrete 64-bit satisfiability of `KickStepSafe`, `iterationSafe`, and `ValidHistory` across
`kickLimit = 3` steps on `testParams` via `validHistory_kickLoopProg`. -/
theorem test_kickLoop_safe_nonvacuous :
    let rp := mkKickRuntimeParams testParams
    let env : KickStepEnv := ⟨rp, 0, 2000⟩
    let s₀ : Memory.State := ⟨fun _ => 0, 3000⟩
    KickStepSafe 64 (env, ⟨0, 7, 42, 0, 1⟩) s₀ ∧
      iterationSafe kickStepGenProg KickStepSafe 64 env testParams.kickLimit
        ⟨0, 7, 42, 0, 1⟩ s₀ ∧
      (Memory.spec 64).ValidHistory s₀
        ((Memory.spec 64).clientHistory s₀ (kickLoopProg testParams 0 2000 7 42 0)) := by
  intro rp env s₀
  have henv := test_kickEnvGen_64.1
  have henvG := test_kickEnvGen_64.2
  have hs0 : KickStepSafe 64 (env, ⟨0, 7, 42, 0, 1⟩) s₀ :=
    ⟨henvG, fun _ => ⟨by decide, by decide, by decide⟩⟩
  have hwf : Memory.WellFormed 64 s₀ := ⟨by decide, fun _ => show 0 < 2 ^ 64 by decide⟩
  have htot : totalSpace testParams ≤ 1500 := by decide
  have hkl : testParams.kickLimit = 3 := rfl
  exact ⟨hs0, validHistory_kickLoopProg testParams henv hwf (by dsimp [s₀]; omega)
    (by dsimp [s₀]; omega) (fun i hi => by omega) (fun _ _ => by dsimp [s₀]; decide)⟩

/-- Non-vacuous native execution and `.halt`-rejection test for `realizes_allocKickTableGen` at
`w = 64`: executes `allocKickTableGenProg` on an emitted width-free code to
`y.regs frontier = totalSpace testParams > 0`, hence `y ≠ x`. -/
theorem test_native_alloc_nonvacuous :
    ∃ (r C : ℕ) (frontier : Fin r) (c : Code .exact r) (x y : Data r),
      let rp := mkKickRuntimeParams testParams
      ¬c.ReadsWidth ∧
      ExecWithin 64 c x y (C * (memoryCost (allocKickTableGenProg rp)
        (memoryState frontier x) + 1)) ∧
      memoryState frontier y = (Memory.spec 64).clientState (memoryState frontier x)
        (allocKickTableGenProg rp) ∧
      x.regs frontier = 0 ∧ y.regs frontier = totalSpace testParams ∧ y ≠ x := by
  obtain ⟨r, C, frontier, src, _, c, hnw, hk_le, hsrc, hrun⟩ :=
    exists_emitted_not_readsWidth realizes_allocKickTableGen
  have : 12 ≤ frontier.1 := hk_le
  let rp := mkKickRuntimeParams testParams
  let x : Data r := {
    regs := fun reg => if h : reg.1 < 12 then WordEncoding.encode rp ⟨reg.1, h⟩ else 0
    mem := fun _ => 0
  }
  have hxf : x.regs frontier = 0 := dite_eq_right (by omega)
  have hms : memoryState frontier x = ⟨fun _ => 0, 0⟩ := Memory.State.ext rfl hxf
  have hfit_rp : ∀ i : Fin 12, Fits 64 (WordEncoding.encode rp i) :=
    fits_encode_mkKickRuntimeParams testParams test_kickEnvGen_64.1 (by decide) (by decide)
  have hxb : x.Bounded 64 := ⟨fun reg => by
    dsimp [x]; split_ifs with h
    · exact hfit_rp ⟨reg.1, h⟩
    · decide, fun _ => show 0 < 2 ^ 64 by decide⟩
  have hin : x.regs ∘ src = WordEncoding.encode rp := by
    funext i; dsimp [x]; rw [dite_eq_left (by rw [hsrc i]; exact i.2)]
    exact congrArg (WordEncoding.encode rp) (Fin.ext (hsrc i))
  have hv : (Memory.spec 64).ValidHistory (memoryState frontier x)
      ((Memory.spec 64).clientHistory (memoryState frontier x) (allocKickTableGenProg rp)) := by
    rw [hms]
    exact validHistory_allocKickTableProg testParams (by decide)
  obtain ⟨y, hex, hm, _⟩ := hrun 64 rp x hxb hin trivial hv
  have hyf : y.regs frontier = totalSpace testParams := by
    have hm_fr := congrArg Memory.State.frontier hm
    rw [hms, clientState_width, (allocKickTableProg_spec testParams test_hw _).2.1, zero_add]
      at hm_fr
    exact hm_fr
  have hpos : 0 < totalSpace testParams := by decide
  exact ⟨r, C, frontier, c, x, y, hnw, hex, hm, hxf, hyf,
    fun heq => by rw [heq, hxf] at hyf; omega⟩

/-- Non-vacuous native execution test for `realizes_querySlotGen` at `w = 64` instantiating
`KickEnvGen` and `ValidHistory`: queries occupied slot `0` (`quot = 7, val = 42`) and verifies the
emitted width-free `Code` writes `WordEncoding.encode (some 42)` into `res`. -/
theorem test_native_query_nonvacuous :
    ∃ (r C : ℕ) (res : Fin 2 → Fin r) (frontier : Fin r) (c : Code .exact r) (x y : Data r),
      let rp := mkKickRuntimeParams testParams
      let d : KickQueryInput := ⟨rp, 0, 0, 7⟩
      ¬c.ReadsWidth ∧
      ExecWithin 64 c x y (C * (memoryCost (querySlotGenProg d)
        (memoryState frontier x) + 1)) ∧
      memoryState frontier y = (Memory.spec 64).clientState (memoryState frontier x)
        (querySlotGenProg d) ∧
      (∀ i : Fin 2, y.regs (res i) = WordEncoding.encode (some (42 : ℕ)) i) := by
  obtain ⟨r, C, frontier, src, res, c, hnw, hk_le, hsrc, hrun⟩ :=
    exists_emitted_not_readsWidth realizes_querySlotGen
  have : 15 ≤ frontier.1 := hk_le
  let rp := mkKickRuntimeParams testParams
  let d : KickQueryInput := ⟨rp, 0, 0, 7⟩
  let mQ : ℕ → ℕ :=
    writeOccMem 0 testParams (writeValMem 0 testParams (writeQuotMem 0 testParams zeroMem 0 7) 0 42)
      0 1
  let x : Data r := {
    regs := fun reg =>
      if h : reg.1 < 15 then WordEncoding.encode d ⟨reg.1, h⟩
      else if reg = frontier then totalSpace testParams else 0
    mem := mQ
  }
  have hxf : x.regs frontier = totalSpace testParams := by
    dsimp [x]; rw [dite_eq_right (by omega), ite_eq_left rfl]
  have hms : memoryState frontier x = ⟨mQ, totalSpace testParams⟩ := Memory.State.ext rfl hxf
  have hfit_d : ∀ i : Fin 15, Fits 64 (WordEncoding.encode d i) :=
    fits_encode_kickQueryInput
      (fits_encode_mkKickRuntimeParams testParams test_kickEnvGen_64.1 (by decide) (by decide))
      (by decide) (by decide) (by decide)
  have hmQ_fit : ∀ a, Fits 64 (mQ a) := by
    have h0 : ∀ a, zeroMem a < 2 ^ 64 := fun _ => Nat.two_pow_pos 64
    have h1 : ∀ a, writeQuotMem 0 testParams zeroMem 0 7 a < 2 ^ 64 :=
      BitPackedArray.writePacked_lt_two_pow (w := 64) (by decide) (by decide) h0 0 7
    have h2 : ∀ a, writeValMem 0 testParams (writeQuotMem 0 testParams zeroMem 0 7) 0 42 a <
        2 ^ 64 :=
      BitPackedArray.writePacked_lt_two_pow (w := 64) (by decide) (by decide) h1 0 42
    exact BitPackedArray.writePacked_lt_two_pow (w := 64) (by decide) (by decide) h2 0 1
  have hxb : x.Bounded 64 := ⟨fun reg => by
    dsimp [x]; split_ifs with h1 h2
    · exact hfit_d ⟨reg.1, h1⟩
    · decide
    · decide, hmQ_fit⟩
  have hin : x.regs ∘ src = WordEncoding.encode d := by
    funext i; dsimp [x]; rw [dite_eq_left (by rw [hsrc i]; exact i.2)]
    exact congrArg (WordEncoding.encode d) (Fin.ext (hsrc i))
  have hs : KickEnvGen 64 d.rp d.base ∧ d.slot < d.rp.nMax :=
    ⟨test_kickEnvGen_64.2, by decide⟩
  have hv : (Memory.spec 64).ValidHistory (memoryState frontier x)
      ((Memory.spec 64).clientHistory (memoryState frontier x) (querySlotGenProg d)) := by
    rw [hms]
    exact validHistory_querySlotProg testParams rfl test_hw (by decide) (by dsimp only; omega)
  obtain ⟨y, hex, hm, hout⟩ := hrun 64 d x hxb hin hs hv
  have hres_eq : (Memory.spec 64).clientResult (memoryState frontier x) (querySlotGenProg d) =
      some 42 := by
    rw [clientResult_width, hms]
    have hq_spec := (querySlotProg_spec testParams (base := 0) (slot := 0) (q := 7)
      (by decide) ⟨mQ, totalSpace testParams⟩).2
    change (Memory.spec 0).clientResult ⟨mQ, totalSpace testParams⟩
      (querySlotProg testParams 0 0 7) = some 42
    rw [hq_spec]
    have heQ := writeQuotMem_effects (base := 0) testParams test_hw zeroMem
      (by decide : 0 < testParams.nMax)
      (by decide : 7 < 2 ^ quotBits testParams)
    have heV := writeValMem_effects (base := 0) testParams test_hw
      (writeQuotMem 0 testParams zeroMem 0 7)
      (by decide : 0 < testParams.nMax) (by decide : 42 < 2 ^ valBits testParams.V)
    have heO := writeOccMem_effects (base := 0) testParams test_hw
      (writeValMem 0 testParams (writeQuotMem 0 testParams zeroMem 0 7) 0 42)
      (by decide : 0 < occLen testParams) (by decide : 1 < 2 ^ 1)
    dsimp only [mQ]
    rw [heO.2.2.1, heO.1, heV.1, heQ.1, heO.2.1, heV.2.1]
    decide
  rw [hres_eq] at hout
  exact ⟨r, C, res, frontier, c, x, y, hnw, hex, hm, hout⟩

/-- Non-vacuous native execution and `.halt`-rejection test for `realizes_clearSlotGen` at `w = 64`
instantiating `KickEnvGen` and `validHistory_clearSlotProg`: clears occupied slot (`occ = 1 ↦ 0`),
hence `y ≠ x`. -/
theorem test_native_clear_nonvacuous :
    ∃ (r T : ℕ) (frontier : Fin r) (c : Code .exact r) (x y : Data r),
      let rp := mkKickRuntimeParams testParams
      let d : KickClearInput := ⟨rp, 0, 0⟩
      ¬c.ReadsWidth ∧
      ExecWithin 64 c x y T ∧
      memoryState frontier y = (Memory.spec 64).clientState (memoryState frontier x)
        (clearSlotGenProg d) ∧
      y ≠ x := by
  obtain ⟨r, C, frontier, src, _, c, hnw, hk_le, hsrc, hrun⟩ :=
    exists_emitted_not_readsWidth realizes_clearSlotGen
  have : 14 ≤ frontier.1 := hk_le
  let rp := mkKickRuntimeParams testParams
  let d : KickClearInput := ⟨rp, 0, 0⟩
  let mC : ℕ → ℕ := writeOccMem 0 testParams zeroMem 0 1
  let x : Data r := {
    regs := fun reg =>
      if h : reg.1 < 14 then WordEncoding.encode d ⟨reg.1, h⟩
      else if reg = frontier then totalSpace testParams else 0
    mem := mC
  }
  have hxf : x.regs frontier = totalSpace testParams := by
    dsimp [x]; rw [dite_eq_right (by omega), ite_eq_left rfl]
  have hms : memoryState frontier x = ⟨mC, totalSpace testParams⟩ := Memory.State.ext rfl hxf
  have hfit_d : ∀ i : Fin 14, Fits 64 (WordEncoding.encode d i) :=
    fits_encode_kickClearInput
      (fits_encode_mkKickRuntimeParams testParams test_kickEnvGen_64.1 (by decide) (by decide))
      (by decide) (by decide)
  have hmC_fit : ∀ a, Fits 64 (mC a) :=
    BitPackedArray.writePacked_lt_two_pow (w := 64) (by decide) (by decide)
      (fun _ => Nat.two_pow_pos 64) 0 1
  have hxb : x.Bounded 64 := ⟨fun reg => by
    dsimp [x]; split_ifs with h1 h2
    · exact hfit_d ⟨reg.1, h1⟩
    · decide
    · decide, hmC_fit⟩
  have hin : x.regs ∘ src = WordEncoding.encode d := by
    funext i; dsimp [x]; rw [dite_eq_left (by rw [hsrc i]; exact i.2)]
    exact congrArg (WordEncoding.encode d) (Fin.ext (hsrc i))
  have hs : KickEnvGen 64 d.rp d.base ∧ d.slot < d.rp.nMax :=
    ⟨test_kickEnvGen_64.2, by decide⟩
  have hwf : Memory.WellFormed 64 ⟨mC, totalSpace testParams⟩ := ⟨by decide, hmC_fit⟩
  have hv : (Memory.spec 64).ValidHistory (memoryState frontier x)
      ((Memory.spec 64).clientHistory (memoryState frontier x) (clearSlotGenProg d)) := by
    rw [hms]
    exact validHistory_clearSlotProg testParams test_kickEnvGen_64.1 (by decide) hwf
      (by dsimp only; omega)
  obtain ⟨y, hex, hm, _⟩ := hrun 64 d x hxb hin hs hv
  have hne : y ≠ x := fun heq => by
    rw [heq, hms, clientState_width] at hm
    have heO := writeOccMem_effects (base := 0) testParams test_hw zeroMem
      (by decide : 0 < occLen testParams) (by decide : 1 < 2 ^ 1)
    have hocc_before : occAt 0 testParams mC 0 = 1 := by rw [heO.2.2.1]; decide
    obtain ⟨_, _, _, _, _, ho_clear, _⟩ :=
      clearSlotProg_spec testParams test_hw (base := 0) (slot := 0) (by decide)
        ⟨mC, totalSpace testParams⟩
    have hmem_eq : mC = ((Memory.spec 0).clientState ⟨mC, totalSpace testParams⟩
        (clearSlotProg testParams 0 0)).mem := congrArg Memory.State.mem hm
    have hocc_after : occAt 0 testParams mC 0 = 0 := by
      conv_lhs => rw [hmem_eq]
      rw [ho_clear]; decide
    omega
  exact ⟨r, _, frontier, c, x, y, hnw, hex, hm, hne⟩

end CslibFrontierTests.DataStructure.WordRAM.KickTree
