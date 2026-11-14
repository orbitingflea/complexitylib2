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

1. **Layout & Space Bounds**: verifies `totalSpace_le_kickTreeWords` and
   `kickTreeWords_le_succinctWords` on concrete parameters.
2. **Pure Extraction & Range Bounds**: verifies zero-initialization and bit-width bounds for
   `quotAt`, `valAt`, `occAt`, and `metaAt`.
3. **Sequential `Memory.Prog` Execution & Caller Specs**: exercises concrete bit-packed execution
   and chains `allocKickTableProg_spec`, `kickStepProg_vacant_spec`, `kickStepProg_displace_spec`,
   `querySlotProg_spec`, and `deleteSlotProg_spec` end to end (covering stored `(quot = 0, val = 0)`
   vs empty slots, displacement along `pathBase`, tail replacement `slot ≠ tailSlot`, and
   self-deletion `slot = tailSlot`).
4. **Width-Freedom (`¬ReadsWidth`) & Non-Vacuous Native Execution**: extracts concrete emitted
   `WordRAM.Code` for all five `Realizes .exact` certificates, checks `¬ReadsWidth`, and proves
   non-trivial native `ExecWithin` execution at `w = 64` (`y ≠ x`, rejecting `.halt`).

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
open Cslib.DataStructure.Dictionary.WordRAM.KickTree

/-! ### 1. Concrete Layout and Space Bound Tests -/

/-- Concrete test parameters: 64-bit machine words, capacity 1000, universe `10^6`, values `10^6`,
kick parameter `k = 2`, header space `hSpace = 16`, metadata multiplicity `cMeta = 2`. -/
@[expose] def testParams : KickTreeParams :=
  mkKickTreeParams 64 1000 1000000 1000000 2 16 2

/-- Small concrete test parameters (`w = 16, nMax = 8`) for kernel `decide` evaluation tests. -/
@[expose] def smallParams : KickTreeParams :=
  mkKickTreeParams 16 8 64 64 2 2 2

/-- Word width of `testParams` is positive. -/
theorem test_hw : 0 < testParams.w := by decide

/-- Metadata multiplicity of `testParams` is at least `1`. -/
theorem test_hc : 1 ≤ testParams.cMeta := by decide

/-- Verify the parameterized master space bound on `testParams`. -/
theorem test_totalSpace_le_kickTreeWords :
    totalSpace testParams ≤
      kickTreeWords (testParams.cMeta + 6) (testParams.hSpace + 11)
        testParams.U testParams.V testParams.w testParams.k testParams.nMax :=
  totalSpace_le_kickTreeWords testParams

/-- Verify specialization to `Dynamic.succinctWords` at `k = 2`. -/
theorem test_kickTreeWords_le_succinctWords :
    kickTreeWords 8 27 testParams.U testParams.V testParams.w 2 testParams.nMax ≤
      Dynamic.succinctWords 8 27 testParams.U testParams.V testParams.w testParams.nMax :=
  kickTreeWords_le_succinctWords 8 27 testParams.U testParams.V testParams.w testParams.nMax

/-! ### 2. Pure Extraction and Range Tests -/

/-- Zero memory function. -/
def zeroMem : ℕ → ℕ := fun _ => 0

/-- All four bit-packed logical arrays extract as identically zero on `zeroMem`. -/
theorem test_zero_of_init :
    quotAt 0 testParams zeroMem = (fun _ => 0) ∧
      valAt 0 testParams zeroMem = (fun _ => 0) ∧
      occAt 0 testParams zeroMem = (fun _ => 0) ∧
      metaAt 0 testParams zeroMem = (fun _ => 0) :=
  ⟨quotAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   valAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   occAt_zero_of_init testParams test_hw (fun _ _ _ => rfl),
   metaAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)⟩

/-- Bit-width range bounds hold on arbitrary memory contents. -/
theorem test_range_bounds (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt 0 testParams mem idx < 2 ^ fullQuotBits testParams.U testParams.nMax ∧
      valAt 0 testParams mem idx < 2 ^ valBits testParams.V ∧
      occAt 0 testParams mem idx < 2 ^ 1 ∧
      metaAt 0 testParams mem idx < 2 ^ metaBits testParams :=
  ⟨quotAt_lt 0 testParams mem idx,
   valAt_lt 0 testParams mem idx,
   occAt_lt 0 testParams mem idx,
   metaAt_lt 0 testParams mem idx⟩

/-! ### 3. End-to-End Sequential `_spec` Caller Tests -/

/-- Representative caller chaining `allocKickTableProg_spec`, `kickLoopProg` (`iterate` +
`kickStepProg_vacant_spec` / `kickStepProg_displace_spec` / `kickStepProg_inactive_spec`),
`querySlotProg_spec`, and `deleteSlotProg_spec` end to end on `smallParams`:
1. Allocates zeroed table at `base = 0` (`s₀.frontier = 0`) with switching path `[100, 101] =
   [3, 5]` outside `[0, totalSpace smallParams)`.
2. Runs 2-step `kickLoopProg` inserting `(quot = 0, val = 0, meta = 1)`: step 0 fills vacant slot
   `3` (`active := 0`), step 1 idles; verifies `some 0` at `(3, 0)` and `none` at vacant `(5, 0)`.
3. Runs 2-step `kickLoopProg` inserting `(quot = 7, val = 9, meta = 1)`: step 0 displaces
   `(0, 0, 1)` from slot `3`, step 1 places `(0, 0, 1)` into vacant slot `5`; verifies `some 9` at
   `(3, 7)`, `none` on mismatch `(3, 8)`, and `some 0` at displaced `(5, 0)`.
4. Deletes slot `3` via tail replacement from slot `5`; verifies slot `3` holds `(0, 0)` (`some 0`)
   and reclaimed tail slot `5` returns `none` at quotient `0`.
5. Self-deletes slot `3` (`slot = tailSlot = 3`); verifies slot `3` returns `none`. -/
theorem test_sequential_caller_specs :
    let mInit : ℕ → ℕ := fun a => if a = 100 then 3 else if a = 101 then 5 else 0
    let s₀ : Memory.State := ⟨mInit, 0⟩
    let s₁ := (Memory.spec 0).clientState s₀ (allocKickTableProg smallParams)
    let r₂ := (Memory.spec 0).clientResult s₁ (kickLoopProg smallParams 0 100 2 0 0 1)
    let s₂ := (Memory.spec 0).clientState s₁ (kickLoopProg smallParams 0 100 2 0 0 1)
    let r₄ := (Memory.spec 0).clientResult s₂ (kickLoopProg smallParams 0 100 2 7 9 1)
    let s₄ := (Memory.spec 0).clientState s₂ (kickLoopProg smallParams 0 100 2 7 9 1)
    let s₅ := (Memory.spec 0).clientState s₄ (deleteSlotProg smallParams 0 3 5)
    let s₆ := (Memory.spec 0).clientState s₅ (deleteSlotProg smallParams 0 3 3)
    r₂ = ⟨1, 0, 0, 0, 0⟩ ∧
      r₄ = ⟨2, 0, 0, 0, 0⟩ ∧
      (Memory.spec 0).clientResult s₂ (querySlotProg smallParams 0 3 0) = some 0 ∧
      (Memory.spec 0).clientResult s₂ (querySlotProg smallParams 0 5 0) = none ∧
      (Memory.spec 0).clientResult s₄ (querySlotProg smallParams 0 3 7) = some 9 ∧
      (Memory.spec 0).clientResult s₄ (querySlotProg smallParams 0 3 8) = none ∧
      (Memory.spec 0).clientResult s₄ (querySlotProg smallParams 0 5 0) = some 0 ∧
      (Memory.spec 0).clientResult s₅ (querySlotProg smallParams 0 3 0) = some 0 ∧
      (Memory.spec 0).clientResult s₅ (querySlotProg smallParams 0 5 0) = none ∧
      (Memory.spec 0).clientResult s₆ (querySlotProg smallParams 0 3 0) = none := by
  intro mInit s₀ s₁ r₂ s₂ r₄ s₄ s₅ s₆
  have shw : 0 < smallParams.w := by decide
  have shc : 1 ≤ smallParams.cMeta := by decide
  have htot_le : totalSpace smallParams ≤ 100 := by decide
  have hs1_100 : s₁.mem 100 = 3 := by
    have hno : ¬(Block.mk 0 (totalSpace smallParams)).Owns 100 := by
      simp only [Block.Owns]; omega
    exact (clear_of_not_owns hno).trans rfl
  have hs1_101 : s₁.mem 101 = 5 := by
    have hno : ¬(Block.mk 0 (totalSpace smallParams)).Owns 101 := by
      simp only [Block.Owns]; omega
    exact (clear_of_not_owns hno).trans rfl
  obtain ⟨hbase, _, hq1, hv1, ho1, hm1⟩ := allocKickTableProg_spec smallParams shw s₀
  have hbase0 : (Memory.spec 0).clientResult s₀ (allocKickTableProg smallParams) = 0 := hbase
  rw [hbase0] at hq1 hv1 ho1 hm1
  -- Unroll 2-step kickLoopProg on s₁: step 0 places (0, 0, 1) at vacant slot 3; step 1 is inactive
  have hloop1_res : r₂ =
      (Memory.spec 0).clientResult
        ((Memory.spec 0).clientState s₁ (kickStepProg smallParams 0 100 ⟨0, 0, 0, 1, 1⟩))
        (kickStepProg smallParams 0 100
          ((Memory.spec 0).clientResult s₁ (kickStepProg smallParams 0 100 ⟨0, 0, 0, 1, 1⟩))) := by
    change (Memory.spec 0).clientResult s₁ (kickLoopProg _ _ _ _ _ _ _) = _
    unfold kickLoopProg kickLoopIterGenProg iterate
    rw [StateTransitionSpec.clientResult_bind]
    unfold iterate
    rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hloop1_st : s₂ =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s₁ (kickStepProg smallParams 0 100 ⟨0, 0, 0, 1, 1⟩))
        (kickStepProg smallParams 0 100
          ((Memory.spec 0).clientResult s₁ (kickStepProg smallParams 0 100 ⟨0, 0, 0, 1, 1⟩))) := by
    change (Memory.spec 0).clientState s₁ (kickLoopProg _ _ _ _ _ _ _) = _
    unfold kickLoopProg kickLoopIterGenProg iterate
    rw [StateTransitionSpec.clientState_bind]
    unfold iterate
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hp100_s1 : s₁.mem (100 + 0) = 3 := hs1_100
  have hvac1 : occAt 0 smallParams s₁.mem (s₁.mem (100 + 0)) = 0 := by rw [ho1]
  have hs1a := kickStepProg_vacant_spec smallParams shw shc (base := 0) (pathBase := 100)
    (st := ⟨0, 0, 0, 1, 1⟩) (s := s₁) (by decide) (by rw [hp100_s1]; decide)
    (by decide) (by decide) (by decide) hvac1
  dsimp only at hs1a
  rw [hp100_s1] at hs1a
  obtain ⟨hr1a, _, hout1a, hq2, hv2, hm2, ho2⟩ := hs1a
  have hinact := kickStepProg_inactive_spec smallParams (base := 0) (pathBase := 100)
    (st := ⟨1, 0, 0, 0, 0⟩) rfl
    ((Memory.spec 0).clientState s₁ (kickStepProg smallParams 0 100 ⟨0, 0, 0, 1, 1⟩))
  have hr2_eq : r₂ = ⟨1, 0, 0, 0, 0⟩ := by rw [hloop1_res, hr1a]; exact hinact.1
  have hs2_eq : s₂ =
      (Memory.spec 0).clientState s₁ (kickStepProg smallParams 0 100 ⟨0, 0, 0, 1, 1⟩) := by
    rw [hloop1_st, hr1a]; exact hinact.2
  rw [ ← hs2_eq] at hout1a hq2 hv2 hm2 ho2
  have hs2_100 : s₂.mem (100 + 0) = 3 := (hout1a 100 (by omega)).trans hs1_100
  have hs2_101 : s₂.mem 101 = 5 := (hout1a 101 (by omega)).trans hs1_101
  -- Unroll 2-step kickLoopProg on s₂: step 0 displaces (0, 0, 1) from slot 3; step 1 lands at 5
  set s₃ := (Memory.spec 0).clientState s₂ (kickStepProg smallParams 0 100 ⟨0, 7, 9, 1, 1⟩)
  set st₃ := (Memory.spec 0).clientResult s₂ (kickStepProg smallParams 0 100 ⟨0, 7, 9, 1, 1⟩)
  have hloop2_res : r₄ =
      (Memory.spec 0).clientResult s₃ (kickStepProg smallParams 0 100 st₃) := by
    change (Memory.spec 0).clientResult s₂ (kickLoopProg _ _ _ _ _ _ _) = _
    unfold kickLoopProg kickLoopIterGenProg iterate
    rw [StateTransitionSpec.clientResult_bind]
    unfold iterate
    rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hloop2_st : s₄ =
      (Memory.spec 0).clientState s₃ (kickStepProg smallParams 0 100 st₃) := by
    change (Memory.spec 0).clientState s₂ (kickLoopProg _ _ _ _ _ _ _) = _
    unfold kickLoopProg kickLoopIterGenProg iterate
    rw [StateTransitionSpec.clientState_bind]
    unfold iterate
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hocc2_3 : occAt 0 smallParams s₂.mem (s₂.mem (100 + 0)) ≠ 0 := by
    rw [hs2_100, ho2, Function.update_self]; decide
  have hs3_spec := kickStepProg_displace_spec smallParams shw shc (base := 0) (pathBase := 100)
    (st := ⟨0, 7, 9, 1, 1⟩) (s := s₂) (by decide) (by rw [hs2_100]; decide)
    (by decide) (by decide) (by decide) hocc2_3
  dsimp only at hs3_spec
  rw [hs2_100] at hs3_spec
  obtain ⟨hst3, _, hout3, hq3, hv3, hm3, ho3⟩ := hs3_spec
  have hst3_eq : st₃ = ⟨1, 0, 0, 1, 1⟩ := by
    change (Memory.spec 0).clientResult s₂ _ = _
    rw [hst3, hq2, hv2, hm2, Function.update_self, Function.update_self, Function.update_self]
  have hs3_101 : s₃.mem (100 + st₃.stepIdx) = 5 := by
    rw [hst3_eq]; exact (hout3 101 (by omega)).trans hs2_101
  have hvac3 : occAt 0 smallParams s₃.mem (s₃.mem (100 + st₃.stepIdx)) = 0 := by
    rw [hs3_101, ho3, ho2, ho1, Function.update_of_ne (by decide)]
  have hs4_spec := kickStepProg_vacant_spec smallParams shw shc (base := 0) (pathBase := 100)
    (st := st₃) (s := s₃) (by rw [hst3_eq]; decide) (by rw [hs3_101]; decide)
    (by rw [hst3_eq]; decide) (by rw [hst3_eq]; decide) (by rw [hst3_eq]; decide) hvac3
  dsimp only at hs4_spec
  rw [hs3_101, hst3_eq] at hs4_spec
  dsimp only at hs4_spec
  obtain ⟨hr4a, _, _, hq4, hv4, _, ho4⟩ := hs4_spec
  rw [hst3_eq] at hloop2_res hloop2_st
  have hr4_eq : r₄ = ⟨2, 0, 0, 0, 0⟩ := by rw [hloop2_res]; exact hr4a
  rw [← hloop2_st] at hq4 hv4 ho4
  obtain ⟨_, _, hq5, hv5, _, ho5⟩ :=
    deleteSlotProg_spec smallParams shw shc (base := 0) (by decide : 3 < smallParams.nMax)
      (by decide : 5 < smallParams.nMax) s₄
  obtain ⟨_, _, hq6, hv6, _, ho6⟩ :=
    deleteSlotProg_spec smallParams shw shc (base := 0) (by decide : 3 < smallParams.nMax)
      (by decide : 3 < smallParams.nMax) s₅
  refine ⟨hr2_eq, hr4_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(querySlotProg_spec smallParams (by decide) s₂).2, ho2, hq2, hv2]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₂).2, ho2, ho1]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₄).2, ho4, ho3, ho2, hq4, hq3, hv4, hv3]
    decide
  · rw [(querySlotProg_spec smallParams (by decide) s₄).2, ho4, ho3, ho2, hq4, hq3]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₄).2, ho4, hq4, hv4]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₅).2, ho5, hq5, hv5, ho4, hq4, hv4]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₅).2, ho5]; decide
  · rw [(querySlotProg_spec smallParams (by decide) s₆).2, ho6]; decide

/-! ### 4. Width-Freedom (`¬ReadsWidth`) and Non-Vacuous Native Execution Tests -/

/-- Instantiate any `Realizes` certificate on a concrete disjoint register bank to witness emitted
`WordRAM.Code` satisfying `¬ReadsWidth` alongside its native `ExecWithin` contract. -/
theorem exists_emitted_not_readsWidth {B : Basis} {k l : ℕ} {δ α : Type}
    {prog : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    (h : Realizes B prog input output safe work) :
    ∃ (r C : ℕ) (frontier : Fin r) (src : Fin k → Fin r) (res : Fin l → Fin r) (c : Code B r),
      ¬c.ReadsWidth ∧
      ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
        safe w d (memoryState frontier x) →
        (Memory.spec w).ValidHistory (memoryState frontier x)
          ((Memory.spec w).clientHistory (memoryState frontier x) (prog d)) →
        ∃ y, ExecWithin w c x y
            (C * (memoryCost (prog d) (memoryState frontier x) +
              work d (memoryState frontier x) + 1)) ∧
          memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (prog d) ∧
          ∀ i : Fin l, y.regs (res i) =
            output ((Memory.spec w).clientResult (memoryState frontier x) (prog d)) i := by
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
    emit frontier src tmp, hnw, fun w d x hx hin hs hv => ?_⟩
  obtain ⟨y, hy, hm, hout, _⟩ := hrun w d x hx hin hs hv
  exact ⟨y, hy, hm, hout⟩

/-- Emitted `Code` for `allocKickTableGenProg` satisfies `¬ReadsWidth`. -/
theorem test_not_readsWidth_alloc :
    ∃ (r : ℕ) (c : Code .exact r), ¬c.ReadsWidth := by
  obtain ⟨r, _, _, _, _, c, hnw, _⟩ := exists_emitted_not_readsWidth realizes_allocKickTableGen
  exact ⟨r, c, hnw⟩

/-- Emitted `Code` for `querySlotGenProg` satisfies `¬ReadsWidth`. -/
theorem test_not_readsWidth_query :
    ∃ (r : ℕ) (c : Code .exact r), ¬c.ReadsWidth := by
  obtain ⟨r, _, _, _, _, c, hnw, _⟩ := exists_emitted_not_readsWidth realizes_querySlotGen
  exact ⟨r, c, hnw⟩

/-- Emitted `Code` for `kickStepGenProg` satisfies `¬ReadsWidth`. -/
theorem test_not_readsWidth_kickStep :
    ∃ (r : ℕ) (c : Code .exact r), ¬c.ReadsWidth := by
  obtain ⟨r, _, _, _, _, c, hnw, _⟩ := exists_emitted_not_readsWidth realizes_kickStepGen
  exact ⟨r, c, hnw⟩

/-- Emitted `Code` for `kickLoopIterGenProg` satisfies `¬ReadsWidth`. -/
theorem test_not_readsWidth_kickLoop :
    ∃ (r : ℕ) (c : Code .exact r), ¬c.ReadsWidth := by
  obtain ⟨r, _, _, _, _, c, hnw, _⟩ := exists_emitted_not_readsWidth realizes_kickLoopGen
  exact ⟨r, c, hnw⟩

/-- Emitted `Code` for `deleteSlotGenProg` satisfies `¬ReadsWidth`. -/
theorem test_not_readsWidth_delete :
    ∃ (r : ℕ) (c : Code .exact r), ¬c.ReadsWidth := by
  obtain ⟨r, _, _, _, _, c, hnw, _⟩ := exists_emitted_not_readsWidth realizes_deleteSlotGen
  exact ⟨r, c, hnw⟩

/-- Non-vacuous native execution and `.halt`-rejection test for `realizes_allocKickTableGen`:
at `w = 64`, the emitted width-free `Code` executes within its certified bound from a concrete
bounded initial machine `x` (`x.regs frontier = 0`) to a terminal machine `y` with
`y.regs frontier = totalSpace testParams > 0`, hence `y ≠ x`. -/
theorem test_native_alloc_nonvacuous :
    ∃ (r T : ℕ) (frontier : Fin r) (c : Code .exact r) (x y : Data r),
      ¬c.ReadsWidth ∧ ExecWithin 64 c x y T ∧
        x.regs frontier = 0 ∧ y.regs frontier = totalSpace testParams ∧ y ≠ x := by
  obtain ⟨n, C, emit, hspec⟩ := realizes_allocKickTableGen
  let r := 10 + (1 + n + 1) + 1
  let frontier : Fin r := ⟨10 + (1 + n + 1), by omega⟩
  let src : Fin 10 → Fin r := fun i => ⟨i.1, by omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun j => ⟨10 + j.1, by omega⟩
  have hinj : Function.Injective tmp := fun j₁ j₂ heq =>
    Fin.ext (by have := congrArg Fin.val heq; dsimp [tmp] at this; omega)
  have hdisj : ∀ i j, src i ≠ tmp j := fun i j heq => by
    have := congrArg Fin.val heq; dsimp [src, tmp] at this; omega
  have htf : ∀ j, tmp j ≠ frontier := fun j heq => by
    have := congrArg Fin.val heq; dsimp [tmp, frontier] at this; omega
  have hsf : ∀ i, src i ≠ frontier := fun i heq => by
    have := congrArg Fin.val heq; dsimp [src, frontier] at this; omega
  obtain ⟨hnw, hrun⟩ := hspec frontier src tmp hinj hdisj htf hsf
  let rp := mkKickRuntimeParams testParams
  let x : Data r := {
    regs := fun reg => if h : reg.1 < 10 then WordEncoding.encode rp ⟨reg.1, h⟩ else 0
    mem := fun _ => 0
  }
  have hxf : x.regs frontier = 0 := by
    dsimp [x, frontier]
    exact dite_eq_right (by omega)
  have hms : memoryState frontier x = ⟨fun _ => 0, 0⟩ :=
    Memory.State.ext rfl hxf
  have hfit_rp : ∀ i : Fin 10, Fits 64 (WordEncoding.encode rp i) := by decide
  have hxb : x.Bounded 64 := by
    refine ⟨fun reg => ?_, fun _ => show 0 < 2 ^ 64 by decide⟩
    dsimp [x]
    split_ifs with h
    · exact hfit_rp ⟨reg.1, h⟩
    · decide
  have hin : x.regs ∘ src = WordEncoding.encode rp := by
    funext i
    dsimp [x, src]
    exact dite_eq_left i.2
  have hv : (Memory.spec 64).ValidHistory (memoryState frontier x)
      ((Memory.spec 64).clientHistory (memoryState frontier x) (allocKickTableGenProg rp)) := by
    rw [hms]
    decide
  obtain ⟨y, hex, hm, _, _⟩ := hrun 64 rp x hxb hin trivial hv
  have hyf : y.regs frontier = totalSpace testParams := by
    have hm_fr := congrArg Memory.State.frontier hm
    rw [hms] at hm_fr
    exact hm_fr
  have hpos : 0 < totalSpace testParams := by decide
  have hne : y ≠ x := fun heq => by
    rw [heq, hxf] at hyf
    omega
  exact ⟨r, _, frontier, emit frontier src tmp, x, y, hnw, hex, hxf, hyf, hne⟩

end CslibFrontierTests.DataStructure.WordRAM.KickTree
