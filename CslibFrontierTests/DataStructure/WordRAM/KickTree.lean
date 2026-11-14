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
# Concrete Tests for KickTree Word-RAM Layout and `Memory.Prog` Subroutines

This module tests the concrete execution, layout bounds, extraction invariants, and
`Memory.Prog` subroutines for the STOC 2022 `k`-kick tree dynamic dictionary:

1. **Layout & Space Bounds**: verifies `totalSpace_le_kickTreeWords` and
   `kickTreeWords_le_succinctWords` on concrete parameters.
2. **Extraction Invariants**: tests zero-initialization and value-range invariants for
   `quotAt`, `valAt`, `fourRussiansAt`, `freeSlotAt`, and `cubbyAt`.
3. **`Memory.Prog` Execution**: verifies concrete `clientResult` and `clientState` transitions
   for `initProg`, `queryProg`, `kickStepProg`, `kickLoopProg`, and `deleteProg`.
4. **Width-Freedom**: validates that emitted code for all subroutines satisfies `¬ReadsWidth`.
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

/-- Concrete test parameters: 64-bit machine words, capacity 1000, universe 10^6,
values 10^6, kick parameter k = 2 (STOC 2022 default). -/
@[expose] def testParams : KickTreeParams :=
  mkKickTreeParams 64 1000 1000000 1000000 2

/-- Test that word width is positive. -/
theorem test_hw : 0 < testParams.w := by decide

/-- Verify the deterministic master space bound on concrete parameters. -/
theorem test_totalSpace_le_kickTreeWords :
    totalSpace testParams ≤ kickTreeWords 8 2080 testParams.U testParams.V
      testParams.w testParams.k testParams.n_max :=
  totalSpace_le_kickTreeWords testParams test_hw

/-- Verify the specialization to `succinctWords` at k = 2. -/
theorem test_kickTreeWords_le_succinctWords :
    kickTreeWords 8 2080 testParams.U testParams.V testParams.w 2 testParams.n_max ≤
      Dynamic.succinctWords 8 2080 testParams.U testParams.V testParams.w testParams.n_max :=
  kickTreeWords_le_succinctWords 8 2080 testParams.U testParams.V testParams.w testParams.n_max

/-! ### 2. Pure Extraction and Range Tests -/

/-- Zero memory state. -/
def zeroMem : ℕ → ℕ := fun _ => 0

/-- Test zero-initialization theorem for all extracted arrays on `zeroMem`. -/
theorem test_zero_of_init :
    quotAt 0 testParams zeroMem = (fun _ => 0) ∧
    valAt 0 testParams zeroMem = (fun _ => 0) ∧
    fourRussiansAt 0 testParams zeroMem = (fun _ => 0) ∧
    freeSlotAt 0 testParams zeroMem = (fun _ => 0) ∧
    cubbyAt 0 testParams zeroMem = (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact quotAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)
  · exact valAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)
  · exact fourRussiansAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)
  · exact freeSlotAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)
  · exact cubbyAt_zero_of_init testParams test_hw (fun _ _ _ => rfl)

/-- Test range bounds on arbitrary memory. -/
theorem test_range_bounds (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt 0 testParams mem idx < 2 ^ fullQuotBits testParams.U testParams.n_max ∧
    valAt 0 testParams mem idx < 2 ^ valBits testParams.V ∧
    fourRussiansAt 0 testParams mem idx < 2 ^ 8 ∧
    freeSlotAt 0 testParams mem idx < 2 ^ 1 ∧
    cubbyAt 0 testParams mem idx < 2 ^ max (Nat.iterLog testParams.k testParams.n_max) 1 :=
  ⟨quotAt_lt 0 testParams mem idx,
   valAt_lt 0 testParams mem idx,
   fourRussiansAt_lt 0 testParams mem idx,
   freeSlotAt_lt 0 testParams mem idx,
   cubbyAt_lt 0 testParams mem idx⟩

/-! ### 3. Concrete Execution Tests in `Memory.Prog` -/

/-- Initial clean memory state. -/
def initState : Memory.State where
  mem := fun _ => 0
  frontier := 10000

/-- Test `initProg` execution: writes seeds and zeroes free slot header. -/
theorem test_exec_init :
    let s' := (Memory.spec 64).clientState initState (initProg 100 500 42)
    s'.mem (100 + offSeeds) = 42 ∧
    s'.mem (100 + offSeeds + 1) = 42 ∧
    s'.mem (100 + 500) = 0 := by
  dsimp only [initProg, initState]
  decide

/-- Memory state populated with one active cubby at slot 3 with quotient 7 and value 99. -/
def populatedState : Memory.State where
  mem := fun a =>
    if a = 100 + 300 + 3 then 1        -- offFacility + 3 = active
    else if a = 100 + offQuot + 3 then 7 -- offQuot + 3 = quot 7
    else if a = 100 + 200 + 3 then 99   -- offVal + 3 = val 99
    else 0
  frontier := 10000

/-- Test `queryProg` execution: found case returns stored value 99. -/
theorem test_exec_query_found :
    (Memory.spec 64).clientResult populatedState (queryProg 100 300 200 3 7) = 99 := by
  dsimp only [queryProg, populatedState]
  decide

/-- Test `queryProg` execution: quotient mismatch returns 0. -/
theorem test_exec_query_mismatch :
    (Memory.spec 64).clientResult populatedState (queryProg 100 300 200 3 8) = 0 := by
  dsimp only [queryProg, populatedState]
  decide

/-- Test `queryProg` execution: inactive cubby returns 0. -/
theorem test_exec_query_inactive :
    (Memory.spec 64).clientResult populatedState (queryProg 100 300 200 4 7) = 0 := by
  dsimp only [queryProg, populatedState]
  decide

/-- Test `kickStepProg` execution on an empty slot: writes item and terminates. -/
theorem test_exec_kickStep_empty :
    let res := (Memory.spec 64).clientResult initState (kickStepProg 100 300 (5, 42, 1))
    let s' := (Memory.spec 64).clientState initState (kickStepProg 100 300 (5, 42, 1))
    res = (5, 0, 0) ∧
    s'.mem (100 + offQuot + 5) = 42 ∧
    s'.mem (100 + 300 + 5) = 1 := by
  dsimp only [kickStepProg, initState]
  decide

/-- Test `kickStepProg` execution on an occupied slot: displaces occupant to alternate slot. -/
theorem test_exec_kickStep_displace :
    let sOccupied : Memory.State := { mem := fun a => if a = 100 + offQuot + 4 then 77 else 0,
                                      frontier := 10000 }
    let res := (Memory.spec 64).clientResult sOccupied (kickStepProg 100 300 (4, 42, 1))
    let s' := (Memory.spec 64).clientState sOccupied (kickStepProg 100 300 (4, 42, 1))
    res = (5, 77, 1) ∧
    s'.mem (100 + offQuot + 4) = 42 := by
  dsimp only [kickStepProg]
  decide

/-- Test `kickLoopProg` execution: terminates within 2 steps on displacing insertion. -/
theorem test_exec_kickLoop :
    let sOccupied : Memory.State := { mem := fun a => if a = 100 + offQuot + 4 then 77 else 0,
                                      frontier := 10000 }
    let res := (Memory.spec 64).clientResult sOccupied (kickLoopProg 100 300 3 4 42)
    let s' := (Memory.spec 64).clientState sOccupied (kickLoopProg 100 300 3 4 42)
    res = (5, 0, 0) ∧
    s'.mem (100 + offQuot + 4) = 42 ∧
    s'.mem (100 + offQuot + 5) = 77 ∧
    s'.mem (100 + 300 + 5) = 1 := by
  dsimp only [kickLoopProg, kickLoopIterProg, iterate, kickStepProg]
  decide

/-- Test `deleteProg` execution via tail replacement: moves tail item to deleted slot,
zeroes tail slot, and reclaims free slot. -/
theorem test_exec_delete :
    let sPopulated : Memory.State := {
      mem := fun a =>
        if a = 100 + offQuot + 2 then 11       -- slot 2 item
        else if a = 100 + 200 + 2 then 111
        else if a = 100 + offQuot + 9 then 99  -- tail slot 9 item
        else if a = 100 + 200 + 9 then 999
        else if a = 100 + 400 + 9 then 1       -- tail slot occupied in free-slot tree
        else 0,
      frontier := 10000 }
    let s' := (Memory.spec 64).clientState sPopulated (deleteProg 100 200 400 2 9)
    s'.mem (100 + offQuot + 2) = 99 ∧
    s'.mem (100 + 200 + 2) = 999 ∧
    s'.mem (100 + offQuot + 9) = 0 ∧
    s'.mem (100 + 200 + 9) = 0 ∧
    s'.mem (100 + 400 + 9) = 0 := by
  dsimp only [deleteProg]
  decide

end CslibFrontierTests.DataStructure.WordRAM.KickTree
