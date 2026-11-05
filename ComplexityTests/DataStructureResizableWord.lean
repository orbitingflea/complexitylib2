/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.DynamicArray.ResizableWordCode
public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinct
public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinctEpoch

/-!
# Word-granular resizable memory and packed dynamic array tests

Concrete execution traces and axiom checks for:
- `Cslib.DataStructure.Memory.Resizable`: growing and shrinking word-granular segments, demonic vs.
  zero-initialized refinement, and two-way memory reuse (`packTwoWay`).
- `Cslib.DataStructure.DynamicArray.ResizableWord`: bit-packed resizable array of `b`-bit items in
  `w`-bit words (`w = 8`, `b = 5`, where item `1` straddles word `1` and word `2`), verifying
  `O(1)` worst-case operation cost (`≤ 7`), exact word count `1 + ⌈n_t * b / w⌉`, and subroutine
  linking via `link`.
-/

@[expose] public section

namespace ComplexityTests.DataStructureResizableWord

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.DataStructure.DynamicArray

/-- Empty resizable memory segment (`0` allocated words). -/
def emptySeg : Memory.State := Resizable.emptyState

/-- A program on `Resizable.spec 8` that grows by 2 words, writes `42` and `99`, shrinks by 1 word
(releasing cell `1`), grows by 1 word again (obtaining a zeroed cell `1`), and reads both cells. -/
def growShrinkGrow : Resizable.Prog (ℕ × ℕ) :=
  .liftBind (.grow 2) fun _ =>
  .liftBind (.write 0 42) fun () =>
  .liftBind (.write 1 99) fun () =>
  .liftBind (.shrink 1) fun () =>
  .liftBind (.grow 1) fun _ =>
  .liftBind (.read 0) fun v0 =>
  .liftBind (.read 1) fun v1 =>
  .pure (v0, v1)

example : (Resizable.spec 8).clientResult emptySeg growShrinkGrow = (42, 0) := by decide

example : ((Resizable.spec 8).clientState emptySeg growShrinkGrow).frontier = 2 := by decide

example :
    (Resizable.spec 8).ValidHistory emptySeg
      ((Resizable.spec 8).clientHistory emptySeg growShrinkGrow) := by decide

/-- With `w = 8` and `b = 5`, `1` item uses `1 + 1 = 2` words (`[0..5)` in word `1`), and `2` items
use `1 + 2 = 3` words (`[5..10)` straddles word `1` and word `2`). Popping the second item shrinks
the segment back to `2` words. -/
def crossWordClient : (ResizableWord.spec 8 5).Client (ℕ × Option ℕ × ℕ) :=
  ResizableWord.subroutineClient 8 5 19 27

def crossWordLinked : (Resizable.spec 8).Client (ℕ × Option ℕ × ℕ) :=
  link (ResizableWord.refinement 8 5 (by decide) (by decide)).methods crossWordClient

example :
    (Resizable.spec 8).ValidHistory ResizableWord.initState
        ((Resizable.spec 8).clientHistory ResizableWord.initState crossWordLinked) ∧
      (Resizable.spec 8).clientResult ResizableWord.initState crossWordLinked = (19, some 27, 27) ∧
      ResizableWord.abs 8 5
        ((Resizable.spec 8).clientState ResizableWord.initState crossWordLinked) = [27] ∧
      ((Resizable.spec 8).clientState ResizableWord.initState crossWordLinked).frontier = 2 ∧
      (Resizable.spec 8).totalCost Resizable.charge ResizableWord.initState
        ((Resizable.spec 8).clientHistory ResizableWord.initState crossWordLinked) ≤ 42 :=
  ResizableWord.subroutineClient_correct_and_tight (w := 8) (b := 5) (x := 19) (y := 27)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/--
info: 'Cslib.DataStructure.Memory.Resizable.refinesDemonic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Resizable.refinesDemonic

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.refinement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.refinement

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.amortized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.amortized

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.space_tight_every_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.space_tight_every_step

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.subroutineClient_correct_and_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.subroutineClient_correct_and_tight

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.twoArrays_reuse_released_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.twoArrays_reuse_released_memory

/--
info: 'Cslib.WordRAM.Resizable.readSubwordCode_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Resizable.readSubwordCode_exec

/--
info: 'Cslib.WordRAM.Resizable.writeSubwordCode_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Resizable.writeSubwordCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.demonicRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.demonicRefinement

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.demonicAmortized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.demonicAmortized

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.readArrayCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.readArrayCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.writeArrayCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.writeArrayCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.appendArrayCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.appendArrayCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.popArrayCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.popArrayCode_exec

/--
info: 'Cslib.DataStructure.Memory.Resizable.ChunkedTape.releaseWord1_then_allocWord1_spec' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Resizable.ChunkedTape.releaseWord1_then_allocWord1_spec

/--
info: 'Cslib.DataStructure.DynamicArray.ResizableWord.twoArrays_singleTape_reuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ResizableWord.twoArrays_singleTape_reuse

/-! ## Stage 2: Resizable Succinct Dictionary Tests -/

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

example : targetCap 16 0 = 0 := by decide
example : targetCap 16 5 = 10 := by decide
example : targetCap 16 10 = 16 := by decide
example : EpochValid 0 0 := by decide
example : EpochValid 5 10 := by decide
example : ¬EpochValid 9 4 := by decide

/-- Sample unbounded-capacity operation history on `Fin 8` with `V = 16`:
three inserts (`0 ↦ 5`, `1 ↦ 9`, `2 ↦ 3`), an overwrite (`1 ↦ 12`), a delete (`0`), and two
queries (`1` and `0`). -/
def sampleDynamicOps : List (Dynamic.Op 8) :=
  [ .insert ⟨0, by decide⟩ 5,
    .insert ⟨1, by decide⟩ 9,
    .insert ⟨2, by decide⟩ 3,
    .insert ⟨1, by decide⟩ 12,
    .delete ⟨0, by decide⟩,
    .query ⟨1, by decide⟩,
    .query ⟨0, by decide⟩ ]

lemma validHistory_sampleDynamicOps :
    (Dynamic.spec 8 16 8).ValidHistory (Dynamic.empty 8) sampleDynamicOps := by
  refine ⟨⟨Or.inl (by decide), by decide⟩,
    ⟨Or.inl (by decide), by decide⟩,
    ⟨Or.inl (by decide), by decide⟩,
    ⟨Or.inr (by decide), by decide⟩,
    trivial, trivial, trivial, trivial⟩

example :
    let s_final := ((Dynamic.spec 8 16 8).run (Dynamic.empty 8) sampleDynamicOps).1
    let n_final := (Dynamic.dom s_final).card
    let n_init_final := runEpochInit 16 (Dynamic.empty 8) 0 sampleDynamicOps
    let N_final := targetCap 8 n_init_final
    EpochValid n_final N_final ∧
    N_final ≤ 8 ∧
    Dynamic.ValuesBounded 16 s_final ∧
    activeEpochWords 8 16 64 N_final n_final ≤ Dynamic.succinctWords 1227 213 8 16 64 n_final ∧
    64 * activeEpochWords 8 16 64 N_final n_final ≤
      Dynamic.optBits 8 16 n_final + 1227 * n_final * Dynamic.logLogFactor n_final + 214 * 64 ∧
    2 * rebuildUnitCost 8 16 64 * natDist n_final n_init_final ≤
      sampleDynamicOps.length * resizableChargeVal 8 16 64 :=
  unbounded_seq_expected_amortized (U := 8) (V := 16) (w := 64)
    (by decide) (by decide) sampleDynamicOps validHistory_sampleDynamicOps

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.activeEpochWords_le_succinctWords_of_le_four_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms activeEpochWords_le_succinctWords_of_le_four_mul

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.succinctWords_mul_w_le_bits' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms succinctWords_mul_w_le_bits

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.init_resizable_succinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms init_resizable_succinct

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.step_resizable_succinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_resizable_succinct

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rebuild_epoch_expected_amortized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rebuild_epoch_expected_amortized

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.unbounded_step_expected_amortized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unbounded_step_expected_amortized

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.unbounded_seq_expected_amortized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unbounded_seq_expected_amortized

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.subroutine_client_reuse_released_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subroutine_client_reuse_released_memory

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.shrink_and_reuse_in_place' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shrink_and_reuse_in_place

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compactedEpochWords_le_succinctWords' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms compactedEpochWords_le_succinctWords

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.w_mul_compactedEpochWords_le_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms w_mul_compactedEpochWords_le_bits

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.dictionary_client_memory_reuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dictionary_client_memory_reuse

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.extractStepRebuildOps_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms extractStepRebuildOps_spec

/--
info: 'Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.unbounded_seq_machine_expected_amortized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unbounded_seq_machine_expected_amortized

end ComplexityTests.DataStructureResizableWord
