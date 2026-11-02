/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.DynamicArray.ResizableWord

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

end ComplexityTests.DataStructureResizableWord
