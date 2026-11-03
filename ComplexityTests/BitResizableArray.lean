/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.DynamicArray.BitResizable

/-!
# Bit-resizable word-RAM and `b`-bit resizable array tests

Concrete execution tests and axiom guards for:
- `Cslib.DataStructure.Memory.BitPacking` (cross-word bit-field reads and writes),
- `Cslib.DataStructure.Memory.BitMemory` (bit-granular resizable memory segments and multi-segment
  composition), and
- `Cslib.DataStructure.DynamicArray.BitResizable` (tight `n_t * b`-bit resizable array of `b`-bit
  items and two-array subroutine composition).
-/

@[expose] public section

namespace ComplexityTests.BitResizableArray

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.DynamicArray Cslib.DataStructure.DynamicArray.BitResizable

/-- Two `5`-bit items `[17, 29]` packed into `8`-bit words (`w = 8`, `b = 5`), where item `1`
(at bit offset `5..10`) straddles word `0` (`3` low bits in bits `5..7`) and word `1` (`2` high bits
in bits `0..1`). We read both items, overwrite the straddling item `1` with `23`, read it back, and
pop it. -/
def sampleClient : (DynamicArray.spec 8 5).Client (Option ℕ × Option ℕ × Option ℕ × Option ℕ) := do
  let _ ← (DynamicArray.spec 8 5).call (.append 17)
  let _ ← (DynamicArray.spec 8 5).call (.append 29)
  let r0 ← (DynamicArray.spec 8 5).call (.read 0)
  let r1 ← (DynamicArray.spec 8 5).call (.read 1)
  let _ ← (DynamicArray.spec 8 5).call (.write 1 23)
  let r1' ← (DynamicArray.spec 8 5).call (.read 1)
  let p1 ← (DynamicArray.spec 8 5).call .pop
  pure (r0, r1, r1', p1)

/-- Linked execution of `sampleClient` over `BitMemory.spec 8` produces the exact specified answers,
including for item `1` straddling the `8`-bit word boundary. -/
example :
    (BitMemory.spec 8).clientResult BitMemory.empty (link (methods 8 5) sampleClient) =
      (some 17, some 29, some 23, some 23) := by
  decide

/-- After 2 appends and 1 pop of `5`-bit items, the bit-resizable segment holds `1` item `[17]` and
occupies `1 * 5 = 5` bits (`1` machine word of `8` bits). -/
example :
    let s' := (BitMemory.spec 8).clientState BitMemory.empty (link (methods 8 5) sampleClient)
    s'.bitSize = 5 ∧ s'.wordSize 8 = 1 ∧ abs 8 5 s' = [17] := by
  decide

/-- Total bit-memory operation cost of `sampleClient`:
2 appends (`2 × 2 = 4`) + 3 reads (`3 × 1 = 3`) + 1 write (`1`) + 1 nonempty pop (`3`)
= `11` bit-memory operations (bounded by `3 × 7 = 21`). -/
example :
    let linked := link (methods 8 5) sampleClient
    (BitMemory.spec 8).totalCost (BitMemory.charge 8) BitMemory.empty
      ((BitMemory.spec 8).clientHistory BitMemory.empty linked) = 11 := by
  decide

/-- Single-tape two-array composition (`w = 8`, `b = 5`): initialize two arrays in one linear
`BitMemory.State`, append `22` to array 2 (at offset `8`, so `bitSize = 13`), and then run
`singleTapePop₂Append₁Prog 8 5` to pop `22` from array 2 via `shrink 5` and reuse those `5` bits
via `grow 5` to append `22` to array 1. -/
def singleTapeTransferProg : BitMemory.Prog ℕ := do
  initSingleTapeTwoArrays 8
  let off ← BitMemory.grow 5
  BitMemory.writeBits off 5 22
  singleTapePop₂Append₁Prog 8 5

example :
    let s' := (BitMemory.spec 8).clientState BitMemory.empty singleTapeTransferProg
    (BitMemory.spec 8).clientResult BitMemory.empty singleTapeTransferProg = 22 ∧
    s'.bitSize = 13 ∧ s'.wordSize 8 = 2 ∧
    s'.getField 8 0 8 = 1 ∧ s'.getField 8 8 5 = 22 := by
  decide

/--
info: 'Cslib.DataStructure.Memory.BitMemory.spec_refines_dirtySpec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitMemory.spec_refines_dirtySpec

/--
info: 'Cslib.DataStructure.Memory.BitMemory.singleTape_reuse_released_bits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitMemory.singleTape_reuse_released_bits

/--
info: 'Cslib.DataStructure.Memory.BitMemory.swapRemoveChunkProg_demonic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitMemory.swapRemoveChunkProg_demonic

/--
info: 'Cslib.WordRAM.BitRAM.readBitsCode_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitRAM.readBitsCode_exec

/--
info: 'Cslib.WordRAM.BitRAM.writeBitsCode_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitRAM.writeBitsCode_exec

/--
info: 'Cslib.WordRAM.BitRAM.realizeOpCode_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitRAM.realizeOpCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.client_run_from_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.client_run_from_empty

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.dirty_client_run_from_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.dirty_client_run_from_empty

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.appendCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.appendCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.popCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.popCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.readCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.readCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.writeCode_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.writeCode_exec

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.singleTape_sequential_subroutine_reuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.singleTape_sequential_subroutine_reuse

/--
info: 'Cslib.DataStructure.DynamicArray.BitResizable.singleTape_pop₂_append₁_reuses_released_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicArray.BitResizable.singleTape_pop₂_append₁_reuses_released_bits

end ComplexityTests.BitResizableArray
