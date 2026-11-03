/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.BitPacking
public import Complexity.DataStructure.Memory.Frame
public import Complexity.DataStructure.StateTransition.Refinement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bit-Granular Resizable Word-RAM Memory Model

This module defines the **bit-granular resizable Word-RAM memory model** on top of the existing
Word-RAM and `Cslib.DataStructure.Memory` infrastructure. In this model (following the virtual
memory framework of Pătrașcu (2008) and Dodis, Pătrașcu, and Thorup (2010)), a data structure's
memory is a single contiguous array of bits `[0, bitSize)` whose allocated length `bitSize : ℕ`
grows and shrinks dynamically in **bits** while being accessed in fields of up to `w` bits on a
`w`-bit Word RAM [Hagerup1998].

## Model design and rejected alternatives

1. **Semantics of growing and shrinking (`grow`, `shrink`) and address-capacity bound (`Fits w`):**
   - `grow δ` (admissible when `Fits w (s.bitSize + δ)`, i.e., `s.bitSize + δ < 2 ^ w`) increases
     `s.bitSize` to `s.bitSize + δ` and returns the old `s.bitSize` (the bit offset of the newly
     allocated `δ`-bit slice). Requiring `Fits w (s.bitSize + δ)` ensures that every bit offset and
     the total bit size `s.bitSize` can be stored and manipulated in a single `w`-bit Word-RAM
     register (`State.WellFormed.bitSize_fits`).
   - `shrink δ` (admissible when `δ ≤ s.bitSize`) decreases `s.bitSize` to `s.bitSize - δ` and
     clears the released bits `[s.bitSize - δ, s.bitSize)`.
   - *Rejected alternative:* Allowing `resize newSize` without separating `grow` and `shrink`, or
     allowing `s.bitSize` to exceed `2 ^ w - 1` (which would make bit offsets overflow `w`-bit
     registers on the Word RAM).

2. **Contents of newly obtained memory (`dirtySpec` vs. `spec`):**
   - Our primary specification is the demonic relational specification `BitMemory.dirtySpec w`, in
     which `grow δ` may place arbitrary Boolean bit values in the newly allocated slice
     `[s.bitSize, s.bitSize + δ)` while preserving all existing bits `[0, s.bitSize)`, maintaining
     `zero_above` for all `i ≥ s.bitSize + δ`, and preserving `w`-bit word bounds
     (`wellFormed_dirtyStep`).
   - Alongside `dirtySpec w`, we provide the deterministic zero-initialized specification
     `BitMemory.spec w` (`HasStepFn`) and prove
     `spec_refines_dirtySpec : Refinement (dirtySpec w) (spec w)` together with
     `writeFieldMem_of_dirtyStep_grow`, which shows that any `grow δ` (`δ ≤ w`) immediately
     followed by overwriting the new `δ`-bit slice transitions to the exact same state under every
     demonic choice of `dirtyStep` as under `spec w`.
   - *Rejected alternative:* Verifying data structures only against zero-initialized `grow δ`, which
     would rely on the allocator clearing newly grown bits for free.

3. **Cost of resizing (`charge`):**
   - Reading or writing a `b`-bit field (`b ≤ w`) costs `1` bit-memory unit (and executes in `O(1)`
     Word-RAM instructions; see `Complexity.Computability.WordRAM.BitResizable`).
   - Resizing by `δ` bits (`grow δ` or `shrink δ`) costs `max 1 (δ ⌈/⌉ w)` units, which is `1`
     whenever `δ ≤ w` and `⌈δ / w⌉` when `δ > w`.
   - *Rejected alternative:* Charging `δ` (one unit per bit) for `grow δ` / `shrink δ`, which
     would make `b`-bit appends cost `Θ(b)` instead of `O(1)` on a Word RAM; or charging `1` for
     arbitrarily large `δ ≫ w`.

4. **Space measure at every step (`spaceBitsAt`, `wordSize`):**
   - In state `s : BitMemory.State`, the current space is `s.bitSize` bits (occupying
     `s.wordSize w = s.bitSize ⌈/⌉ w` words of `w` bits).
   - Space is measured at **every step `t`** by the current `bitSize` after `t` operations, so
     `shrink δ` reduces the space measure by `δ` bits immediately.
   - *Rejected alternative:* Measuring space only by a monotone high-water mark (`frontier`),
     which cannot express space reclamation when a structure shrinks.

5. **Frame condition and single-tape composition (`DirtyFramed`, `Framed`, `boundedDirtySpec`,
   `swapRemoveChunkProg`):**
   - `BitMemory.DirtyFramed D w` and `BitMemory.Framed D w` equip refinements over `dirtySpec w`
     and `spec w` with an exact bit-size profile `sizeBits : D.State → ℕ` such that
     `s.bitSize = sizeBits (abs s)` in every represented state. Every `DirtyFramed D w` induces a
     `Framed D w` via `DirtyFramed.toFramed`.
   - Multiple structures share **one** linear `BitMemory.State` `[0, s.bitSize)` (rather than
     separate `State × State` tapes). Under `boundedDirtySpec w B`, shrinking by `δ` bits on the
     single tape immediately reduces `s.bitSize` by `δ` and makes those `δ` bits available for a
     subsequent `grow δ` (`singleTape_reuse_released_bits`). For general multi-segment composition
     with `O(1)` worst-case operations per segment on a single `[0, s.bitSize)` tape, we provide
     the swap-with-last physical chunk compaction primitive `swapRemoveChunkProg` (`O(1)` operations
     on `dirtySpec w`), which releases an interior `s`-bit chunk by moving the last physical chunk
     into the freed slot and calling `shrink s` at the end of the single tape.
   - *Rejected alternative:* Modeling multi-structure composition only as a cartesian product
     `State × State` of separate memory tapes, which sidesteps multiplexing inside one linear
     address space `[0, s.bitSize)`.

## Main definitions

* `BitMemory.State`, `BitMemory.Op`, `BitMemory.dirtyStep`, `BitMemory.dirtySpec`: state,
  operations, and demonic specification of bit-granular resizable memory.
* `BitMemory.stepFn`, `BitMemory.spec`, `BitMemory.spec_refines_dirtySpec`: deterministic
  zero-initialized specification and its refinement of `dirtySpec w`.
* `BitMemory.charge`: operation cost charging `1` for `b ≤ w` field accesses and `max 1 (δ ⌈/⌉ w)`
  for `δ`-bit resizes.
* `BitMemory.DirtyFramed`, `BitMemory.Framed`: bit-size-tracked refinements over `dirtySpec w` and
  `spec w`.
* `BitMemory.boundedDirtySpec`, `BitMemory.boundedSpec`: single-tape bit-budgeted specifications.
* `BitMemory.swapRemoveChunkProg`: single-tape `O(1)` swap-with-last chunk release primitive.

## Main results

* `BitMemory.wellFormed_dirtyStep`, `BitMemory.wellFormed_stepFn`: every valid operation preserves
  `State.WellFormed w` under both `dirtySpec w` and `spec w`.
* `BitMemory.writeFieldMem_of_dirtyStep_grow`: overwriting a newly grown `δ`-bit slice (`δ ≤ w`)
  yields the exact same state under any demonic `dirtyStep` as under deterministic `stepFn`.
* `BitMemory.singleTape_reuse_released_bits`: shrinking a single tape by `δ` bits frees `δ` bits
  that a subsequent `grow δ` can immediately allocate within the same bit budget `B`.
* `BitMemory.swapRemoveChunkProg_demonic`: `swapRemoveChunkProg` compacts an interior `s`-bit chunk
  and shrinks the single tape by `s` bits in `3` `BitMemory` operations under `dirtySpec w`.
* `BitMemory.realize_readBits_triple`, `BitMemory.realize_writeBits_triple`: realization of
  bit-field operations on `Memory.spec w`.

## References

* [T. Hagerup, *Sorting and Searching on the Word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.DataStructure.Memory.BitMemory

open scoped BigOperators
open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking

/-! ## Concrete state and bitwise range clearing -/

/-- The state of a bit-granular resizable memory segment: word-indexed storage `mem : ℕ → ℕ`
together with the current allocated size `bitSize : ℕ` in **bits**. -/
@[ext]
structure State where
  /-- Underlying `w`-bit word storage; word `q` holds bits `[q * w, (q + 1) * w)`. -/
  mem : ℕ → ℕ
  /-- Current allocated size in bits. -/
  bitSize : ℕ

/-- The empty bit-resizable memory with `0` allocated bits and zeroed words. -/
def empty : State where
  mem _ := 0
  bitSize := 0

@[simp] theorem empty_bitSize : empty.bitSize = 0 := rfl
@[simp] theorem empty_mem (q : ℕ) : empty.mem q = 0 := rfl

/-- The number of `w`-bit words occupied by `s.bitSize` bits (`⌈s.bitSize / w⌉`). -/
def State.wordSize (s : State) (w : ℕ) : ℕ :=
  s.bitSize ⌈/⌉ w

/-- Project a bit-resizable memory state to a word-level `Memory.State` with frontier
`s.wordSize w`. -/
def State.toMemoryState (s : State) (w : ℕ) : Memory.State where
  mem := s.mem
  frontier := s.wordSize w

/-- Read bit `i` from `s` at word width `w`. -/
def State.getBit (s : State) (w i : ℕ) : Bool :=
  readBit w 0 s.mem i

/-- Read a `b`-bit field at bit offset `a` from `s` at word width `w`. -/
def State.getField (s : State) (w a b : ℕ) : ℕ :=
  readField w 0 s.mem a b

@[simp]
theorem getBit_empty (w i : ℕ) : empty.getBit w i = false := by
  simp [State.getBit, readBit]

/-- Clear all bits of `word` whose bit indices `q * w + j` (`j < w`) lie in `[lo, hi)`,
simultaneously masking `word` to `w` bits, using pure bitwise/shift operations (`&&&`, `^^^`,
`<<<`, `-`). -/
def clearRangeWord (w word q lo hi : ℕ) : ℕ :=
  let start := lo - q * w
  let stop := min w (hi - q * w)
  clearMask (word &&& bitMask w) (sliceMask start (stop - start))

/-- Clear all bits in the half-open bit interval `[lo, hi)` across `mem : ℕ → ℕ`. -/
def clearRangeMem (w : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → ℕ :=
  fun q => clearRangeWord w (mem q) q lo hi

theorem clearRangeMem_fits (w : ℕ) (mem : ℕ → ℕ) (lo hi q : ℕ) :
    Fits w (clearRangeMem w mem lo hi q) :=
  clearMask_lt (Nat.and_lt_two_pow (mem q) (bitMask_lt w)) _

theorem readBit_clearRangeMem {w : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) (lo hi i : ℕ) :
    readBit w 0 (clearRangeMem w mem lo hi) i =
      if lo ≤ i ∧ i < hi then false else readBit w 0 mem i := by
  have hmod : i % w < w := Nat.mod_lt i hw
  have hdiv_mod : i / w * w + i % w = i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i w
  simp only [readBit, Nat.zero_add, clearRangeMem, clearRangeWord, clearMask_testBit,
    Nat.testBit_and, bitMask_testBit, hmod, decide_true, Bool.and_true, sliceMask_testBit]
  by_cases h : lo ≤ i ∧ i < hi
  · have hcond : lo - i / w * w ≤ i % w ∧
        i % w < lo - i / w * w + (min w (hi - i / w * w) - (lo - i / w * w)) := by
      omega
    simp [h, hcond]
  · have hcond : ¬(lo - i / w * w ≤ i % w ∧
        i % w < lo - i / w * w + (min w (hi - i / w * w) - (lo - i / w * w))) := by
      omega
    rw [ite_eq_right h, decide_eq_false hcond]
    simp

/-- Well-formedness at word width `w`: every word fits in `w` bits, the allocated bit size
`s.bitSize` fits in a `w`-bit word (`s.bitSize < 2 ^ w`), and every bit outside the allocated range
`[0, s.bitSize)` is `false`. -/
structure State.WellFormed (s : State) (w : ℕ) : Prop where
  /-- Every word in `s.mem` is `< 2 ^ w`. -/
  mem_fits : ∀ q, Fits w (s.mem q)
  /-- The allocated bit size fits in a `w`-bit register (`s.bitSize < 2 ^ w`). -/
  bitSize_fits : Fits w s.bitSize
  /-- All bits at or above `s.bitSize` are zero. -/
  zero_above : ∀ i, s.bitSize ≤ i → s.getBit w i = false

theorem wellFormed_empty (w : ℕ) : empty.WellFormed w where
  mem_fits _ := fits_zero w
  bitSize_fits := fits_zero w
  zero_above i _ := getBit_empty w i

/-! ## Operations and transitions -/

/-- Operations on a bit-granular resizable memory. -/
inductive Op where
  /-- Read a `len`-bit integer (`len ≤ w`) starting at bit offset `bitAddr`. -/
  | readBits (bitAddr len : ℕ)
  /-- Write `val` (`< 2 ^ len`) into the `len`-bit field (`len ≤ w`) at bit offset `bitAddr`. -/
  | writeBits (bitAddr len val : ℕ)
  /-- Grow the allocated bit size by `δ` bits, returning the previous `bitSize`. -/
  | grow (δ : ℕ)
  /-- Shrink the allocated bit size by `δ` bits (`δ ≤ bitSize`), releasing the trailing `δ` bits. -/
  | shrink (δ : ℕ)
  /-- Query the current allocated size in bits (`bitSize`). -/
  | size

/-- Result type of each `BitMemory.Op`. -/
abbrev Op.Result : Op → Type
  | .readBits _ _ => ℕ
  | .writeBits _ _ _ => Unit
  | .grow _ => ℕ
  | .shrink _ => Unit
  | .size => ℕ

/-- Admissibility of a `BitMemory.Op` at word width `w` in state `s`.
In particular, `.grow δ` requires `Fits w (s.bitSize + δ)` so that the new bit size and all valid
bit addresses fit in a single `w`-bit machine word. -/
def valid (w : ℕ) (s : State) : Op → Prop
  | .readBits bitAddr len => len ≤ w ∧ bitAddr + len ≤ s.bitSize
  | .writeBits bitAddr len val => len ≤ w ∧ bitAddr + len ≤ s.bitSize ∧ Fits len val
  | .grow δ => Fits w (s.bitSize + δ)
  | .shrink δ => δ ≤ s.bitSize
  | .size => True

/-- Deterministic transition function for `BitMemory.Op` at word width `w`.
In `grow δ`, newly obtained bits in `[s.bitSize, s.bitSize + δ)` are zero-initialized.
In `shrink δ`, released bits in `[s.bitSize - δ, s.bitSize)` are cleared. -/
def stepFn (w : ℕ) (s : State) : (o : Op) → State × o.Result
  | .readBits bitAddr len =>
      (s, readField w 0 s.mem bitAddr len)
  | .writeBits bitAddr len val =>
      (⟨writeFieldMem w 0 s.mem bitAddr len val, s.bitSize⟩, ())
  | .grow δ =>
      (⟨clearRangeMem w s.mem s.bitSize (s.bitSize + δ), s.bitSize + δ⟩, s.bitSize)
  | .shrink δ =>
      (⟨clearRangeMem w s.mem (s.bitSize - δ) s.bitSize, s.bitSize - δ⟩, ())
  | .size =>
      (s, s.bitSize)

/-- Deterministic state-transition specification of bit-granular resizable memory at word width
`w`. -/
abbrev spec (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (stepFn w) (valid w)

/-- Programs over `BitMemory.Op`. -/
abbrev Prog (α : Type) : Type := PFunctor.FreeM ⟨Op, Op.Result⟩ α

/-- Read `len` bits at `bitAddr`. -/
abbrev readBits (bitAddr len : ℕ) : Prog ℕ :=
  PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.readBits bitAddr len)

/-- Write `val` into `len` bits at `bitAddr`. -/
abbrev writeBits (bitAddr len val : ℕ) : Prog Unit :=
  PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.writeBits bitAddr len val)

/-- Grow the bit allocation by `δ` bits. -/
abbrev grow (δ : ℕ) : Prog ℕ :=
  PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.grow δ)

/-- Shrink the bit allocation by `δ` bits. -/
abbrev shrink (δ : ℕ) : Prog Unit :=
  PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.shrink δ)

/-- Query the current allocated size in bits. -/
abbrev getSize : Prog ℕ :=
  PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) .size

@[simp] theorem stepFn_readBits (w : ℕ) (s : State) (bitAddr len : ℕ) :
    stepFn w s (.readBits bitAddr len) = (s, readField w 0 s.mem bitAddr len) := rfl

@[simp] theorem stepFn_writeBits (w : ℕ) (s : State) (bitAddr len val : ℕ) :
    stepFn w s (.writeBits bitAddr len val) =
      (⟨writeFieldMem w 0 s.mem bitAddr len val, s.bitSize⟩, ()) := rfl

@[simp] theorem stepFn_grow (w : ℕ) (s : State) (δ : ℕ) :
    stepFn w s (.grow δ) =
      (⟨clearRangeMem w s.mem s.bitSize (s.bitSize + δ), s.bitSize + δ⟩, s.bitSize) := rfl

@[simp] theorem stepFn_shrink (w : ℕ) (s : State) (δ : ℕ) :
    stepFn w s (.shrink δ) =
      (⟨clearRangeMem w s.mem (s.bitSize - δ) s.bitSize, s.bitSize - δ⟩, ()) := rfl

@[simp] theorem stepFn_size (w : ℕ) (s : State) :
    stepFn w s .size = (s, s.bitSize) := rfl

@[simp] theorem valid_readBits (w : ℕ) (s : State) (bitAddr len : ℕ) :
    valid w s (.readBits bitAddr len) ↔ len ≤ w ∧ bitAddr + len ≤ s.bitSize := Iff.rfl

@[simp] theorem valid_writeBits (w : ℕ) (s : State) (bitAddr len val : ℕ) :
    valid w s (.writeBits bitAddr len val) ↔
      len ≤ w ∧ bitAddr + len ≤ s.bitSize ∧ Fits len val := Iff.rfl

@[simp] theorem valid_grow (w : ℕ) (s : State) (δ : ℕ) :
    valid w s (.grow δ) ↔ Fits w (s.bitSize + δ) := Iff.rfl

@[simp] theorem valid_shrink (w : ℕ) (s : State) (δ : ℕ) :
    valid w s (.shrink δ) ↔ δ ≤ s.bitSize := Iff.rfl

@[simp] theorem valid_size (w : ℕ) (s : State) :
    valid w s .size ↔ True := Iff.rfl

@[simp] theorem runClient_readBits_bind {w : ℕ} {α : Type} (bitAddr len : ℕ)
    (k : ℕ → Prog α) (s : State) :
    (spec w).runClient s (readBits bitAddr len >>= k) =
      let (v, s', os) := (spec w).runClient s (k (readField w 0 s.mem bitAddr len))
      (v, s', .readBits bitAddr len :: os) := rfl

@[simp] theorem runClient_writeBits_bind {w : ℕ} {α : Type} (bitAddr len val : ℕ)
    (k : Unit → Prog α) (s : State) :
    (spec w).runClient s (writeBits bitAddr len val >>= k) =
      let (v, s', os) := (spec w).runClient
        ⟨writeFieldMem w 0 s.mem bitAddr len val, s.bitSize⟩ (k ())
      (v, s', .writeBits bitAddr len val :: os) := rfl

@[simp] theorem runClient_grow_bind {w : ℕ} {α : Type} (δ : ℕ)
    (k : ℕ → Prog α) (s : State) :
    (spec w).runClient s (grow δ >>= k) =
      let (v, s', os) := (spec w).runClient
        ⟨clearRangeMem w s.mem s.bitSize (s.bitSize + δ), s.bitSize + δ⟩ (k s.bitSize)
      (v, s', .grow δ :: os) := rfl

@[simp] theorem runClient_shrink_bind {w : ℕ} {α : Type} (δ : ℕ)
    (k : Unit → Prog α) (s : State) :
    (spec w).runClient s (shrink δ >>= k) =
      let (v, s', os) := (spec w).runClient
        ⟨clearRangeMem w s.mem (s.bitSize - δ) s.bitSize, s.bitSize - δ⟩ (k ())
      (v, s', .shrink δ :: os) := rfl

@[simp] theorem runClient_getSize_bind {w : ℕ} {α : Type}
    (k : ℕ → Prog α) (s : State) :
    (spec w).runClient s (getSize >>= k) =
      let (v, s', os) := (spec w).runClient s (k s.bitSize)
      (v, s', .size :: os) := rfl

/-! ## Preservation of well-formedness and bit-level transition laws -/

/-- Every admissible operation preserves `State.WellFormed w` when `0 < w`. -/
theorem wellFormed_stepFn {w : ℕ} (hw : 0 < w) {s : State} (hs : s.WellFormed w)
    {o : Op} (hv : valid w s o) : (stepFn w s o).1.WellFormed w := by
  cases o with
  | readBits bitAddr len => exact hs
  | writeBits bitAddr len val =>
    obtain ⟨hlen, hbound, _⟩ := hv
    refine ⟨writeFieldMem_fits hw hs.mem_fits hlen val, hs.bitSize_fits, fun i hi => ?_⟩
    simp only [stepFn, State.getBit] at hi ⊢
    rw [readBit_writeFieldMem hw s.mem hlen i, ite_eq_right (by omega)]
    exact hs.zero_above i hi
  | grow δ =>
    refine ⟨clearRangeMem_fits w s.mem s.bitSize (s.bitSize + δ), hv, fun i hi => ?_⟩
    simp only [stepFn, State.getBit] at hi ⊢
    rw [readBit_clearRangeMem hw s.mem s.bitSize (s.bitSize + δ) i, ite_eq_right (by omega)]
    exact hs.zero_above i (by omega)
  | shrink δ =>
    refine ⟨clearRangeMem_fits w s.mem (s.bitSize - δ) s.bitSize,
      lt_of_le_of_lt (Nat.sub_le _ _) hs.bitSize_fits, fun i hi => ?_⟩
    simp only [stepFn, State.getBit] at hi ⊢
    rw [readBit_clearRangeMem hw s.mem (s.bitSize - δ) s.bitSize i]
    by_cases hlt : i < s.bitSize
    · exact ite_eq_left ⟨hi, hlt⟩
    · rw [ite_eq_right (by omega)]
      exact hs.zero_above i (by omega)
  | size => exact hs

/-- `grow δ` preserves all existing bits below `s.bitSize`. -/
theorem getBit_stepFn_grow_of_lt {w : ℕ} (hw : 0 < w) (s : State) (δ : ℕ)
    {i : ℕ} (hi : i < s.bitSize) :
    (stepFn w s (.grow δ)).1.getBit w i = s.getBit w i := by
  simp only [stepFn, State.getBit]
  rw [readBit_clearRangeMem hw s.mem s.bitSize (s.bitSize + δ) i, ite_eq_right (by omega)]

/-- `grow δ` preserves all existing fields within `[0, s.bitSize)`. -/
theorem getField_stepFn_grow {w : ℕ} (hw : 0 < w) (s : State) (δ : ℕ)
    {a b : ℕ} (hbw : b ≤ w) (hab : a + b ≤ s.bitSize) :
    (stepFn w s (.grow δ)).1.getField w a b = s.getField w a b := by
  apply readField_congr_bits hw hbw
  intro k hk
  exact getBit_stepFn_grow_of_lt hw s δ (by omega)

/-- `shrink δ` preserves all surviving bits below `s.bitSize - δ`. -/
theorem getBit_stepFn_shrink_of_lt {w : ℕ} (hw : 0 < w) (s : State) (δ : ℕ)
    {i : ℕ} (hi : i < s.bitSize - δ) :
    (stepFn w s (.shrink δ)).1.getBit w i = s.getBit w i := by
  simp only [stepFn, State.getBit]
  rw [readBit_clearRangeMem hw s.mem (s.bitSize - δ) s.bitSize i, ite_eq_right (by omega)]

/-- `shrink δ` preserves all surviving fields within `[0, s.bitSize - δ)`. -/
theorem getField_stepFn_shrink {w : ℕ} (hw : 0 < w) (s : State) (δ : ℕ)
    {a b : ℕ} (hbw : b ≤ w) (hab : a + b ≤ s.bitSize - δ) :
    (stepFn w s (.shrink δ)).1.getField w a b = s.getField w a b := by
  apply readField_congr_bits hw hbw
  intro k hk
  exact getBit_stepFn_shrink_of_lt hw s δ (by omega)

/-! ## Relational dirty-allocation specification (`dirtySpec`) and refinement -/

/-- Relational step semantics where `grow δ` may place arbitrary Boolean bit values in the newly
allocated slice `[s.bitSize, s.bitSize + δ)` while preserving all existing bits `[0, s.bitSize)`,
clearing all bits at or above `s.bitSize + δ`, and maintaining `w`-bit word bounds. -/
def dirtyStep (w : ℕ) (s : State) (o : Op) (s' : State) (r : o.Result) : Prop :=
  match o with
  | .grow δ =>
      s'.bitSize = s.bitSize + δ ∧ r = s.bitSize ∧
      (∀ q, Fits w (s'.mem q)) ∧
      (∀ i < s.bitSize, s'.getBit w i = s.getBit w i) ∧
      (∀ i, s.bitSize + δ ≤ i → s'.getBit w i = false)
  | o => stepFn w s o = (s', r)

/-- Relational specification of bit-granular resizable memory with uninitialized (`dirty`) newly
grown bits. -/
abbrev dirtySpec (w : ℕ) : StateTransitionSpec where
  State := State
  Op := Op
  Result := Op.Result
  step := dirtyStep w
  valid := valid w

/-- Every deterministic `stepFn` transition from a well-formed state satisfies `dirtyStep`. -/
theorem dirtyStep_of_stepFn {w : ℕ} (hw : 0 < w) {s : State} (hs : s.WellFormed w) (o : Op) :
    dirtyStep w s o (stepFn w s o).1 (stepFn w s o).2 := by
  cases o with
  | grow δ =>
    refine ⟨rfl, rfl, clearRangeMem_fits w s.mem s.bitSize (s.bitSize + δ),
      fun i hi => getBit_stepFn_grow_of_lt hw s δ hi, fun i hi => ?_⟩
    simp only [stepFn, State.getBit]
    rw [readBit_clearRangeMem hw s.mem s.bitSize (s.bitSize + δ) i, ite_eq_right (by omega)]
    exact hs.zero_above i (by omega)
  | readBits _ _ => rfl
  | writeBits _ _ _ => rfl
  | shrink _ => rfl
  | size => rfl

/-- Every admissible `dirtyStep` transition preserves `State.WellFormed w` when `0 < w`. -/
theorem wellFormed_dirtyStep {w : ℕ} (hw : 0 < w) {s s' : State} {o : Op} {r : o.Result}
    (hs : s.WellFormed w) (hv : valid w s o) (hstep : dirtyStep w s o s' r) :
    s'.WellFormed w := by
  cases o with
  | grow δ =>
    obtain ⟨hsz, _, hmem, _, hzero⟩ := hstep
    exact ⟨hmem, hsz ▸ hv, fun i hi => hzero i (hsz ▸ hi)⟩
  | readBits _ _ =>
    have h := wellFormed_stepFn hw hs hv
    rwa [hstep] at h
  | writeBits _ _ _ =>
    have h := wellFormed_stepFn hw hs hv
    rwa [hstep] at h
  | shrink _ =>
    have h := wellFormed_stepFn hw hs hv
    rwa [hstep] at h
  | size =>
    have h := wellFormed_stepFn hw hs hv
    rwa [hstep] at h

/-- **Demonic grow followed by full slice overwrite is deterministic**: when `s` is well-formed at
`w > 0`, `δ ≤ w`, and `dirtyStep w s (.grow δ) s₁ offset` transitions to any demonic state `s₁`,
overwriting `[offset, offset + δ)` with `val` produces the exact same memory state
`writeFieldMem w 0 s.mem s.bitSize δ val` independent of the demonic bits in `s₁`. -/
theorem writeFieldMem_of_dirtyStep_grow {w : ℕ} (hw : 0 < w) {s s₁ : State}
    (hs : s.WellFormed w) {δ offset val : ℕ} (hδ : δ ≤ w)
    (hstep : dirtyStep w s (.grow δ) s₁ offset) :
    writeFieldMem w 0 s₁.mem offset δ val = writeFieldMem w 0 s.mem s.bitSize δ val := by
  obtain ⟨hsz, rfl, hmem₁, hpres, hzero₁⟩ := hstep
  funext q
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · have hmod : (q * w + j) % w = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    have hdiv : (q * w + j) / w = q := by
      rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]
    have hbit := readBit_writeFieldMem hw s₁.mem (base := 0) (a := s.bitSize) (b := δ)
      (val := val) hδ (q * w + j)
    have hbit₀ := readBit_writeFieldMem hw s.mem (base := 0) (a := s.bitSize) (b := δ)
      (val := val) hδ (q * w + j)
    simp only [readBit, Nat.zero_add, hdiv, hmod] at hbit hbit₀
    rw [hbit, hbit₀]
    split_ifs with hrange
    · rfl
    · by_cases hlt : q * w + j < s.bitSize
      · have hp := hpres (q * w + j) hlt
        simpa [State.getBit, readBit, hdiv, hmod] using hp
      · have hge : s.bitSize + δ ≤ q * w + j := by omega
        have hz₁ := hzero₁ (q * w + j) hge
        have hz₀ := hs.zero_above (q * w + j) (by omega)
        simp only [State.getBit, readBit, Nat.zero_add, hdiv, hmod] at hz₁ hz₀
        rw [hz₁, hz₀]
  · have hf₁ := writeFieldMem_fits (base := 0) (a := s.bitSize) hw hmem₁ hδ val q
    have hf₀ := writeFieldMem_fits (base := 0) (a := s.bitSize) hw hs.mem_fits hδ val q
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hf₁
        (Nat.pow_le_pow_right Nat.two_pos (Nat.le_of_not_lt hj))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hf₀
        (Nat.pow_le_pow_right Nat.two_pos (Nat.le_of_not_lt hj)))]

/-- In particular, deterministic `stepFn` on `.grow δ` (`δ ≤ w`) followed by `writeFieldMem`
simplifies `writeFieldMem w 0 (clearRangeMem w s.mem s.bitSize (s.bitSize + δ)) s.bitSize δ val`
to `writeFieldMem w 0 s.mem s.bitSize δ val`. -/
theorem writeFieldMem_clearRangeMem_self {w : ℕ} (hw : 0 < w) {s : State}
    (hs : s.WellFormed w) {δ : ℕ} (hδ : δ ≤ w) (val : ℕ) :
    writeFieldMem w 0 (clearRangeMem w s.mem s.bitSize (s.bitSize + δ)) s.bitSize δ val =
      writeFieldMem w 0 s.mem s.bitSize δ val :=
  writeFieldMem_of_dirtyStep_grow hw hs hδ (dirtyStep_of_stepFn hw hs (.grow δ))

/-! ## Operation cost, `spec_refines_dirtySpec`, and space measure -/

/-- Operation cost in the bit-granular resizable memory model at word width `w`:
* `readBits`, `writeBits`, `size` cost `1` unit;
* `grow δ` and `shrink δ` cost `max 1 (δ ⌈/⌉ w)` units (`1` whenever `δ ≤ w`). -/
def charge (w : ℕ) (_ : State) : Op → ℕ
  | .readBits _ _ => 1
  | .writeBits _ _ _ => 1
  | .grow δ => max 1 (δ ⌈/⌉ w)
  | .shrink δ => max 1 (δ ⌈/⌉ w)
  | .size => 1

@[simp]
theorem charge_readBits (w : ℕ) (s : State) (a b : ℕ) :
    charge w s (.readBits a b) = 1 := rfl

@[simp]
theorem charge_writeBits (w : ℕ) (s : State) (a b v : ℕ) :
    charge w s (.writeBits a b v) = 1 := rfl

@[simp]
theorem charge_size (w : ℕ) (s : State) :
    charge w s .size = 1 := rfl

/-- Growing by `δ ≤ w` bits costs `1` unit. -/
@[simp]
theorem charge_grow_of_le {w δ : ℕ} (hw : 0 < w) (hδ : δ ≤ w) (s : State) :
    charge w s (.grow δ) = 1 := by
  have hle : δ ⌈/⌉ w ≤ 1 := by rwa [Nat.ceilDiv_le_iff hw, one_mul]
  exact max_eq_left hle

/-- Shrinking by `δ ≤ w` bits costs `1` unit. -/
@[simp]
theorem charge_shrink_of_le {w δ : ℕ} (hw : 0 < w) (hδ : δ ≤ w) (s : State) :
    charge w s (.shrink δ) = 1 := by
  have hle : δ ⌈/⌉ w ≤ 1 := by rwa [Nat.ceilDiv_le_iff hw, one_mul]
  exact max_eq_left hle

/-- Every operation in `BitMemory` costs at least `1` unit. -/
theorem one_le_charge (w : ℕ) (s : State) (o : Op) : 1 ≤ charge w s o := by
  cases o <;> simp [charge]

/-- The deterministic zero-initialized specification `BitMemory.spec w` refines the demonic
dirty-allocation specification `BitMemory.dirtySpec w` on well-formed states. -/
@[nolint defsWithUnderscore] def spec_refines_dirtySpec {w : ℕ} (hw : 0 < w) :
    Refinement (dirtySpec w) (spec w) where
  methods o := .liftBind o fun a => .pure a
  inv s := s.WellFormed w
  abs s := s
  valid o _ hv := .liftBind (D := spec w) o _ hv fun s' a _ => .pure s' a
  correct {s} o {a s' tr} hs hv hrun := by
    cases hrun with
    | liftBind _ _ a _ hstep hrest =>
      cases hrest
      have hfn : stepFn w s o = (s', a) := (((spec w).step_iff_stepFn _ _ _ _).mp hstep).symm
      have hdirty := dirtyStep_of_stepFn hw hs o
      have hwf := wellFormed_stepFn hw hs hv
      rw [hfn] at hdirty hwf
      exact ⟨hdirty, hwf⟩

/-- `spec_refines_dirtySpec` preserves `BitMemory.charge w` with zero potential. -/
theorem spec_refines_dirtySpec_amortized {w : ℕ} (hw : 0 < w) :
    (spec_refines_dirtySpec hw).Amortized (charge w) (charge w) (fun _ => 0) := by
  refine ⟨fun {s} o {a s' tr} _ _ hrun => ?_⟩
  cases hrun with
  | liftBind _ _ r _ _ hrest =>
    cases hrest
    simp [spec_refines_dirtySpec]

/-- The current allocated space in bits at step `t` along an operation sequence `ops` from `s₀`. -/
def spaceBitsAt (w : ℕ) (s₀ : State) (ops : List Op) (t : ℕ) : ℕ :=
  (((spec w).run s₀ (ops.take t)).1).bitSize

/-! ## Frame condition and single-tape memory reuse -/

/-- A refinement of an abstract specification `D` over the demonic `BitMemory.dirtySpec w` with an
exact bit-space profile `sizeBits : D.State → ℕ` at every step. -/
structure DirtyFramed (D : StateTransitionSpec) (w : ℕ) extends Refinement D (dirtySpec w) where
  /-- Exact allocated bit count of a represented abstract state `d : D.State`. -/
  sizeBits : D.State → ℕ
  /-- Every represented concrete state has `s.bitSize = sizeBits (abs s)`. -/
  bitSize_eq : ∀ {s}, inv s → s.bitSize = sizeBits (abs s)
  /-- Every represented concrete state is well-formed at word width `w`. -/
  wellFormed : ∀ {s}, inv s → s.WellFormed w

/-- A refinement of an abstract specification `D` over the deterministic `BitMemory.spec w` with an
exact bit-space profile `sizeBits : D.State → ℕ` at every step. -/
structure Framed (D : StateTransitionSpec) (w : ℕ) extends Refinement D (spec w) where
  /-- Exact allocated bit count of a represented abstract state `d : D.State`. -/
  sizeBits : D.State → ℕ
  /-- Every represented concrete state has `s.bitSize = sizeBits (abs s)`. -/
  bitSize_eq : ∀ {s}, inv s → s.bitSize = sizeBits (abs s)
  /-- Every represented concrete state is well-formed at word width `w`. -/
  wellFormed : ∀ {s}, inv s → s.WellFormed w

/-- Any `DirtyFramed D w` refinement over `dirtySpec w` automatically induces a `Framed D w`
refinement over `spec w` by composing with `spec_refines_dirtySpec`. -/
def DirtyFramed.toFramed {D : StateTransitionSpec} {w : ℕ} (hw : 0 < w)
    (M : DirtyFramed D w) : Framed D w where
  toRefinement := M.toRefinement.comp (spec_refines_dirtySpec hw)
  sizeBits := M.sizeBits
  bitSize_eq hi := M.bitSize_eq hi.2
  wellFormed hi := hi.1

/-- Single-tape bit-budgeted demonic specification: a single `BitMemory.State` `[0, s.bitSize)`
operating within a total bit budget `B` (`B < 2 ^ w`). -/
abbrev boundedDirtySpec (w B : ℕ) : StateTransitionSpec where
  State := State
  Op := Op
  Result := Op.Result
  step := dirtyStep w
  valid s o := valid w s o ∧
    match o with
    | .grow δ => s.bitSize + δ ≤ B
    | _ => s.bitSize ≤ B

/-- Single-tape bit-budgeted deterministic specification: a single `BitMemory.State`
`[0, s.bitSize)` operating within a total bit budget `B`. -/
abbrev boundedSpec (w B : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (stepFn w) (boundedDirtySpec w B).valid

/-- **Single-tape memory reuse theorem**: on a single bit-resizable tape `[0, s.bitSize)` within bit
budget `B` (`Fits w B`), shrinking by `δ ≤ s.bitSize` bits immediately reduces `s₁.bitSize` to
`s.bitSize - δ`, and those `δ` released bits can be immediately re-allocated on the **same** tape
via `grow δ` (under any demonic transition of `dirtyStep w`) without exceeding the bit budget
`B`. -/
theorem singleTape_reuse_released_bits {w B δ : ℕ} {s : State}
    (hB_fits : Fits w B) (hB : s.bitSize ≤ B) (hδ : δ ≤ s.bitSize) :
    let s₁ := (stepFn w s (.shrink δ)).1
    (boundedDirtySpec w B).valid s (.shrink δ) ∧
      s₁.bitSize = s.bitSize - δ ∧
      (boundedDirtySpec w B).valid s₁ (.grow δ) ∧
      ∀ s₂ r, dirtyStep w s₁ (.grow δ) s₂ r → s₂.bitSize = s.bitSize ∧ s₂.bitSize ≤ B := by
  refine ⟨⟨hδ, hB⟩, rfl, ⟨?_, ?_⟩, fun s₂ r hstep => ?_⟩
  · change (s.bitSize - δ) + δ < 2 ^ w
    exact lt_of_le_of_lt (by omega) hB_fits
  · dsimp only [stepFn]
    omega
  · obtain ⟨hsz, _⟩ := hstep
    dsimp only [stepFn] at hsz
    exact ⟨by omega, by omega⟩

/-- **Single-tape `O(1)` swap-with-last chunk release (`[LLYZ23a]` Lemma 5.1 / `[BHKLZ26]`
Lemma 2.1)**: given a single bit-resizable tape `[0, headerBits + (lastPhys + 1) * s)` containing
`lastPhys + 1` physical chunks of `s` bits (`s ≤ w`) after a `headerBits`-bit header, releasing
physical chunk `p ≤ lastPhys` copies the last physical chunk `lastPhys` into slot `p` and shrinks
the single tape by `s` bits in `3` `BitMemory` operations (`readBits`, `writeBits`, `shrink s`). -/
def swapRemoveChunkProg (headerBits s p lastPhys : ℕ) : Prog Unit := do
  let lastVal ← readBits (headerBits + lastPhys * s) s
  writeBits (headerBits + p * s) s lastVal
  shrink s

/-- `swapRemoveChunkProg` is demonically valid on `dirtySpec w` and shrinks the single tape from
`headerBits + (lastPhys + 1) * s` bits to `headerBits + lastPhys * s` bits while preserving all
other physical chunks `q ≠ p` (`q < lastPhys`) and placing the old contents of chunk `lastPhys`
into slot `p`. -/
theorem swapRemoveChunkProg_demonic {w headerBits s p lastPhys : ℕ} (hw : 0 < w) (hsw : s ≤ w)
    {st : State} (hsz : st.bitSize = headerBits + (lastPhys + 1) * s)
    (hp : p ≤ lastPhys) :
    (dirtySpec w).DemonicValid st (swapRemoveChunkProg headerBits s p lastPhys) ∧
      ∀ u st' tr,
        (dirtySpec w).ClientRun st (swapRemoveChunkProg headerBits s p lastPhys) u st' tr →
        st'.bitSize = headerBits + lastPhys * s ∧
        (p < lastPhys →
          st'.getField w (headerBits + p * s) s = st.getField w (headerBits + lastPhys * s) s) ∧
        (∀ q < lastPhys, q ≠ p →
          st'.getField w (headerBits + q * s) s = st.getField w (headerBits + q * s) s) := by
  have hlast_bound : headerBits + lastPhys * s + s ≤ st.bitSize := by
    rw [hsz, Nat.succ_mul]
    omega
  have hp_bound : headerBits + p * s + s ≤ st.bitSize := by
    have : p * s ≤ lastPhys * s := Nat.mul_le_mul_right s hp
    omega
  have hv_read : (dirtySpec w).valid st (.readBits (headerBits + lastPhys * s) s) :=
    ⟨hsw, hlast_bound⟩
  refine ⟨.liftBind _ _ hv_read fun st₁ v hstep₁ => ?_, fun u st' tr hrun => ?_⟩
  · obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
    subst h1
    subst h1v
    have hv_write : (dirtySpec w).valid st
        (.writeBits (headerBits + p * s) s (readField w 0 st.mem (headerBits + lastPhys * s) s)) :=
      ⟨hsw, hp_bound, readField_fits w 0 st.mem _ s⟩
    refine .liftBind _ _ hv_write fun st₂ _ hstep₂ => ?_
    obtain ⟨h2, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
    subst h2
    have hv_shrink : (dirtySpec w).valid
        ⟨writeFieldMem w 0 st.mem (headerBits + p * s) s
          (readField w 0 st.mem (headerBits + lastPhys * s) s), st.bitSize⟩ (.shrink s) := by
      change s ≤ st.bitSize
      omega
    exact .liftBind _ _ hv_shrink fun st₃ _ _ => .pure st₃ ()
  · obtain ⟨_, v, st₁, tr₁, hstep₁, hrest₁, _⟩ :=
      ((dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
    obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
    subst h1
    subst h1v
    obtain ⟨_, _, st₂, tr₂, hstep₂, hrest₂, _⟩ :=
      ((dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrest₁
    obtain ⟨h2, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
    subst h2
    obtain ⟨_, _, st₃, tr₃, hstep₃, hrest₃, _⟩ :=
      ((dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrest₂
    obtain ⟨h3, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₃
    subst h3
    obtain ⟨_, rfl, _⟩ := ((dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrest₃
    have hsz' : st.bitSize = headerBits + lastPhys * s + s := by
      rw [hsz, Nat.succ_mul, Nat.add_assoc]
    refine ⟨by dsimp only [stepFn]; omega, fun hplt => ?_, fun q hq hqp => ?_⟩
    · have hp_surv : headerBits + p * s + s ≤ st.bitSize - s := by
        have : (p + 1) * s ≤ lastPhys * s := Nat.mul_le_mul_right s hplt
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hget := getField_stepFn_shrink hw
        ⟨writeFieldMem w 0 st.mem (headerBits + p * s) s
          (readField w 0 st.mem (headerBits + lastPhys * s) s), st.bitSize⟩ s hsw hp_surv
      dsimp only [stepFn, State.getField] at hget ⊢
      rw [hget]
      exact readField_writeFieldMem_same hw st.mem hsw (readField_fits w 0 st.mem _ s)
    · have hq_surv : headerBits + q * s + s ≤ st.bitSize - s := by
        have : (q + 1) * s ≤ lastPhys * s := Nat.mul_le_mul_right s hq
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hget := getField_stepFn_shrink hw
        ⟨writeFieldMem w 0 st.mem (headerBits + p * s) s
          (readField w 0 st.mem (headerBits + lastPhys * s) s), st.bitSize⟩ s hsw hq_surv
      dsimp only [stepFn, State.getField] at hget ⊢
      rw [hget]
      have hdisj : (headerBits + q * s) + s ≤ headerBits + p * s ∨
          (headerBits + p * s) + s ≤ headerBits + q * s := by
        rcases lt_or_gt_of_ne hqp with hlt | hgt
        · left
          have : (q + 1) * s ≤ p * s := Nat.mul_le_mul_right s hlt
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        · right
          have : (p + 1) * s ≤ q * s := Nat.mul_le_mul_right s hgt
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
      exact readField_writeFieldMem_of_disjoint hw st.mem hsw hsw hdisj

/-! ## Realization of bit-field operations on `Memory.spec w` -/

/-- When a `BitMemory.State` is stored in physical `Memory.State` starting at word `base + 1`
(with word `base` holding `s.bitSize`), reading a `len`-bit field (`len ≤ w`,
`bitAddr + len ≤ s.bitSize`) via `readFieldProg w (base + 1) bitAddr len` costs at most `2` memory
units and returns `(stepFn w s (.readBits bitAddr len)).2`. -/
theorem realize_readBits_triple {w base bitAddr len : ℕ} (hw : 0 < w)
    {s : State} {m : Memory.State}
    (hmem : ∀ q < s.wordSize w, m.mem (base + 1 + q) = s.mem q)
    (hfront : base + 1 + s.wordSize w ≤ m.frontier)
    (hv : valid w s (.readBits bitAddr len)) :
    Triple w m (readFieldProg w (base + 1) bitAddr len) 2
      (fun r m' => r = (stepFn w s (.readBits bitAddr len)).2 ∧ m' = m) := by
  obtain ⟨hlen, hbound⟩ := hv
  rcases Nat.eq_zero_or_pos len with rfl | hpos
  · refine (readFieldProg_triple hw hlen (Or.inl rfl)).mono le_rfl ?_
    rintro r m' ⟨hr, hm'⟩
    exact ⟨by simp [hr, stepFn], hm'⟩
  · have hcov : s.bitSize ≤ s.wordSize w * w := Nat.le_ceilDiv_mul hw
    have ⟨hq₀, hq₁⟩ := word_indices_lt_of_bit_bound hw hpos (hbound.trans hcov)
    refine (readFieldProg_triple hw hlen (Or.inr ⟨by omega, by omega⟩)).mono le_rfl ?_
    rintro r m' ⟨hr, hm'⟩
    refine ⟨?_, hm'⟩
    rw [hr]
    simp only [stepFn]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [readField_testBit hw (base + 1) m.mem hlen k, readField_testBit hw 0 s.mem hlen k]
    split_ifs with hk
    · simp only [readBit, Nat.zero_add]
      have hk_lt : (bitAddr + k) / w < s.wordSize w :=
        (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
      rw [hmem _ hk_lt]
    · rfl

/-- When a `BitMemory.State` is stored in physical `Memory.State` starting at word `base + 1`,
writing a `len`-bit field (`len ≤ w`, `bitAddr + len ≤ s.bitSize`, `Fits len val`) via
`writeFieldProg w (base + 1) bitAddr len val` costs at most `4` memory units, preserves
`m.frontier`, and updates `m.mem (base + 1 + q)` to
`(stepFn w s (.writeBits bitAddr len val)).1.mem q` for all `q < s.wordSize w`. -/
theorem realize_writeBits_triple {w base bitAddr len val : ℕ} (hw : 0 < w)
    {s : State} {m : Memory.State}
    (hm_fits : ∀ addr, Fits w (m.mem addr))
    (hmem : ∀ q < s.wordSize w, m.mem (base + 1 + q) = s.mem q)
    (hfront : base + 1 + s.wordSize w ≤ m.frontier)
    (hv : valid w s (.writeBits bitAddr len val)) :
    Triple w m (writeFieldProg w (base + 1) bitAddr len val) 4
      (fun _ m' =>
        (∀ q < s.wordSize w,
          m'.mem (base + 1 + q) = (stepFn w s (.writeBits bitAddr len val)).1.mem q) ∧
        m'.frontier = m.frontier) := by
  obtain ⟨hlen, hbound, _⟩ := hv
  rcases Nat.eq_zero_or_pos len with rfl | hpos
  · refine (writeFieldProg_triple hw hlen hm_fits (Or.inl rfl)).mono le_rfl ?_
    rintro ⟨⟩ m' ⟨hm, hf⟩
    refine ⟨fun q hq => ?_, hf⟩
    simp [hm, stepFn, hmem q hq]
  · have hcov : s.bitSize ≤ s.wordSize w * w := Nat.le_ceilDiv_mul hw
    have ⟨hq₀, hq₁⟩ := word_indices_lt_of_bit_bound hw hpos (hbound.trans hcov)
    refine (writeFieldProg_triple hw hlen hm_fits (Or.inr ⟨by omega, by omega⟩)).mono le_rfl ?_
    rintro ⟨⟩ m' ⟨hm, hf⟩
    refine ⟨fun q hq => ?_, hf⟩
    rw [hm]
    simp only [stepFn]
    unfold writeFieldMem
    have hlen0 : ¬len = 0 := by omega
    rw [ite_eq_right hlen0, ite_eq_right hlen0]
    simp only [Nat.zero_add]
    by_cases hstrad : w - bitAddr % w < len
    · rw [ite_eq_left hstrad, ite_eq_left hstrad]
      have hne : (bitAddr + len - 1) / w ≠ bitAddr / w :=
        (sub_mod_lt_iff_div_ne hw hpos).mp hstrad
      have hq₁_eq : (bitAddr + len - 1) / w = bitAddr / w + 1 := by
        rcases div_add_pred_eq_or_succ hw hpos hlen with h | h
        · exact absurd h hne
        · exact h
      have hq₁' : bitAddr / w + 1 < s.wordSize w := hq₁_eq ▸ hq₁
      by_cases h1 : q = bitAddr / w + 1
      · subst h1
        have hassoc : base + 1 + (bitAddr / w + 1) = base + 1 + bitAddr / w + 1 := by omega
        rw [hassoc, Function.update_self, Function.update_self,
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          ← hassoc, hmem _ hq₁']
      · rw [Function.update_of_ne (by omega), Function.update_of_ne h1]
        by_cases h0 : q = bitAddr / w
        · subst h0
          rw [Function.update_self, Function.update_self, hmem _ hq₀]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne h0]
          exact hmem q hq
    · rw [ite_eq_right hstrad, ite_eq_right hstrad]
      by_cases h0 : q = bitAddr / w
      · subst h0
        rw [Function.update_self, Function.update_self, hmem _ hq₀]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne h0]
        exact hmem q hq

/-! ## Complete words, partially owned tail word, and `BitUnchangedOutside` frame condition -/

/-- Number of complete `w`-bit words `L = ⌊bitSize / w⌋` in `s`. -/
def State.completeWords (s : State) (w : ℕ) : ℕ :=
  s.bitSize / w

/-- Number of bits `T = bitSize % w` in the partially owned tail word
`s.mem (s.completeWords w)`. -/
def State.tailBits (s : State) (w : ℕ) : ℕ :=
  s.bitSize % w

/-- In a well-formed state at word width `w > 0`, the partially owned tail word at index
`s.completeWords w = s.bitSize / w` fits in `s.tailBits w = s.bitSize % w` bits. -/
theorem State.WellFormed.tail_fits {w : ℕ} (hw : 0 < w) {s : State}
    (hs : s.WellFormed w) : Fits (s.tailBits w) (s.mem (s.completeWords w)) := by
  have heq : s.mem (s.completeWords w) =
      extractSlice (s.mem (s.completeWords w)) 0 (s.tailBits w) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [extractSlice_testBit, Nat.zero_add]
    by_cases hj : j < s.tailBits w
    · simp [hj]
    · simp only [hj, decide_false, Bool.false_and]
      by_cases hjw : j < w
      · have hmod : (s.completeWords w * w + j) % w = j := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hjw]
        have hdiv : (s.completeWords w * w + j) / w = s.completeWords w := by
          rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hjw, Nat.add_zero]
        have hge : s.bitSize ≤ s.completeWords w * w + j := by
          have := Nat.div_add_mod s.bitSize w
          have := Nat.mul_comm w (s.bitSize / w)
          dsimp only [State.completeWords, State.tailBits] at hj ⊢
          omega
        have hzero := hs.zero_above (s.completeWords w * w + j) hge
        simpa [State.getBit, readBit, hdiv, hmod] using hzero
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hs.mem_fits _)
          (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hjw)))
  rw [Fits, heq]
  exact extractSlice_lt _ _ _

/-- In a well-formed state at word width `w > 0`, all words strictly beyond the tail word
(`q > s.completeWords w`) are `0`. -/
theorem State.WellFormed.zero_of_gt_completeWords {w : ℕ} (hw : 0 < w) {s : State}
    (hs : s.WellFormed w) {q : ℕ} (hq : s.completeWords w < q) : s.mem q = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hjw : j < w
  · have hmod : (q * w + j) % w = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hjw]
    have hdiv : (q * w + j) / w = q := by
      rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hjw, Nat.add_zero]
    have hge : s.bitSize ≤ q * w + j := by
      have := Nat.div_add_mod s.bitSize w
      have : s.bitSize % w < w := Nat.mod_lt s.bitSize hw
      dsimp only [State.completeWords] at hq
      have hle : (s.bitSize / w + 1) * w ≤ q * w := Nat.mul_le_mul_right w hq
      nlinarith
    have hzero := hs.zero_above (q * w + j) hge
    simpa [State.getBit, readBit, hdiv, hmod] using hzero
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hs.mem_fits q)
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hjw)))

/-- Contiguous bit interval `[bitAddr, bitAddr + len)` as a `Finset ℕ`. -/
def bitInterval (bitAddr len : ℕ) : Finset ℕ :=
  (Block.mk bitAddr len).footprint

@[simp]
theorem mem_bitInterval {bitAddr len i : ℕ} :
    i ∈ bitInterval bitAddr len ↔ bitAddr ≤ i ∧ i < bitAddr + len :=
  Block.mem_footprint

/-- Bit-level frame predicate across a transition or resize: every bit index
`i < min s.bitSize s'.bitSize` outside the modified bit set `B : Finset ℕ` retains its value. -/
def BitUnchangedOutside (w : ℕ) (s s' : State) (B : Finset ℕ) : Prop :=
  ∀ i < min s.bitSize s'.bitSize, i ∉ B → s'.getBit w i = s.getBit w i

/-- `writeBits bitAddr len val` preserves all bits outside `bitInterval bitAddr len`. -/
theorem bitUnchangedOutside_writeBits {w : ℕ} (hw : 0 < w) {s : State}
    {bitAddr len val : ℕ} (hlen : len ≤ w) :
    BitUnchangedOutside w s (stepFn w s (.writeBits bitAddr len val)).1
      (bitInterval bitAddr len) := by
  intro i _ hiB
  rw [mem_bitInterval] at hiB
  simp only [stepFn, State.getBit]
  rw [readBit_writeFieldMem hw s.mem hlen i, ite_eq_right hiB]

/-- Deterministic `grow δ` preserves all existing bits (`BitUnchangedOutside w s s' ∅`). -/
theorem bitUnchangedOutside_grow {w : ℕ} (hw : 0 < w) (s : State) (δ : ℕ) :
    BitUnchangedOutside w s (stepFn w s (.grow δ)).1 ∅ := by
  intro i hi _
  exact getBit_stepFn_grow_of_lt hw s δ (by omega)

/-- Relational `dirtyStep w s (.grow δ) s' res` also satisfies `BitUnchangedOutside w s s' ∅`. -/
theorem bitUnchangedOutside_dirtyStep_grow {w : ℕ} {s s' : State} {δ res : ℕ}
    (h : dirtyStep w s (.grow δ) s' res) :
    BitUnchangedOutside w s s' ∅ := by
  obtain ⟨hsz, _, _, hpres, _⟩ := h
  intro i hi _
  exact hpres i (by omega)

/-- `shrink δ` preserves all surviving bits (`BitUnchangedOutside w s s' ∅`). -/
theorem bitUnchangedOutside_shrink {w : ℕ} (hw : 0 < w) (s : State) (δ : ℕ) :
    BitUnchangedOutside w s (stepFn w s (.shrink δ)).1 ∅ := by
  intro i hi _
  dsimp only [stepFn] at hi
  exact getBit_stepFn_shrink_of_lt hw s δ (by omega)

/-- **Bridge from bit-level `BitUnchangedOutside` to word-level equality**: if `s` and `s'` are
well-formed at word width `w > 0` and satisfy `BitUnchangedOutside w s s' B`, then every complete
word `q` with `(q + 1) * w ≤ min s.bitSize s'.bitSize` whose bit interval `bitInterval (q * w) w`
is disjoint from `B` satisfies `s'.mem q = s.mem q`. -/
theorem BitUnchangedOutside.mem_eq_of_disjoint {w : ℕ} (hw : 0 < w) {s s' : State}
    (hs : s.WellFormed w) (hs' : s'.WellFormed w) {B : Finset ℕ}
    (hframe : BitUnchangedOutside w s s' B) {q : ℕ}
    (hq : (q + 1) * w ≤ min s.bitSize s'.bitSize)
    (hdisj : Disjoint (bitInterval (q * w) w) B) :
    s'.mem q = s.mem q := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · have hi_lt : q * w + j < min s.bitSize s'.bitSize := by
      have : (q + 1) * w = q * w + w := Nat.succ_mul q w
      omega
    have hi_mem : q * w + j ∈ bitInterval (q * w) w := by
      rw [mem_bitInterval]
      omega
    have hi_notB : q * w + j ∉ B := Finset.disjoint_left.mp hdisj hi_mem
    have hbit := hframe (q * w + j) hi_lt hi_notB
    have hmod : (q * w + j) % w = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    have hdiv : (q * w + j) / w = q := by
      rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]
    simpa [State.getBit, readBit, hdiv, hmod] using hbit
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hs'.mem_fits q)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hs.mem_fits q)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj)))]

end Cslib.DataStructure.Memory.BitMemory
