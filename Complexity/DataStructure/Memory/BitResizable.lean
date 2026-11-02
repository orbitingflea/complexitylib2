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
memory is an array of bits `[0, bitSize)` whose allocated length `bitSize : ℕ` grows and shrinks
dynamically in **bits** while being accessed in fields of up to `w` bits on a `w`-bit Word RAM
[Hagerup1998].

## Model design and rejected alternatives

1. **Semantics of growing and shrinking (`grow`, `growDirty`, `shrink`):**
   - `grow δ` increases `s.bitSize` to `s.bitSize + δ` and returns the old `s.bitSize` (the bit
     offset of the newly allocated `δ`-bit slice).
   - `shrink δ` (admissible when `δ ≤ s.bitSize`) decreases `s.bitSize` to `s.bitSize - δ` and
     clears the released bits `[s.bitSize - δ, s.bitSize)`.
   - *Rejected alternative:* Allowing `resize newSize` without separating `grow` and `shrink` or
     without a `δ ≤ s.bitSize` precondition. Separating `grow` and `shrink` mirrors `Memory.alloc`
     (which returns the base offset of the newly obtained slice) and makes underflow an explicit
     admissibility obligation (`D.valid`).

2. **Contents of newly obtained memory (`spec` vs. `dirtySpec`):**
   - We provide both the deterministic zero-initialized specification `BitMemory.spec w` (where
     newly grown bits `[bitSize, bitSize + δ)` are `0`, equipping `BitMemory.spec w` with
     `StateTransitionSpec.HasStepFn`) and the relational specification `BitMemory.dirtySpec w`
     (where `grow δ` may place arbitrary bit values in `[bitSize, bitSize + δ)` while preserving
     all existing bits `[0, bitSize)`). We prove `spec_refines_dirtySpec`, showing that `spec w`
     refines `dirtySpec w`.
   - *Rejected alternative:* Providing only a nondeterministic dirty-allocation specification.
     Retaining the deterministic `HasStepFn` specification alongside `dirtySpec` allows
     deterministic data structures (such as the Stage 1 resizable array) to use functional
     execution (`runClient`, `ValidHistory`, `Refinement.ofFn`) while randomized or dirty-tolerant
     structures can target either specification.

3. **Cost of resizing (`charge`):**
   - Reading or writing a `b`-bit field (`b ≤ w`) costs `1` bit-memory unit (and compiles to at
     most `2` word reads or `4` word accesses on `Memory.spec w` via `BitPacking.readFieldProg`
     and `BitPacking.writeFieldProg`).
   - Resizing by `δ` bits (`grow δ` or `shrink δ`) costs `max 1 (δ ⌈/⌉ w)` units, which is `1`
     whenever `δ ≤ w` (e.g., growing or shrinking by one `b`-bit item with `b ≤ w`) and `⌈δ / w⌉`
     when `δ > w`.
   - *Rejected alternative:* Charging `δ` (one unit per bit) for `grow δ` / `shrink δ`, which
     would make `b`-bit appends cost `Θ(b)` instead of `O(1)` on a Word RAM; or charging `1` for
     arbitrarily large `δ ≫ w`, which would allow zero-initializing `m` words in `O(1)` time.

4. **Space measure at every step (`spaceBitsAt`, `wordSize`, `pairTotalBitsWithMetadata`):**
   - For a single structure in state `s : BitMemory.State`, its current space is `s.bitSize` bits
     (occupying `s.wordSize w = s.bitSize ⌈/⌉ w` words of `w` bits, plus `w` bits = 1 word if the
     descriptor `s.bitSize` is stored in memory).
   - Along an execution history, space is measured at **every step `t`** by the current `bitSize`
     of the state after `t` operations (not only the peak high-water mark), so `shrink δ` reduces
     the space measure by `δ` bits immediately.
   - *Rejected alternative:* Measuring space only by a monotone word high-water mark (`frontier`),
     which cannot express space reclamation when a structure shrinks.

5. **Frame condition and composition with reusable released memory (`Framed`, `boundedPairSpec`):**
   - `BitMemory.Framed D w` equips a refinement `Refinement D (BitMemory.spec w)` with an exact
     bit-size profile `sizeBits : D.State → ℕ` such that `s.bitSize = sizeBits (abs s)` in every
     represented state.
   - Multiple structures compose over `pairSpec w = product (BitMemory.spec w) (BitMemory.spec w)`.
     Each structure owns an independent bit-resizable region; operations on one structure leave
     the other structure's `mem` and `bitSize` unchanged (`pairSpec_stepFn_inl`,
     `pairSpec_stepFn_inr`). Under a shared bit budget `B` (`boundedPairSpec w B`), bits released
     by shrinking one structure immediately reduce `s₁.bitSize + s₂.bitSize` and can be allocated
     by another structure (`reuse_released_bits`).
   - *Rejected alternative:* Placing multiple variable-size bit structures directly at fixed
     offsets in a single flat bit array without virtual segments or paging, which would require
     `Θ(n / w)` word shifts whenever an earlier structure grows by `b` bits.

## Main definitions

* `BitMemory.State`, `BitMemory.Op`, `BitMemory.stepFn`, `BitMemory.spec`: state, operations, and
  deterministic specification of bit-granular resizable memory.
* `BitMemory.dirtyStep`, `BitMemory.dirtySpec`: relational specification where newly grown bits
  have arbitrary contents.
* `BitMemory.charge`: operation cost charging `1` for `b ≤ w` field accesses and `max 1 (δ ⌈/⌉ w)`
  for `δ`-bit resizes.
* `BitMemory.Framed`: bit-size-tracked refinements over `BitMemory.spec w`.
* `BitMemory.boundedPairSpec`: two bit-resizable structures sharing a total bit budget `B`.

## Main results

* `BitMemory.wellFormed_stepFn`: every valid operation preserves `State.WellFormed w`.
* `BitMemory.dirtyStep_of_stepFn`: every deterministic `stepFn` step satisfies `dirtyStep`.
* `BitMemory.reuse_released_bits`: shrinking structure 1 by `δ` bits frees `δ` bits that
  structure 2 can immediately allocate via `grow δ` within the same total bit budget `B`.
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

/-! ## Concrete state and bit-level helpers -/

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

/-- Clear all bits in the half-open bit interval `[lo, hi)` across `mem : ℕ → ℕ`. -/
def clearRangeMem (w : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → ℕ :=
  fun q => Nat.ofBits (fun j : Fin w =>
    if lo ≤ q * w + j.val ∧ q * w + j.val < hi then false
    else (mem q).testBit j.val)

theorem clearRangeMem_fits (w : ℕ) (mem : ℕ → ℕ) (lo hi q : ℕ) :
    Fits w (clearRangeMem w mem lo hi q) :=
  Nat.ofBits_lt_two_pow _

theorem readBit_clearRangeMem {w : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) (lo hi i : ℕ) :
    readBit w 0 (clearRangeMem w mem lo hi) i =
      if lo ≤ i ∧ i < hi then false else readBit w 0 mem i := by
  have hmod : i % w < w := Nat.mod_lt i hw
  have hdiv_mod : i / w * w + i % w = i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i w
  simp [readBit, clearRangeMem, Nat.testBit_ofBits_lt _ _ hmod, hdiv_mod]

/-- Well-formedness at word width `w`: every word fits in `w` bits and every bit outside the
allocated range `[0, s.bitSize)` is `false`. -/
structure State.WellFormed (s : State) (w : ℕ) : Prop where
  /-- Every word in `s.mem` is `< 2 ^ w`. -/
  mem_fits : ∀ q, Fits w (s.mem q)
  /-- All bits at or above `s.bitSize` are zero. -/
  zero_above : ∀ i, s.bitSize ≤ i → s.getBit w i = false

theorem wellFormed_empty (w : ℕ) : empty.WellFormed w where
  mem_fits _ := fits_zero w
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

/-- Admissibility of a `BitMemory.Op` at word width `w` in state `s`. -/
def valid (w : ℕ) (s : State) : Op → Prop
  | .readBits bitAddr len => len ≤ w ∧ bitAddr + len ≤ s.bitSize
  | .writeBits bitAddr len val => len ≤ w ∧ bitAddr + len ≤ s.bitSize ∧ Fits len val
  | .grow _ => True
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

/-- Programs over `BitMemory.spec w`. -/
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
    valid w s (.grow δ) ↔ True := Iff.rfl

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
    refine ⟨writeFieldMem_fits hs.mem_fits bitAddr len val, fun i hi => ?_⟩
    simp only [stepFn, State.getBit] at hi ⊢
    rw [readBit_writeFieldMem hw s.mem hlen i, ite_eq_right (by omega)]
    exact hs.zero_above i hi
  | grow δ =>
    refine ⟨clearRangeMem_fits w s.mem s.bitSize (s.bitSize + δ), fun i hi => ?_⟩
    simp only [stepFn, State.getBit] at hi ⊢
    rw [readBit_clearRangeMem hw s.mem s.bitSize (s.bitSize + δ) i, ite_eq_right (by omega)]
    exact hs.zero_above i (by omega)
  | shrink δ =>
    refine ⟨clearRangeMem_fits w s.mem (s.bitSize - δ) s.bitSize, fun i hi => ?_⟩
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
    {a b : ℕ} (hab : a + b ≤ s.bitSize) :
    (stepFn w s (.grow δ)).1.getField w a b = s.getField w a b := by
  apply readField_congr_bits
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
    {a b : ℕ} (hab : a + b ≤ s.bitSize - δ) :
    (stepFn w s (.shrink δ)).1.getField w a b = s.getField w a b := by
  apply readField_congr_bits
  intro k hk
  exact getBit_stepFn_shrink_of_lt hw s δ (by omega)

/-! ## Relational dirty-allocation specification (`dirtySpec`) -/

/-- Relational step semantics where `grow δ` may place arbitrary bit values in the newly allocated
slice `[s.bitSize, s.bitSize + δ)` while preserving all existing bits `[0, s.bitSize)` and word
bounds. -/
def dirtyStep (w : ℕ) (s : State) (o : Op) (s' : State) (r : o.Result) : Prop :=
  match o with
  | .grow δ =>
      s'.bitSize = s.bitSize + δ ∧ r = s.bitSize ∧
      (∀ q, Fits w (s'.mem q)) ∧
      (∀ i < s.bitSize, s'.getBit w i = s.getBit w i)
  | o => stepFn w s o = (s', r)

/-- Relational specification of bit-granular resizable memory with uninitialized (`dirty`) newly
grown bits. -/
def dirtySpec (w : ℕ) : StateTransitionSpec where
  State := State
  Op := Op
  Result := Op.Result
  step := dirtyStep w
  valid := valid w

/-- Every deterministic `stepFn` transition satisfies `dirtyStep`. -/
theorem dirtyStep_of_stepFn {w : ℕ} (hw : 0 < w) (s : State) (o : Op) :
    dirtyStep w s o (stepFn w s o).1 (stepFn w s o).2 := by
  cases o with
  | grow δ =>
    refine ⟨rfl, rfl, clearRangeMem_fits w s.mem s.bitSize (s.bitSize + δ), fun i hi => ?_⟩
    exact getBit_stepFn_grow_of_lt hw s δ hi
  | readBits _ _ => rfl
  | writeBits _ _ _ => rfl
  | shrink _ => rfl
  | size => rfl

/-! ## Operation cost and space measure -/

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

/-- The current allocated space in bits at step `t` along an operation sequence `ops` from `s₀`. -/
def spaceBitsAt (w : ℕ) (s₀ : State) (ops : List Op) (t : ℕ) : ℕ :=
  (((spec w).run s₀ (ops.take t)).1).bitSize

/-! ## Frame condition and multi-structure composition with reusable memory -/

/-- A refinement of an abstract specification `D` over `BitMemory.spec w` with an exact bit-space
profile `sizeBits : D.State → ℕ` at every step. -/
structure Framed (D : StateTransitionSpec) (w : ℕ) extends Refinement D (spec w) where
  /-- Exact allocated bit count of a represented abstract state `d : D.State`. -/
  sizeBits : D.State → ℕ
  /-- Every represented concrete state has `s.bitSize = sizeBits (abs s)`. -/
  bitSize_eq : ∀ {s}, inv s → s.bitSize = sizeBits (abs s)
  /-- Every represented concrete state is well-formed at word width `w`. -/
  wellFormed : ∀ {s}, inv s → s.WellFormed w

/-- Two independent bit-resizable memory segments in one machine. -/
abbrev pairSpec (w : ℕ) : StateTransitionSpec :=
  product (spec w) (spec w)

/-- Charge function on `pairSpec w` summing the operation cost on whichever segment is called. -/
def pairCharge (w : ℕ) : (pairSpec w).State → (pairSpec w).Op → ℕ :=
  productCharge (charge w) (charge w)

/-- Lift a `BitMemory.Prog α` to operate on the left segment of `pairSpec w`. -/
def liftLeft (w : ℕ) {α : Type} (p : Prog α) : (pairSpec w).Client α :=
  p.liftM fun o => PFunctor.FreeM.lift (P := (pairSpec w).signature) (.inl o)

/-- Lift a `BitMemory.Prog α` to operate on the right segment of `pairSpec w`. -/
def liftRight (w : ℕ) {α : Type} (p : Prog α) : (pairSpec w).Client α :=
  p.liftM fun o => PFunctor.FreeM.lift (P := (pairSpec w).signature) (.inr o)

/-- Evaluating `liftLeft w p` on `(s₁, s₂)` runs `p` on `s₁` and preserves `s₂`. -/
theorem runClient_liftLeft (w : ℕ) {α : Type} (s₁ s₂ : State) (p : Prog α) :
    (pairSpec w).runClient (s₁, s₂) (liftLeft w p) =
      let (v, s₁', os) := (spec w).runClient s₁ p
      (v, (s₁', s₂), os.map Sum.inl) := by
  induction p generalizing s₁ with
  | pure a => rfl
  | liftBind o k ih =>
    change (let r := (pairSpec w).stepFn (s₁, s₂) (.inl o);
      let res := (pairSpec w).runClient r.1 (liftLeft w (k r.2));
      (res.1, res.2.1, .inl o :: res.2.2)) = _
    have h := ih ((stepFn w s₁ o).2) ((stepFn w s₁ o).1)
    dsimp only at h ⊢
    rw [h]
    rfl

/-- Evaluating `liftRight w p` on `(s₁, s₂)` preserves `s₁` and runs `p` on `s₂`. -/
theorem runClient_liftRight (w : ℕ) {α : Type} (s₁ s₂ : State) (p : Prog α) :
    (pairSpec w).runClient (s₁, s₂) (liftRight w p) =
      let (v, s₂', os) := (spec w).runClient s₂ p
      (v, (s₁, s₂'), os.map Sum.inr) := by
  induction p generalizing s₂ with
  | pure a => rfl
  | liftBind o k ih =>
    change (let r := (pairSpec w).stepFn (s₁, s₂) (.inr o);
      let res := (pairSpec w).runClient r.1 (liftRight w (k r.2));
      (res.1, res.2.1, .inr o :: res.2.2)) = _
    have h := ih ((stepFn w s₂ o).2) ((stepFn w s₂ o).1)
    dsimp only at h ⊢
    rw [h]
    rfl

/-- Admissibility of a left-lifted history on `pairSpec w`. -/
theorem validHistory_map_inl (w : ℕ) (s₁ s₂ : State) (os : List Op) :
    (pairSpec w).ValidHistory (s₁, s₂) (os.map Sum.inl) ↔ (spec w).ValidHistory s₁ os := by
  induction os generalizing s₁ with
  | nil => rfl
  | cons o os ih => exact and_congr_right fun _ => ih _

/-- Admissibility of a right-lifted history on `pairSpec w`. -/
theorem validHistory_map_inr (w : ℕ) (s₁ s₂ : State) (os : List Op) :
    (pairSpec w).ValidHistory (s₁, s₂) (os.map Sum.inr) ↔ (spec w).ValidHistory s₂ os := by
  induction os generalizing s₂ with
  | nil => rfl
  | cons o os ih => exact and_congr_right fun _ => ih _

/-- Cost of a left-lifted history on `pairSpec w`. -/
theorem totalCost_map_inl (w : ℕ) (s₁ s₂ : State) (os : List Op) :
    (pairSpec w).totalCost (pairCharge w) (s₁, s₂) (os.map Sum.inl) =
      (spec w).totalCost (charge w) s₁ os := by
  induction os generalizing s₁ with
  | nil => rfl
  | cons o os ih => exact congrArg (charge w s₁ o + ·) (ih _)

/-- Cost of a right-lifted history on `pairSpec w`. -/
theorem totalCost_map_inr (w : ℕ) (s₁ s₂ : State) (os : List Op) :
    (pairSpec w).totalCost (pairCharge w) (s₁, s₂) (os.map Sum.inr) =
      (spec w).totalCost (charge w) s₂ os := by
  induction os generalizing s₂ with
  | nil => rfl
  | cons o os ih => exact congrArg (charge w s₂ o + ·) (ih _)

/-- Combine method tables on two independent `BitMemory.spec w` segments into a method table on
`pairSpec w`. -/
def prodMethods (w : ℕ) {D₁ D₂ : StateTransitionSpec}
    (m₁ : Methods D₁ (spec w)) (m₂ : Methods D₂ (spec w)) :
    Methods (product D₁ D₂) (pairSpec w)
  | .inl o => liftLeft w (m₁ o)
  | .inr o => liftRight w (m₂ o)

/-- Total allocated bits across two bit-resizable segments. -/
def pairTotalBits (s : State × State) : ℕ :=
  s.1.bitSize + s.2.bitSize

/-- Total allocated bits including one `w`-bit descriptor word per segment (`2 * w` additive
bits). -/
def pairTotalBitsWithMetadata (w : ℕ) (s : State × State) : ℕ :=
  s.1.bitSize + s.2.bitSize + 2 * w

/-- **Frame condition for composed bit-resizable segments**: an operation on the first segment
leaves the second segment's `mem` and `bitSize` completely unchanged, and vice versa. -/
@[simp]
theorem pairSpec_stepFn_inl (w : ℕ) (s : State × State) (o : Op) :
    ((pairSpec w).stepFn s (.inl o)).1.2 = s.2 := rfl

@[simp]
theorem pairSpec_stepFn_inr (w : ℕ) (s : State × State) (o : Op) :
    ((pairSpec w).stepFn s (.inr o)).1.1 = s.1 := rfl

/-- Two bit-resizable segments sharing a single pool of `B` bits: an operation is admissible iff it
is admissible on its target segment and the resulting total live bit count
`s'₁.bitSize + s'₂.bitSize` stays within the shared budget `B`. -/
abbrev boundedPairSpec (w B : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn
    (fun (s : State × State) (o : Op ⊕ Op) => (pairSpec w).stepFn s o)
    (fun (s : State × State) (o : Op ⊕ Op) =>
      (pairSpec w).valid s o ∧ pairTotalBits ((pairSpec w).stepFn s o).1 ≤ B)

/-- **Memory reuse theorem**: when segment 1 shrinks by `δ` bits from a state within budget `B`,
those `δ` released bits immediately reduce `pairTotalBits` by `δ` and can be allocated by segment 2
via `grow δ` without exceeding the shared bit budget `B`. -/
theorem reuse_released_bits {w B δ : ℕ} {s : State × State}
    (hB : pairTotalBits s ≤ B) (hδ : δ ≤ s.1.bitSize) :
    let s₁ := ((boundedPairSpec w B).stepFn s (.inl (.shrink δ))).1
    (boundedPairSpec w B).valid s (.inl (.shrink δ)) ∧
      pairTotalBits s₁ = pairTotalBits s - δ ∧
      (boundedPairSpec w B).valid s₁ (.inr (.grow δ)) ∧
      pairTotalBits ((boundedPairSpec w B).stepFn s₁ (.inr (.grow δ))).1 = pairTotalBits s := by
  change (valid w s.1 (.shrink δ) ∧
      (stepFn w s.1 (.shrink δ)).1.bitSize + s.2.bitSize ≤ B) ∧
    (stepFn w s.1 (.shrink δ)).1.bitSize + s.2.bitSize = (s.1.bitSize + s.2.bitSize) - δ ∧
    (valid w s.2 (.grow δ) ∧
      (stepFn w s.1 (.shrink δ)).1.bitSize + (stepFn w s.2 (.grow δ)).1.bitSize ≤ B) ∧
    (stepFn w s.1 (.shrink δ)).1.bitSize + (stepFn w s.2 (.grow δ)).1.bitSize =
      s.1.bitSize + s.2.bitSize
  simp only [valid, stepFn]
  have hB' : s.1.bitSize + s.2.bitSize ≤ B := hB
  exact ⟨⟨hδ, by omega⟩, by omega, ⟨trivial, by omega⟩, by omega⟩

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
    rw [readField_testBit, readField_testBit]
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
  · refine (writeFieldProg_triple (Or.inl rfl)).mono le_rfl ?_
    rintro ⟨⟩ m' ⟨hm, hf⟩
    refine ⟨fun q hq => ?_, hf⟩
    simp [hm, stepFn, hmem q hq]
  · have hcov : s.bitSize ≤ s.wordSize w * w := Nat.le_ceilDiv_mul hw
    have ⟨hq₀, hq₁⟩ := word_indices_lt_of_bit_bound hw hpos (hbound.trans hcov)
    refine (writeFieldProg_triple (Or.inr ⟨by omega, by omega⟩)).mono le_rfl ?_
    rintro ⟨⟩ m' ⟨hm, hf⟩
    refine ⟨fun q hq => ?_, hf⟩
    rw [hm]
    simp only [stepFn]
    unfold writeFieldMem
    have hlen0 : ¬len = 0 := by omega
    rw [ite_eq_right hlen0, ite_eq_right hlen0]
    simp only [Nat.zero_add]
    by_cases hqq : (bitAddr + len - 1) / w = bitAddr / w
    · rw [ite_eq_left hqq, ite_eq_left hqq]
      by_cases h0 : q = bitAddr / w
      · subst h0
        rw [Function.update_self, Function.update_self, hmem _ hq₀]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne h0]
        exact hmem q hq
    · rw [ite_eq_right hqq, ite_eq_right hqq]
      by_cases h1 : q = (bitAddr + len - 1) / w
      · subst h1
        rw [Function.update_self, Function.update_self,
          Function.update_of_ne (by omega), Function.update_of_ne hqq, hmem _ hq₁]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne h1]
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
      Nat.ofBits (fun j : Fin (s.tailBits w) => (s.mem (s.completeWords w)).testBit j.val) := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < s.tailBits w
    · rw [Nat.testBit_ofBits_lt _ _ hj]
    · rw [Nat.testBit_ofBits_ge _ _ (Nat.le_of_not_lt hj)]
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
  exact Nat.ofBits_lt_two_pow _

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
  obtain ⟨hsz, _, _, hpres⟩ := h
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
