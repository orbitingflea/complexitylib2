/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.BitResizable
public import Complexity.DataStructure.DynamicArray.Spec
public import Complexity.DataStructure.Memory.BitResizable

/-!
# Resizable Array of `b`-Bit Items in the Bit-Granular Resizable Word RAM

This module implements `DynamicArray.spec w b` (for `0 < b ≤ w`) over both:
1. the demonic bit-granular resizable memory `BitMemory.dirtySpec w` (where newly grown bits have
   arbitrary Boolean contents, `[KLZ26]` §5.1) and its deterministic specialization
   `BitMemory.spec w`, and
2. the concrete bit-granular resizable Word-RAM instruction set `BitRAM.Code .standard 12`
   (`appendCode`, `popCode`, `readCode`, `writeCode`) with proven worst-case machine-instruction
   bounds (`BitRAM.DemonicExecWithin`).

Because the underlying memory grows and shrinks in **bits**, an array of `n_t` items of `b` bits is
stored contiguously in `n_t * b` bits without wasted padding bits between items or doubling slack:

* `append x`: calls `BitMemory.grow b` (extending `bitSize` from `n_t * b` to `(n_t + 1) * b` with
  arbitrary demonic bits in `[n_t * b, (n_t + 1) * b)`) and immediately overwrites those `b` bits
  via `BitMemory.writeBits (n_t * b) b x`. Worst-case cost: `2` bit-memory operations (`≤ 45`
  `BitRAM` machine instructions).
* `pop`: queries `sz ← BitMemory.getSize`; if `sz < b` (`n_t = 0`), returns `none`; otherwise reads
  the last item at `sz - b = (n_t - 1) * b` and calls `BitMemory.shrink b`, immediately releasing
  `b` bits so `bitSize` drops to `(n_t - 1) * b`. Worst-case cost: at most `3` bit-memory
  operations (`≤ 38` `BitRAM` machine instructions).
* `read i`: calls `BitMemory.readBits (i * b) b`. Worst-case cost: `1` bit-memory operation (`≤ 34`
  `BitRAM` machine instructions).
* `write i x`: calls `BitMemory.writeBits (i * b) b x`. Worst-case cost: `1` bit-memory operation
  (`≤ 44` `BitRAM` machine instructions).

## Space bound at every step

At every step `t` with current array length `n_t`, the allocated bit-segment size is **exactly**
`n_t * b` bits (`bitSize_eq_length_mul`), occupying `(n_t * b) ⌈/⌉ w` words of `w` bits. Including
the single `w`-bit descriptor word that records `bitSize`, the total space at step `t` is
`n_t * b + w` bits (`O(1)` words of additive metadata overhead).

## Single-tape subroutine composition and reuse of released memory

All multi-structure and subroutine compositions in this module live in a **single** linear
bit-resizable memory state `s : BitMemory.State` (`[0, s.bitSize)`):
1. `singleTape_sequential_subroutine_reuse`: a client runs a first resizable-array computation on
   `BitMemory.dirtySpec w` that shrinks back to empty (`s₁.bitSize = 0`), and a second
   resizable-array computation immediately reuses the released `[0, M)` bit address space from bit
   offset `0` on the same `BitMemory.State`.
2. `SingleTapeTwoArrays`: two resizable `b`-bit arrays `(xs₁, xs₂)` coexist simultaneously in one
   `BitMemory.State` with a `w`-bit header at `[0, w)` storing `n₁ = xs₁.length`, `xs₁` packed in
   `[w, w + n₁ * b)`, and `xs₂` packed in `[w + n₁ * b, w + (n₁ + n₂) * b)`, so the single tape
   has exact bit size `s.bitSize = w + (xs₁.length + xs₂.length) * b` at every step. When an item
   is popped from the tail of `xs₂` (shrinking `s.bitSize` by `b` bits via `shrink b`) and appended
   to `xs₁` (`singleTape_pop₂_append₁_reuses_released_bits`), the `b` bits released by `shrink b`
   are immediately reused by `grow b` on the same `BitMemory.State` under demonic `dirtySpec w`
   without exceeding `w + (xs₁.length + xs₂.length) * b` bits.

## Main definitions

* `append`, `pop`, `read`, `write`, `ops`, `methods`: the resizable array operations as
  `BitMemory.Prog` programs.
* `abs`, `Inv`: abstraction function and representation invariant.
* `dirtyRefinement`, `dirtyFramed`, `refinement`, `framed`: verified refinements and bit-size-framed
  implementations of `DynamicArray.spec w b` over `BitMemory.dirtySpec w` and `BitMemory.spec w`.
* `appendCode`, `popCode`, `readCode`, `writeCode`: concrete `BitRAM.Code .standard 12` machine
  programs for the four array operations.
* `SingleTapeTwoArrays`: concurrent single-tape representation of two `b`-bit arrays in one
  `BitMemory.State`.

## Main results

* `dirtyAmortized`, `dirty_client_run_from_empty`: worst-case `O(1)` (`≤ 3` bit-memory units)
  correctness, exact `n_t * b`-bit space bound, and adaptive client theorem directly over demonic
  `BitMemory.dirtySpec w`.
* `appendCode_exec`, `popCode_exec`, `readCode_exec`, `writeCode_exec`: machine-level
  `BitRAM.DemonicExecWithin` correctness and instruction-count bounds (`≤ 45` instructions).
* `singleTape_sequential_subroutine_reuse`, `singleTape_pop₂_append₁_reuses_released_bits`:
  single-tape subroutine composition and released-bit reuse on `BitMemory.dirtySpec w`.

## References

* [T. Hagerup, *Sorting and Searching on the Word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.DataStructure.DynamicArray.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory

variable {w b : ℕ}

/-! ## Method implementations over `BitMemory.dirtySpec w` and `BitMemory.spec w` -/

/-- Append a `b`-bit value `x` by growing the bit segment by `b` bits and writing `x` at the new
bit offset. -/
def append (b x : ℕ) : BitMemory.Prog Unit := do
  let offset ← BitMemory.grow b
  BitMemory.writeBits offset b x

/-- Pop the last `b`-bit value: query the current bit size `sz`; if `sz < b`, return `none`;
otherwise read the trailing `b` bits at `sz - b`, shrink the bit segment by `b` bits, and return
the value. -/
def pop (b : ℕ) : BitMemory.Prog (Option ℕ) := do
  let sz ← BitMemory.getSize
  if sz < b then
    pure none
  else do
    let x ← BitMemory.readBits (sz - b) b
    BitMemory.shrink b
    pure (some x)

/-- Read the `b`-bit item at array index `i` (stored at bit offset `i * b`). -/
def read (b i : ℕ) : BitMemory.Prog ℕ :=
  BitMemory.readBits (i * b) b

/-- Write `x` to the `b`-bit item at array index `i` (stored at bit offset `i * b`). -/
def write (b i x : ℕ) : BitMemory.Prog Unit :=
  BitMemory.writeBits (i * b) b x

/-- Dispatch a `DynamicArray.Op` to its `BitMemory.Prog` implementation. -/
def ops (b : ℕ) : (o : DynamicArray.Op) → BitMemory.Prog o.Result
  | .append x => append b x
  | .pop => pop b
  | .read i => read b i
  | .write i x => write b i x

/-- Method table implementing `DynamicArray.spec w b` over `BitMemory.spec w`. -/
abbrev methods (w b : ℕ) : Methods (DynamicArray.spec w b) (BitMemory.spec w) :=
  ops b

/-- Method table implementing `DynamicArray.spec w b` over demonic `BitMemory.dirtySpec w`. -/
abbrev dirtyMethods (w b : ℕ) : Methods (DynamicArray.spec w b) (BitMemory.dirtySpec w) :=
  ops b

/-! ## Abstraction function and representation invariant -/

/-- Number of `b`-bit items currently stored in `s`. -/
def count (b : ℕ) (s : BitMemory.State) : ℕ :=
  s.bitSize / b

/-- Abstract list of `b`-bit items represented by `s`: `s.bitSize / b` items read at bit offsets
`0, b, 2 * b, ...`. -/
def abs (w b : ℕ) (s : BitMemory.State) : DynamicArray.State :=
  List.ofFn (fun i : Fin (count b s) => s.getField w (i.val * b) b)

@[simp]
theorem length_abs (w b : ℕ) (s : BitMemory.State) :
    (abs w b s).length = count b s :=
  List.length_ofFn

/-- Representation invariant for a `b`-bit resizable array in `BitMemory.State`:
1. `s` is well-formed at word width `w`;
2. `s.bitSize` is an exact multiple of `b` (`s.bitSize = count b s * b`). -/
structure Inv (w b : ℕ) (s : BitMemory.State) : Prop where
  /-- Underlying bit-memory state is well-formed. -/
  wellFormed : s.WellFormed w
  /-- Allocated bit size is an exact multiple of `b`. -/
  bitSize_eq : s.bitSize = count b s * b

/-- The empty `BitMemory.State` satisfies `Inv w b` and represents the empty array `[]`. -/
theorem inv_empty (w b : ℕ) : Inv w b BitMemory.empty ∧ abs w b BitMemory.empty = [] := by
  refine ⟨⟨BitMemory.wellFormed_empty w, by simp [count]⟩, ?_⟩
  simp [abs, count]

/-- **Tight bit-space bound**: in every state satisfying `Inv w b s`, the allocated size in bits is
exactly `(abs w b s).length * b`. -/
theorem bitSize_eq_length_mul {s : BitMemory.State} (hs : Inv w b s) :
    s.bitSize = (abs w b s).length * b := by
  rw [length_abs, hs.bitSize_eq]

/-- Including one `w`-bit word of segment-size metadata, the total space in bits at state `s` is
`(abs w b s).length * b + w`. -/
theorem totalBitsWithMetadata_eq {s : BitMemory.State} (hs : Inv w b s) :
    s.bitSize + w = (abs w b s).length * b + w := by
  rw [bitSize_eq_length_mul hs]

/-! ## Arithmetic helper lemmas for `b`-bit field indexing -/

/-- Two distinct `b`-bit slots `i ≠ j` have disjoint bit intervals `[i * b, i * b + b)` and
`[j * b, j * b + b)`. -/
theorem slot_disjoint_of_ne {i j : ℕ} (b : ℕ) (hne : i ≠ j) :
    j * b + b ≤ i * b ∨ i * b + b ≤ j * b := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · right
    have : i + 1 ≤ j := hlt
    calc
      i * b + b = (i + 1) * b := by ring
      _ ≤ j * b := Nat.mul_le_mul_right b this
  · left
    have : j + 1 ≤ i := hgt
    calc
      j * b + b = (j + 1) * b := by ring
      _ ≤ i * b := Nat.mul_le_mul_right b this

/-- If `i < n`, then `i * b + b ≤ n * b`. -/
theorem slot_end_le_of_lt {i n : ℕ} (b : ℕ) (hi : i < n) :
    i * b + b ≤ n * b := by
  have : i + 1 ≤ n := hi
  calc
    i * b + b = (i + 1) * b := by ring
    _ ≤ n * b := Nat.mul_le_mul_right b this

/-! ## One-step evaluation of the array operations -/

/-- `append b x` grows the bit segment by `b` bits and writes `x` at the old `bitSize`. -/
theorem runClient_append (s : BitMemory.State) (x : ℕ) :
    (BitMemory.spec w).runClient s (append b x) =
      ((), ⟨writeFieldMem w 0 (clearRangeMem w s.mem s.bitSize (s.bitSize + b)) s.bitSize b x,
          s.bitSize + b⟩,
        [.grow b, .writeBits s.bitSize b x]) := rfl

/-- `pop b` on an empty array (`s.bitSize < b`) only queries the bit size. -/
theorem runClient_pop_of_lt {s : BitMemory.State} (hlt : s.bitSize < b) :
    (BitMemory.spec w).runClient s (pop b) = (none, s, [.size]) := by
  simp [pop, hlt]

/-- `pop b` on a non-empty array (`¬s.bitSize < b`) queries the bit size, reads the last `b` bits,
and shrinks the bit segment by `b` bits. -/
theorem runClient_pop_of_ge {s : BitMemory.State} (hlt : ¬s.bitSize < b) :
    (BitMemory.spec w).runClient s (pop b) =
      (some (s.getField w (s.bitSize - b) b),
        ⟨clearRangeMem w s.mem (s.bitSize - b) s.bitSize, s.bitSize - b⟩,
        [.size, .readBits (s.bitSize - b) b, .shrink b]) := by
  unfold pop
  simp only [BitMemory.runClient_getSize_bind, hlt, ↓reduceIte]
  rfl

/-- `read b i` reads `b` bits at bit offset `i * b`. -/
theorem runClient_read (s : BitMemory.State) (i : ℕ) :
    (BitMemory.spec w).runClient s (read b i) =
      (s.getField w (i * b) b, s, [.readBits (i * b) b]) := rfl

/-- `write b i x` writes `x` into the `b` bits at bit offset `i * b`. -/
theorem runClient_write (s : BitMemory.State) (i x : ℕ) :
    (BitMemory.spec w).runClient s (write b i x) =
      ((), ⟨writeFieldMem w 0 s.mem (i * b) b x, s.bitSize⟩,
        [.writeBits (i * b) b x]) := rfl

/-! ## Per-operation correctness, admissibility, and worst-case cost -/

/-- Admissibility of `ops b o` over `BitMemory.spec w`. -/
theorem ops_validHistory (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) (o : DynamicArray.Op)
    (hv : (DynamicArray.spec w b).valid (abs w b s) o) :
    (BitMemory.spec w).ValidHistory s ((BitMemory.spec w).clientHistory s (ops b o)) := by
  cases o with
  | append x =>
    obtain ⟨hx, hfits⟩ := hv
    have hgrow : Fits w (s.bitSize + b) := by
      rw [bitSize_eq_length_mul hs]
      simpa [Nat.succ_mul] using hfits
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_append]
    exact ⟨hgrow, ⟨hbw, le_rfl, hx⟩, trivial⟩
  | pop =>
    by_cases hlt : s.bitSize < b
    · dsimp only [ops, StateTransitionSpec.clientHistory]
      rw [runClient_pop_of_lt hlt]
      exact ⟨trivial, trivial⟩
    · have hle : b ≤ s.bitSize := Nat.le_of_not_lt hlt
      dsimp only [ops, StateTransitionSpec.clientHistory]
      rw [runClient_pop_of_ge hlt]
      dsimp only [StateTransitionSpec.ValidHistory, StateTransitionSpec.stepFn,
        BitMemory.stepFn_size, BitMemory.valid]
      exact ⟨trivial, ⟨hbw, by omega⟩, hle, trivial⟩
  | read i =>
    have hi : i < count b s := by simpa [length_abs] using hv
    have hslot : i * b + b ≤ s.bitSize := by
      rw [hs.bitSize_eq]
      exact slot_end_le_of_lt b hi
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_read]
    exact ⟨⟨hbw, hslot⟩, trivial⟩
  | write i x =>
    obtain ⟨hi', hx⟩ := hv
    have hi : i < count b s := by simpa [length_abs] using hi'
    have hslot : i * b + b ≤ s.bitSize := by
      rw [hs.bitSize_eq]
      exact slot_end_le_of_lt b hi
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_write]
    exact ⟨⟨hbw, hslot, hx⟩, trivial⟩

/-- Worst-case cost bound: every operation of the resizable `b`-bit array executes in at most `3`
bit-memory units (`2` for `append`, `≤ 3` for `pop`, `1` for `read`, `1` for `write`). -/
theorem ops_cost (hw : 0 < w) (hbw : b ≤ w) (s : BitMemory.State) (o : DynamicArray.Op) :
    (BitMemory.spec w).totalCost (BitMemory.charge w) s
      ((BitMemory.spec w).clientHistory s (ops b o)) ≤ 3 := by
  have hcharge_b : BitMemory.charge w s (.grow b) = 1 :=
    BitMemory.charge_grow_of_le hw hbw s
  cases o with
  | append x =>
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_append]
    simp only [StateTransitionSpec.totalCost_cons, StateTransitionSpec.totalCost_nil,
      hcharge_b, BitMemory.charge_writeBits]
    omega
  | pop =>
    by_cases hlt : s.bitSize < b
    · dsimp only [ops, StateTransitionSpec.clientHistory]
      rw [runClient_pop_of_lt hlt]
      simp only [StateTransitionSpec.totalCost_cons, StateTransitionSpec.totalCost_nil,
        BitMemory.charge_size]
      omega
    · have hsh : BitMemory.charge w s (.shrink b) = 1 :=
        BitMemory.charge_shrink_of_le hw hbw s
      dsimp only [ops, StateTransitionSpec.clientHistory]
      rw [runClient_pop_of_ge hlt]
      simp only [StateTransitionSpec.totalCost_cons, StateTransitionSpec.totalCost_nil,
        StateTransitionSpec.stepFn, BitMemory.stepFn_size, BitMemory.stepFn_readBits,
        BitMemory.charge_size, BitMemory.charge_readBits, hsh]
      omega
  | read i =>
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_read]
    simp only [StateTransitionSpec.totalCost_cons, StateTransitionSpec.totalCost_nil,
      BitMemory.charge_readBits]
    omega
  | write i x =>
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_write]
    simp only [StateTransitionSpec.totalCost_cons, StateTransitionSpec.totalCost_nil,
      BitMemory.charge_writeBits]
    omega

/-- Semantic correctness and invariant preservation of `append`. -/
theorem step_append (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) {x : ℕ}
    (hv : (DynamicArray.spec w b).valid (abs w b s) (.append x)) :
    let s' := (BitMemory.spec w).clientState s (append b x)
    let r := (BitMemory.spec w).clientResult s (append b x)
    (abs w b s', r) = DynamicArray.stepFn (abs w b s) (.append x) ∧ Inv w b s' := by
  obtain ⟨hx, hfits⟩ := hv
  have hv_grow : BitMemory.valid w s (.grow b) := by
    rw [BitMemory.valid_grow, bitSize_eq_length_mul hs]
    simpa [Nat.succ_mul] using hfits
  have hwf₁ : (BitMemory.stepFn w s (.grow b)).1.WellFormed w :=
    wellFormed_stepFn hw hs.wellFormed hv_grow
  have hv_write : BitMemory.valid w (BitMemory.stepFn w s (.grow b)).1
      (.writeBits s.bitSize b x) := ⟨hbw, le_rfl, hx⟩
  have hwf₂ : (BitMemory.stepFn w (BitMemory.stepFn w s (.grow b)).1
      (.writeBits s.bitSize b x)).1.WellFormed w :=
    wellFormed_stepFn hw hwf₁ hv_write
  have hcount : count b ((BitMemory.spec w).clientState s (append b x)) = count b s + 1 := by
    change (s.bitSize + b) / b = count b s + 1
    rw [hs.bitSize_eq, Nat.add_div_right _ hb, Nat.mul_div_cancel _ hb]
  have hinv' : Inv w b ((BitMemory.spec w).clientState s (append b x)) := by
    refine ⟨hwf₂, ?_⟩
    change s.bitSize + b = count b ((BitMemory.spec w).clientState s (append b x)) * b
    rw [hcount, hs.bitSize_eq]
    ring
  rw [DynamicArray.stepFn_append]
  refine ⟨Prod.ext ?_ rfl, hinv'⟩
  apply List.ext_getElem
  · simp [length_abs, hcount]
  · intro i hi₁ hi₂
    rw [length_abs, hcount] at hi₁
    simp only [abs, List.getElem_ofFn]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi₁) with hi_lt | rfl
    · rw [List.getElem_append_left (by simp [hi_lt]), List.getElem_ofFn]
      change readField w 0 (writeFieldMem w 0
        (clearRangeMem w s.mem s.bitSize (s.bitSize + b)) s.bitSize b x) (i * b) b =
        s.getField w (i * b) b
      have hdisj : i * b + b ≤ s.bitSize := by
        rw [hs.bitSize_eq]
        exact slot_end_le_of_lt b hi_lt
      rw [readField_writeFieldMem_of_disjoint hw _ hbw hbw (Or.inl hdisj)]
      exact getField_stepFn_grow hw s b hbw hdisj
    · rw [List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton]
      change readField w 0 (writeFieldMem w 0
        (clearRangeMem w s.mem s.bitSize (s.bitSize + b)) s.bitSize b x) (count b s * b) b = x
      rw [← hs.bitSize_eq]
      exact readField_writeFieldMem_same hw _ hbw hx

/-- Semantic correctness and invariant preservation of `pop`. -/
theorem step_pop (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) :
    let s' := (BitMemory.spec w).clientState s (pop b)
    let r := (BitMemory.spec w).clientResult s (pop b)
    (abs w b s', r) = DynamicArray.stepFn (abs w b s) .pop ∧ Inv w b s' := by
  by_cases hlt : s.bitSize < b
  · have hcount0 : count b s = 0 := Nat.div_eq_of_lt hlt
    have habs0 : abs w b s = [] := by simp [abs, hcount0]
    dsimp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult]
    rw [runClient_pop_of_lt hlt]
    simp [DynamicArray.stepFn, habs0, hs]
  · have hle : b ≤ s.bitSize := Nat.le_of_not_lt hlt
    have hcount_pos : 0 < count b s := Nat.div_pos hle hb
    have hwf' : (BitMemory.stepFn w s (.shrink b)).1.WellFormed w :=
      wellFormed_stepFn hw hs.wellFormed hle
    have hcount' : count b (BitMemory.stepFn w s (.shrink b)).1 = count b s - 1 := by
      change (s.bitSize - b) / b = count b s - 1
      rw [hs.bitSize_eq]
      have : count b s * b - b = (count b s - 1) * b := by
        cases h : count b s with
        | zero => omega
        | succ k => simp [Nat.succ_mul]
      rw [this, Nat.mul_div_cancel _ hb]
    have hinv' : Inv w b (BitMemory.stepFn w s (.shrink b)).1 := by
      refine ⟨hwf', ?_⟩
      change s.bitSize - b = count b (BitMemory.stepFn w s (.shrink b)).1 * b
      rw [hcount', hs.bitSize_eq]
      cases h : count b s with
      | zero => omega
      | succ k => simp [Nat.succ_mul]
    have hstate : (BitMemory.spec w).clientState s (pop b) =
        (BitMemory.stepFn w s (.shrink b)).1 := by
      dsimp only [StateTransitionSpec.clientState]
      rw [runClient_pop_of_ge hlt]
      rfl
    have hres : (BitMemory.spec w).clientResult s (pop b) =
        some (s.getField w (s.bitSize - b) b) := by
      dsimp only [StateTransitionSpec.clientResult]
      rw [runClient_pop_of_ge hlt]
    dsimp only
    rw [hstate, hres, DynamicArray.stepFn_pop]
    refine ⟨Prod.ext ?_ ?_, hinv'⟩
    · apply List.ext_getElem
      · rw [length_abs, hcount', List.length_dropLast, length_abs]
      · intro i hi₁ hi₂
        rw [length_abs, hcount'] at hi₁
        simp only [abs, List.getElem_dropLast, List.getElem_ofFn]
        have hslot : i * b + b ≤ s.bitSize - b := by
          have hsub : s.bitSize - b = (count b s - 1) * b := by
            rw [hs.bitSize_eq]
            cases h : count b s with
            | zero => omega
            | succ k => simp [Nat.succ_mul]
          rw [hsub]
          exact slot_end_le_of_lt b hi₁
        exact getField_stepFn_shrink hw s b hbw hslot
    · have hne : abs w b s ≠ [] := by
        intro hnil
        have := congrArg List.length hnil
        simp only [length_abs, List.length_nil] at this
        omega
      rw [List.getLast?_eq_some_getLast hne, Option.some.injEq]
      rw [List.getLast_eq_getElem]
      simp only [abs, List.length_ofFn, List.getElem_ofFn]
      congr 2
      rw [hs.bitSize_eq]
      cases h : count b s with
      | zero => omega
      | succ k => simp [Nat.succ_mul]

/-- Semantic correctness and invariant preservation of `read`. -/
theorem step_read {s : BitMemory.State} (hs : Inv w b s) {i : ℕ}
    (hi : i < (abs w b s).length) :
    let s' := (BitMemory.spec w).clientState s (read b i)
    let r := (BitMemory.spec w).clientResult s (read b i)
    (abs w b s', r) = DynamicArray.stepFn (abs w b s) (.read i) ∧ Inv w b s' := by
  refine ⟨Prod.ext rfl ?_, hs⟩
  change s.getField w (i * b) b = (abs w b s).getD i 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  simp [abs]

/-- Semantic correctness and invariant preservation of `write`. -/
theorem step_write (hw : 0 < w) (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) {i x : ℕ}
    (hi : i < (abs w b s).length) (hx : Fits b x) :
    let s' := (BitMemory.spec w).clientState s (write b i x)
    let r := (BitMemory.spec w).clientResult s (write b i x)
    (abs w b s', r) = DynamicArray.stepFn (abs w b s) (.write i x) ∧ Inv w b s' := by
  have hi' : i < count b s := by simpa [length_abs] using hi
  have hslot : i * b + b ≤ s.bitSize := by
    rw [hs.bitSize_eq]
    exact slot_end_le_of_lt b hi'
  have hv_write : BitMemory.valid w s (.writeBits (i * b) b x) := ⟨hbw, hslot, hx⟩
  have hwf' : (BitMemory.stepFn w s (.writeBits (i * b) b x)).1.WellFormed w :=
    wellFormed_stepFn hw hs.wellFormed hv_write
  have hinv' : Inv w b ((BitMemory.spec w).clientState s (write b i x)) :=
    ⟨hwf', hs.bitSize_eq⟩
  have hstate : (BitMemory.spec w).clientState s (write b i x) =
      ⟨writeFieldMem w 0 s.mem (i * b) b x, s.bitSize⟩ := rfl
  dsimp only
  rw [DynamicArray.stepFn_write]
  refine ⟨Prod.ext ?_ rfl, hinv'⟩
  rw [hstate]
  apply List.ext_getElem
  · simp [length_abs, count]
  · intro j hj₁ hj₂
    rw [length_abs] at hj₁
    simp only [abs, List.getElem_set, List.getElem_ofFn]
    change readField w 0 (writeFieldMem w 0 s.mem (i * b) b x) (j * b) b =
      if i = j then x else s.getField w (j * b) b
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      exact readField_writeFieldMem_same hw s.mem hbw hx
    · rw [ite_eq_right hij]
      exact readField_writeFieldMem_of_disjoint hw s.mem hbw hbw (slot_disjoint_of_ne b hij)

/-- Combined step correctness for all four `DynamicArray.Op` operations. -/
theorem ops_step (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) (o : DynamicArray.Op)
    (hv : (DynamicArray.spec w b).valid (abs w b s) o) :
    (abs w b ((BitMemory.spec w).clientState s (ops b o)),
      (BitMemory.spec w).clientResult s (ops b o)) =
        DynamicArray.stepFn (abs w b s) o ∧
      Inv w b ((BitMemory.spec w).clientState s (ops b o)) := by
  cases o with
  | append x => exact step_append hw hb hbw hs hv
  | pop => exact step_pop hw hb hbw hs
  | read i => exact step_read hs hv
  | write i x => exact step_write hw hbw hs hv.1 hv.2

/-! ## Direct verification against demonic `BitMemory.dirtySpec w` -/

/-- Each array method `ops b o` is demonically admissible on `BitMemory.dirtySpec w` whenever `s`
satisfies `Inv w b s` and `o` is admissible in `abs w b s`. -/
theorem ops_demonicValid (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) (o : DynamicArray.Op)
    (hv : (DynamicArray.spec w b).valid (abs w b s) o) :
    (BitMemory.dirtySpec w).DemonicValid s (ops b o) := by
  cases o with
  | append x =>
    obtain ⟨hx, hfits⟩ := hv
    have hgrow : Fits w (s.bitSize + b) := by
      rw [bitSize_eq_length_mul hs]
      simpa [Nat.succ_mul] using hfits
    refine .liftBind (D := BitMemory.dirtySpec w) (.grow b) _ hgrow fun s₁ offset hstep₁ => ?_
    have hsz₁ : s₁.bitSize = s.bitSize + b := hstep₁.1
    have hoff : offset = s.bitSize := hstep₁.2.1
    subst hoff
    have hv_wr : (BitMemory.dirtySpec w).valid s₁ (.writeBits s.bitSize b x) :=
      ⟨hbw, by omega, hx⟩
    exact .liftBind (D := BitMemory.dirtySpec w) (.writeBits s.bitSize b x) _ hv_wr
      fun s₂ a _ => .pure (D := BitMemory.dirtySpec w) s₂ a
  | pop =>
    refine .liftBind (D := BitMemory.dirtySpec w) .size _ trivial fun s₁ sz hstep₁ => ?_
    obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
    subst h1; subst h1v
    change (BitMemory.dirtySpec w).DemonicValid s
      (if s.bitSize < b then
        pure none
      else do
        let x ← BitMemory.readBits (s.bitSize - b) b
        BitMemory.shrink b
        pure (some x))
    by_cases hlt : s.bitSize < b
    · simp only [hlt, ↓reduceIte]
      exact .pure (D := BitMemory.dirtySpec w) s none
    · simp only [hlt, ↓reduceIte]
      have hle : b ≤ s.bitSize := Nat.le_of_not_lt hlt
      have hv_rd : (BitMemory.dirtySpec w).valid s (.readBits (s.bitSize - b) b) :=
        ⟨hbw, by omega⟩
      refine .liftBind (D := BitMemory.dirtySpec w) (.readBits (s.bitSize - b) b) _ hv_rd
        fun s₂ x hstep₂ => ?_
      obtain ⟨h2, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
      subst h2
      exact .liftBind (D := BitMemory.dirtySpec w) (.shrink b) _ hle
        fun s₃ _ _ => .pure (D := BitMemory.dirtySpec w) s₃ (some x)
  | read i =>
    have hi : i < count b s := by simpa [length_abs] using hv
    have hslot : i * b + b ≤ s.bitSize := by
      rw [hs.bitSize_eq]
      exact slot_end_le_of_lt b hi
    exact .liftBind (D := BitMemory.dirtySpec w) (.readBits (i * b) b) _ ⟨hbw, hslot⟩
      fun s₁ a _ => .pure (D := BitMemory.dirtySpec w) s₁ a
  | write i x =>
    obtain ⟨hi', hx⟩ := hv
    have hi : i < count b s := by simpa [length_abs] using hi'
    have hslot : i * b + b ≤ s.bitSize := by
      rw [hs.bitSize_eq]
      exact slot_end_le_of_lt b hi
    exact .liftBind (D := BitMemory.dirtySpec w) (.writeBits (i * b) b x) _ ⟨hbw, hslot, hx⟩
      fun s₁ a _ => .pure (D := BitMemory.dirtySpec w) s₁ a

/-- Under `Inv w b s`, every demonic execution of `ops b o` on `BitMemory.dirtySpec w` produces the
exact same result and post-state as `BitMemory.spec w` and costs at most `3` bit-memory units,
because `append b x` immediately overwrites the newly grown `b` bits `[s.bitSize, s.bitSize + b)`
via `writeBits`. -/
theorem clientRun_ops_dirty (hw : 0 < w) (hbw : b ≤ w)
    {s s' : BitMemory.State} (hs : Inv w b s) (o : DynamicArray.Op)
    {r : o.Result} {tr : (BitMemory.dirtySpec w).Transcript}
    (hrun : (BitMemory.dirtySpec w).ClientRun s (ops b o) r s' tr) :
    r = (BitMemory.spec w).clientResult s (ops b o) ∧
      s' = (BitMemory.spec w).clientState s (ops b o) ∧
      (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) s tr ≤ 3 := by
  cases o with
  | append x =>
    obtain ⟨_, offset, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
      ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
    obtain ⟨_, u, s₂, tr₂, hstep₂, hrun₂, rfl⟩ :=
      ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₁
    obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₂
    have hoff : offset = s.bitSize := hstep₁.2.1
    subst hoff
    have hsz₁ : s₁.bitSize = s.bitSize + b := hstep₁.1
    obtain ⟨h2, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
    have hmem_eq : writeFieldMem w 0 s₁.mem s.bitSize b x =
        writeFieldMem w 0 (clearRangeMem w s.mem s.bitSize (s.bitSize + b)) s.bitSize b x := by
      rw [writeFieldMem_of_dirtyStep_grow hw hs.wellFormed hbw hstep₁,
        ← writeFieldMem_clearRangeMem_self hw hs.wellFormed hbw x]
    refine ⟨rfl, ?_, ?_⟩
    · rw [← h2]
      change BitMemory.State.mk (writeFieldMem w 0 s₁.mem s.bitSize b x) s₁.bitSize =
        ((BitMemory.spec w).runClient s (append b x)).2.1
      rw [runClient_append]
      change BitMemory.State.mk (writeFieldMem w 0 s₁.mem s.bitSize b x) s₁.bitSize =
        BitMemory.State.mk
          (writeFieldMem w 0 (clearRangeMem w s.mem s.bitSize (s.bitSize + b)) s.bitSize b x)
          (s.bitSize + b)
      rw [hmem_eq, hsz₁]
    · have hch : BitMemory.charge w s (.grow b) = 1 :=
        BitMemory.charge_grow_of_le hw hbw s
      simp only [StateTransitionSpec.totalCostTranscript_cons,
        StateTransitionSpec.totalCostTranscript_nil, hch, BitMemory.charge_writeBits]
      omega
  | pop =>
    obtain ⟨_, sz, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
      ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
    obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
    subst h1; subst h1v
    change (BitMemory.dirtySpec w).ClientRun s
      (if s.bitSize < b then
        pure none
      else do
        let x ← BitMemory.readBits (s.bitSize - b) b
        BitMemory.shrink b
        pure (some x)) r s' tr₁ at hrun₁
    by_cases hlt : s.bitSize < b
    · simp only [hlt, ↓reduceIte] at hrun₁
      obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₁
      change none = ((BitMemory.spec w).runClient s' (pop b)).1 ∧
        s' = ((BitMemory.spec w).runClient s' (pop b)).2.1 ∧ _
      rw [runClient_pop_of_lt hlt]
      refine ⟨rfl, rfl, ?_⟩
      simp only [StateTransitionSpec.totalCostTranscript_cons,
        StateTransitionSpec.totalCostTranscript_nil, BitMemory.charge_size]
      omega
    · simp only [hlt, ↓reduceIte] at hrun₁
      obtain ⟨_, x, s₂, tr₂, hstep₂, hrun₂, rfl⟩ :=
        ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₁
      obtain ⟨h2, h2v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
      subst h2; subst h2v
      obtain ⟨_, u, s₃, tr₃, hstep₃, hrun₃, rfl⟩ :=
        ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₂
      obtain ⟨h3, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₃
      subst h3
      obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₃
      change some (readField w 0 s.mem (s.bitSize - b) b) =
          ((BitMemory.spec w).runClient s (pop b)).1 ∧
        { mem := clearRangeMem w s.mem (s.bitSize - b) s.bitSize, bitSize := s.bitSize - b } =
          ((BitMemory.spec w).runClient s (pop b)).2.1 ∧ _
      rw [runClient_pop_of_ge hlt]
      refine ⟨rfl, rfl, ?_⟩
      have hsh : BitMemory.charge w s (.shrink b) = 1 :=
        BitMemory.charge_shrink_of_le hw hbw s
      simp only [StateTransitionSpec.totalCostTranscript_cons,
        StateTransitionSpec.totalCostTranscript_nil, BitMemory.charge_size,
        BitMemory.charge_readBits, hsh]
      omega
  | read i =>
    obtain ⟨_, a, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
      ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
    obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
    subst h1; subst h1v
    obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₁
    refine ⟨rfl, rfl, ?_⟩
    simp only [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.totalCostTranscript_nil, BitMemory.charge_readBits]
    omega
  | write i x =>
    obtain ⟨_, a, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
      ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
    obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
    subst h1; subst h1v
    obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₁
    refine ⟨rfl, rfl, ?_⟩
    simp only [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.totalCostTranscript_nil, BitMemory.charge_writeBits]
    omega

/-- Direct refinement of `DynamicArray.spec w b` over the demonic `BitMemory.dirtySpec w`. -/
def dirtyRefinement (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    Refinement (DynamicArray.spec w b) (BitMemory.dirtySpec w) where
  methods := dirtyMethods w b
  inv := Inv w b
  abs := abs w b
  valid {_} o hs hv := ops_demonicValid hbw hs o hv
  correct {_} o {_ _ _} hs hv hrun := by
    obtain ⟨rfl, rfl, _⟩ := clientRun_ops_dirty hw hbw hs o hrun
    exact ops_step hw hb hbw hs o hv

/-- Demonic bit-size-framed implementation of `DynamicArray.spec w b` over `BitMemory.dirtySpec w`,
recording that every represented array `xs` occupies `xs.length * b` bits. -/
def dirtyFramed (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    BitMemory.DirtyFramed (DynamicArray.spec w b) w where
  toRefinement := dirtyRefinement hw hb hbw
  sizeBits xs := xs.length * b
  bitSize_eq hs := bitSize_eq_length_mul hs
  wellFormed hs := hs.wellFormed

/-- **Demonic worst-case `O(1)` cost certificate (zero potential)**: every operation of
`DynamicArray.spec w b` costs at most `3` bit-memory operations on every demonic execution path of
`BitMemory.dirtySpec w`. -/
theorem dirtyAmortized (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    (dirtyRefinement hw hb hbw).Amortized (BitMemory.charge w) (fun _ _ => 3) (fun _ => 0) where
  step {_} o {_ _ _} hs _ hrun := by
    obtain ⟨_, _, hcost⟩ := clientRun_ops_dirty hw hbw hs o hrun
    simpa using hcost

/-- **Main Stage 1 theorem for adaptive clients on demonic `BitMemory.dirtySpec w`**: running any
admissible adaptive client `p : (DynamicArray.spec w b).Client α` from `BitMemory.empty` (`[]`)
over `BitMemory.dirtySpec w` is demonically valid (`DemonicValid`), and every demonic execution path
produces the exact specified answer and final array state `xs'`, executes in at most `3 * m`
bit-memory operations (where `m` is the number of array operations issued by `p`), and ends with
allocated bit size `xs'.length * b` bits (`xs'.length * b + w` bits including the `w`-bit segment
descriptor). -/
theorem dirty_client_run_from_empty {α : Type} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (p : (DynamicArray.spec w b).Client α)
    (hv : (DynamicArray.spec w b).ValidHistory [] ((DynamicArray.spec w b).clientHistory [] p)) :
    let linked := link (dirtyMethods w b) p
    (BitMemory.dirtySpec w).DemonicValid BitMemory.empty linked ∧
      ∀ r s' tr,
        (BitMemory.dirtySpec w).ClientRun BitMemory.empty linked r s' tr →
        (BitMemory.dirtySpec w).ValidTranscript BitMemory.empty tr s' ∧
          r = (DynamicArray.spec w b).clientResult [] p ∧
          abs w b s' = (DynamicArray.spec w b).clientState [] p ∧
          s'.bitSize = ((DynamicArray.spec w b).clientState [] p).length * b ∧
          (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) BitMemory.empty tr ≤
            3 * ((DynamicArray.spec w b).clientHistory [] p).length := by
  have ⟨hinv0, habs0⟩ := inv_empty w b
  have hv0 : (DynamicArray.spec w b).ValidHistory (abs w b BitMemory.empty)
      ((DynamicArray.spec w b).clientHistory (abs w b BitMemory.empty) p) := by
    rwa [habs0]
  have hvD : (DynamicArray.spec w b).DemonicValid (abs w b BitMemory.empty) p :=
    ((DynamicArray.spec w b).demonicValid_iff_validHistory_runClient _ p).mpr hv0
  refine ⟨((dirtyRefinement hw hb hbw).simulates_demonic p hinv0 hvD).1, fun r s' tr hrun => ?_⟩
  obtain ⟨hinv', tr_D, hrun_D, hcost_le⟩ :=
    (dirtyAmortized hw hb hbw).demonic p hinv0 hvD hrun
  dsimp only [dirtyRefinement] at hinv' hrun_D hcost_le
  rw [habs0] at hrun_D hcost_le
  obtain ⟨_, hr, habs', rfl⟩ :=
    ((DynamicArray.spec w b).clientRun_iff_runClient [] p r (abs w b s') tr_D).mp hrun_D
  rw [StateTransitionSpec.totalCostTranscript_canonicalTranscript,
    StateTransitionSpec.totalCost_const, Nat.mul_comm] at hcost_le
  refine ⟨hrun.validTranscript, hr, habs', ?_, by omega⟩
  rw [bitSize_eq_length_mul hinv', habs']

/-! ## Deterministic specialization over `BitMemory.spec w` -/

/-- Verified refinement of `DynamicArray.spec w b` over `BitMemory.spec w`. -/
def refinement (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    Refinement (DynamicArray.spec w b) (BitMemory.spec w) :=
  Refinement.ofFn (methods w b) (Inv w b) (abs w b)
    (fun {_} o hs hv => ops_validHistory hbw hs o hv)
    (fun {_} o hs hv => by
      obtain ⟨hstep, hinv⟩ := ops_step hw hb hbw hs o hv
      exact ⟨hstep.symm, hinv⟩)

/-- Bit-size-framed implementation of `DynamicArray.spec w b` over `BitMemory.spec w`, recording
that every represented array `xs` occupies `xs.length * b` bits. -/
def framed (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    BitMemory.Framed (DynamicArray.spec w b) w where
  toRefinement := refinement hw hb hbw
  sizeBits xs := xs.length * b
  bitSize_eq hs := bitSize_eq_length_mul hs
  wellFormed hs := hs.wellFormed

/-- **Worst-case `O(1)` cost certificate (zero potential)**: every operation of
`DynamicArray.spec w b` costs at most `3` bit-memory operations in the worst case. -/
theorem amortized (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    (refinement hw hb hbw).Amortized (BitMemory.charge w) (fun _ _ => 3) (fun _ => 0) :=
  Refinement.Amortized.ofFn fun {s} o _ _ => by
    simpa [refinement, methods] using ops_cost hw hbw s o

/-- **Stage 1 theorem for adaptive clients over `BitMemory.spec w`**: running any admissible
adaptive client `p : (DynamicArray.spec w b).Client α` from `BitMemory.empty` (`[]`) produces the
exact specified answer and final array state `xs'`, executes in at most `3 * m` bit-memory
operations, and ends with allocated bit size `xs'.length * b` bits. -/
theorem client_run_from_empty {α : Type} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (p : (DynamicArray.spec w b).Client α)
    (hv : (DynamicArray.spec w b).ValidHistory [] ((DynamicArray.spec w b).clientHistory [] p)) :
    let linked := link (methods w b) p
    let s' := (BitMemory.spec w).clientState BitMemory.empty linked
    (BitMemory.spec w).ValidHistory BitMemory.empty
        ((BitMemory.spec w).clientHistory BitMemory.empty linked) ∧
      (BitMemory.spec w).clientResult BitMemory.empty linked =
        (DynamicArray.spec w b).clientResult [] p ∧
      abs w b s' = (DynamicArray.spec w b).clientState [] p ∧
      s'.bitSize = ((DynamicArray.spec w b).clientState [] p).length * b ∧
      (BitMemory.spec w).totalCost (BitMemory.charge w) BitMemory.empty
        ((BitMemory.spec w).clientHistory BitMemory.empty linked) ≤
          3 * ((DynamicArray.spec w b).clientHistory [] p).length := by
  have ⟨hinv0, habs0⟩ := inv_empty w b
  have hv0 : (DynamicArray.spec w b).ValidHistory (abs w b BitMemory.empty)
      ((DynamicArray.spec w b).clientHistory (abs w b BitMemory.empty) p) := by
    rwa [habs0]
  obtain ⟨hv_low, hres, habs', hinv'⟩ := (refinement hw hb hbw).simulates_client p hinv0 hv0
  have hcost := (amortized hw hb hbw).client p hinv0 hv0
  dsimp only [refinement, Refinement.ofFn] at hv_low hres habs' hinv' hcost
  rw [habs0] at hres habs' hcost
  rw [StateTransitionSpec.totalCost_const, Nat.mul_comm] at hcost
  refine ⟨hv_low, hres, habs', ?_, by omega⟩
  rw [bitSize_eq_length_mul hinv', habs']

/-! ## Concrete `BitRAM` machine-instruction grounding of the resizable `b`-bit array -/

/-- Concrete `BitRAM.Code .standard 12` program for `DynamicArray.Op.append x` (with `x` in `r3`):
loads `b` into `r1`, executes `.grow 1 1` (growing `bitSize` by `b` bits and placing old `bitSize`
in `r1`), loads `b` into `r2`, and executes `BitRAM.writeBitsCode`. -/
def appendCode (b : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 b))
    (.seq (.grow 1 1)
      (.seq (.op (.const 2 b))
        BitRAM.writeBitsCode))

/-- **Machine-level correctness of `appendCode`**: for any well-formed machine state `x : Data 12`
satisfying `Inv w b x.toBitMemoryState` and `(DynamicArray.spec w b).valid _ (.append (x.regs 3))`,
`appendCode b` executes in at most `45` `BitRAM` instructions under demonic `.grow`, preserving
`Inv w b`, updating the abstract array to `abs w b x.toBitMemoryState ++ [x.regs 3]`, and setting
`y.bitSize = ((abs w b x.toBitMemoryState).length + 1) * b`. -/
theorem appendCode_exec (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {x : BitRAM.Data 12} (hx : x.WellFormed w) (hinv : Inv w b x.toBitMemoryState)
    (hv : (DynamicArray.spec w b).valid (abs w b x.toBitMemoryState) (.append (x.regs 3))) :
    BitRAM.DemonicExecWithin w (appendCode b) x
      (fun y =>
        Inv w b y.toBitMemoryState ∧
        abs w b y.toBitMemoryState = abs w b x.toBitMemoryState ++ [x.regs 3] ∧
        y.bitSize = ((abs w b x.toBitMemoryState).length + 1) * b) 45 := by
  obtain ⟨hval_b, hfits_new⟩ := hv
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have hgrow_fits : Fits w (x.bitSize + b) := by
    have hsz : x.bitSize = (abs w b x.toBitMemoryState).length * b := bitSize_eq_length_mul hinv
    rw [hsz]
    simpa [Nat.succ_mul] using hfits_new
  refine DemonicExecWithin.step_const (T := 44) hb_fits ?_
  have hcost_grow : max 1 (b ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hbw x.toBitMemoryState).le
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w x.toBitMemoryState (.grow b) s₁ x.bitSize ∧
        y₁ = ⟨Function.update (x.set 1 b).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 43)
    (.grow hgrow_fits hcost_grow fun s₁ hs₁ => ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  refine DemonicExecWithin.step_const (T := 42) hb_fits ?_
  let x₂ : BitRAM.Data 12 :=
    (⟨Function.update (x.set 1 b).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩ : BitRAM.Data 12).set 2 b
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep hw hinv.wellFormed
      (show BitMemory.valid w x.toBitMemoryState (.grow b) from hgrow_fits) hs₁
  have hx₂_wf : x₂.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi2 : i = 2
    · subst hi2; exact hb_fits
    · by_cases hi1 : i = 1
      · subst hi1
        change Fits w x.bitSize
        exact hx.mem_wf.bitSize_fits
      · simp only [x₂, BitRAM.Data.set, Function.update_of_ne hi2, Function.update_of_ne hi1]
        exact hx.regs_fits i
  have hv_write : BitMemory.valid w x₂.toBitMemoryState
      (.writeBits (x₂.regs 1) (x₂.regs 2) (x₂.regs 3)) := by
    refine ⟨hbw, ?_, hval_b⟩
    change x.bitSize + b ≤ s₁.bitSize
    rw [hs₁.1]
    exact le_rfl
  refine (BitRAM.writeBitsCode_exec hw hx₂_wf hv_write).mono (fun y hy => ?_) le_rfl
  have hmem_eq : writeFieldMem w 0 s₁.mem x.bitSize b (x.regs 3) =
      writeFieldMem w 0 (clearRangeMem w x.mem x.bitSize (x.bitSize + b))
        x.bitSize b (x.regs 3) := by
    rw [writeFieldMem_of_dirtyStep_grow hw hinv.wellFormed hbw hs₁,
      ← writeFieldMem_clearRangeMem_self hw hinv.wellFormed hbw (x.regs 3)]
    rfl
  have hy_st : y.toBitMemoryState =
      (BitMemory.spec w).clientState x.toBitMemoryState (append b (x.regs 3)) := by
    rw [hy]
    ext q
    · change writeFieldMem w 0 s₁.mem x.bitSize b (x.regs 3) q = _
      rw [hmem_eq]
      rfl
    · exact hs₁.1
  obtain ⟨hstep_app, hinv_app⟩ := step_append hw hb hbw hinv ⟨hval_b, hfits_new⟩
  have habs_app :
      abs w b ((BitMemory.spec w).clientState x.toBitMemoryState (append b (x.regs 3))) =
        abs w b x.toBitMemoryState ++ [x.regs 3] := congrArg Prod.fst hstep_app
  change Inv w b y.toBitMemoryState ∧
    abs w b y.toBitMemoryState = abs w b x.toBitMemoryState ++ [x.regs 3] ∧
    y.toBitMemoryState.bitSize = ((abs w b x.toBitMemoryState).length + 1) * b
  rw [hy_st]
  refine ⟨hinv_app, habs_app, ?_⟩
  rw [bitSize_eq_length_mul hinv_app, habs_app, List.length_append, List.length_singleton]

/-- Concrete `BitRAM.Code .standard 12` program for `DynamicArray.Op.pop`:
loads `b` into `r2`, reads `bitSize` into `r1`, and branches on `r1 < r2` (`bitSize < b`). If
empty, sets `r1 := 0` (`none`); otherwise sets `r1 := r1 - r2` (`bitSize - b`), runs
`readBitsCode` (putting the last item in `r0`), loads `b` into `r1`, runs `.shrink 1` (shrinking
`bitSize` by `b` bits), and sets `r1 := 1` (`some r0`). -/
def popCode (b : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 2 b))
    (.seq (.size 1)
      (.branch (.lt 1 2)
        (.op (.const 1 0))
        (.seq (.op (.bin .sub 1 1 2))
          (.seq BitRAM.readBitsCode
            (.seq (.op (.const 1 b))
              (.seq (.shrink 1)
                (.op (.const 1 1))))))))

/-- **Machine-level correctness of `popCode`**: for any well-formed machine state `x : Data 12`
satisfying `Inv w b x.toBitMemoryState`, `popCode b` executes in at most `40` `BitRAM` instructions,
preserving `Inv w b`, updating `abs w b y.toBitMemoryState` to
`(abs w b x.toBitMemoryState).dropLast`, encoding `(abs w b x.toBitMemoryState).getLast?` via
`(if y.regs 1 = 0 then none else some (y.regs 0))`, and shrinking `y.bitSize` to
`((abs w b x.toBitMemoryState).length - 1) * b`. -/
theorem popCode_exec (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {x : BitRAM.Data 12} (hx : x.WellFormed w) (hinv : Inv w b x.toBitMemoryState) :
    BitRAM.DemonicExecWithin w (popCode b) x
      (fun y =>
        Inv w b y.toBitMemoryState ∧
        abs w b y.toBitMemoryState = (abs w b x.toBitMemoryState).dropLast ∧
        (if y.regs 1 = 0 then none else some (y.regs 0)) =
          (abs w b x.toBitMemoryState).getLast? ∧
        y.bitSize = ((abs w b x.toBitMemoryState).length - 1) * b) 40 := by
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  refine DemonicExecWithin.step_const (T := 39) hb_fits ?_
  refine .seq (T₁ := 1) (T₂ := 38)
    (.size hx.mem_wf.bitSize_fits rfl le_rfl)
    (fun x₁ hx₁ => ?_) (by omega)
  subst hx₁
  by_cases hlt : x.bitSize < b
  · refine .branch_pos (T₀ := 1) hlt (DemonicExecWithin.const h0 ?_) (by omega)
    have hcount0 : count b x.toBitMemoryState = 0 := Nat.div_eq_of_lt hlt
    have habs0 : abs w b x.toBitMemoryState = [] := by simp [abs, hcount0]
    have hsz0 : x.bitSize = 0 := by
      change x.toBitMemoryState.bitSize = 0
      rw [hinv.bitSize_eq, hcount0, Nat.zero_mul]
    refine ⟨hinv, ?_, ?_, ?_⟩
    · change abs w b x.toBitMemoryState = (abs w b x.toBitMemoryState).dropLast
      simp [habs0]
    · simp [habs0]
    · change x.bitSize = ((abs w b x.toBitMemoryState).length - 1) * b
      simp [hsz0, habs0]
  · have hle : b ≤ x.bitSize := Nat.le_of_not_lt hlt
    have hsub_fits : Fits w (x.bitSize - b) :=
      Fits.of_le hx.mem_wf.bitSize_fits (Nat.sub_le _ _)
    refine .branch_neg (T₀ := 36) hlt ?_ (by omega)
    refine DemonicExecWithin.step_bin (T := 35) hsub_fits ?_
    let x₂ : BitRAM.Data 12 := ((x.set 2 b).set 1 x.bitSize).set 1 (x.bitSize - b)
    have hx₂_wf : x₂.WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi1 : i = 1
      · subst hi1; exact hsub_fits
      · by_cases hi2 : i = 2
        · subst hi2; exact hb_fits
        · simp only [x₂, BitRAM.Data.set, Function.update_of_ne hi1, Function.update_of_ne hi2]
          exact hx.regs_fits i
    have hv_read : BitMemory.valid w x₂.toBitMemoryState (.readBits (x₂.regs 1) (x₂.regs 2)) := by
      refine ⟨hbw, ?_⟩
      change (x.bitSize - b) + b ≤ x.bitSize
      exact (Nat.sub_add_cancel hle).le
    refine .seq (T₁ := 32) (T₂ := 3)
      (BitRAM.readBitsCode_exec hw hx₂_wf hv_read)
      (fun y₁ ⟨hr0, hst₁⟩ => ?_) (by omega)
    change y₁.regs 0 = readField w 0 x.mem (x.bitSize - b) b at hr0
    change y₁.toBitMemoryState = x.toBitMemoryState at hst₁
    refine DemonicExecWithin.step_const (T := 2) hb_fits ?_
    have hle₁ : (y₁.set 1 b).regs 1 ≤ (y₁.set 1 b).bitSize := by
      change b ≤ y₁.toBitMemoryState.bitSize
      rw [hst₁]
      exact hle
    have hcost_sh : max 1 (((y₁.set 1 b).regs 1) ⌈/⌉ w) ≤ 1 :=
      (BitMemory.charge_shrink_of_le hw hbw x.toBitMemoryState).le
    refine .seq (T₁ := 1) (T₂ := 1)
      (.shrink hle₁ hcost_sh rfl)
      (fun y₂ hy₂ => ?_) (by omega)
    subst hy₂
    refine DemonicExecWithin.const h1 ?_
    obtain ⟨hstep_pop, hinv_pop⟩ := step_pop hw hb hbw hinv
    have hstate_pop : (BitMemory.spec w).clientState x.toBitMemoryState (pop b) =
        (BitMemory.stepFn w x.toBitMemoryState (.shrink b)).1 := by
      dsimp only [StateTransitionSpec.clientState]
      rw [runClient_pop_of_ge hlt]
      rfl
    have hres_pop : (BitMemory.spec w).clientResult x.toBitMemoryState (pop b) =
        some (x.toBitMemoryState.getField w (x.bitSize - b) b) := by
      dsimp only [StateTransitionSpec.clientResult]
      rw [runClient_pop_of_ge hlt]
      rfl
    let y₃ : BitRAM.Data 12 :=
      (⟨(y₁.set 1 b).regs,
        (BitMemory.stepFn w (y₁.set 1 b).toBitMemoryState (.shrink ((y₁.set 1 b).regs 1))).1.mem,
        (y₁.set 1 b).bitSize - (y₁.set 1 b).regs 1⟩ : BitRAM.Data 12).set 1 1
    have hy₃_st : y₃.toBitMemoryState =
        (BitMemory.spec w).clientState x.toBitMemoryState (pop b) := by
      rw [hstate_pop]
      ext q
      · change (BitMemory.stepFn w y₁.toBitMemoryState (.shrink b)).1.mem q = _
        rw [hst₁]
      · change y₁.toBitMemoryState.bitSize - b = _
        rw [hst₁]
        rfl
    have habs_pop : abs w b ((BitMemory.spec w).clientState x.toBitMemoryState (pop b)) =
        (abs w b x.toBitMemoryState).dropLast := congrArg Prod.fst hstep_pop
    have hget_pop : (BitMemory.spec w).clientResult x.toBitMemoryState (pop b) =
        (abs w b x.toBitMemoryState).getLast? := congrArg Prod.snd hstep_pop
    change Inv w b y₃.toBitMemoryState ∧
      abs w b y₃.toBitMemoryState = (abs w b x.toBitMemoryState).dropLast ∧
      (if y₃.regs 1 = 0 then none else some (y₃.regs 0)) =
        (abs w b x.toBitMemoryState).getLast? ∧
      y₃.toBitMemoryState.bitSize = ((abs w b x.toBitMemoryState).length - 1) * b
    rw [hy₃_st]
    refine ⟨hinv_pop, habs_pop, ?_, ?_⟩
    · change (if (1 : ℕ) = 0 then none else some (y₁.regs 0)) = _
      simp only [Nat.one_ne_zero, ↓reduceIte, hr0, ← hget_pop, hres_pop]
      rfl
    · rw [bitSize_eq_length_mul hinv_pop, habs_pop, List.length_dropLast]

/-- Concrete `BitRAM.Code .standard 12` program for `DynamicArray.Op.read i` (with `i` in `r1`):
loads `b` into `r2`, computes `r1 := r1 * r2` (`i * b`), and executes `BitRAM.readBitsCode`. -/
def readCode (b : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 2 b))
    (.seq (.op (.bin .mul 1 1 2))
      BitRAM.readBitsCode)

/-- **Machine-level correctness of `readCode`**: for any well-formed machine state `x : Data 12`
satisfying `Inv w b x.toBitMemoryState` and `x.regs 1 < (abs w b x.toBitMemoryState).length`,
`readCode b` executes in at most `34` `BitRAM` instructions, leaving `y.toBitMemoryState` unchanged
and setting `y.regs 0 = (abs w b x.toBitMemoryState).getD (x.regs 1) 0`. -/
theorem readCode_exec (hw : 0 < w) (hbw : b ≤ w)
    {x : BitRAM.Data 12} (hx : x.WellFormed w) (hinv : Inv w b x.toBitMemoryState)
    (hv : (DynamicArray.spec w b).valid (abs w b x.toBitMemoryState) (.read (x.regs 1))) :
    BitRAM.DemonicExecWithin w (readCode b) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.regs 0 = (abs w b x.toBitMemoryState).getD (x.regs 1) 0) 34 := by
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have hi' : x.regs 1 < count b x.toBitMemoryState := by simpa [length_abs] using hv
  have hslot : x.regs 1 * b + b ≤ x.bitSize := by
    change x.regs 1 * b + b ≤ x.toBitMemoryState.bitSize
    rw [hinv.bitSize_eq]
    exact slot_end_le_of_lt b hi'
  have hmul_fits : Fits w (x.regs 1 * b) :=
    Fits.of_le hx.mem_wf.bitSize_fits (Nat.le_trans (Nat.le_add_right _ b) hslot)
  refine DemonicExecWithin.step_const (T := 33) hb_fits ?_
  refine DemonicExecWithin.step_bin (T := 32) hmul_fits ?_
  let x₁ : BitRAM.Data 12 := (x.set 2 b).set 1 (x.regs 1 * b)
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hmul_fits
    · by_cases hi2 : i = 2
      · subst hi2; exact hb_fits
      · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi1, Function.update_of_ne hi2]
        exact hx.regs_fits i
  have hv_read : BitMemory.valid w x₁.toBitMemoryState (.readBits (x₁.regs 1) (x₁.regs 2)) :=
    ⟨hbw, hslot⟩
  refine (BitRAM.readBitsCode_exec hw hx₁_wf hv_read).mono (fun y ⟨hr0, hst⟩ => ?_) le_rfl
  obtain ⟨hstep_rd, _⟩ := step_read hinv hv
  have hrd_eq : x.toBitMemoryState.getField w (x.regs 1 * b) b =
      (abs w b x.toBitMemoryState).getD (x.regs 1) 0 := congrArg Prod.snd hstep_rd
  exact ⟨hst, hr0.trans hrd_eq⟩

/-- Concrete `BitRAM.Code .standard 12` program for `DynamicArray.Op.write i v` (with `i` in `r1`
and `v` in `r3`): loads `b` into `r2`, computes `r1 := r1 * r2` (`i * b`), and executes
`BitRAM.writeBitsCode`. -/
def writeCode (b : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 2 b))
    (.seq (.op (.bin .mul 1 1 2))
      BitRAM.writeBitsCode)

/-- **Machine-level correctness of `writeCode`**: for any well-formed machine state `x : Data 12`
satisfying `Inv w b x.toBitMemoryState` and
`(DynamicArray.spec w b).valid _ (.write (x.regs 1) (x.regs 3))`, `writeCode b` executes in at most
`44` `BitRAM` instructions, preserving `Inv w b`, updating `abs w b y.toBitMemoryState` to
`(abs w b x.toBitMemoryState).set (x.regs 1) (x.regs 3)`, and maintaining
`y.bitSize = (abs w b x.toBitMemoryState).length * b`. -/
theorem writeCode_exec (hw : 0 < w) (hbw : b ≤ w)
    {x : BitRAM.Data 12} (hx : x.WellFormed w) (hinv : Inv w b x.toBitMemoryState)
    (hv : (DynamicArray.spec w b).valid (abs w b x.toBitMemoryState)
      (.write (x.regs 1) (x.regs 3))) :
    BitRAM.DemonicExecWithin w (writeCode b) x
      (fun y =>
        Inv w b y.toBitMemoryState ∧
        abs w b y.toBitMemoryState =
          (abs w b x.toBitMemoryState).set (x.regs 1) (x.regs 3) ∧
        y.bitSize = (abs w b x.toBitMemoryState).length * b) 44 := by
  obtain ⟨hi, hval_b⟩ := hv
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have hi' : x.regs 1 < count b x.toBitMemoryState := by simpa [length_abs] using hi
  have hslot : x.regs 1 * b + b ≤ x.bitSize := by
    change x.regs 1 * b + b ≤ x.toBitMemoryState.bitSize
    rw [hinv.bitSize_eq]
    exact slot_end_le_of_lt b hi'
  have hmul_fits : Fits w (x.regs 1 * b) :=
    Fits.of_le hx.mem_wf.bitSize_fits (Nat.le_trans (Nat.le_add_right _ b) hslot)
  refine DemonicExecWithin.step_const (T := 43) hb_fits ?_
  refine DemonicExecWithin.step_bin (T := 42) hmul_fits ?_
  let x₁ : BitRAM.Data 12 := (x.set 2 b).set 1 (x.regs 1 * b)
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hx.mem_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hmul_fits
    · by_cases hi2 : i = 2
      · subst hi2; exact hb_fits
      · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi1, Function.update_of_ne hi2]
        exact hx.regs_fits i
  have hv_write : BitMemory.valid w x₁.toBitMemoryState
      (.writeBits (x₁.regs 1) (x₁.regs 2) (x₁.regs 3)) :=
    ⟨hbw, hslot, hval_b⟩
  refine (BitRAM.writeBitsCode_exec hw hx₁_wf hv_write).mono (fun y hy => ?_) le_rfl
  obtain ⟨hstep_wr, hinv_wr⟩ := step_write hw hbw hinv hi hval_b
  have habs_wr : abs w b ((BitMemory.spec w).clientState x.toBitMemoryState
      (write b (x.regs 1) (x.regs 3))) =
      (abs w b x.toBitMemoryState).set (x.regs 1) (x.regs 3) := congrArg Prod.fst hstep_wr
  have hy_eq : y.toBitMemoryState =
      (BitMemory.spec w).clientState x.toBitMemoryState (write b (x.regs 1) (x.regs 3)) := hy
  change Inv w b y.toBitMemoryState ∧
    abs w b y.toBitMemoryState = (abs w b x.toBitMemoryState).set (x.regs 1) (x.regs 3) ∧
    y.toBitMemoryState.bitSize = (abs w b x.toBitMemoryState).length * b
  rw [hy_eq]
  exact ⟨hinv_wr, habs_wr, bitSize_eq_length_mul hinv⟩

/-! ## Single-tape subroutine composition in ONE `BitMemory.State` -/

/-- Linking commutes with monadic bind on `Client`. -/
theorem link_bind {D E : StateTransitionSpec} {α β : Type} (m : Methods D E)
    (p : D.Client α) (k : α → D.Client β) :
    (link m p).bind (fun a => link m (k a)) = link m (p.bind k) := by
  induction p with
  | pure a => rfl
  | liftBind o cont ih =>
    change ((m o).bind (fun x => link m (cont x))).bind (fun a => link m (k a)) =
      (m o).bind (fun x => link m ((cont x).bind k))
    rw [PFunctor.FreeM.bind_assoc]
    congr 1
    funext x
    exact ih x

/-- **Sequential single-tape subroutine composition on demonic `BitMemory.dirtySpec w`**:
when a client runs a phase-1 array program `p₁` from `BitMemory.empty` that returns the array to
empty (`(DynamicArray.spec w b).clientState [] p₁ = []`, releasing all allocated bits via `shrink`
so `s₁.bitSize = 0`), and then runs a phase-2 array program `p₂` on the **same** single tape `s₁`,
phase 2 reuses the released bit address space `[0, M)` from bit offset `0`, producing the exact
phase-2 result and final array `xs₂'` with `s₂.bitSize = xs₂'.length * b` and combined cost at most
`3 * (m₁ + m₂)`. -/
theorem singleTape_sequential_subroutine_reuse {α β : Type}
    (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (p₁ : (DynamicArray.spec w b).Client α)
    (p₂ : α → (DynamicArray.spec w b).Client β)
    (hv₁ : (DynamicArray.spec w b).ValidHistory []
      ((DynamicArray.spec w b).clientHistory [] p₁))
    (hempty₁ : (DynamicArray.spec w b).clientState [] p₁ = [])
    (hv₂ : (DynamicArray.spec w b).ValidHistory []
      ((DynamicArray.spec w b).clientHistory []
        (p₂ ((DynamicArray.spec w b).clientResult [] p₁)))) :
    let a₁ := (DynamicArray.spec w b).clientResult [] p₁
    let combined := do
      let a ← link (dirtyMethods w b) p₁
      link (dirtyMethods w b) (p₂ a)
    (BitMemory.dirtySpec w).DemonicValid BitMemory.empty combined ∧
      ∀ r s₂ tr,
        (BitMemory.dirtySpec w).ClientRun BitMemory.empty combined r s₂ tr →
        (BitMemory.dirtySpec w).ValidTranscript BitMemory.empty tr s₂ ∧
          r = (DynamicArray.spec w b).clientResult [] (p₂ a₁) ∧
          abs w b s₂ = (DynamicArray.spec w b).clientState [] (p₂ a₁) ∧
          s₂.bitSize = ((DynamicArray.spec w b).clientState [] (p₂ a₁)).length * b ∧
          (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) BitMemory.empty tr ≤
            3 * (((DynamicArray.spec w b).clientHistory [] p₁).length +
              ((DynamicArray.spec w b).clientHistory [] (p₂ a₁)).length) := by
  intro a₁ combined
  have hcomp : combined = link (dirtyMethods w b) (p₁ >>= p₂) :=
    link_bind (dirtyMethods w b) p₁ p₂
  have hv_both : (DynamicArray.spec w b).ValidHistory []
      ((DynamicArray.spec w b).clientHistory [] (p₁ >>= p₂)) := by
    rw [StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append]
    refine ⟨hv₁, ?_⟩
    rw [(DynamicArray.spec w b).run_runClient p₁ [], hempty₁]
    exact hv₂
  obtain ⟨hdv, hmain_run⟩ := dirty_client_run_from_empty hw hb hbw (p₁ >>= p₂) hv_both
  rw [← hcomp] at hdv hmain_run
  refine ⟨hdv, fun r s₂ tr hrun => ?_⟩
  rcases hmain_run r s₂ tr hrun with ⟨hv_low, hr, habs₂, hsz₂, hcost⟩
  have hr_eq : (DynamicArray.spec w b).clientResult [] (p₁ >>= p₂) =
      (DynamicArray.spec w b).clientResult [] (p₂ a₁) := by
    rw [StateTransitionSpec.clientResult_bind, hempty₁]
  have hst_eq : (DynamicArray.spec w b).clientState [] (p₁ >>= p₂) =
      (DynamicArray.spec w b).clientState [] (p₂ a₁) := by
    rw [StateTransitionSpec.clientState_bind, hempty₁]
  have hhist_eq : ((DynamicArray.spec w b).clientHistory [] (p₁ >>= p₂)).length =
      ((DynamicArray.spec w b).clientHistory [] p₁).length +
        ((DynamicArray.spec w b).clientHistory [] (p₂ a₁)).length := by
    rw [StateTransitionSpec.clientHistory_bind, hempty₁, List.length_append]
  rw [hr_eq] at hr
  rw [hst_eq] at habs₂ hsz₂
  rw [hhist_eq] at hcost
  exact ⟨hv_low, hr, habs₂, hsz₂, hcost⟩

/-- **Concurrent single-tape two-array representation (`SingleTapeTwoArrays`)**:
two resizable `b`-bit arrays `(xs₁, xs₂)` stored simultaneously in a **single** linear
`s : BitMemory.State` (`[0, s.bitSize)`):
* Bits `[0, w)` hold the `w`-bit header `n₁ = xs₁.length`.
* Bits `[w, w + n₁ * b)` hold the `n₁` items of `xs₁`.
* Bits `[w + n₁ * b, w + (n₁ + n₂) * b)` hold the `n₂` items of `xs₂`.
* The total allocated bit size of the single tape is `s.bitSize = w + (n₁ + n₂) * b`. -/
structure SingleTapeTwoArrays (w b : ℕ) (s : BitMemory.State)
    (xs₁ xs₂ : DynamicArray.State) : Prop where
  /-- The single bit-memory state is well-formed at word width `w`. -/
  wellFormed : s.WellFormed w
  /-- Header `[0, w)` stores `xs₁.length`. -/
  header_eq : s.getField w 0 w = xs₁.length
  /-- `xs₁.length` fits in a `w`-bit word. -/
  len₁_fits : Fits w xs₁.length
  /-- Total allocated bit size is `w + (xs₁.length + xs₂.length) * b`. -/
  bitSize_eq : s.bitSize = w + (xs₁.length + xs₂.length) * b
  /-- Array 1 items sit in `[w, w + xs₁.length * b)`. -/
  items₁ : ∀ i (hi : i < xs₁.length), s.getField w (w + i * b) b = xs₁[i]
  /-- Array 2 items sit in `[w + xs₁.length * b, w + (xs₁.length + xs₂.length) * b)`. -/
  items₂ : ∀ j (hj : j < xs₂.length),
    s.getField w (w + (xs₁.length + j) * b) b = xs₂[j]

/-- Initialize the single-tape two-array layout `(xs₁ = [], xs₂ = [])` from `BitMemory.empty` by
growing `w` bits for the header and writing `0` into `[0, w)`. -/
def initSingleTapeTwoArrays (w : ℕ) : BitMemory.Prog Unit := do
  let _ ← BitMemory.grow w
  BitMemory.writeBits 0 w 0

/-- Initializing `SingleTapeTwoArrays` from `BitMemory.empty` on demonic `BitMemory.dirtySpec w`
establishes `SingleTapeTwoArrays w b s' [] []` with `s'.bitSize = w` in `2` bit-memory units. -/
theorem initSingleTapeTwoArrays_demonic (hw : 0 < w)
    {r : Unit} {s' : BitMemory.State} {tr : (BitMemory.dirtySpec w).Transcript}
    (hrun : (BitMemory.dirtySpec w).ClientRun BitMemory.empty
      (initSingleTapeTwoArrays w) r s' tr) :
    SingleTapeTwoArrays w b s' [] [] ∧ s'.bitSize = w ∧
      (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) BitMemory.empty tr = 2 := by
  obtain ⟨_, off, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
  obtain ⟨_, u, s₂, tr₂, hstep₂, hrun₂, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₁
  obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₂
  have hoff : off = 0 := hstep₁.2.1
  subst hoff
  have hsz₁ : s₁.bitSize = w := by simpa using hstep₁.1
  have hvalid₁ : BitMemory.valid w BitMemory.empty (.grow w) := by
    change Fits w (0 + w)
    simpa using fits_self w
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow w) hw (BitMemory.wellFormed_empty w)
      hvalid₁ hstep₁
  obtain ⟨h2, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
  have hs'_wf : s'.WellFormed w := by
    rw [← h2]
    exact BitMemory.wellFormed_stepFn (o := .writeBits 0 w 0) hw hs₁_wf
      ⟨le_rfl, by omega, fits_zero w⟩
  have hsz' : s'.bitSize = w := by
    rw [← h2]
    exact hsz₁
  refine ⟨⟨hs'_wf, ?_, fits_zero w, by simp [hsz'], fun i hi => by simp at hi,
    fun j hj => by simp at hj⟩, hsz', ?_⟩
  · rw [← h2]
    change readField w 0 (writeFieldMem w 0 s₁.mem 0 w 0) 0 w = 0
    exact readField_writeFieldMem_same hw s₁.mem le_rfl (fits_zero w)
  · have hch : BitMemory.charge w BitMemory.empty (.grow w) = 1 :=
      BitMemory.charge_grow_of_le hw le_rfl BitMemory.empty
    simp [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.totalCostTranscript_nil, hch]

/-- Single-tape program that pops the sole item of `xs₂ = [v]` (at bit offset `w + n₁ * b`) by
calling `shrink b` on the single tape, and then appends `v` to `xs₁` by calling `grow b`, writing
`v` into `[w + n₁ * b, w + (n₁ + 1) * b)`, and incrementing the header `n₁` in `[0, w)`. -/
def singleTapePop₂Append₁Prog (w b : ℕ) : BitMemory.Prog ℕ := do
  let n₁ ← BitMemory.readBits 0 w
  let v ← BitMemory.readBits (w + n₁ * b) b
  BitMemory.shrink b
  let off ← BitMemory.grow b
  BitMemory.writeBits off b v
  BitMemory.writeBits 0 w (n₁ + 1)
  pure v

/-- **Single-tape released-memory reuse (`singleTape_pop₂_append₁_reuses_released_bits`)**:
in a **single** linear `BitMemory.State` holding `SingleTapeTwoArrays w b s xs₁ [v]`, executing
`singleTapePop₂Append₁Prog w b` on demonic `BitMemory.dirtySpec w` pops `v` from array 2 via
`shrink b` (reducing `s.bitSize` from `w + (xs₁.length + 1) * b` to `w + xs₁.length * b`) and
immediately reuses those `b` bits via `grow b` to append `v` to array 1, ending in a state `s'`
on the **same** single tape satisfying `SingleTapeTwoArrays w b s' (xs₁ ++ [v]) []` with
`s'.bitSize = s.bitSize = w + (xs₁.length + 1) * b` in `6` bit-memory units (`O(1)` time). -/
theorem singleTape_pop₂_append₁_reuses_released_bits (hw : 0 < w) (hbw : b ≤ w)
    {s : BitMemory.State} {xs₁ : DynamicArray.State} {v : ℕ}
    (hst : SingleTapeTwoArrays w b s xs₁ [v])
    (hn₁_succ : Fits w (xs₁.length + 1)) (hv_fits : Fits b v)
    {r : ℕ} {s' : BitMemory.State} {tr : (BitMemory.dirtySpec w).Transcript}
    (hrun : (BitMemory.dirtySpec w).ClientRun s (singleTapePop₂Append₁Prog w b) r s' tr) :
    r = v ∧
      SingleTapeTwoArrays w b s' (xs₁ ++ [v]) [] ∧
      s'.bitSize = s.bitSize ∧
      (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) s tr = 6 := by
  obtain ⟨_, n₁, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
  obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
  subst h1; subst h1v
  obtain ⟨_, v', s₂, tr₂, hstep₂, hrun₂, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₁
  obtain ⟨h2, h2v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
  subst h2; subst h2v
  obtain ⟨_, u₃, s₃, tr₃, hstep₃, hrun₃, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₂
  obtain ⟨h3, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₃
  subst h3
  obtain ⟨_, off, s₄, tr₄, hstep₄, hrun₄, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₃
  obtain ⟨_, u₅, s₅, tr₅, hstep₅, hrun₅, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₄
  obtain ⟨h5, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₅
  subst h5
  obtain ⟨_, u₆, s₆, tr₆, hstep₆, hrun₆, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₅
  obtain ⟨h6, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₆
  subst h6
  obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₆
  have hn₁_eq : readField w 0 s.mem 0 w = xs₁.length := hst.header_eq
  have hv_eq : readField w 0 s.mem (w + readField w 0 s.mem 0 w * b) b = v := by
    rw [hn₁_eq]
    have h0 := hst.items₂ 0 (by simp)
    change readField w 0 s.mem (w + (xs₁.length + 0) * b) b = [v][0] at h0
    simpa using h0
  have hsz_s : s.bitSize = w + (xs₁.length + 1) * b := by
    simpa using hst.bitSize_eq
  have hle_b : b ≤ s.bitSize := by
    rw [hsz_s, Nat.add_mul, Nat.one_mul]
    omega
  have hs₃_wf : (BitMemory.stepFn w s (.shrink b)).1.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink b) hw hst.wellFormed hle_b
  have hsz₃ : s.bitSize - b = w + xs₁.length * b := by
    rw [hsz_s, Nat.add_mul, Nat.one_mul]
    omega
  have hoff_step : off = s.bitSize - b := hstep₄.2.1
  subst hoff_step
  have hstep₄_sz : s₄.bitSize = (s.bitSize - b) + b := hstep₄.1
  have hsz₄ : s₄.bitSize = s.bitSize := by
    rw [hstep₄_sz, Nat.sub_add_cancel hle_b]
  have hgrow_valid : BitMemory.valid w (BitMemory.stepFn w s (.shrink b)).1 (.grow b) := by
    change Fits w ((s.bitSize - b) + b)
    rw [Nat.sub_add_cancel hle_b]
    exact hst.wellFormed.bitSize_fits
  have hs₄_wf : s₄.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow b) hw hs₃_wf hgrow_valid hstep₄
  have hmem₅_eq : writeFieldMem w 0 s₄.mem (s.bitSize - b) b v =
      writeFieldMem w 0 (BitMemory.stepFn w s (.shrink b)).1.mem (w + xs₁.length * b) b v := by
    have h1 := writeFieldMem_of_dirtyStep_grow hw hs₃_wf hbw hstep₄ (val := v)
    change writeFieldMem w 0 s₄.mem (s.bitSize - b) b v =
      writeFieldMem w 0 (BitMemory.stepFn w s (.shrink b)).1.mem (s.bitSize - b) b v at h1
    exact h1.trans (by rw [hsz₃])
  rw [hv_eq, hn₁_eq]
  have hs₅_wf : (BitMemory.stepFn w s₄ (.writeBits (s.bitSize - b) b v)).1.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .writeBits (s.bitSize - b) b v) hw hs₄_wf
      ⟨hbw, by rw [hsz₄]; exact (Nat.sub_add_cancel hle_b).le, hv_fits⟩
  have hs'_wf : (BitMemory.stepFn w (BitMemory.stepFn w s₄ (.writeBits (s.bitSize - b) b v)).1
      (.writeBits 0 w (xs₁.length + 1))).1.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .writeBits 0 w (xs₁.length + 1)) hw hs₅_wf
      ⟨le_rfl, by change 0 + w ≤ s₄.bitSize; omega, hn₁_succ⟩
  refine ⟨rfl, ⟨hs'_wf, ?_, ?_, ?_, ?_, ?_⟩, hsz₄, ?_⟩
  · change readField w 0 (writeFieldMem w 0 _ 0 w (xs₁.length + 1)) 0 w = (xs₁ ++ [v]).length
    rw [List.length_append, List.length_singleton]
    exact readField_writeFieldMem_same hw _ le_rfl hn₁_succ
  · simpa using hn₁_succ
  · change s₄.bitSize = w + ((xs₁ ++ [v]).length + [].length) * b
    simpa [hsz_s] using hsz₄
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    change readField w 0 (writeFieldMem w 0 (writeFieldMem w 0 s₄.mem (s.bitSize - b) b v)
        0 w (xs₁.length + 1)) (w + i * b) b = (xs₁ ++ [v])[i]
    rw [readField_writeFieldMem_of_disjoint hw _ le_rfl hbw (Or.inr (by omega)), hmem₅_eq]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi_lt | rfl
    · rw [List.getElem_append_left hi_lt]
      have hdisj : (w + i * b) + b ≤ w + xs₁.length * b := by
        have := slot_end_le_of_lt b hi_lt
        omega
      rw [readField_writeFieldMem_of_disjoint hw _ hbw hbw (Or.inl hdisj)]
      have hsh := getField_stepFn_shrink (a := w + i * b) hw s b hbw (by omega)
      exact hsh.trans (hst.items₁ i hi_lt)
    · rw [List.getElem_append_right (le_rfl)]
      simp only [Nat.sub_self, List.getElem_singleton]
      exact readField_writeFieldMem_same hw _ hbw hv_fits
  · intro j hj
    simp at hj
  · have hch_sh : BitMemory.charge w s (.shrink b) = 1 :=
      BitMemory.charge_shrink_of_le hw hbw s
    have hch_gr : BitMemory.charge w
        { mem := clearRangeMem w s.mem (s.bitSize - b) s.bitSize, bitSize := s.bitSize - b }
        (.grow b) = 1 :=
      BitMemory.charge_grow_of_le hw hbw _
    simp only [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.totalCostTranscript_nil, BitMemory.charge_readBits,
      BitMemory.charge_writeBits, hch_sh, hch_gr]

end Cslib.DataStructure.DynamicArray.BitResizable
