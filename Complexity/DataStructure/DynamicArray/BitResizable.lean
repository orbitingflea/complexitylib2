/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.DynamicArray.Spec
public import Complexity.DataStructure.Memory.BitResizable

/-!
# Resizable Array of `b`-Bit Items in the Bit-Granular Resizable Word RAM

This module implements `DynamicArray.spec b` (for `0 < b ≤ w`) over the bit-granular resizable
memory `BitMemory.spec w`.

Because the underlying memory grows and shrinks in **bits**, an array of `n_t` items of `b` bits is
stored contiguously in `n_t * b` bits without wasted padding bits between items or doubling slack:

* `append x`: calls `BitMemory.grow b` (extending `bitSize` from `n_t * b` to `(n_t + 1) * b`) and
  `BitMemory.writeBits (n_t * b) b x`. Worst-case cost: `2` bit-memory operations (`O(1)`
  worst-case time).
* `pop`: queries `sz ← BitMemory.getSize`; if `sz < b` (`n_t = 0`), returns `none`; otherwise reads
  the last item at `sz - b = (n_t - 1) * b` and calls `BitMemory.shrink b`, immediately releasing
  `b` bits so `bitSize` drops to `(n_t - 1) * b`. Worst-case cost: at most `3` bit-memory
  operations (`O(1)` worst-case time).
* `read i`: calls `BitMemory.readBits (i * b) b`. Worst-case cost: `1` bit-memory operation (`O(1)`
  worst-case time).
* `write i x`: calls `BitMemory.writeBits (i * b) b x`. Worst-case cost: `1` bit-memory operation
  (`O(1)` worst-case time).

## Space bound at every step

At every step `t` with current array length `n_t`, the allocated bit-segment size is **exactly**
`n_t * b` bits (`bitSize_eq_length_mul`), occupying `(n_t * b) ⌈/⌉ w` words of `w` bits. Including
the single `w`-bit descriptor word that records `bitSize`, the total space at step `t` is
`n_t * b + w` bits (`O(1)` words of additive metadata overhead).

## Subroutine composition and reuse of released memory

We compose two resizable `b`-bit arrays in one machine (`twoArraysRefinement`, `twoArraysFramed`)
and prove a concrete client theorem (`popPushTransfer_reuses_released_bits`) that pops an item
from array 1 and appends it to array 2 under a shared bit budget
`B = (xs₁.length + xs₂.length) * b`: the `b` bits released by `pop` on array 1 are immediately
reused by `append` on array 2 without increasing the total allocated bit count above `B`.

## Main definitions

* `append`, `pop`, `read`, `write`, `ops`, `methods`: the resizable array operations as
  `BitMemory.Prog w` programs.
* `abs`, `Inv`: abstraction function and representation invariant.
* `refinement`, `framed`: verified refinement and bit-size-framed implementation of
  `DynamicArray.spec b` over `BitMemory.spec w`.
* `twoArraysSpec`, `twoArraysRefinement`: composition of two resizable `b`-bit arrays in one
  machine.
* `popPushTransfer`: client subroutine that pops from array 1 and appends to array 2.

## Main results

* `ops_validHistory`, `ops_step`, `ops_cost`: worst-case `O(1)` correctness and cost (`≤ 3`
  bit-memory units) of every array operation.
* `bitSize_eq_length_mul`: at every represented state, `s.bitSize = (abs w b s).length * b`
  (and `s.bitSize + w = (abs w b s).length * b + w` including the `w`-bit segment descriptor).
* `amortized`: worst-case (zero-potential) cost certificate of `3` units per operation.
* `client_run_from_empty`: adaptive client theorem starting from `BitMemory.empty` (`[]`).
* `twoArrays_client_run_from_empty`: adaptive client theorem for a caller using two resizable
  `b`-bit arrays in one machine.
* `popPushTransfer_reuses_released_bits`: popping from array 1 and appending to array 2 reuses the
  released `b` bits within the shared bit budget `B = (xs₁.length + xs₂.length) * b`.

## References

* [T. Hagerup, *Sorting and Searching on the Word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.DataStructure.DynamicArray.BitResizable

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory

variable {w b : ℕ}

/-! ## Method implementations over `BitMemory.spec w` -/

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

/-- Method table implementing `DynamicArray.spec b` over `BitMemory.spec w`. -/
abbrev methods (w b : ℕ) : Methods (DynamicArray.spec b) (BitMemory.spec w) :=
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
  refine ⟨⟨wellFormed_empty w, by simp [count]⟩, ?_⟩
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
    (hv : (DynamicArray.spec b).valid (abs w b s) o) :
    (BitMemory.spec w).ValidHistory s ((BitMemory.spec w).clientHistory s (ops b o)) := by
  cases o with
  | append x =>
    have hx : Fits b x := hv
    dsimp only [ops, StateTransitionSpec.clientHistory]
    rw [runClient_append]
    exact ⟨trivial, ⟨hbw, le_rfl, hx⟩, trivial⟩
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
    {s : BitMemory.State} (hs : Inv w b s) {x : ℕ} (hx : Fits b x) :
    let s' := (BitMemory.spec w).clientState s (append b x)
    let r := (BitMemory.spec w).clientResult s (append b x)
    (abs w b s', r) = DynamicArray.stepFn (abs w b s) (.append x) ∧ Inv w b s' := by
  have hv_grow : BitMemory.valid w s (.grow b) := trivial
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
      rw [readField_writeFieldMem_of_disjoint hw _ hbw (Or.inl hdisj)]
      exact getField_stepFn_grow hw s b hdisj
    · rw [List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton]
      change readField w 0 (writeFieldMem w 0
        (clearRangeMem w s.mem s.bitSize (s.bitSize + b)) s.bitSize b x) (count b s * b) b = x
      rw [← hs.bitSize_eq]
      exact readField_writeFieldMem_same hw _ hbw hx

/-- Semantic correctness and invariant preservation of `pop`. -/
theorem step_pop (hw : 0 < w) (hb : 0 < b)
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
        exact getField_stepFn_shrink hw s b hslot
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
  have hi' : i < count b s := by simpa [length_abs] using hi
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
    have hj' : j < count b s := hj₁
    simp only [abs, List.getElem_set, List.getElem_ofFn]
    change readField w 0 (writeFieldMem w 0 s.mem (i * b) b x) (j * b) b =
      if i = j then x else s.getField w (j * b) b
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      exact readField_writeFieldMem_same hw s.mem hbw hx
    · rw [ite_eq_right hij]
      exact readField_writeFieldMem_of_disjoint hw s.mem hbw (slot_disjoint_of_ne b hij)

/-- Combined step correctness for all four `DynamicArray.Op` operations. -/
theorem ops_step (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {s : BitMemory.State} (hs : Inv w b s) (o : DynamicArray.Op)
    (hv : (DynamicArray.spec b).valid (abs w b s) o) :
    (abs w b ((BitMemory.spec w).clientState s (ops b o)),
      (BitMemory.spec w).clientResult s (ops b o)) =
        DynamicArray.stepFn (abs w b s) o ∧
      Inv w b ((BitMemory.spec w).clientState s (ops b o)) := by
  cases o with
  | append x => exact step_append hw hb hbw hs hv
  | pop => exact step_pop hw hb hs
  | read i => exact step_read hs hv
  | write i x => exact step_write hw hbw hs hv.1 hv.2

/-! ## Refinement, framed implementation, and client theorems -/

/-- Verified refinement of `DynamicArray.spec b` over `BitMemory.spec w`. -/
def refinement (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    Refinement (DynamicArray.spec b) (BitMemory.spec w) :=
  Refinement.ofFn (methods w b) (Inv w b) (abs w b)
    (fun {_} o hs hv => ops_validHistory hbw hs o hv)
    (fun {_} o hs hv => by
      obtain ⟨hstep, hinv⟩ := ops_step hw hb hbw hs o hv
      exact ⟨hstep.symm, hinv⟩)

/-- Bit-size-framed implementation of `DynamicArray.spec b` over `BitMemory.spec w`, recording that
every represented array `xs` occupies `xs.length * b` bits. -/
def framed (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    BitMemory.Framed (DynamicArray.spec b) w where
  toRefinement := refinement hw hb hbw
  sizeBits xs := xs.length * b
  bitSize_eq hs := bitSize_eq_length_mul hs
  wellFormed hs := hs.wellFormed

/-- **Worst-case `O(1)` cost certificate (zero potential)**: every operation of
`DynamicArray.spec b` costs at most `3` bit-memory operations in the worst case. -/
theorem amortized (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    (refinement hw hb hbw).Amortized (BitMemory.charge w) (fun _ _ => 3) (fun _ => 0) :=
  Refinement.Amortized.ofFn fun {s} o _ _ => by
    simpa [refinement, methods] using ops_cost hw hbw s o

/-- **Main Stage 1 theorem for adaptive clients from empty**: running any admissible adaptive
client `p : (DynamicArray.spec b).Client α` from `BitMemory.empty` (`[]`) produces the exact
specified answer and final array state `xs'`, executes in at most `3 * m` bit-memory operations
(where `m` is the number of array operations issued by `p`), and ends with allocated bit size
`xs'.length * b` bits (`xs'.length * b + w` bits including the `w`-bit segment descriptor). -/
theorem client_run_from_empty {α : Type} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (p : (DynamicArray.spec b).Client α)
    (hv : (DynamicArray.spec b).ValidHistory [] ((DynamicArray.spec b).clientHistory [] p)) :
    let linked := link (methods w b) p
    let s' := (BitMemory.spec w).clientState BitMemory.empty linked
    (BitMemory.spec w).ValidHistory BitMemory.empty
        ((BitMemory.spec w).clientHistory BitMemory.empty linked) ∧
      (BitMemory.spec w).clientResult BitMemory.empty linked =
        (DynamicArray.spec b).clientResult [] p ∧
      abs w b s' = (DynamicArray.spec b).clientState [] p ∧
      s'.bitSize = ((DynamicArray.spec b).clientState [] p).length * b ∧
      (BitMemory.spec w).totalCost (BitMemory.charge w) BitMemory.empty
        ((BitMemory.spec w).clientHistory BitMemory.empty linked) ≤
          3 * ((DynamicArray.spec b).clientHistory [] p).length := by
  have ⟨hinv0, habs0⟩ := inv_empty w b
  have hv0 : (DynamicArray.spec b).ValidHistory (abs w b BitMemory.empty)
      ((DynamicArray.spec b).clientHistory (abs w b BitMemory.empty) p) := by
    rwa [habs0]
  obtain ⟨hv_low, hres, habs', hinv'⟩ := (refinement hw hb hbw).simulates_client p hinv0 hv0
  have hcost := (amortized hw hb hbw).client p hinv0 hv0
  dsimp only [refinement, Refinement.ofFn] at hv_low hres habs' hinv' hcost
  rw [habs0] at hres habs' hcost
  rw [StateTransitionSpec.totalCost_const, Nat.mul_comm] at hcost
  refine ⟨hv_low, hres, habs', ?_, by omega⟩
  rw [bitSize_eq_length_mul hinv', habs']

/-! ## Client subroutine composition: two resizable `b`-bit arrays in one machine -/

/-- Specification of two independent resizable `b`-bit arrays in one machine. -/
abbrev twoArraysSpec (b : ℕ) : StateTransitionSpec :=
  product (DynamicArray.spec b) (DynamicArray.spec b)

/-- Refinement implementing two resizable `b`-bit arrays over `BitMemory.pairSpec w`. -/
def twoArraysRefinement (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    Refinement (twoArraysSpec b) (BitMemory.pairSpec w) :=
  Refinement.ofFn
    (BitMemory.prodMethods w (methods w b) (methods w b))
    (fun s => Inv w b s.1 ∧ Inv w b s.2)
    (fun s => (abs w b s.1, abs w b s.2))
    (fun {s} o hs hv => by
      rcases s with ⟨s₁, s₂⟩
      cases o with
      | inl o =>
        dsimp only [twoArraysSpec, product, Sum.elim_inl, BitMemory.prodMethods, methods,
          StateTransitionSpec.clientHistory]
        rw [BitMemory.runClient_liftLeft]
        exact (BitMemory.validHistory_map_inl w s₁ s₂ _).mpr
          (ops_validHistory hbw hs.1 o hv)
      | inr o =>
        dsimp only [twoArraysSpec, product, Sum.elim_inr, BitMemory.prodMethods, methods,
          StateTransitionSpec.clientHistory]
        rw [BitMemory.runClient_liftRight]
        exact (BitMemory.validHistory_map_inr w s₁ s₂ _).mpr
          (ops_validHistory hbw hs.2 o hv))
    (fun {s} o hs hv => by
      rcases s with ⟨s₁, s₂⟩
      cases o with
      | inl o =>
        obtain ⟨hstep, hinv⟩ := ops_step hw hb hbw hs.1 o hv
        dsimp only [twoArraysSpec, product, Sum.elim_inl, BitMemory.prodMethods, methods,
          StateTransitionSpec.clientState, StateTransitionSpec.clientResult] at hstep ⊢
        rw [BitMemory.runClient_liftLeft]
        dsimp only
        have h1 : abs w b ((BitMemory.spec w).runClient s₁ (ops b o)).2.1 =
            (DynamicArray.stepFn (abs w b s₁) o).1 := congrArg Prod.fst hstep
        have h2 : ((BitMemory.spec w).runClient s₁ (ops b o)).1 =
            (DynamicArray.stepFn (abs w b s₁) o).2 := congrArg Prod.snd hstep
        exact ⟨Prod.ext (Prod.ext h1.symm rfl) h2.symm, hinv, hs.2⟩
      | inr o =>
        obtain ⟨hstep, hinv⟩ := ops_step hw hb hbw hs.2 o hv
        dsimp only [twoArraysSpec, product, Sum.elim_inr, BitMemory.prodMethods, methods,
          StateTransitionSpec.clientState, StateTransitionSpec.clientResult] at hstep ⊢
        rw [BitMemory.runClient_liftRight]
        dsimp only
        have h1 : abs w b ((BitMemory.spec w).runClient s₂ (ops b o)).2.1 =
            (DynamicArray.stepFn (abs w b s₂) o).1 := congrArg Prod.fst hstep
        have h2 : ((BitMemory.spec w).runClient s₂ (ops b o)).1 =
            (DynamicArray.stepFn (abs w b s₂) o).2 := congrArg Prod.snd hstep
        exact ⟨Prod.ext (Prod.ext rfl h1.symm) h2.symm, hs.1, hinv⟩)

/-- Every operation on either array in `twoArraysRefinement` costs at most `3` bit-memory units in
the worst case. -/
theorem twoArrays_amortized (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    (twoArraysRefinement hw hb hbw).Amortized (BitMemory.pairCharge w)
      (fun _ _ => 3) (fun _ => 0) :=
  Refinement.Amortized.ofFn fun {s} o _ _ => by
    rcases s with ⟨s₁, s₂⟩
    cases o with
    | inl o =>
      dsimp only [twoArraysSpec, product, Sum.elim_inl, twoArraysRefinement, Refinement.ofFn,
        BitMemory.prodMethods, methods, StateTransitionSpec.clientHistory]
      rw [BitMemory.runClient_liftLeft]
      dsimp only
      rw [BitMemory.totalCost_map_inl, Nat.add_zero]
      exact ops_cost hw hbw s₁ o
    | inr o =>
      dsimp only [twoArraysSpec, product, Sum.elim_inr, twoArraysRefinement, Refinement.ofFn,
        BitMemory.prodMethods, methods, StateTransitionSpec.clientHistory]
      rw [BitMemory.runClient_liftRight]
      dsimp only
      rw [BitMemory.totalCost_map_inr, Nat.add_zero]
      exact ops_cost hw hbw s₂ o

/-- **Client theorem for two composed resizable `b`-bit arrays**: any adaptive client `p` calling
two resizable `b`-bit arrays as subroutines from `(BitMemory.empty, BitMemory.empty)` (`([], [])`)
produces the specified result and final pair of arrays `(xs₁', xs₂')`, runs in at most `3 * m`
bit-memory operations for `m` array calls, and at completion uses
`(xs₁'.length + xs₂'.length) * b` bits of segment storage (`+ 2 * w` bits with segment
descriptors). -/
theorem twoArrays_client_run_from_empty {α : Type} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (p : (twoArraysSpec b).Client α)
    (hv : (twoArraysSpec b).ValidHistory ([], []) ((twoArraysSpec b).clientHistory ([], []) p)) :
    let R := twoArraysRefinement hw hb hbw
    let s₀ : BitMemory.State × BitMemory.State := (BitMemory.empty, BitMemory.empty)
    let linked := link R.methods p
    let s' := (BitMemory.pairSpec w).clientState s₀ linked
    let d' := (twoArraysSpec b).clientState ([], []) p
    (BitMemory.pairSpec w).ValidHistory s₀ ((BitMemory.pairSpec w).clientHistory s₀ linked) ∧
      (BitMemory.pairSpec w).clientResult s₀ linked =
        (twoArraysSpec b).clientResult ([], []) p ∧
      (abs w b s'.1, abs w b s'.2) = d' ∧
      pairTotalBits s' = (d'.1.length + d'.2.length) * b ∧
      (BitMemory.pairSpec w).totalCost (BitMemory.pairCharge w) s₀
        ((BitMemory.pairSpec w).clientHistory s₀ linked) ≤
          3 * ((twoArraysSpec b).clientHistory ([], []) p).length := by
  have ⟨hinv1, habs1⟩ := inv_empty w b
  have ⟨hinv2, habs2⟩ := inv_empty w b
  let R := twoArraysRefinement hw hb hbw
  let s₀ : BitMemory.State × BitMemory.State := (BitMemory.empty, BitMemory.empty)
  have hinv0 : R.inv s₀ := ⟨hinv1, hinv2⟩
  have habs0 : R.abs s₀ = ([], []) := Prod.ext habs1 habs2
  have hv0 : (twoArraysSpec b).ValidHistory (R.abs s₀)
      ((twoArraysSpec b).clientHistory (R.abs s₀) p) := by
    rwa [habs0]
  obtain ⟨hv_low, hres, habs', hinv'⟩ := R.simulates_client p hinv0 hv0
  have hcost := (twoArrays_amortized hw hb hbw).client p hinv0 hv0
  rw [habs0] at hres habs' hcost
  rw [StateTransitionSpec.totalCost_const, Nat.mul_comm] at hcost
  refine ⟨hv_low, hres, habs', ?_, by omega⟩
  change ((BitMemory.pairSpec w).clientState s₀ (link R.methods p)).1.bitSize +
    ((BitMemory.pairSpec w).clientState s₀ (link R.methods p)).2.bitSize =
    (((twoArraysSpec b).clientState ([], []) p).1.length +
      ((twoArraysSpec b).clientState ([], []) p).2.length) * b
  rw [bitSize_eq_length_mul hinv'.1, bitSize_eq_length_mul hinv'.2]
  have h1 : abs w b ((BitMemory.pairSpec w).clientState s₀ (link R.methods p)).1 =
      ((twoArraysSpec b).clientState ([], []) p).1 := congrArg Prod.fst habs'
  have h2 : abs w b ((BitMemory.pairSpec w).clientState s₀ (link R.methods p)).2 =
      ((twoArraysSpec b).clientState ([], []) p).2 := congrArg Prod.snd habs'
  rw [h1, h2, Nat.add_mul]

/-- A client subroutine on `twoArraysSpec b` that pops the last item from array 1 and, if present,
appends it to array 2. -/
def popPushTransfer (b : ℕ) : (twoArraysSpec b).Client (Option ℕ) := do
  let mx ← PFunctor.FreeM.lift (P := (twoArraysSpec b).signature) (.inl .pop)
  match mx with
  | none => pure none
  | some x => do
    PFunctor.FreeM.lift (P := (twoArraysSpec b).signature) (.inr (.append x))
    pure (some x)

/-- Abstract evaluation of `popPushTransfer b` when the first array `xs₁` is non-empty. -/
theorem runClient_popPushTransfer {xs₁ xs₂ : DynamicArray.State} (hne : xs₁ ≠ []) :
    (twoArraysSpec b).runClient (xs₁, xs₂) (popPushTransfer b) =
      (some (xs₁.getLast hne), (xs₁.dropLast, xs₂ ++ [xs₁.getLast hne]),
        [.inl .pop, .inr (.append (xs₁.getLast hne))]) := by
  unfold popPushTransfer
  simp only [StateTransitionSpec.runClient_lift_bind', DynamicArray.stepFn_pop,
    List.getLast?_eq_some_getLast hne]
  rfl

/-- **Released-memory reuse across two resizable `b`-bit arrays**: when array 1 is non-empty
(`xs₁ ≠ []`), executing `popPushTransfer b` over `(s₁, s₂)` pops the last `b`-bit item from array 1
(immediately shrinking `s₁.bitSize` by `b` bits) and appends it to array 2 (growing `s₂.bitSize` by
the released `b` bits), so that the combined bit usage `pairTotalBits` at every intermediate and
final state never exceeds `(xs₁.length + xs₂.length) * b` bits. -/
theorem popPushTransfer_reuses_released_bits (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    {s₁ s₂ : BitMemory.State} (hs₁ : Inv w b s₁) (hs₂ : Inv w b s₂)
    (hne : abs w b s₁ ≠ []) :
    let R := twoArraysRefinement hw hb hbw
    let s : BitMemory.State × BitMemory.State := (s₁, s₂)
    let s_after_pop : BitMemory.State × BitMemory.State :=
      ((BitMemory.spec w).clientState s₁ (pop b), s₂)
    let s_final : BitMemory.State × BitMemory.State :=
      (BitMemory.pairSpec w).clientState s (link R.methods (popPushTransfer b))
    pairTotalBits s = ((abs w b s₁).length + (abs w b s₂).length) * b ∧
      pairTotalBits s_after_pop = pairTotalBits s - b ∧
      pairTotalBits s_final = pairTotalBits s ∧
      abs w b s_final.1 = (abs w b s₁).dropLast ∧
      abs w b s_final.2 = abs w b s₂ ++ [(abs w b s₁).getLast hne] := by
  have hlen_pos : 0 < (abs w b s₁).length := List.length_pos_iff.mpr hne
  have ⟨hpop_step, hpop_inv⟩ := step_pop hw hb hs₁
  have hpop_abs : abs w b ((BitMemory.spec w).clientState s₁ (pop b)) = (abs w b s₁).dropLast :=
    congrArg Prod.fst hpop_step
  have hlast_fits : Fits b ((abs w b s₁).getLast hne) := by
    rw [List.getLast_eq_getElem]
    simp only [abs, List.getElem_ofFn]
    exact readField_fits w 0 s₁.mem _ b
  have htotal_init : pairTotalBits (s₁, s₂) = ((abs w b s₁).length + (abs w b s₂).length) * b := by
    simp only [pairTotalBits, bitSize_eq_length_mul hs₁, bitSize_eq_length_mul hs₂, Nat.add_mul]
  have htotal_mid : pairTotalBits ((BitMemory.spec w).clientState s₁ (pop b), s₂) =
      pairTotalBits (s₁, s₂) - b := by
    simp only [pairTotalBits, bitSize_eq_length_mul hpop_inv, bitSize_eq_length_mul hs₁,
      bitSize_eq_length_mul hs₂, hpop_abs, List.length_dropLast]
    cases h : (abs w b s₁).length with
    | zero => omega
    | succ k =>
      simp only [Nat.add_sub_cancel, Nat.succ_mul]
      omega
  let R := twoArraysRefinement hw hb hbw
  have hinv_init : R.inv (s₁, s₂) := ⟨hs₁, hs₂⟩
  have hv_abs : (twoArraysSpec b).ValidHistory (R.abs (s₁, s₂))
      ((twoArraysSpec b).clientHistory (R.abs (s₁, s₂)) (popPushTransfer b)) := by
    dsimp only [R, twoArraysRefinement, Refinement.ofFn, StateTransitionSpec.clientHistory]
    rw [runClient_popPushTransfer hne]
    exact ⟨trivial, hlast_fits, trivial⟩
  obtain ⟨_, _, habs_final, hinv_final⟩ := R.simulates_client (popPushTransfer b) hinv_init hv_abs
  have habs_eq : (twoArraysSpec b).clientState (R.abs (s₁, s₂)) (popPushTransfer b) =
      ((abs w b s₁).dropLast, abs w b s₂ ++ [(abs w b s₁).getLast hne]) := by
    dsimp only [R, twoArraysRefinement, Refinement.ofFn, StateTransitionSpec.clientState]
    rw [runClient_popPushTransfer hne]
  have hf1 : abs w b ((BitMemory.pairSpec w).clientState (s₁, s₂)
      (link R.methods (popPushTransfer b))).1 = (abs w b s₁).dropLast :=
    congrArg Prod.fst (habs_final.trans habs_eq)
  have hf2 : abs w b ((BitMemory.pairSpec w).clientState (s₁, s₂)
      (link R.methods (popPushTransfer b))).2 =
      abs w b s₂ ++ [(abs w b s₁).getLast hne] :=
    congrArg Prod.snd (habs_final.trans habs_eq)
  refine ⟨htotal_init, htotal_mid, ?_, hf1, hf2⟩
  change ((BitMemory.pairSpec w).clientState (s₁, s₂)
      (link R.methods (popPushTransfer b))).1.bitSize +
    ((BitMemory.pairSpec w).clientState (s₁, s₂)
      (link R.methods (popPushTransfer b))).2.bitSize =
    pairTotalBits (s₁, s₂)
  rw [bitSize_eq_length_mul hinv_final.1, bitSize_eq_length_mul hinv_final.2, hf1, hf2,
    htotal_init, List.length_dropLast, List.length_append, List.length_singleton]
  cases h : (abs w b s₁).length with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.add_mul]
    omega

end Cslib.DataStructure.DynamicArray.BitResizable
