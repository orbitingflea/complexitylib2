/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Resizable
public import Complexity.Foundations.Data.Nat.Bitwise.Subword

/-!
# Tightly packed resizable array of `b`-bit items in word-granular resizable memory

This module implements Stage 1 of the word-granular resizable memory development: a tightly packed
resizable array of `b`-bit items (`0 < b ≤ w`) supporting `append`, `pop`, `read i`, and
`write i x` from the empty array in **`O(1)` worst-case time** (at most `7` memory operations per
array operation, hence also `O(1)` amortized time with zero potential) and **tight space at every
step** in the current length `n_t`.

## Representations and additive space terms

We provide two closely related representations sharing the same sub-word bit-packing primitives
(`readSubwordAt` and `writeSubwordAt` from `Complexity.Foundations.Data.Nat.Bitwise.Subword`):

1. **Self-contained in-memory representation (`refinement`, `base = 1`)**:
   - Word `0` of `Memory.State` stores the current item count `n_t`, and words
     `1, …, packedWords w b n_t` store the `n_t` packed `b`-bit items (`packedWords w b n_t =
     ⌈n_t * b / w⌉`).
   - Allocated words at step `t`: `s_t.frontier = 1 + packedWords w b n_t = 1 + ⌈n_t * b / w⌉`.
   - Allocated bits at step `t` (`space_tight_every_step`):
     $$n_t \cdot b + w \le \mathrm{spaceBits}(w, s_t) \le n_t \cdot b + 2w - 1\text{ bits.}$$
     The additive space term is at most $2w - 1$ bits ($1$ header word of $w$ bits storing $n_t$
     plus at most $w - 1$ bits of word-alignment rounding in the last data word).

2. **Zero-header packed representation with length `n_t` in a register/spillover (`PackedInv`,
   `base = 0`)**:
   - Words `0, …, packedWords w b n_t - 1` store the `n_t` packed `b`-bit items, while `n_t` is
     maintained in a machine register (an $O(w)$-bit spillover in `[LLYZ23a]` Definition 1).
   - Allocated words at step `t`: `s_t.frontier = packedWords w b n_t = ⌈n_t * b / w⌉`.
   - Allocated bits in virtual memory at step `t` (`packed_space_tight`):
     $$n_t \cdot b \le \mathrm{spaceBits}(w, s_t) \le n_t \cdot b + (w - 1)\text{ bits.}$$
     The additive space term forced by word-granular allocation alone is at most $w - 1$ bits (and
     $0$ bits whenever $w \mid n_t b$, in particular when $b = w$).

## Why `O(1)` time is worst-case (not merely amortized)

Unlike classical doubling/halving dynamic arrays (which allocate/copy $\Theta(n)$ words during a
resize and achieve $O(1)$ time only in the amortized sense), in the word-granular Virtual Memory
model (`Memory.Resizable.spec w`), growing or shrinking the active prefix by `1` word at the
frontier costs `1` memory operation (`grow 1` / `shrink 1`) and requires **no copying** of existing
words. Since `b ≤ w`, appending or popping one `b`-bit item changes `packedWords w b n_t =
⌈n_t * b / w⌉` by at most `1` word (`packedWords_succ_le`), and reading or writing a `b`-bit item
touches at most `2` consecutive words (`(i * b) / w` and `(i * b) / w + 1`). Consequently, every
`append`, `pop`, `read`, and `write` executes in at most `7` memory operations in the **worst
case**.

## Main definitions and results

* `Cslib.DataStructure.DynamicArray.ResizableWord.Op`, `step`, `valid`, `spec`: abstract
  specification of a resizable array of `b`-bit items from `empty := []`.
* `Cslib.DataStructure.DynamicArray.ResizableWord.readSubwordAt`, `writeSubwordAt`: effectful
  `Resizable.Prog` procedures reading and writing a `b`-bit item at index `i` above word offset
  `base`.
* `Cslib.DataStructure.DynamicArray.ResizableWord.Inv`, `abs`, `refinement`, `demonicRefinement`:
  `Refinement` of `spec w b` over `Memory.Resizable.spec w` and `Memory.Resizable.demonicSpec w`
  (where `.grow 1` initializes the new word with an arbitrary valid `w`-bit value).
* `Cslib.DataStructure.DynamicArray.ResizableWord.worstCase_cost_le_seven`, `amortized`,
  `demonicAmortized`: worst-case and amortized $O(1)$ time bounds ($\le 7$ memory units per
  operation).
* `Cslib.DataStructure.DynamicArray.ResizableWord.readArrayCode_exec`, `writeArrayCode_exec`,
  `appendArrayCode_exec`, `popArrayCode_exec`: concrete 16-register `WordRAM.Resizable.RCode`
  machine-instruction implementations and `RDemonicExec` instruction-count proofs ($\le 31$,
  $\le 40$, $\le 58$, and $\le 51$ instructions).
* `Cslib.DataStructure.DynamicArray.ResizableWord.space_tight_every_step`, `packed_space_tight`:
  tight every-step space bounds in the current length `n_t`.
* `Cslib.DataStructure.DynamicArray.ResizableWord.subroutineClient_correct_and_tight`,
  `twoArrays_reuse_released_memory`, `twoArrays_singleTape_reuse`: client composition theorems,
  including single-linear-tape memory reuse via `Memory.Resizable.ChunkedTape`.
-/

@[expose] public section

namespace Cslib.DataStructure.DynamicArray.ResizableWord

open Cslib.WordRAM Cslib.BitString Cslib.DataStructure Cslib.DataStructure.Memory

/-! ## Abstract specification of a resizable `b`-bit array -/

/-- Operations on a resizable array of `b`-bit items. -/
inductive Op where
  /-- Append `x` to the end of the array. -/
  | append (x : ℕ)
  /-- Pop and return the last item (`none` if the array is empty). -/
  | pop
  /-- Read the item at index `i`. -/
  | read (i : ℕ)
  /-- Overwrite the item at index `i` with `x`. -/
  | write (i x : ℕ)
  deriving DecidableEq, Repr

/-- Result type of each resizable-array operation. -/
abbrev Op.Result : Op → Type
  | .append _ => Unit
  | .pop => Option ℕ
  | .read _ => ℕ
  | .write _ _ => Unit

/-- The empty array state. -/
abbrev empty : List ℕ := []

/-- Pure transition function on `List ℕ`. -/
def step (xs : List ℕ) : (o : Op) → List ℕ × o.Result
  | .append x => (xs ++ [x], ())
  | .pop => (xs.dropLast, xs.getLast?)
  | .read i => (xs, xs.getD i 0)
  | .write i x => (xs.set i x, ())

/-- Admissibility at word width `w` and item bit-width `b`: appended and written items fit in `b`
bits, indices `i` are in bounds (`i < xs.length`), and appending keeps the new length
`xs.length + 1` and word count `1 + packedWords w b (xs.length + 1)` fitting in a `w`-bit word. -/
def valid (w b : ℕ) (xs : List ℕ) : Op → Prop
  | .append x =>
      Fits b x ∧ Fits w (xs.length + 1) ∧ Fits w (1 + packedWords w b (xs.length + 1))
  | .pop => True
  | .read i => i < xs.length
  | .write i x => i < xs.length ∧ Fits b x

/-- Deterministic state-transition specification of a resizable array of `b`-bit items at word
width `w`. -/
abbrev spec (w b : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := List ℕ) (Op := Op) (Result := Op.Result)
    step (valid w b)

@[simp]
theorem step_append (xs : List ℕ) (x : ℕ) :
    step xs (.append x) = (xs ++ [x], ()) := rfl

@[simp]
theorem step_pop (xs : List ℕ) :
    step xs .pop = (xs.dropLast, xs.getLast?) := rfl

@[simp]
theorem step_read (xs : List ℕ) (i : ℕ) :
    step xs (.read i) = (xs, xs.getD i 0) := rfl

@[simp]
theorem step_write (xs : List ℕ) (i x : ℕ) :
    step xs (.write i x) = (xs.set i x, ()) := rfl

theorem clientState_pure {α : Type} (w b : ℕ) (xs : List ℕ) (a : α) :
    (spec w b).clientState xs (.pure a) = xs := rfl

theorem clientResult_pure {α : Type} (w b : ℕ) (xs : List ℕ) (a : α) :
    (spec w b).clientResult xs (.pure a) = a := rfl

theorem clientHistory_pure {α : Type} (w b : ℕ) (xs : List ℕ) (a : α) :
    (spec w b).clientHistory xs (.pure a) = [] := rfl

theorem clientState_liftBind {α : Type} (w b : ℕ) (xs : List ℕ) (o : Op)
    (k : o.Result → (spec w b).Client α) :
    (spec w b).clientState xs (.liftBind o k) =
      (spec w b).clientState (step xs o).1 (k (step xs o).2) := rfl

theorem clientResult_liftBind {α : Type} (w b : ℕ) (xs : List ℕ) (o : Op)
    (k : o.Result → (spec w b).Client α) :
    (spec w b).clientResult xs (.liftBind o k) =
      (spec w b).clientResult (step xs o).1 (k (step xs o).2) := rfl

theorem clientHistory_liftBind {α : Type} (w b : ℕ) (xs : List ℕ) (o : Op)
    (k : o.Result → (spec w b).Client α) :
    (spec w b).clientHistory xs (.liftBind o k) =
      o :: (spec w b).clientHistory (step xs o).1 (k (step xs o).2) := rfl

/-! ## Shifted memory view and sub-word access procedures -/

/-- View memory `mem` starting at word offset `base`. -/
def shiftMem (base : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  fun a => mem (base + a)

@[simp]
theorem shiftMem_zero (mem : ℕ → ℕ) : shiftMem 0 mem = mem := by
  funext a
  simp [shiftMem]

theorem shiftMem_update (base : ℕ) (mem : ℕ → ℕ) (idx v : ℕ) :
    shiftMem base (Function.update mem (base + idx) v) =
      Function.update (shiftMem base mem) idx v := by
  funext a
  unfold shiftMem
  by_cases ha : a = idx
  · subst ha
    rw [Function.update_self, Function.update_self]
  · have hba : base + a ≠ base + idx := by omega
    rw [Function.update_of_ne hba, Function.update_of_ne ha]

theorem shiftMem_update_lt {base a : ℕ} (mem : ℕ → ℕ) (ha : a < base) (v : ℕ) :
    shiftMem base (Function.update mem a v) = shiftMem base mem := by
  funext k
  unfold shiftMem
  have hne : base + k ≠ a := by omega
  exact Function.update_of_ne hne v mem

/-- Effectful procedure in `(Resizable.spec w).Client` that reads the `b`-bit item at index `i` from
the packed array starting at word address `base` (at most `2` word reads). -/
def readSubwordAt (w base b i : ℕ) : (Resizable.spec w).Client ℕ :=
  let bitOff := i * b
  let wordIdx := bitOff / w
  let inWordOff := bitOff % w
  if inWordOff + b ≤ w then
    .liftBind (.read (base + wordIdx)) fun w0 =>
      .pure (extractSlice w0 inWordOff b)
  else
    let lowLen := w - inWordOff
    let highLen := b - lowLen
    .liftBind (.read (base + wordIdx)) fun w0 =>
      .liftBind (.read (base + (wordIdx + 1))) fun w1 =>
        .pure (combineSlices b lowLen
          (extractSlice w0 inWordOff lowLen)
          (extractSlice w1 0 highLen))

/-- Effectful procedure in `(Resizable.spec w).Client` that writes the `b`-bit item `val` at index
`i` into the packed array starting at word address `base` (at most `2` word reads and `2` word
writes). -/
def writeSubwordAt (w base b i val : ℕ) : (Resizable.spec w).Client Unit :=
  let bitOff := i * b
  let wordIdx := bitOff / w
  let inWordOff := bitOff % w
  if inWordOff + b ≤ w then
    .liftBind (.read (base + wordIdx)) fun w0 =>
      .liftBind (.write (base + wordIdx) (spliceWord w w0 inWordOff b val)) fun _ =>
        .pure ()
  else
    let lowLen := w - inWordOff
    let highLen := b - lowLen
    .liftBind (.read (base + wordIdx)) fun w0 =>
      .liftBind (.write (base + wordIdx) (spliceWord w w0 inWordOff lowLen val)) fun _ =>
        .liftBind (.read (base + (wordIdx + 1))) fun w1 =>
          .liftBind (.write (base + (wordIdx + 1))
              (spliceWord w w1 0 highLen (val / 2 ^ lowLen))) fun _ =>
            .pure ()

/-- `readSubwordAt` leaves the memory state unchanged and returns
`readSubword w (shiftMem base s.mem) b i`. -/
theorem runClient_readSubwordAt (w base b i : ℕ) (s : Memory.State) :
    (Resizable.spec w).clientState s (readSubwordAt w base b i) = s ∧
      (Resizable.spec w).clientResult s (readSubwordAt w base b i) =
        readSubword w (shiftMem base s.mem) b i := by
  dsimp only [readSubwordAt, readSubword, shiftMem]
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- `readSubwordAt` is admissible and costs at most `2` memory units when `i < n` and
`base + packedWords w b n ≤ s.frontier`. -/
theorem valid_and_cost_readSubwordAt {w base b n i : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hi : i < n)
    (hfront : base + packedWords w b n ≤ s.frontier) :
    (Resizable.spec w).ValidHistory s
        ((Resizable.spec w).clientHistory s (readSubwordAt w base b i)) ∧
      (Resizable.spec w).totalCost Resizable.charge s
        ((Resizable.spec w).clientHistory s (readSubwordAt w base b i)) ≤ 2 := by
  have hw0 : (i * b) / w < packedWords w b n := wordIdx_lt_packedWords_of_pos hw hb_pos hi
  have hlt0 : base + (i * b) / w < s.frontier :=
    lt_of_lt_of_le (Nat.add_lt_add_left hw0 base) hfront
  dsimp only [readSubwordAt]
  split_ifs with hfit
  · dsimp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      StateTransitionSpec.stepFn, Resizable.step,
      StateTransitionSpec.ValidHistory, StateTransitionSpec.totalCost, Resizable.charge]
    exact ⟨⟨hlt0, trivial⟩, by omega⟩
  · have hw1 : (i * b) / w + 1 < packedWords w b n := wordIdx_succ_lt_packedWords hw hi hfit
    have hlt1 : base + ((i * b) / w + 1) < s.frontier :=
      lt_of_lt_of_le (Nat.add_lt_add_left hw1 base) hfront
    dsimp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      StateTransitionSpec.stepFn, Resizable.step,
      StateTransitionSpec.ValidHistory, StateTransitionSpec.totalCost, Resizable.charge]
    exact ⟨⟨hlt0, ⟨hlt1, trivial⟩⟩, by omega⟩

/-- `writeSubwordAt` preserves `s.frontier`, preserves all cells `< base`, and updates
`shiftMem base s.mem` to `writeSubword w (shiftMem base s.mem) b i val`. -/
theorem clientState_writeSubwordAt (w base b i val : ℕ) (s : Memory.State) :
    let s' := (Resizable.spec w).clientState s (writeSubwordAt w base b i val)
    s'.frontier = s.frontier ∧
      (∀ a < base, s'.mem a = s.mem a) ∧
      shiftMem base s'.mem = writeSubword w (shiftMem base s.mem) b i val := by
  dsimp only [writeSubwordAt, writeSubword]
  split_ifs with hfit
  · dsimp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient,
      StateTransitionSpec.stepFn, Resizable.step]
    refine ⟨rfl, ?_, shiftMem_update base s.mem ((i * b) / w) _⟩
    intro a ha
    have hne : a ≠ base + (i * b) / w :=
      ne_of_lt (lt_of_lt_of_le ha (Nat.le_add_right _ _))
    exact Function.update_of_ne hne _ s.mem
  · dsimp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient,
      StateTransitionSpec.stepFn, Resizable.step]
    refine ⟨rfl, ?_, ?_⟩
    · intro a ha
      have hne0 : a ≠ base + (i * b) / w :=
        ne_of_lt (lt_of_lt_of_le ha (Nat.le_add_right _ _))
      have hne1 : a ≠ base + ((i * b) / w + 1) :=
        ne_of_lt (lt_of_lt_of_le ha (Nat.le_add_right _ _))
      rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
    · rw [shiftMem_update, shiftMem_update]
      have hne_idx : base + (i * b / w + 1) ≠ base + i * b / w := by omega
      have hne_idx' : i * b / w + 1 ≠ i * b / w := by omega
      rw [Function.update_of_ne hne_idx, Function.update_of_ne hne_idx']
      rfl

/-- `writeSubwordAt` is admissible and costs at most `4` memory units when `i < n` and
`base + packedWords w b n ≤ s.frontier`. -/
theorem valid_and_cost_writeSubwordAt {w base b n i val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hi : i < n)
    (hfront : base + packedWords w b n ≤ s.frontier) :
    (Resizable.spec w).ValidHistory s
        ((Resizable.spec w).clientHistory s (writeSubwordAt w base b i val)) ∧
      (Resizable.spec w).totalCost Resizable.charge s
        ((Resizable.spec w).clientHistory s (writeSubwordAt w base b i val)) ≤ 4 := by
  have hw0 : (i * b) / w < packedWords w b n := wordIdx_lt_packedWords_of_pos hw hb_pos hi
  have hlt0 : base + (i * b) / w < s.frontier :=
    lt_of_lt_of_le (Nat.add_lt_add_left hw0 base) hfront
  dsimp only [writeSubwordAt]
  split_ifs with hfit
  · dsimp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      StateTransitionSpec.stepFn, Resizable.step,
      StateTransitionSpec.ValidHistory, StateTransitionSpec.totalCost, Resizable.charge]
    exact ⟨⟨hlt0, ⟨⟨hlt0, spliceWord_fits _ _ _ _ _⟩, trivial⟩⟩, by omega⟩
  · have hw1 : (i * b) / w + 1 < packedWords w b n := wordIdx_succ_lt_packedWords hw hi hfit
    have hlt1 : base + ((i * b) / w + 1) < s.frontier :=
      lt_of_lt_of_le (Nat.add_lt_add_left hw1 base) hfront
    dsimp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      StateTransitionSpec.stepFn, Resizable.step,
      StateTransitionSpec.ValidHistory, StateTransitionSpec.totalCost, Resizable.charge]
    exact ⟨⟨hlt0, ⟨⟨hlt0, spliceWord_fits _ _ _ _ _⟩,
      ⟨hlt1, ⟨⟨hlt1, spliceWord_fits _ _ _ _ _⟩, trivial⟩⟩⟩⟩, by omega⟩

/-! ## Canonical state preservation across `(Resizable.spec w).Client` runs -/

/-- Any admissible `(Resizable.spec w).Client` execution preserves `Resizable.Canonical w`. -/
theorem canonical_clientState {α : Type} {w : ℕ} {s : Memory.State}
    {p : (Resizable.spec w).Client α}
    (hs : Resizable.Canonical w s)
    (hv : (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p)) :
    Resizable.Canonical w ((Resizable.spec w).clientState s p) := by
  induction p generalizing s with
  | pure _ => exact hs
  | liftBind o k ih =>
    exact ih _ (Resizable.canonical_step hs hv.1) hv.2

/-! ## Self-contained in-memory representation (`base = 1`, word `0` stores `n_t`) -/

/-- Initial state of the self-contained resizable array after allocating word `0` (`frontier = 1`,
`mem 0 = 0`, representing the empty array `[]`). -/
def initState : Memory.State :=
  (Resizable.step Resizable.emptyState (.grow 1)).1

/-- Initialization program allocating the 1-word length header from `emptyState`. -/
def allocInit : Resizable.Prog Unit :=
  .liftBind (.grow 1) fun _ => .pure ()

/-- Representation invariant of the self-contained resizable array at word width `w` and item
bit-width `b`: the memory state `s` is canonical (`WellFormed w s ∧ ZeroAbove s`) and its frontier
is `1 + packedWords w b (s.mem 0)`. -/
structure Inv (w b : ℕ) (s : Memory.State) : Prop where
  /-- All words and the frontier fit in `w` bits, and all addresses `≥ s.frontier` hold `0`. -/
  canonical : Resizable.Canonical w s
  /-- The allocated word count is `1` (for the length header at word `0`) plus
  `packedWords w b (s.mem 0)` data words. -/
  frontier_eq : s.frontier = 1 + packedWords w b (s.mem 0)

/-- Abstraction function mapping a concrete memory state `s` to the represented list of `s.mem 0`
packed `b`-bit items stored starting at word `1`. -/
def abs (w b : ℕ) (s : Memory.State) : List ℕ :=
  List.ofFn (fun i : Fin (s.mem 0) => readSubword w (shiftMem 1 s.mem) b i.val)

@[simp]
theorem length_abs (w b : ℕ) (s : Memory.State) :
    (abs w b s).length = s.mem 0 := by
  simp [abs]

@[simp]
theorem getElem_abs (w b : ℕ) (s : Memory.State) (i : ℕ) (hi : i < (abs w b s).length) :
    (abs w b s)[i] = readSubword w (shiftMem 1 s.mem) b i := by
  simp [abs]

theorem getD_abs (w b : ℕ) (s : Memory.State) {i : ℕ} (hi : i < s.mem 0) :
    (abs w b s).getD i 0 = readSubword w (shiftMem 1 s.mem) b i := by
  have hi' : i < (abs w b s).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
    getElem_abs w b s i hi']

theorem inv_initState {w b : ℕ} (hw : 0 < w) :
    Inv w b initState ∧ abs w b initState = [] := by
  have h1 : Fits w 1 := by
    change 1 < 2 ^ w
    exact Nat.one_lt_pow (by omega) (by decide)
  have hcan : Resizable.Canonical w initState :=
    Resizable.canonical_step (Resizable.canonical_emptyState w) (by simpa using h1)
  have hmem0 : initState.mem 0 = 0 := by
    dsimp only [initState, Resizable.step, Resizable.emptyState]
    exact clear_of_owns ⟨le_rfl, Nat.zero_lt_one⟩
  have hfr0 : initState.frontier = 1 := rfl
  refine ⟨⟨hcan, ?_⟩, ?_⟩
  · rw [hfr0, hmem0, packedWords_zero]
  · simp [abs, hmem0]

/-! ## Method implementations (`readProg`, `writeProg`, `appendProg`, `popProg`) -/

/-- Read the `b`-bit item at index `i` (`≤ 2` memory operations). -/
abbrev readProg (w b i : ℕ) : (Resizable.spec w).Client ℕ :=
  readSubwordAt w 1 b i

/-- Write the `b`-bit item `x` at index `i` (`≤ 4` memory operations). -/
abbrev writeProg (w b i x : ℕ) : (Resizable.spec w).Client Unit :=
  writeSubwordAt w 1 b i x

/-- Append the `b`-bit item `x` to the end of the array (`≤ 7` memory operations). -/
def appendProg (w b x : ℕ) : (Resizable.spec w).Client Unit :=
  .liftBind (.read 0) fun n =>
    .liftBind (.write 0 (n + 1)) fun _ =>
      if packedWords w b n < packedWords w b (n + 1) then
        .liftBind (.grow 1) fun _ =>
          writeSubwordAt w 1 b n x
      else
        writeSubwordAt w 1 b n x

/-- Pop and return the last `b`-bit item (`none` if empty; `≤ 5` memory operations). -/
def popProg (w b : ℕ) : (Resizable.spec w).Client (Option ℕ) :=
  .liftBind (.read 0) fun n =>
    if n = 0 then
      .pure none
    else
      let m := n - 1
      readSubwordAt w 1 b m >>= fun v =>
        .liftBind (.write 0 m) fun _ =>
          if packedWords w b m < packedWords w b n then
            .liftBind (.shrink 1) fun _ => .pure (some v)
          else
            .pure (some v)

/-- Method table for `spec w b` over `Resizable.spec w`. -/
def methods (w b : ℕ) : Methods (spec w b) (Resizable.spec w)
  | .append x => appendProg w b x
  | .pop => popProg w b
  | .read i => readProg w b i
  | .write i x => writeProg w b i x

/-! ## Correctness and worst-case cost of each method -/

theorem readProg_correct {w b i : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hinv : Inv w b s) (hv : valid w b (abs w b s) (.read i)) :
    let p := readProg w b i
    (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p) ∧
      (Resizable.spec w).totalCost Resizable.charge s ((Resizable.spec w).clientHistory s p) ≤ 2 ∧
      step (abs w b s) (.read i) =
        (abs w b ((Resizable.spec w).clientState s p), (Resizable.spec w).clientResult s p) ∧
      Inv w b ((Resizable.spec w).clientState s p) := by
  have hi : i < s.mem 0 := by simpa [valid] using hv
  have hfront : 1 + packedWords w b (s.mem 0) ≤ s.frontier := le_of_eq hinv.frontier_eq.symm
  obtain ⟨hvh, hcost⟩ := valid_and_cost_readSubwordAt hw hb_pos hi hfront
  obtain ⟨hst, hres⟩ := runClient_readSubwordAt w 1 b i s
  refine ⟨hvh, hcost, ?_, hst.symm ▸ hinv⟩
  change step (abs w b s) (.read i) =
    (abs w b ((Resizable.spec w).clientState s (readSubwordAt w 1 b i)),
      (Resizable.spec w).clientResult s (readSubwordAt w 1 b i))
  rw [hst, hres, step_read, getD_abs w b s hi]

theorem writeProg_correct {w b i x : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b s) (hv : valid w b (abs w b s) (.write i x)) :
    let p := writeProg w b i x
    (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p) ∧
      (Resizable.spec w).totalCost Resizable.charge s ((Resizable.spec w).clientHistory s p) ≤ 4 ∧
      step (abs w b s) (.write i x) =
        (abs w b ((Resizable.spec w).clientState s p), (Resizable.spec w).clientResult s p) ∧
      Inv w b ((Resizable.spec w).clientState s p) := by
  have hi : i < s.mem 0 := by simpa [valid] using hv.1
  have hx : Fits b x := hv.2
  have hfront : 1 + packedWords w b (s.mem 0) ≤ s.frontier := le_of_eq hinv.frontier_eq.symm
  obtain ⟨hvh, hcost⟩ := valid_and_cost_writeSubwordAt (val := x) hw hb_pos hi hfront
  obtain ⟨hfr', hmem0, hshift⟩ := clientState_writeSubwordAt w 1 b i x s
  have hmem0_eq : ((Resizable.spec w).clientState s (writeSubwordAt w 1 b i x)).mem 0 = s.mem 0 :=
    hmem0 0 Nat.zero_lt_one
  have hinv' : Inv w b ((Resizable.spec w).clientState s (writeSubwordAt w 1 b i x)) :=
    ⟨canonical_clientState hinv.canonical hvh, by rw [hfr', hmem0_eq, hinv.frontier_eq]⟩
  refine ⟨hvh, hcost, ?_, hinv'⟩
  apply Prod.ext
  · change (abs w b s).set i x =
      abs w b ((Resizable.spec w).clientState s (writeSubwordAt w 1 b i x))
    apply List.ext_getElem
    · simp [hmem0_eq]
    · intro j hj1 hj2
      rw [List.getElem_set, getElem_abs, getElem_abs, hshift]
      by_cases hji : j = i
      · subst hji
        simp [readSubword_writeSubword_self _ hw hb hx]
      · rw [ite_eq_right (Ne.symm hji), readSubword_writeSubword_of_ne _ hw hb hji]
  · rfl

theorem appendProg_correct {w b x : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b s) (hv : valid w b (abs w b s) (.append x)) :
    let p := appendProg w b x
    (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p) ∧
      (Resizable.spec w).totalCost Resizable.charge s ((Resizable.spec w).clientHistory s p) ≤ 7 ∧
      step (abs w b s) (.append x) =
        (abs w b ((Resizable.spec w).clientState s p), (Resizable.spec w).clientResult s p) ∧
      Inv w b ((Resizable.spec w).clientState s p) := by
  have hx : Fits b x := hv.1
  have hn1_fits : Fits w (s.mem 0 + 1) := by simpa using hv.2.1
  have hfw_fits : Fits w (1 + packedWords w b (s.mem 0 + 1)) := by simpa using hv.2.2
  have hpos_fr : 0 < s.frontier := by
    have := hinv.frontier_eq
    omega
  have hmono : packedWords w b (s.mem 0) ≤ packedWords w b (s.mem 0 + 1) :=
    packedWords_mono (Nat.le_succ _)
  have hsucc : packedWords w b (s.mem 0 + 1) ≤ packedWords w b (s.mem 0) + 1 :=
    packedWords_succ_le hb
  let s₁ : Memory.State := (Resizable.step s (.write 0 (s.mem 0 + 1))).1
  have hcan₁ : Resizable.Canonical w s₁ :=
    Resizable.canonical_step hinv.canonical ⟨hpos_fr, hn1_fits⟩
  have hshift₁ : shiftMem 1 s₁.mem = shiftMem 1 s.mem :=
    shiftMem_update_lt s.mem Nat.zero_lt_one (s.mem 0 + 1)
  have hmem0₁ : s₁.mem 0 = s.mem 0 + 1 := by
    dsimp only [s₁, Resizable.step]
    exact Function.update_self 0 (s.mem 0 + 1) s.mem
  by_cases hgrow : packedWords w b (s.mem 0) < packedWords w b (s.mem 0 + 1)
  · have hpw_eq : packedWords w b (s.mem 0 + 1) = packedWords w b (s.mem 0) + 1 := by omega
    let s₂ : Memory.State := (Resizable.step s₁ (.grow 1)).1
    have hfr₂ : s₂.frontier = 1 + packedWords w b (s.mem 0 + 1) := by
      dsimp only [s₂, s₁, Resizable.step]
      rw [hinv.frontier_eq, hpw_eq]
      omega
    have hgrow_valid : Resizable.valid w s₁ (.grow 1) := by
      rw [Resizable.valid_grow]
      have : s₁.frontier + 1 = 1 + packedWords w b (s.mem 0 + 1) := by
        dsimp only [s₁, Resizable.step]
        rw [hinv.frontier_eq, hpw_eq]
        omega
      rw [this]
      exact hfw_fits
    have hmem₂ : s₂.mem = s₁.mem :=
      Resizable.clear_frontier_eq_of_zeroAbove hcan₁.2 1
    obtain ⟨hvh_w, hcost_w⟩ :=
      valid_and_cost_writeSubwordAt (s := s₂) (base := 1) (n := s.mem 0 + 1) (i := s.mem 0)
        (val := x) hw hb_pos (Nat.lt_succ_self _) (le_of_eq hfr₂.symm)
    obtain ⟨hfr_w, hmem0_w, hshift_w⟩ := clientState_writeSubwordAt w 1 b (s.mem 0) x s₂
    have hhist_eq :
        (Resizable.spec w).clientHistory s (appendProg w b x) =
          .read 0 :: .write 0 (s.mem 0 + 1) :: .grow 1 ::
            (Resizable.spec w).clientHistory s₂ (writeSubwordAt w 1 b (s.mem 0) x) := by
      dsimp only [appendProg, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_left hgrow]
      rfl
    have hst_eq :
        (Resizable.spec w).clientState s (appendProg w b x) =
          (Resizable.spec w).clientState s₂ (writeSubwordAt w 1 b (s.mem 0) x) := by
      dsimp only [appendProg, StateTransitionSpec.clientState, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_left hgrow]
      rfl
    have hvh_all :
        (Resizable.spec w).ValidHistory s
          ((Resizable.spec w).clientHistory s (appendProg w b x)) := by
      rw [hhist_eq]
      exact ⟨hpos_fr, ⟨⟨hpos_fr, hn1_fits⟩, ⟨hgrow_valid, hvh_w⟩⟩⟩
    have hcost_all :
        (Resizable.spec w).totalCost Resizable.charge s
          ((Resizable.spec w).clientHistory s (appendProg w b x)) ≤ 7 := by
      rw [hhist_eq]
      change 1 + (1 + (1 + (Resizable.spec w).totalCost Resizable.charge s₂
        ((Resizable.spec w).clientHistory s₂ (writeSubwordAt w 1 b (s.mem 0) x)))) ≤ 7
      omega
    have hmem0_fin :
        ((Resizable.spec w).clientState s₂ (writeSubwordAt w 1 b (s.mem 0) x)).mem 0 =
          s.mem 0 + 1 := by
      rw [hmem0_w 0 Nat.zero_lt_one, hmem₂, hmem0₁]
    have hinv_fin : Inv w b ((Resizable.spec w).clientState s (appendProg w b x)) := by
      refine ⟨canonical_clientState hinv.canonical hvh_all, ?_⟩
      rw [hst_eq, hfr_w, hfr₂, hmem0_fin]
    refine ⟨hvh_all, hcost_all, ?_, hinv_fin⟩
    refine Prod.ext ?_ rfl
    change abs w b s ++ [x] = abs w b ((Resizable.spec w).clientState s (appendProg w b x))
    rw [hst_eq]
    apply List.ext_getElem
    · simp [hmem0_fin]
    · intro j hj1 hj2
      rw [getElem_abs, hshift_w, hmem₂, hshift₁]
      by_cases hjn : j < s.mem 0
      · have hj_abs : j < (abs w b s).length := by simpa using hjn
        rw [List.getElem_append_left hj_abs, getElem_abs,
          readSubword_writeSubword_of_ne _ hw hb (by omega)]
      · have hjeq : j = s.mem 0 := by
          simp only [List.length_append, length_abs, List.length_singleton] at hj1
          omega
        subst hjeq
        have hlen : (abs w b s).length ≤ s.mem 0 := by simp
        rw [List.getElem_append_right hlen]
        simp [readSubword_writeSubword_self _ hw hb hx]
  · have hpw_eq : packedWords w b (s.mem 0 + 1) = packedWords w b (s.mem 0) := by omega
    have hfr₁ : s₁.frontier = 1 + packedWords w b (s.mem 0 + 1) := by
      dsimp only [s₁, Resizable.step]
      rw [hinv.frontier_eq, hpw_eq]
    obtain ⟨hvh_w, hcost_w⟩ :=
      valid_and_cost_writeSubwordAt (s := s₁) (base := 1) (n := s.mem 0 + 1) (i := s.mem 0)
        (val := x) hw hb_pos (Nat.lt_succ_self _) (le_of_eq hfr₁.symm)
    obtain ⟨hfr_w, hmem0_w, hshift_w⟩ := clientState_writeSubwordAt w 1 b (s.mem 0) x s₁
    have hhist_eq :
        (Resizable.spec w).clientHistory s (appendProg w b x) =
          .read 0 :: .write 0 (s.mem 0 + 1) ::
            (Resizable.spec w).clientHistory s₁ (writeSubwordAt w 1 b (s.mem 0) x) := by
      dsimp only [appendProg, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_right hgrow]
      rfl
    have hst_eq :
        (Resizable.spec w).clientState s (appendProg w b x) =
          (Resizable.spec w).clientState s₁ (writeSubwordAt w 1 b (s.mem 0) x) := by
      dsimp only [appendProg, StateTransitionSpec.clientState, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_right hgrow]
      rfl
    have hvh_all :
        (Resizable.spec w).ValidHistory s
          ((Resizable.spec w).clientHistory s (appendProg w b x)) := by
      rw [hhist_eq]
      exact ⟨hpos_fr, ⟨⟨hpos_fr, hn1_fits⟩, hvh_w⟩⟩
    have hcost_all :
        (Resizable.spec w).totalCost Resizable.charge s
          ((Resizable.spec w).clientHistory s (appendProg w b x)) ≤ 7 := by
      rw [hhist_eq]
      change 1 + (1 + (Resizable.spec w).totalCost Resizable.charge s₁
        ((Resizable.spec w).clientHistory s₁ (writeSubwordAt w 1 b (s.mem 0) x))) ≤ 7
      omega
    have hmem0_fin :
        ((Resizable.spec w).clientState s₁ (writeSubwordAt w 1 b (s.mem 0) x)).mem 0 =
          s.mem 0 + 1 := by
      rw [hmem0_w 0 Nat.zero_lt_one, hmem0₁]
    have hinv_fin : Inv w b ((Resizable.spec w).clientState s (appendProg w b x)) := by
      refine ⟨canonical_clientState hinv.canonical hvh_all, ?_⟩
      rw [hst_eq, hfr_w, hfr₁, hmem0_fin]
    refine ⟨hvh_all, hcost_all, ?_, hinv_fin⟩
    refine Prod.ext ?_ rfl
    change abs w b s ++ [x] = abs w b ((Resizable.spec w).clientState s (appendProg w b x))
    rw [hst_eq]
    apply List.ext_getElem
    · simp [hmem0_fin]
    · intro j hj1 hj2
      rw [getElem_abs, hshift_w, hshift₁]
      by_cases hjn : j < s.mem 0
      · have hj_abs : j < (abs w b s).length := by simpa using hjn
        rw [List.getElem_append_left hj_abs, getElem_abs,
          readSubword_writeSubword_of_ne _ hw hb (by omega)]
      · have hjeq : j = s.mem 0 := by
          simp only [List.length_append, length_abs, List.length_singleton] at hj1
          omega
        subst hjeq
        have hlen : (abs w b s).length ≤ s.mem 0 := by simp
        rw [List.getElem_append_right hlen]
        simp [readSubword_writeSubword_self _ hw hb hx]

theorem popProg_correct {w b : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b s) :
    let p := popProg w b
    (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p) ∧
      (Resizable.spec w).totalCost Resizable.charge s ((Resizable.spec w).clientHistory s p) ≤ 5 ∧
      step (abs w b s) .pop =
        (abs w b ((Resizable.spec w).clientState s p), (Resizable.spec w).clientResult s p) ∧
      Inv w b ((Resizable.spec w).clientState s p) := by
  have hpos_fr : 0 < s.frontier := by
    have := hinv.frontier_eq
    omega
  by_cases hn0 : s.mem 0 = 0
  · have habs_nil : abs w b s = [] := List.eq_nil_of_length_eq_zero (by simp [hn0])
    have hhist : (Resizable.spec w).clientHistory s (popProg w b) = [.read 0] := by
      dsimp only [popProg, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_left hn0]
      rfl
    have hst : (Resizable.spec w).clientState s (popProg w b) = s := by
      dsimp only [popProg, StateTransitionSpec.clientState, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_left hn0]
      rfl
    have hres : (Resizable.spec w).clientResult s (popProg w b) = none := by
      dsimp only [popProg, StateTransitionSpec.clientResult, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_left hn0]
      rfl
    have hvh : (Resizable.spec w).ValidHistory s
        ((Resizable.spec w).clientHistory s (popProg w b)) := by
      rw [hhist]
      exact ⟨hpos_fr, trivial⟩
    have hcost : (Resizable.spec w).totalCost Resizable.charge s
        ((Resizable.spec w).clientHistory s (popProg w b)) ≤ 5 := by
      rw [hhist]
      change 1 + 0 ≤ 5
      omega
    refine ⟨hvh, hcost, ?_, hst.symm ▸ hinv⟩
    rw [hst, hres, habs_nil]
    rfl
  · set n := s.mem 0
    set m := n - 1
    have hnm : m + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)
    have hm_lt : m < n := by omega
    have hm_fits : Fits w m := (hinv.canonical.1.mem_fits 0).of_le (by omega)
    have hfront : 1 + packedWords w b n ≤ s.frontier := le_of_eq hinv.frontier_eq.symm
    obtain ⟨hvh_r, hcost_r⟩ := valid_and_cost_readSubwordAt hw hb_pos hm_lt hfront
    obtain ⟨hst_r, hres_r⟩ := runClient_readSubwordAt w 1 b m s
    set v := readSubword w (shiftMem 1 s.mem) b m
    let cont : ℕ → (Resizable.spec w).Client (Option ℕ) := fun val =>
      .liftBind (.write 0 m) fun _ =>
        if packedWords w b m < packedWords w b n then
          .liftBind (.shrink 1) fun _ => .pure (some val)
        else
          .pure (some val)
    have hhist_pop :
        (Resizable.spec w).clientHistory s (popProg w b) =
          .read 0 :: ((Resizable.spec w).clientHistory s (readSubwordAt w 1 b m) ++
            (Resizable.spec w).clientHistory s (cont v)) := by
      dsimp only [popProg, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_right hn0]
      change .read 0 :: (Resizable.spec w).clientHistory s (readSubwordAt w 1 b m >>= cont) = _
      rw [(Resizable.spec w).clientHistory_bind, hst_r, hres_r]
    have hst_pop :
        (Resizable.spec w).clientState s (popProg w b) =
          (Resizable.spec w).clientState s (cont v) := by
      dsimp only [popProg, StateTransitionSpec.clientState, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_right hn0]
      change (Resizable.spec w).clientState s (readSubwordAt w 1 b m >>= cont) = _
      rw [(Resizable.spec w).clientState_bind, hst_r, hres_r]
    have hres_pop :
        (Resizable.spec w).clientResult s (popProg w b) =
          (Resizable.spec w).clientResult s (cont v) := by
      dsimp only [popProg, StateTransitionSpec.clientResult, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_right hn0]
      change (Resizable.spec w).clientResult s (readSubwordAt w 1 b m >>= cont) = _
      rw [(Resizable.spec w).clientResult_bind, hst_r, hres_r]
    have hrun_r :
        ((Resizable.spec w).run s ((Resizable.spec w).clientHistory s (readSubwordAt w 1 b m))).1 =
          s := by
      rw [(Resizable.spec w).run_runClient, hst_r]
    have hmono : packedWords w b m ≤ packedWords w b n := packedWords_mono (by omega)
    have hsucc : packedWords w b n ≤ packedWords w b m + 1 := by
      rw [← hnm]
      exact packedWords_succ_le hb
    let s₁ : Memory.State := (Resizable.step s (.write 0 m)).1
    have hshift₁ : shiftMem 1 s₁.mem = shiftMem 1 s.mem :=
      shiftMem_update_lt s.mem Nat.zero_lt_one m
    have hmem0₁ : s₁.mem 0 = m := by
      dsimp only [s₁, Resizable.step]
      exact Function.update_self 0 m s.mem
    have hgetLast : (abs w b s).getLast? = some v := by
      have hlen : (abs w b s).length = n := length_abs w b s
      have hm_abs : m < (abs w b s).length := by omega
      rw [List.getLast?_eq_getElem?, hlen, show n - 1 = m from rfl,
        List.getElem?_eq_getElem hm_abs, getElem_abs]
    by_cases hshrink : packedWords w b m < packedWords w b n
    · have hpw_eq : packedWords w b n = packedWords w b m + 1 := by omega
      let s₂ : Memory.State := (Resizable.step s₁ (.shrink 1)).1
      have hshrink_valid : Resizable.valid w s₁ (.shrink 1) := by
        rw [Resizable.valid_shrink]
        dsimp only [s₁, Resizable.step]
        omega
      have hhist_cont :
          (Resizable.spec w).clientHistory s (cont v) = [.write 0 m, .shrink 1] := by
        dsimp only [cont, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
          StateTransitionSpec.stepFn, Resizable.step]
        rw [ite_eq_left hshrink]
        rfl
      have hvh_cont :
          (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s (cont v)) := by
        rw [hhist_cont]
        exact ⟨⟨hpos_fr, hm_fits⟩, ⟨hshrink_valid, trivial⟩⟩
      have hcost_cont :
          (Resizable.spec w).totalCost Resizable.charge s
            ((Resizable.spec w).clientHistory s (cont v)) = 2 := by
        rw [hhist_cont]
        rfl
      have hvh_all :
          (Resizable.spec w).ValidHistory s
            ((Resizable.spec w).clientHistory s (popProg w b)) := by
        rw [hhist_pop, (Resizable.spec w).validHistory_cons]
        refine ⟨hpos_fr, ?_⟩
        change (Resizable.spec w).ValidHistory s _
        rw [(Resizable.spec w).validHistory_append, hrun_r]
        exact ⟨hvh_r, hvh_cont⟩
      have hcost_all :
          (Resizable.spec w).totalCost Resizable.charge s
            ((Resizable.spec w).clientHistory s (popProg w b)) ≤ 5 := by
        rw [hhist_pop, (Resizable.spec w).totalCost_cons]
        change 1 + (Resizable.spec w).totalCost Resizable.charge s _ ≤ 5
        rw [(Resizable.spec w).totalCost_append, hrun_r, hcost_cont]
        omega
      have hst_cont : (Resizable.spec w).clientState s (cont v) = s₂ := by
        dsimp only [cont, StateTransitionSpec.clientState, StateTransitionSpec.runClient,
          StateTransitionSpec.stepFn, Resizable.step]
        rw [ite_eq_left hshrink]
        rfl
      have hres_cont : (Resizable.spec w).clientResult s (cont v) = some v := by
        dsimp only [cont, StateTransitionSpec.clientResult, StateTransitionSpec.runClient,
          StateTransitionSpec.stepFn, Resizable.step]
        rw [ite_eq_left hshrink]
        rfl
      have hmem0₂ : s₂.mem 0 = m := by
        dsimp only [s₂, s₁, Resizable.step]
        rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
        exact Function.update_self 0 m s.mem
      have hfr_n : s.frontier = 1 + packedWords w b n := hinv.frontier_eq
      have hfr₂ : s₂.frontier = 1 + packedWords w b (s₂.mem 0) := by
        rw [hmem0₂]
        dsimp only [s₂, s₁, Resizable.step]
        rw [hfr_n, hpw_eq]
        omega
      have hinv_fin : Inv w b ((Resizable.spec w).clientState s (popProg w b)) := by
        refine ⟨canonical_clientState hinv.canonical hvh_all, ?_⟩
        rw [hst_pop, hst_cont]
        exact hfr₂
      refine ⟨hvh_all, hcost_all, ?_, hinv_fin⟩
      rw [hst_pop, hst_cont, hres_pop, hres_cont, step_pop, hgetLast]
      refine Prod.ext ?_ rfl
      change (abs w b s).dropLast = abs w b s₂
      apply List.ext_getElem
      · simp [hmem0₂, m, n]
      · intro j hj1 hj2
        rw [List.getElem_dropLast, getElem_abs, getElem_abs]
        have hj_m : j < m := by
          simp only [List.length_dropLast, length_abs] at hj1
          exact hj1
        symm
        apply readSubword_congr hw hb hj_m
        intro a ha
        unfold shiftMem
        dsimp only [s₂, Resizable.step]
        have hnot_own : ¬ (Block.mk (s₁.frontier - 1) 1).Owns (1 + a) := by
          dsimp only [s₁, Resizable.step]
          simp only [Block.Owns, hfr_n, hpw_eq]
          omega
        rw [clear_of_not_owns hnot_own]
        exact congrFun hshift₁ a
    · have hpw_eq : packedWords w b n = packedWords w b m := by omega
      have hhist_cont :
          (Resizable.spec w).clientHistory s (cont v) = [.write 0 m] := by
        dsimp only [cont, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
          StateTransitionSpec.stepFn, Resizable.step]
        rw [ite_eq_right hshrink]
        rfl
      have hvh_cont :
          (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s (cont v)) := by
        rw [hhist_cont]
        exact ⟨⟨hpos_fr, hm_fits⟩, trivial⟩
      have hcost_cont :
          (Resizable.spec w).totalCost Resizable.charge s
            ((Resizable.spec w).clientHistory s (cont v)) = 1 := by
        rw [hhist_cont]
        rfl
      have hvh_all :
          (Resizable.spec w).ValidHistory s
            ((Resizable.spec w).clientHistory s (popProg w b)) := by
        rw [hhist_pop, (Resizable.spec w).validHistory_cons]
        refine ⟨hpos_fr, ?_⟩
        change (Resizable.spec w).ValidHistory s _
        rw [(Resizable.spec w).validHistory_append, hrun_r]
        exact ⟨hvh_r, hvh_cont⟩
      have hcost_all :
          (Resizable.spec w).totalCost Resizable.charge s
            ((Resizable.spec w).clientHistory s (popProg w b)) ≤ 5 := by
        rw [hhist_pop, (Resizable.spec w).totalCost_cons]
        change 1 + (Resizable.spec w).totalCost Resizable.charge s _ ≤ 5
        rw [(Resizable.spec w).totalCost_append, hrun_r, hcost_cont]
        omega
      have hst_cont : (Resizable.spec w).clientState s (cont v) = s₁ := by
        dsimp only [cont, StateTransitionSpec.clientState, StateTransitionSpec.runClient,
          StateTransitionSpec.stepFn, Resizable.step]
        rw [ite_eq_right hshrink]
        rfl
      have hres_cont : (Resizable.spec w).clientResult s (cont v) = some v := by
        dsimp only [cont, StateTransitionSpec.clientResult, StateTransitionSpec.runClient,
          StateTransitionSpec.stepFn, Resizable.step]
        rw [ite_eq_right hshrink]
        rfl
      have hfr_n : s.frontier = 1 + packedWords w b n := hinv.frontier_eq
      have hfr₁ : s₁.frontier = 1 + packedWords w b (s₁.mem 0) := by
        rw [hmem0₁]
        dsimp only [s₁, Resizable.step]
        rw [hfr_n, hpw_eq]
      have hinv_fin : Inv w b ((Resizable.spec w).clientState s (popProg w b)) := by
        refine ⟨canonical_clientState hinv.canonical hvh_all, ?_⟩
        rw [hst_pop, hst_cont]
        exact hfr₁
      refine ⟨hvh_all, hcost_all, ?_, hinv_fin⟩
      rw [hst_pop, hst_cont, hres_pop, hres_cont, step_pop, hgetLast]
      refine Prod.ext ?_ rfl
      change (abs w b s).dropLast = abs w b s₁
      apply List.ext_getElem
      · simp [hmem0₁, m, n]
      · intro j hj1 hj2
        rw [List.getElem_dropLast, getElem_abs, getElem_abs, hshift₁]

/-! ## Main Stage 1 theorems: `refinement`, worst-case/amortized `O(1)` time, and tight space -/

/-- Every admissible resizable-array operation (`append`, `pop`, `read`, `write`) executes validly
on `Memory.Resizable.spec w`, costs at most `7` memory units in the worst case, realizes `step`,
and preserves `Inv w b`. -/
theorem methods_correct_and_cost {w b : ℕ} (hb_pos : 0 < b) (hb : b ≤ w)
    {s : Memory.State} (o : Op) (hinv : Inv w b s) (hv : valid w b (abs w b s) o) :
    let p := methods w b o
    (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p) ∧
      (Resizable.spec w).totalCost Resizable.charge s ((Resizable.spec w).clientHistory s p) ≤ 7 ∧
      step (abs w b s) o =
        (abs w b ((Resizable.spec w).clientState s p), (Resizable.spec w).clientResult s p) ∧
      Inv w b ((Resizable.spec w).clientState s p) := by
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  cases o with
  | append x =>
    exact appendProg_correct hw hb_pos hb hinv hv
  | pop =>
    dsimp only [methods]
    obtain ⟨h1, h2, h3, h4⟩ := popProg_correct hw hb_pos hb hinv
    exact ⟨h1, by omega, h3, h4⟩
  | read i =>
    dsimp only [methods]
    obtain ⟨h1, h2, h3, h4⟩ := readProg_correct hw hb_pos hinv hv
    exact ⟨h1, by omega, h3, h4⟩
  | write i x =>
    dsimp only [methods]
    obtain ⟨h1, h2, h3, h4⟩ := writeProg_correct hw hb_pos hb hinv hv
    exact ⟨h1, by omega, h3, h4⟩

/-- **Refinement of the resizable `b`-bit array over `Memory.Resizable.spec w`.** -/
def refinement (w b : ℕ) (hb_pos : 0 < b) (hb : b ≤ w) :
    Refinement (spec w b) (Resizable.spec w) :=
  Refinement.ofFn (methods w b) (Inv w b) (abs w b)
    (fun o hi hv => (methods_correct_and_cost hb_pos hb o hi hv).1)
    (fun o hi hv => ⟨(methods_correct_and_cost hb_pos hb o hi hv).2.2.1,
      (methods_correct_and_cost hb_pos hb o hi hv).2.2.2⟩)

/-- **Worst-case `O(1)` time bound**: every operation (`append`, `pop`, `read`, `write`) costs at
most `7` memory units in the worst case (`totalCost Resizable.charge ≤ 7`). -/
theorem worstCase_cost_le_seven {w b : ℕ} (hb_pos : 0 < b) (hb : b ≤ w)
    {s : Memory.State} (o : Op) (hinv : Inv w b s) (hv : valid w b (abs w b s) o) :
    (Resizable.spec w).totalCost Resizable.charge s
      ((Resizable.spec w).clientHistory s (methods w b o)) ≤ 7 :=
  (methods_correct_and_cost hb_pos hb o hinv hv).2.1

/-- **Amortized `O(1)` time certificate with zero potential** (`potential = 0`, `upper = 7`). -/
theorem amortized (w b : ℕ) (hb_pos : 0 < b) (hb : b ≤ w) :
    (refinement w b hb_pos hb).Amortized Resizable.charge (fun _ _ => 7) (fun _ => 0) :=
  Refinement.Amortized.ofFn fun o hi hv => by
    have hcost := worstCase_cost_le_seven hb_pos hb o hi hv
    dsimp only [refinement, Refinement.ofFn]
    omega

/-- **Tight every-step space bound (self-contained in-memory representation, `base = 1`).**
At any state `s` satisfying `Inv w b s` with current array `xs = abs w b s` of length
`n = xs.length`, the allocated word count is
`s.frontier = 1 + packedWords w b n = 1 + ⌈n * b / w⌉` words, and the allocated space in bits
satisfies `n * b + w ≤ Resizable.spaceBits w s ≤ n * b + 2 * w - 1`
(additive space term at most `2 * w - 1` bits: `w` bits for the length header word at address `0`
plus at most `w - 1` bits of word-alignment rounding in the last data word). -/
theorem space_tight_every_step {w b : ℕ} {s : Memory.State}
    (hw : 0 < w) (hinv : Inv w b s) :
    let n := (abs w b s).length
    s.frontier = 1 + packedWords w b n ∧
      n * b + w ≤ Resizable.spaceBits w s ∧
      Resizable.spaceBits w s ≤ n * b + 2 * w - 1 := by
  intro n
  have hn : n = s.mem 0 := length_abs w b s
  have hfr : s.frontier = 1 + packedWords w b n := by rw [hn, hinv.frontier_eq]
  have hlo : n * b ≤ packedWords w b n * w := mul_le_packedWords_mul hw
  have hhi : packedWords w b n * w ≤ n * b + (w - 1) := packedWords_mul_le
  refine ⟨hfr, ?_, ?_⟩
  · unfold Resizable.spaceBits
    rw [hfr, Nat.mul_add, Nat.mul_one, Nat.mul_comm w (packedWords w b n)]
    omega
  · unfold Resizable.spaceBits
    rw [hfr, Nat.mul_add, Nat.mul_one, Nat.mul_comm w (packedWords w b n)]
    omega

/-! ## Zero-header packed representation (`base = 0`, length `n` in a 1-word register/spillover) -/

/-- Representation invariant of the zero-header packed array (`base = 0`) when the current item
count `n` is maintained in a machine register / `O(w)`-bit spillover (`[LLYZ23a]` Definition 1). -/
structure PackedInv (w b n : ℕ) (s : Memory.State) : Prop where
  /-- All words and the frontier fit in `w` bits, and all addresses `≥ s.frontier` hold `0`. -/
  canonical : Resizable.Canonical w s
  /-- The allocated word count is `packedWords w b n = ⌈n * b / w⌉`. -/
  frontier_eq : s.frontier = packedWords w b n

/-- Abstraction function of the zero-header packed array (`base = 0`) at length `n`. -/
def packedAbs (w b n : ℕ) (s : Memory.State) : List ℕ :=
  List.ofFn (fun i : Fin n => readSubword w s.mem b i.val)

/-- **Tight every-step space bound (zero-header packed representation, `base = 0`).**
At any state `s` satisfying `PackedInv w b n s`, the allocated word count is
`s.frontier = packedWords w b n = ⌈n * b / w⌉` words, and the allocated space in bits in virtual
memory satisfies `n * b ≤ Resizable.spaceBits w s ≤ n * b + (w - 1)`
(additive space term from word-granularity alone: at most `w - 1` bits). -/
theorem packed_space_tight {w b n : ℕ} {s : Memory.State}
    (hw : 0 < w) (hinv : PackedInv w b n s) :
    s.frontier = packedWords w b n ∧
      n * b ≤ Resizable.spaceBits w s ∧
      Resizable.spaceBits w s ≤ n * b + (w - 1) := by
  have hlo : n * b ≤ packedWords w b n * w := mul_le_packedWords_mul hw
  have hhi : packedWords w b n * w ≤ n * b + (w - 1) := packedWords_mul_le
  refine ⟨hinv.frontier_eq, ?_, ?_⟩
  · unfold Resizable.spaceBits
    rw [hinv.frontier_eq, Nat.mul_comm w (packedWords w b n)]
    exact hlo
  · unfold Resizable.spaceBits
    rw [hinv.frontier_eq, Nat.mul_comm w (packedWords w b n)]
    exact hhi

theorem packedWords_lt_succ_iff {w b i : ℕ} (hw : 0 < w) (hb_pos : 0 < b) (hb : b ≤ w) :
    packedWords w b i < packedWords w b (i + 1) ↔
      (i * b) % w = 0 ∨ w - (i * b) % w < b := by
  set q := (i * b) / w
  set r := (i * b) % w
  have hr : r < w := Nat.mod_lt _ hw
  have hdiv : i * b = w * q + r := (Nat.div_add_mod (i * b) w).symm
  have hib1 : (i + 1) * b = w * q + r + b := by
    rw [Nat.add_mul, Nat.one_mul, hdiv]
  rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
  · have hpw_i : packedWords w b i = q := by
      unfold packedWords
      rw [hdiv, hr0, Nat.add_zero]
      have h1 : w * q + w - 1 = (w - 1) + w * q := by omega
      rw [h1, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have hpw_i1 : packedWords w b (i + 1) = q + 1 := by
      unfold packedWords
      rw [hib1, hr0, Nat.add_zero]
      have h1 : w * q + b + w - 1 = (b - 1) + w * (q + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [h1, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [hpw_i, hpw_i1]
    exact ⟨fun _ => Or.inl hr0, fun _ => Nat.lt_succ_self q⟩
  · have hr_ne : r ≠ 0 := Nat.ne_of_gt hr_pos
    have hpw_i : packedWords w b i = q + 1 := by
      unfold packedWords
      rw [hdiv]
      have h1 : w * q + r + w - 1 = (r - 1) + w * (q + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [h1, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    by_cases hsplit : w - r < b
    · have hpw_i1 : packedWords w b (i + 1) = q + 2 := by
        unfold packedWords
        rw [hib1]
        have h1 : w * q + r + b + w - 1 = (r + b - w - 1) + w * (q + 2) := by
          rw [Nat.mul_add, show w * 2 = w + w by omega]
          omega
        rw [h1, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
      rw [hpw_i, hpw_i1]
      exact ⟨fun _ => Or.inr hsplit, fun _ => by omega⟩
    · have hpw_i1 : packedWords w b (i + 1) = q + 1 := by
        unfold packedWords
        rw [hib1]
        have h1 : w * q + r + b + w - 1 = (r + b - 1) + w * (q + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        rw [h1, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
      rw [hpw_i, hpw_i1]
      exact ⟨fun h => False.elim (Nat.lt_irrefl _ h),
        fun h => False.elim (h.elim hr_ne hsplit)⟩

/-! ## Direct demonic verification against `Memory.Resizable.demonicSpec w` -/

/-- Predicate on `Resizable.Op` excluding `.grow` and `.growDirty`; on such operations,
`Resizable.demonicStep w` is deterministic and coincides with `Resizable.step`. -/
def NoGrow : Resizable.Op → Prop
  | .grow _ => False
  | .growDirty _ => False
  | _ => True

theorem demonicStep_eq_step_of_noGrow {w : ℕ} {s s' : Memory.State} {o : Resizable.Op}
    {a : o.Result} (hno : NoGrow o) (hd : Resizable.demonicStep w s o s' a) :
    s' = (Resizable.step s o).1 ∧ a = (Resizable.step s o).2 := by
  cases o with
  | read _ => exact hd
  | write _ _ => exact ⟨hd, Subsingleton.elim a ()⟩
  | shrink _ => exact ⟨hd, Subsingleton.elim a ()⟩
  | grow _ => exact False.elim hno
  | growDirty _ => exact False.elim hno

theorem noGrow_writeSubwordAt (w base b i val : ℕ) (s : Memory.State) :
    ∀ o ∈ (Resizable.spec w).clientHistory s (writeSubwordAt w base b i val), NoGrow o := by
  dsimp only [writeSubwordAt]
  split_ifs
  · intro o ho
    simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> trivial
  · intro o ho
    simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> trivial

theorem noGrow_readSubwordAt (w base b i : ℕ) (s : Memory.State) :
    ∀ o ∈ (Resizable.spec w).clientHistory s (readSubwordAt w base b i), NoGrow o := by
  dsimp only [readSubwordAt]
  split_ifs
  · intro o ho
    simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho; trivial
  · intro o ho
    simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> trivial

theorem noGrow_popProg (w b : ℕ) (s : Memory.State) :
    ∀ o ∈ (Resizable.spec w).clientHistory s (popProg w b), NoGrow o := by
  by_cases hn : s.mem 0 = 0
  · intro o ho
    have hhist : (Resizable.spec w).clientHistory s (popProg w b) = [.read 0] := by
      dsimp only [popProg, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_left hn]
      rfl
    rw [hhist, List.mem_singleton] at ho
    subst ho; trivial
  · intro o ho
    have hhist :
        (Resizable.spec w).clientHistory s (popProg w b) =
          .read 0 ::
            ((Resizable.spec w).clientHistory s (readSubwordAt w 1 b (s.mem 0 - 1)) ++
              if packedWords w b (s.mem 0 - 1) < packedWords w b (s.mem 0) then
                [.write 0 (s.mem 0 - 1), .shrink 1]
              else
                [.write 0 (s.mem 0 - 1)]) := by
      dsimp only [popProg, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      rw [ite_eq_right hn]
      rcases runClient_readSubwordAt w 1 b (s.mem 0 - 1) s with ⟨hst_r, _⟩
      have hrun := (Resizable.spec w).clientHistory_bind (readSubwordAt w 1 b (s.mem 0 - 1))
        (fun v => .liftBind (.write 0 (s.mem 0 - 1)) fun _ =>
          if packedWords w b (s.mem 0 - 1) < packedWords w b (s.mem 0) then
            .liftBind (.shrink 1) fun _ => .pure (some v)
          else .pure (some v)) s
      rw [hst_r] at hrun
      change .read 0 ::
        (Resizable.spec w).clientHistory s (readSubwordAt w 1 b (s.mem 0 - 1) >>= _) = _
      rw [hrun]
      congr 2
      dsimp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        StateTransitionSpec.stepFn, Resizable.step]
      split_ifs <;> rfl
    rw [hhist, List.mem_cons, List.mem_append] at ho
    rcases ho with rfl | h_read | h_tail
    · trivial
    · exact noGrow_readSubwordAt w 1 b (s.mem 0 - 1) s o h_read
    · split_ifs at h_tail
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tail
        rcases h_tail with rfl | rfl <;> trivial
      · simp only [List.mem_singleton] at h_tail
        subst h_tail; trivial

theorem demonicValid_of_noGrow {α : Type} {w : ℕ} {s : Memory.State}
    {p : Resizable.Prog α}
    (hno : ∀ o ∈ (Resizable.spec w).clientHistory s p, NoGrow o)
    (hv : (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p)) :
    (Resizable.demonicSpec w).DemonicValid s p := by
  induction p generalizing s with
  | pure a => exact StateTransitionSpec.DemonicValid.pure (D := Resizable.demonicSpec w) s a
  | liftBind o k ih =>
    have ho : NoGrow o := hno o List.mem_cons_self
    have hk : ∀ x ∈ (Resizable.spec w).clientHistory ((Resizable.step s o).1)
        (k (Resizable.step s o).2), NoGrow x :=
      fun x hx => hno x (List.mem_cons_of_mem _ hx)
    refine StateTransitionSpec.DemonicValid.liftBind (D := Resizable.demonicSpec w) o k hv.1
      fun s₁ a hstep => ?_
    obtain ⟨rfl, rfl⟩ := demonicStep_eq_step_of_noGrow ho hstep
    exact ih _ hk hv.2

theorem clientRun_demonicSpec_of_noGrow {α : Type} {w : ℕ} {s s' : Memory.State}
    {p : Resizable.Prog α} {v : α} {tr : (Resizable.demonicSpec w).Transcript}
    (hno : ∀ o ∈ (Resizable.spec w).clientHistory s p, NoGrow o)
    (hrun : (Resizable.demonicSpec w).ClientRun s p v s' tr) :
    (Resizable.spec w).ValidHistory s ((Resizable.spec w).clientHistory s p) ∧
      v = (Resizable.spec w).clientResult s p ∧
      s' = (Resizable.spec w).clientState s p ∧
      (Resizable.demonicSpec w).totalCostTranscript Resizable.charge s tr =
        (Resizable.spec w).totalCost Resizable.charge s
          ((Resizable.spec w).clientHistory s p) := by
  induction p generalizing s tr with
  | pure a =>
    obtain ⟨rfl, rfl, rfl⟩ :=
      ((Resizable.demonicSpec w).clientRun_pure_iff s a v s' tr).mp hrun
    exact ⟨trivial, rfl, rfl, rfl⟩
  | liftBind o k ih =>
    have ho : NoGrow o := hno o List.mem_cons_self
    have hk : ∀ x ∈ (Resizable.spec w).clientHistory ((Resizable.step s o).1)
        (k (Resizable.step s o).2), NoGrow x :=
      fun x hx => hno x (List.mem_cons_of_mem _ hx)
    obtain ⟨hv_o, a, s₁, tr', hstep, hrest, rfl⟩ :=
      ((Resizable.demonicSpec w).clientRun_liftBind_iff s o k v s' tr).mp hrun
    obtain ⟨rfl, rfl⟩ := demonicStep_eq_step_of_noGrow ho hstep
    obtain ⟨hvh_k, rfl, rfl, hcost_k⟩ := ih _ hk hrest
    refine ⟨⟨hv_o, hvh_k⟩, rfl, rfl, ?_⟩
    change Resizable.charge s o +
        (Resizable.demonicSpec w).totalCostTranscript Resizable.charge
          (Resizable.step s o).1 tr' =
      Resizable.charge s o +
        (Resizable.spec w).totalCost Resizable.charge (Resizable.step s o).1
          ((Resizable.spec w).clientHistory (Resizable.step s o).1 (k (Resizable.step s o).2))
    rw [hcost_k]

/-- `appendProg` is demonically admissible and correct against `Resizable.demonicSpec w` even when
`.grow 1` initializes the newly allocated word with an arbitrary valid `w`-bit value, and every
permitted transcript costs at most `7` memory units. -/
theorem appendProg_demonic_correct {w b x : ℕ} {s : Memory.State}
    (hw : 0 < w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b s) (hv : valid w b (abs w b s) (.append x)) :
    (Resizable.demonicSpec w).DemonicValid s (appendProg w b x) ∧
      ∀ a s' tr, (Resizable.demonicSpec w).ClientRun s (appendProg w b x) a s' tr →
        (spec w b).step (abs w b s) (.append x) (abs w b s') a ∧
          Inv w b s' ∧
          (Resizable.demonicSpec w).totalCostTranscript Resizable.charge s tr ≤ 7 := by
  have hx : Fits b x := hv.1
  have hn1_fits : Fits w (s.mem 0 + 1) := by simpa using hv.2.1
  have hfw_fits : Fits w (1 + packedWords w b (s.mem 0 + 1)) := by simpa using hv.2.2
  have hpos_fr : 0 < s.frontier := by
    have := hinv.frontier_eq
    omega
  have hmono : packedWords w b (s.mem 0) ≤ packedWords w b (s.mem 0 + 1) :=
    packedWords_mono (Nat.le_succ _)
  have hsucc : packedWords w b (s.mem 0 + 1) ≤ packedWords w b (s.mem 0) + 1 :=
    packedWords_succ_le hb
  let s₁ : Memory.State := (Resizable.step s (.write 0 (s.mem 0 + 1))).1
  have hcan₁ : Resizable.Canonical w s₁ :=
    Resizable.canonical_step hinv.canonical ⟨hpos_fr, hn1_fits⟩
  have hshift₁ : shiftMem 1 s₁.mem = shiftMem 1 s.mem :=
    shiftMem_update_lt s.mem Nat.zero_lt_one (s.mem 0 + 1)
  have hmem0₁ : s₁.mem 0 = s.mem 0 + 1 := by
    dsimp only [s₁, Resizable.step]
    exact Function.update_self 0 (s.mem 0 + 1) s.mem
  constructor
  · refine StateTransitionSpec.DemonicValid.liftBind (D := Resizable.demonicSpec w)
      (Resizable.Op.read 0) _ hpos_fr fun s₀ n hread => ?_
    rcases hread with ⟨hs₀, hn⟩
    rw [hs₀, hn]
    refine StateTransitionSpec.DemonicValid.liftBind (D := Resizable.demonicSpec w)
      (Resizable.Op.write 0 (s.mem 0 + 1)) _ ⟨hpos_fr, hn1_fits⟩ fun s₁' u hwrite => ?_
    have hs₁' : s₁' = s₁ := hwrite
    rw [hs₁']
    split_ifs with hgrow
    · have hpw_eq : packedWords w b (s.mem 0 + 1) = packedWords w b (s.mem 0) + 1 := by omega
      have hgrow_valid : Resizable.valid w s₁ (.grow 1) := by
        rw [Resizable.valid_grow]
        have : s₁.frontier + 1 = 1 + packedWords w b (s.mem 0 + 1) := by
          dsimp only [s₁, Resizable.step]
          rw [hinv.frontier_eq, hpw_eq]
          omega
        rw [this]
        exact hfw_fits
      refine StateTransitionSpec.DemonicValid.liftBind (D := Resizable.demonicSpec w)
        (Resizable.Op.grow 1) _ hgrow_valid fun s₂ _ hstep_grow => ?_
      have hfr₂ : s₂.frontier = 1 + packedWords w b (s.mem 0 + 1) := by
        have hfr_step := hstep_grow.1
        dsimp only [s₁, Resizable.step] at hfr_step
        rw [hfr_step, hinv.frontier_eq, hpw_eq]
        omega
      obtain ⟨hvh_w, _⟩ :=
        valid_and_cost_writeSubwordAt (s := s₂) (base := 1) (n := s.mem 0 + 1) (i := s.mem 0)
          (val := x) hw hb_pos (Nat.lt_succ_self _) (le_of_eq hfr₂.symm)
      exact demonicValid_of_noGrow (noGrow_writeSubwordAt w 1 b (s.mem 0) x s₂) hvh_w
    · have hpw_eq : packedWords w b (s.mem 0 + 1) = packedWords w b (s.mem 0) := by omega
      have hfr₁ : s₁.frontier = 1 + packedWords w b (s.mem 0 + 1) := by
        dsimp only [s₁, Resizable.step]
        rw [hinv.frontier_eq, hpw_eq]
      obtain ⟨hvh_w, _⟩ :=
        valid_and_cost_writeSubwordAt (s := s₁) (base := 1) (n := s.mem 0 + 1) (i := s.mem 0)
          (val := x) hw hb_pos (Nat.lt_succ_self _) (le_of_eq hfr₁.symm)
      exact demonicValid_of_noGrow (noGrow_writeSubwordAt w 1 b (s.mem 0) x s₁) hvh_w
  · intro a s' tr hrun
    dsimp only [appendProg] at hrun
    obtain ⟨_, n, s₀, tr₁, hread, hrun₁, rfl⟩ :=
      ((Resizable.demonicSpec w).clientRun_liftBind_iff s (Resizable.Op.read 0) _ a s' tr).mp hrun
    rcases hread with ⟨hs₀, hn⟩
    rw [hs₀, hn] at hrun₁ ⊢
    obtain ⟨_, u, s₁', tr₂, hwrite, hrun₂, rfl⟩ :=
      ((Resizable.demonicSpec w).clientRun_liftBind_iff s
        (Resizable.Op.write 0 (s.mem 0 + 1)) _ a s' tr₁).mp hrun₁
    have hs₁' : s₁' = s₁ := hwrite
    rw [hs₁'] at hrun₂ ⊢
    split_ifs at hrun₂ with hgrow
    · have hpw_eq : packedWords w b (s.mem 0 + 1) = packedWords w b (s.mem 0) + 1 := by omega
      have hgrow_valid : Resizable.valid w s₁ (.grow 1) := by
        rw [Resizable.valid_grow]
        have : s₁.frontier + 1 = 1 + packedWords w b (s.mem 0 + 1) := by
          dsimp only [s₁, Resizable.step]
          rw [hinv.frontier_eq, hpw_eq]
          omega
        rw [this]
        exact hfw_fits
      obtain ⟨_, u₂, s₂, tr_w, hstep_grow, hrun_w, rfl⟩ :=
        ((Resizable.demonicSpec w).clientRun_liftBind_iff s₁
          (Resizable.Op.grow 1) _ a s' tr₂).mp hrun₂
      have hcan₂ : Resizable.Canonical w s₂ :=
        Resizable.canonical_demonicStep hcan₁ hgrow_valid hstep_grow
      have hfr₂ : s₂.frontier = 1 + packedWords w b (s.mem 0 + 1) := by
        have hfr_step := hstep_grow.1
        dsimp only [s₁, Resizable.step] at hfr_step
        rw [hfr_step, hinv.frontier_eq, hpw_eq]
        omega
      have hmem0₂ : s₂.mem 0 = s.mem 0 + 1 := by
        rw [hstep_grow.2.2.1 0 (Or.inl hpos_fr), hmem0₁]
      obtain ⟨hvh_w, rfl, rfl, hcost_w_eq⟩ :=
        clientRun_demonicSpec_of_noGrow (noGrow_writeSubwordAt w 1 b (s.mem 0) x s₂) hrun_w
      obtain ⟨_, hcost_w⟩ :=
        valid_and_cost_writeSubwordAt (s := s₂) (base := 1) (n := s.mem 0 + 1)
          (i := s.mem 0) (val := x) hw hb_pos (Nat.lt_succ_self _) (le_of_eq hfr₂.symm)
      obtain ⟨hfr_w, hmem0_w, hshift_w⟩ := clientState_writeSubwordAt w 1 b (s.mem 0) x s₂
      have hmem0_fin :
          ((Resizable.spec w).clientState s₂ (writeSubwordAt w 1 b (s.mem 0) x)).mem 0 =
            s.mem 0 + 1 := by
        rw [hmem0_w 0 Nat.zero_lt_one, hmem0₂]
      have hinv_fin :
          Inv w b ((Resizable.spec w).clientState s₂ (writeSubwordAt w 1 b (s.mem 0) x)) :=
        ⟨canonical_clientState hcan₂ hvh_w, by rw [hfr_w, hfr₂, hmem0_fin]⟩
      refine ⟨?_, hinv_fin, ?_⟩
      · rw [(spec w b).step_iff_stepFn]
        refine Prod.ext ?_ rfl
        change abs w b _ = abs w b s ++ [x]
        symm
        apply List.ext_getElem
        · simp [hmem0_fin]
        · intro j hj1 hj2
          rw [getElem_abs, hshift_w]
          by_cases hjn : j < s.mem 0
          · have hj_abs : j < (abs w b s).length := by simpa using hjn
            rw [List.getElem_append_left hj_abs, getElem_abs,
              readSubword_writeSubword_of_ne _ hw hb (by omega)]
            apply readSubword_congr hw hb hjn
            intro k hk
            unfold shiftMem
            have hlt_fr : 1 + k < s₁.frontier := by
              dsimp only [s₁, Resizable.step]
              rw [hinv.frontier_eq]
              omega
            rw [hstep_grow.2.2.1 (1 + k) (Or.inl hlt_fr)]
            exact (congrFun hshift₁ k).symm
          · have hjeq : j = s.mem 0 := by
              simp only [List.length_append, length_abs, List.length_singleton] at hj1
              omega
            subst hjeq
            have hlen : (abs w b s).length ≤ s.mem 0 := by simp
            rw [List.getElem_append_right hlen]
            simp [readSubword_writeSubword_self _ hw hb hx]
      · change 1 + (1 + (1 +
          (Resizable.demonicSpec w).totalCostTranscript Resizable.charge s₂ tr_w)) ≤ 7
        rw [hcost_w_eq]
        omega
    · have hpw_eq : packedWords w b (s.mem 0 + 1) = packedWords w b (s.mem 0) := by omega
      have hfr₁ : s₁.frontier = 1 + packedWords w b (s.mem 0 + 1) := by
        dsimp only [s₁, Resizable.step]
        rw [hinv.frontier_eq, hpw_eq]
      obtain ⟨hvh_w, rfl, rfl, hcost_w_eq⟩ :=
        clientRun_demonicSpec_of_noGrow (noGrow_writeSubwordAt w 1 b (s.mem 0) x s₁) hrun₂
      obtain ⟨_, hcost_w⟩ :=
        valid_and_cost_writeSubwordAt (s := s₁) (base := 1) (n := s.mem 0 + 1)
          (i := s.mem 0) (val := x) hw hb_pos (Nat.lt_succ_self _) (le_of_eq hfr₁.symm)
      obtain ⟨hfr_w, hmem0_w, hshift_w⟩ := clientState_writeSubwordAt w 1 b (s.mem 0) x s₁
      have hmem0_fin :
          ((Resizable.spec w).clientState s₁ (writeSubwordAt w 1 b (s.mem 0) x)).mem 0 =
            s.mem 0 + 1 := by
        rw [hmem0_w 0 Nat.zero_lt_one, hmem0₁]
      have hinv_fin :
          Inv w b ((Resizable.spec w).clientState s₁ (writeSubwordAt w 1 b (s.mem 0) x)) :=
        ⟨canonical_clientState hcan₁ hvh_w, by rw [hfr_w, hfr₁, hmem0_fin]⟩
      refine ⟨?_, hinv_fin, ?_⟩
      · rw [(spec w b).step_iff_stepFn]
        refine Prod.ext ?_ rfl
        change abs w b _ = abs w b s ++ [x]
        symm
        apply List.ext_getElem
        · simp [hmem0_fin]
        · intro j hj1 hj2
          rw [getElem_abs, hshift_w, hshift₁]
          by_cases hjn : j < s.mem 0
          · have hj_abs : j < (abs w b s).length := by simpa using hjn
            rw [List.getElem_append_left hj_abs, getElem_abs,
              readSubword_writeSubword_of_ne _ hw hb (by omega)]
          · have hjeq : j = s.mem 0 := by
              simp only [List.length_append, length_abs, List.length_singleton] at hj1
              omega
            subst hjeq
            have hlen : (abs w b s).length ≤ s.mem 0 := by simp
            rw [List.getElem_append_right hlen]
            simp [readSubword_writeSubword_self _ hw hb hx]
      · change 1 + (1 + (Resizable.demonicSpec w).totalCostTranscript Resizable.charge s₁ tr₂) ≤ 7
        rw [hcost_w_eq]
        omega

/-- **Direct demonic refinement of the resizable `b`-bit array over
`Memory.Resizable.demonicSpec w`** (where `.grow k` initializes newly allocated words with
arbitrary valid `w`-bit values). -/
def demonicRefinement (w b : ℕ) (hb_pos : 0 < b) (hb : b ≤ w) :
    Refinement (spec w b) (Resizable.demonicSpec w) where
  methods := methods w b
  inv := Inv w b
  abs := abs w b
  valid {s} o hinv hv := by
    have hw : 0 < w := lt_of_lt_of_le hb_pos hb
    cases o with
    | append x => exact (appendProg_demonic_correct hw hb_pos hb hinv hv).1
    | pop =>
      exact demonicValid_of_noGrow (noGrow_popProg w b s)
        (methods_correct_and_cost hb_pos hb .pop hinv hv).1
    | read i =>
      exact demonicValid_of_noGrow (noGrow_readSubwordAt w 1 b i s)
        (methods_correct_and_cost hb_pos hb (.read i) hinv hv).1
    | write i x =>
      exact demonicValid_of_noGrow (noGrow_writeSubwordAt w 1 b i x s)
        (methods_correct_and_cost hb_pos hb (.write i x) hinv hv).1
  correct {s} o {a s' tr} hinv hv hrun := by
    have hw : 0 < w := lt_of_lt_of_le hb_pos hb
    cases o with
    | append x =>
      obtain ⟨hstep, hinv', _⟩ := (appendProg_demonic_correct hw hb_pos hb hinv hv).2 a s' tr hrun
      exact ⟨hstep, hinv'⟩
    | pop =>
      obtain ⟨_, rfl, rfl, _⟩ := clientRun_demonicSpec_of_noGrow (noGrow_popProg w b s) hrun
      obtain ⟨_, _, hstep, hinv'⟩ := methods_correct_and_cost hb_pos hb .pop hinv hv
      exact ⟨((spec w b).step_iff_stepFn _ _ _ _).mpr hstep.symm, hinv'⟩
    | read i =>
      obtain ⟨_, rfl, rfl, _⟩ :=
        clientRun_demonicSpec_of_noGrow (noGrow_readSubwordAt w 1 b i s) hrun
      obtain ⟨_, _, hstep, hinv'⟩ := methods_correct_and_cost hb_pos hb (.read i) hinv hv
      exact ⟨((spec w b).step_iff_stepFn _ _ _ _).mpr hstep.symm, hinv'⟩
    | write i x =>
      obtain ⟨_, rfl, rfl, _⟩ :=
        clientRun_demonicSpec_of_noGrow (noGrow_writeSubwordAt w 1 b i x s) hrun
      obtain ⟨_, _, hstep, hinv'⟩ := methods_correct_and_cost hb_pos hb (.write i x) hinv hv
      exact ⟨((spec w b).step_iff_stepFn _ _ _ _).mpr hstep.symm, hinv'⟩

/-- **Demonic amortized `O(1)` time certificate (`potential = 0`, `upper = 7`)** over
`Memory.Resizable.demonicSpec w`. -/
theorem demonicAmortized (w b : ℕ) (hb_pos : 0 < b) (hb : b ≤ w) :
    (demonicRefinement w b hb_pos hb).Amortized Resizable.charge (fun _ _ => 7) (fun _ => 0) where
  step {s} o {a s' tr} hinv hv hrun := by
    have hw : 0 < w := lt_of_lt_of_le hb_pos hb
    cases o with
    | append x =>
      obtain ⟨_, _, hcost⟩ := (appendProg_demonic_correct hw hb_pos hb hinv hv).2 a s' tr hrun
      omega
    | pop =>
      obtain ⟨_, _, _, hcost_eq⟩ := clientRun_demonicSpec_of_noGrow (noGrow_popProg w b s) hrun
      have hcost := (methods_correct_and_cost hb_pos hb .pop hinv hv).2.1
      dsimp only [methods] at hcost
      omega
    | read i =>
      obtain ⟨_, _, _, hcost_eq⟩ :=
        clientRun_demonicSpec_of_noGrow (noGrow_readSubwordAt w 1 b i s) hrun
      have hcost := (methods_correct_and_cost hb_pos hb (.read i) hinv hv).2.1
      dsimp only [methods, readProg] at hcost
      omega
    | write i x =>
      obtain ⟨_, _, _, hcost_eq⟩ :=
        clientRun_demonicSpec_of_noGrow (noGrow_writeSubwordAt w 1 b i x s) hrun
      have hcost := (methods_correct_and_cost hb_pos hb (.write i x) hinv hv).2.1
      dsimp only [methods, writeProg] at hcost
      omega

/-! ## Concrete `WordRAM.Resizable.RCode` machine-instruction implementation -/

open Cslib.WordRAM.Resizable

/-- Project an `RData r` machine state to its underlying `Memory.State`. -/
abbrev toMemState {r : ℕ} (x : RData r) : Memory.State :=
  ⟨x.mem, x.frontier⟩

theorem canonical_toMemState {w r : ℕ} {x : RData r} (hx : x.Bounded w) :
    Resizable.Canonical w (toMemState x) :=
  ⟨⟨hx.2.1, fun a => hx.1.2 a⟩, hx.2.2⟩

/-- Machine-level `RCode .standard 16` procedure for reading the `b`-bit item at index `regs regIdx`
(`≤ 31` instructions). -/
abbrev readArrayCode : RCode .standard 16 :=
  readSubwordCode

/-- `readArrayCode` executes in at most `31` `WordRAM` instructions, preserves `Bounded w`,
`Inv w b`, and `abs w b`, and places `(abs w b (toMemState x)).getD i 0` in `regVal`. -/
theorem readArrayCode_exec {w b : ℕ} {x : RData 16}
    (hx : x.Bounded w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b (toMemState x))
    (hbase : x.regs regBase = 1) (hb_reg : x.regs regB = b)
    (hv : valid w b (abs w b (toMemState x)) (.read (x.regs regIdx)))
    (hbitOff : Fits w (x.regs regIdx * b)) :
    RDemonicExec w readArrayCode x 31 fun y =>
      y.Bounded w ∧
        Inv w b (toMemState y) ∧
        abs w b (toMemState y) = abs w b (toMemState x) ∧
        y.regs regVal = (abs w b (toMemState x)).getD (x.regs regIdx) 0 ∧
        y.regs regBase = 1 ∧
        y.regs regB = b := by
  have hi : x.regs regIdx < x.mem 0 := by simpa [valid, toMemState] using hv
  have hfront : x.regs regBase + packedWords w (x.regs regB) (x.mem 0) ≤ x.frontier := by
    rw [hbase, hb_reg]
    exact le_of_eq hinv.frontier_eq.symm
  refine (readSubwordCode_exec hx (by rw [hb_reg]; exact hb_pos) (by rw [hb_reg]; exact hb)
    hi (by rw [hb_reg]; exact hbitOff) hfront).mono le_rfl ?_
  rintro y ⟨hy_bdd, hy_mem, hy_fr, hy_val, _, _, _, hy_base, hy_b⟩
  have hstate_eq : toMemState y = toMemState x := Memory.State.ext hy_mem hy_fr
  refine ⟨hy_bdd, hstate_eq ▸ hinv, congrArg (abs w b) hstate_eq, ?_,
    hy_base.trans hbase, hy_b.trans hb_reg⟩
  rw [hy_val, hbase, hb_reg, getD_abs w b (toMemState x) hi]
  rfl

/-- Machine-level `RCode .standard 16` procedure for writing the `b`-bit item `regs regVal` at
index `regs regIdx` (`≤ 40` instructions). -/
abbrev writeArrayCode : RCode .standard 16 :=
  writeSubwordCode

/-- `writeArrayCode` executes in at most `40` `WordRAM` instructions, preserves `Bounded w` and
`Inv w b`, and updates `abs w b (toMemState y)` to `(abs w b (toMemState x)).set i val`. -/
theorem writeArrayCode_exec {w b : ℕ} {x : RData 16}
    (hx : x.Bounded w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b (toMemState x))
    (hbase : x.regs regBase = 1) (hb_reg : x.regs regB = b)
    (hv : valid w b (abs w b (toMemState x)) (.write (x.regs regIdx) (x.regs regVal)))
    (hbitOff : Fits w (x.regs regIdx * b)) :
    RDemonicExec w writeArrayCode x 40 fun y =>
      y.Bounded w ∧
        Inv w b (toMemState y) ∧
        abs w b (toMemState y) = (abs w b (toMemState x)).set (x.regs regIdx) (x.regs regVal) ∧
        y.regs regBase = 1 ∧
        y.regs regB = b := by
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  have hi : x.regs regIdx < x.mem 0 := by simpa [valid, toMemState] using hv.1
  have hval_fits : Fits b (x.regs regVal) := hv.2
  have hfront : x.regs regBase + packedWords w (x.regs regB) (x.mem 0) ≤ x.frontier := by
    rw [hbase, hb_reg]
    exact le_of_eq hinv.frontier_eq.symm
  refine (writeSubwordCode_exec hx (by rw [hb_reg]; exact hb_pos) (by rw [hb_reg]; exact hb)
    hi (by rw [hb_reg]; exact hbitOff) hfront).mono le_rfl ?_
  rintro y ⟨hy_bdd, hy_fr, hy_below, hy_shift, hy_pres⟩
  have hy_mem0 : y.mem 0 = x.mem 0 := hy_below 0 (by rw [hbase]; exact Nat.zero_lt_one)
  have hinv_y : Inv w b (toMemState y) := by
    refine ⟨canonical_toMemState hy_bdd, ?_⟩
    change y.frontier = 1 + packedWords w b (y.mem 0)
    rw [hy_fr, hy_mem0]
    exact hinv.frontier_eq
  refine ⟨hy_bdd, hinv_y, ?_,
    (hy_pres regBase (by decide)).trans hbase,
    (hy_pres regB (by decide)).trans hb_reg⟩
  apply List.ext_getElem
  · simp [toMemState, hy_mem0]
  · intro j hj1 hj2
    have hshift_eq : shiftMem 1 y.mem =
        writeSubword w (shiftMem 1 x.mem) b (x.regs regIdx) (x.regs regVal) := by
      change (fun a => y.mem (1 + a)) = _
      rw [← hbase, ← hb_reg]
      exact hy_shift
    rw [getElem_abs, List.getElem_set, getElem_abs, hshift_eq]
    by_cases hji : j = x.regs regIdx
    · subst hji
      simp [readSubword_writeSubword_self _ hw hb hval_fits]
    · rw [ite_eq_right (Ne.symm hji), readSubword_writeSubword_of_ne _ hw hb hji]

/-- Machine-level `RCode .standard 16` procedure for appending `regs regVal` to the resizable array
(`≤ 58` instructions). -/
def appendArrayCode : RCode .standard 16 :=
  .seq (.op (.const regTmp1 0)) <|
  .seq (.op (.load regIdx regTmp1)) <|
  .seq (.op (.const regTmp2 1)) <|
  .seq (.op (.bin .add regTmp2 regIdx regTmp2)) <|
  .seq (.op (.store regTmp1 regTmp2)) <|
  .seq (RCode.ofCode subwordHeaderCode) <|
  .seq (.op (.const regTmp2 1)) <|
  .seq (.op (.const regTmp1 0)) <|
  .seq (.branch (.eq regOff regTmp1)
         (.grow regTmp1 regTmp2)
         (.branch (.lt regLow regB)
           (.grow regTmp1 regTmp2)
           (.op (.const regTmp1 0)))) <|
       writeSubwordCode

/-- `appendArrayCode` executes in at most `58` `WordRAM` instructions under demonic `.grow 1`,
preserves `Bounded w` and `Inv w b` (`y.frontier = 1 + packedWords w b (n + 1)`), and updates
`abs w b (toMemState y)` to `abs w b (toMemState x) ++ [x.regs regVal]`. -/
theorem appendArrayCode_exec {w b : ℕ} {x : RData 16}
    (hx : x.Bounded w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b (toMemState x))
    (hbase : x.regs regBase = 1) (hb_reg : x.regs regB = b)
    (hv : valid w b (abs w b (toMemState x)) (.append (x.regs regVal)))
    (hbitOff : Fits w ((abs w b (toMemState x)).length * b)) :
    RDemonicExec w appendArrayCode x 58 fun y =>
      y.Bounded w ∧
        Inv w b (toMemState y) ∧
        abs w b (toMemState y) = abs w b (toMemState x) ++ [x.regs regVal] ∧
        y.frontier = 1 + packedWords w b ((abs w b (toMemState x)).length + 1) ∧
        y.regs regBase = 1 ∧
        y.regs regB = b := by
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  have hw_ne : w ≠ 0 := by omega
  set n := x.mem 0
  set val := x.regs regVal
  have hval_fits : Fits b val := hv.1
  have hn1_fits : Fits w (n + 1) := by simpa [toMemState] using hv.2.1
  have hfw_fits : Fits w (1 + packedWords w b (n + 1)) := by simpa [toMemState] using hv.2.2
  have hn_bitOff : Fits w (n * b) := by simpa [toMemState] using hbitOff
  have hpos_fr : 0 < x.frontier := by
    have : x.frontier = 1 + packedWords w b n := hinv.frontier_eq
    omega
  set x₁ := x.set regTmp1 0
  have e₁ : RDemonicExec (B := .standard) w (.op (.const regTmp1 0)) x 1 (· = x₁) :=
    RDemonicExec.const (fits_zero w)
  set x₂ := x₁.set regIdx n
  have e₂ : RDemonicExec (B := .standard) w (.op (.load regIdx regTmp1)) x₁ 1 (· = x₂) := by
    rw [show x₂ = x₁.set regIdx (x₁.mem (x₁.regs regTmp1)) by rfl]
    exact RDemonicExec.load hpos_fr
  set x₃ := x₂.set regTmp2 1
  have e₃ : RDemonicExec (B := .standard) w (.op (.const regTmp2 1)) x₂ 1 (· = x₃) :=
    RDemonicExec.const (fits_one hw_ne)
  set x₄ := x₃.set regTmp2 (n + 1)
  have e₄ : RDemonicExec w (.op (.bin .add regTmp2 regIdx regTmp2)) x₃ 1 (· = x₄) :=
    RDemonicExec.bin hn1_fits
  set x₅ := x₄.write 0 (n + 1)
  have e₅ : RDemonicExec (B := .standard) w (.op (.store regTmp1 regTmp2)) x₄ 1 (· = x₅) := by
    rw [show x₅ = x₄.write (x₄.regs regTmp1) (x₄.regs regTmp2) by rfl]
    exact RDemonicExec.store hpos_fr
  have hx₅_bdd : x₅.Bounded w :=
    ((((hx.set (fits_zero w)).set (hx.mem_fits 0)).set (fits_one hw_ne)).set hn1_fits).write
      hpos_fr hn1_fits
  have haddr0_lt : 1 + (n * b) / w < 1 + packedWords w b (n + 1) :=
    Nat.add_lt_add_left (wordIdx_lt_packedWords_of_pos hw hb_pos (Nat.lt_succ_self n)) 1
  have haddr0_fits : Fits w (x₅.regs regBase + (x₅.regs regIdx * x₅.regs regB) / w) := by
    change Fits w (x.regs regBase + (n * x.regs regB) / w)
    rw [hbase, hb_reg]
    exact hfw_fits.of_le (le_of_lt haddr0_lt)
  obtain ⟨d₆, hd₆_exec, hd₆_mem, _, hd₆_widx, hd₆_off, hd₆_low, hd₆_pres⟩ :=
    subwordHeaderCode_exec (x := x₅.toData) hw
      (by change Fits w (n * x.regs regB); rw [hb_reg]; exact hn_bitOff)
      haddr0_fits
  set x₆ : RData 16 := ⟨d₆.regs, d₆.mem, x.frontier⟩
  have e₆ : RDemonicExec w (RCode.ofCode subwordHeaderCode) x₅ 6 (· = x₆) :=
    RDemonicExec.of_exec_regOnly (by decide) hd₆_exec
  have hx₆_bdd : x₆.Bounded w :=
    ⟨hd₆_exec.bounded hx₅_bdd.1, hx₅_bdd.2.1,
      by change ∀ a ≥ x.frontier, d₆.mem a = 0; rw [hd₆_mem]; exact hx₅_bdd.2.2⟩
  set x₇ := x₆.set regTmp2 1
  have e₇ : RDemonicExec (B := .standard) w (.op (.const regTmp2 1)) x₆ 1 (· = x₇) :=
    RDemonicExec.const (fits_one hw_ne)
  set x₈ := x₇.set regTmp1 0
  have e₈ : RDemonicExec (B := .standard) w (.op (.const regTmp1 0)) x₇ 1 (· = x₈) :=
    RDemonicExec.const (fits_zero w)
  have hx₈_bdd : x₈.Bounded w := (hx₆_bdd.set (fits_one hw_ne)).set (fits_zero w)
  have hx₈_mem : x₈.mem = Function.update x.mem 0 (n + 1) := hd₆_mem
  have hx₈_off : x₈.regs regOff = (n * b) % w := by
    change d₆.regs regOff = (n * b) % w
    rw [hd₆_off]
    change (n * x.regs regB) % w = (n * b) % w
    rw [hb_reg]
  have hx₈_low : x₈.regs regLow = w - (n * b) % w := by
    change d₆.regs regLow = w - (n * b) % w
    rw [hd₆_low]
    change w - (n * x.regs regB) % w = w - (n * b) % w
    rw [hb_reg]
  have hx₈_b : x₈.regs regB = b :=
    (hd₆_pres regB (by decide)).trans hb_reg
  have hx₈_base : x₈.regs regBase = 1 :=
    (hd₆_pres regBase (by decide)).trans hbase
  have hx₈_idx : x₈.regs regIdx = n :=
    hd₆_pres regIdx (by decide)
  have hx₈_val : x₈.regs regVal = val :=
    hd₆_pres regVal (by decide)
  -- Helper invariant `P_g` after the conditional `.grow 1` branch:
  let P_g (xg : RData 16) : Prop :=
    xg.Bounded w ∧
      xg.frontier = 1 + packedWords w b (n + 1) ∧
      xg.mem 0 = n + 1 ∧
      (∀ a < packedWords w b n, xg.mem (1 + a) = x.mem (1 + a)) ∧
      (∀ r : Fin 16, r.val < 6 → xg.regs r = x₈.regs r)
  have e_grow_branch :
      RDemonicExec (B := .standard) w
        (.branch (.eq regOff regTmp1)
          (.grow regTmp1 regTmp2)
          (.branch (.lt regLow regB)
            (.grow regTmp1 regTmp2)
            (.op (.const regTmp1 0)))) x₈ 5 P_g := by
    have hsucc : packedWords w b (n + 1) ≤ packedWords w b n + 1 := packedWords_succ_le hb
    have hmono : packedWords w b n ≤ packedWords w b (n + 1) := packedWords_mono (Nat.le_succ n)
    have h_grow_post :
        packedWords w b n < packedWords w b (n + 1) →
          Fits w (x₈.frontier + x₈.regs regTmp2) ∧
            ∀ mem', DemonicGrow w x₈.frontier (x₈.regs regTmp2) x₈.mem mem' →
              P_g ⟨Function.update x₈.regs regTmp1 x₈.frontier, mem',
                x₈.frontier + x₈.regs regTmp2⟩ := by
      intro hlt_pw
      have hpw_eq : packedWords w b (n + 1) = packedWords w b n + 1 := by omega
      have hfr_xg : x.frontier + 1 = 1 + packedWords w b (n + 1) := by
        have hfr_x : x.frontier = 1 + packedWords w b n := hinv.frontier_eq
        omega
      have hfr_fits : Fits w (x₈.frontier + x₈.regs regTmp2) := by
        change Fits w (x.frontier + 1)
        rw [hfr_xg]
        exact hfw_fits
      refine ⟨hfr_fits, fun mem' hdem => ⟨hx₈_bdd.grow hfr_fits hdem, hfr_xg, ?_, ?_, ?_⟩⟩
      · change mem' 0 = n + 1
        rw [hdem.1 0 hpos_fr, hx₈_mem, Function.update_self]
      · intro a ha
        change mem' (1 + a) = x.mem (1 + a)
        have hfr8 : x₈.frontier = 1 + packedWords w b n := hinv.frontier_eq
        rw [hdem.1 (1 + a) (by omega), hx₈_mem, Function.update_of_ne (by omega)]
      · intro r hr
        have hne : r ≠ regTmp1 :=
          (by decide : ∀ k : Fin 16, k.val < 6 → k ≠ regTmp1) r hr
        exact Function.update_of_ne hne _ _
    by_cases hoff0 : (n * b) % w = 0
    · have hcond : (Cond.eq regOff regTmp1).Holds x₈.toData := by
        change x₈.regs regOff = 0
        rw [hx₈_off, hoff0]
      have hlt_pw : packedWords w b n < packedWords w b (n + 1) :=
        (packedWords_lt_succ_iff hw hb_pos hb).mpr (Or.inl hoff0)
      obtain ⟨hfit, hpost⟩ := h_grow_post hlt_pw
      exact (RDemonicExec.branch_pos hcond (RDemonicExec.grow hfit hpost)).mono
        (by decide) fun _ h => h
    · have hcond1 : ¬ (Cond.eq regOff regTmp1).Holds x₈.toData := by
        change x₈.regs regOff ≠ 0
        rw [hx₈_off]
        exact hoff0
      by_cases hlow : w - (n * b) % w < b
      · have hcond2 : (Cond.lt regLow regB).Holds x₈.toData := by
          change x₈.regs regLow < x₈.regs regB
          rw [hx₈_low, hx₈_b]
          exact hlow
        have hlt_pw : packedWords w b n < packedWords w b (n + 1) :=
          (packedWords_lt_succ_iff hw hb_pos hb).mpr (Or.inr hlow)
        obtain ⟨hfit, hpost⟩ := h_grow_post hlt_pw
        exact (RDemonicExec.branch_neg hcond1
          (RDemonicExec.branch_pos hcond2 (RDemonicExec.grow hfit hpost))).mono
          (by decide) fun _ h => h
      · have hcond2 : ¬ (Cond.lt regLow regB).Holds x₈.toData := by
          change ¬ (x₈.regs regLow < x₈.regs regB)
          rw [hx₈_low, hx₈_b]
          exact hlow
        have hnot_lt : ¬ (packedWords w b n < packedWords w b (n + 1)) := by
          rw [packedWords_lt_succ_iff hw hb_pos hb]
          exact fun h => h.elim hoff0 hlow
        have hpw_eq : packedWords w b (n + 1) = packedWords w b n := by omega
        refine (RDemonicExec.branch_neg hcond1
          (RDemonicExec.branch_neg hcond2 (RDemonicExec.const (fits_zero w)))).mono (by decide) ?_
        rintro _ rfl
        have hfr_x8 : (x₈.set regTmp1 0).frontier = 1 + packedWords w b (n + 1) := by
          have hfr_x : x.frontier = 1 + packedWords w b n := hinv.frontier_eq
          change x.frontier = _
          omega
        refine ⟨hx₈_bdd.set (fits_zero w), hfr_x8, ?_, ?_, ?_⟩
        · change x₈.mem 0 = n + 1
          rw [hx₈_mem, Function.update_self]
        · intro a _
          change x₈.mem (1 + a) = x.mem (1 + a)
          rw [hx₈_mem, Function.update_of_ne (by omega)]
        · intro r hr
          have hne : r ≠ regTmp1 :=
            (by decide : ∀ k : Fin 16, k.val < 6 → k ≠ regTmp1) r hr
          exact Function.update_of_ne hne _ _
  have e_tail : ∀ xg, P_g xg → RDemonicExec w writeSubwordCode xg 40 fun y =>
      y.Bounded w ∧
        Inv w b (toMemState y) ∧
        abs w b (toMemState y) = abs w b (toMemState x) ++ [x.regs regVal] ∧
        y.frontier = 1 + packedWords w b ((abs w b (toMemState x)).length + 1) ∧
        y.regs regBase = 1 ∧
        y.regs regB = b := by
    rintro xg ⟨hxg_bdd, hxg_fr, hxg_mem0, hxg_below, hxg_regs⟩
    have hxg_b : xg.regs regB = b := (hxg_regs regB (by decide)).trans hx₈_b
    have hxg_base : xg.regs regBase = 1 := (hxg_regs regBase (by decide)).trans hx₈_base
    have hxg_idx : xg.regs regIdx = n := (hxg_regs regIdx (by decide)).trans hx₈_idx
    have hxg_val : xg.regs regVal = val := (hxg_regs regVal (by decide)).trans hx₈_val
    refine (writeSubwordCode_exec (n := n + 1) hxg_bdd
      (by rw [hxg_b]; exact hb_pos)
      (by rw [hxg_b]; exact hb)
      (by rw [hxg_idx]; exact Nat.lt_succ_self n)
      (by rw [hxg_idx, hxg_b]; exact hn_bitOff)
      (by rw [hxg_base, hxg_b, hxg_fr])).mono le_rfl ?_
    rintro y ⟨hy_bdd, hy_fr, hy_below, hy_shift, hy_pres⟩
    have hy_mem0 : y.mem 0 = n + 1 := by
      rw [hy_below 0 (by rw [hxg_base]; exact Nat.zero_lt_one), hxg_mem0]
    have hy_fr_eq : y.frontier = 1 + packedWords w b (n + 1) := by
      rw [hy_fr, hxg_fr]
    have hinv_y : Inv w b (toMemState y) := by
      refine ⟨canonical_toMemState hy_bdd, ?_⟩
      change y.frontier = 1 + packedWords w b (y.mem 0)
      rw [hy_fr_eq, hy_mem0]
    refine ⟨hy_bdd, hinv_y, ?_, ?_,
      (hy_pres regBase (by decide)).trans hxg_base,
      (hy_pres regB (by decide)).trans hxg_b⟩
    · apply List.ext_getElem
      · simp [toMemState, hy_mem0, n]
      · intro j hj1 hj2
        have hshift_eq : shiftMem 1 y.mem = writeSubword w (shiftMem 1 xg.mem) b n val := by
          change (fun a => y.mem (1 + a)) = _
          rw [← hxg_base, ← hxg_b, ← hxg_idx, ← hxg_val]
          exact hy_shift
        rw [getElem_abs, hshift_eq]
        by_cases hjn : j < n
        · have hj_abs : j < (abs w b (toMemState x)).length := by simpa [toMemState] using hjn
          rw [List.getElem_append_left hj_abs, getElem_abs,
            readSubword_writeSubword_of_ne _ hw hb (by omega)]
          exact readSubword_congr hw hb hjn hxg_below
        · have hjeq : j = n := by
            simp only [length_abs, toMemState] at hj1
            omega
          subst hjeq
          have hlen : (abs w b (toMemState x)).length ≤ n := by simp [toMemState, n]
          rw [List.getElem_append_right hlen]
          simp [readSubword_writeSubword_self _ hw hb hval_fits, val]
    · simpa [toMemState, n] using hy_fr_eq
  exact (e₁.seq_eq (e₂.seq_eq (e₃.seq_eq (e₄.seq_eq (e₅.seq_eq
    (e₆.seq_eq (e₇.seq_eq (e₈.seq_eq (e_grow_branch.seq e_tail))))))))).mono
      (by decide) fun _ h => h

/-- Machine-level `RCode .standard 16` procedure for popping the last item from the resizable array
(`≤ 51` instructions). Sets `regRet = 0` when the array is empty (`none`), or `regRet = 1` and
`regVal = v` when popping `some v`. -/
def popArrayCode : RCode .standard 16 :=
  .seq (.op (.const regTmp1 0)) <|
  .seq (.op (.load regIdx regTmp1)) <|
  .branch (.eq regIdx regTmp1)
    (.op (.const regRet 0))
    (.seq (.op (.const regRet 1)) <|
     .seq (.op (.bin .sub regIdx regIdx regRet)) <|
     .seq (.op (.store regTmp1 regIdx)) <|
     .seq readSubwordCode <|
     .seq (RCode.ofCode subwordHeaderCode) <|
     .seq (.op (.const regTmp2 1)) <|
     .seq (.op (.const regTmp1 0)) <|
          (.branch (.eq regOff regTmp1)
            (.shrink regTmp2)
            (.branch (.lt regLow regB)
              (.shrink regTmp2)
              (.op (.const regTmp1 0)))))

/-- `popArrayCode` executes in at most `51` `WordRAM` instructions, preserves `Bounded w` and
`Inv w b` (`y.frontier = 1 + packedWords w b (n - 1)`), updates `abs w b (toMemState y)` to
`(abs w b (toMemState x)).dropLast`, and returns `(abs w b (toMemState x)).getLast?` via
`(y.regs regRet, y.regs regVal)`. -/
theorem popArrayCode_exec {w b : ℕ} {x : RData 16}
    (hx : x.Bounded w) (hb_pos : 0 < b) (hb : b ≤ w)
    (hinv : Inv w b (toMemState x))
    (hbase : x.regs regBase = 1) (hb_reg : x.regs regB = b)
    (hbitOff : Fits w (((abs w b (toMemState x)).length - 1) * b)) :
    RDemonicExec w popArrayCode x 51 fun y =>
      y.Bounded w ∧
        Inv w b (toMemState y) ∧
        abs w b (toMemState y) = (abs w b (toMemState x)).dropLast ∧
        y.frontier = 1 + packedWords w b ((abs w b (toMemState x)).length - 1) ∧
        (if (abs w b (toMemState x)).isEmpty then y.regs regRet = 0
         else y.regs regRet = 1 ∧ some (y.regs regVal) = (abs w b (toMemState x)).getLast?) ∧
        y.regs regBase = 1 ∧
        y.regs regB = b := by
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  have hw_ne : w ≠ 0 := by omega
  set n := x.mem 0
  have hpos_fr : 0 < x.frontier := by
    have : x.frontier = 1 + packedWords w b n := hinv.frontier_eq
    omega
  set x₁ := x.set regTmp1 0
  have e₁ : RDemonicExec (B := .standard) w (.op (.const regTmp1 0)) x 1 (· = x₁) :=
    RDemonicExec.const (fits_zero w)
  set x₂ := x₁.set regIdx n
  have e₂ : RDemonicExec (B := .standard) w (.op (.load regIdx regTmp1)) x₁ 1 (· = x₂) := by
    rw [show x₂ = x₁.set regIdx (x₁.mem (x₁.regs regTmp1)) by rfl]
    exact RDemonicExec.load hpos_fr
  have hx₂_bdd : x₂.Bounded w := (hx.set (fits_zero w)).set (hx.mem_fits 0)
  by_cases hn0 : n = 0
  · have hcond : (Cond.eq regIdx regTmp1).Holds x₂.toData := by
      change n = 0
      exact hn0
    set x₃ := x₂.set regRet 0
    have e₃ : RDemonicExec (B := .standard) w (.op (.const regRet 0)) x₂ 1 (· = x₃) :=
      RDemonicExec.const (fits_zero w)
    refine (e₁.seq_eq (e₂.seq_eq (RDemonicExec.branch_pos hcond e₃))).mono (by decide) ?_
    rintro _ rfl
    have habs_nil : abs w b (toMemState x) = [] := by
      simp [abs, n, hn0]
    have hto_eq : toMemState x₃ = toMemState x := rfl
    refine ⟨hx₂_bdd.set (fits_zero w), hinv, ?_, ?_, ?_, hbase, hb_reg⟩
    · rw [hto_eq, habs_nil]; rfl
    · rw [habs_nil]
      change x.frontier = 1 + packedWords w b 0
      exact hinv.frontier_eq.trans (by rw [show (toMemState x).mem 0 = 0 from hn0])
    · rw [habs_nil]
      rfl
  · have hcond : ¬ (Cond.eq regIdx regTmp1).Holds x₂.toData := hn0
    set m := n - 1
    have hmn : m + 1 = n := by omega
    have hm_lt : m < n := by omega
    have hm_fits : Fits w m := (hx.mem_fits 0).of_le (Nat.sub_le n 1)
    have hm_bitOff : Fits w (m * b) := by simpa [toMemState, m, n] using hbitOff
    set x₃ := x₂.set regRet 1
    have e₃ : RDemonicExec (B := .standard) w (.op (.const regRet 1)) x₂ 1 (· = x₃) :=
      RDemonicExec.const (fits_one hw_ne)
    set x₄ := x₃.set regIdx m
    have e₄ : RDemonicExec w (.op (.bin .sub regIdx regIdx regRet)) x₃ 1 (· = x₄) :=
      RDemonicExec.bin hm_fits
    set x₅ := x₄.write 0 m
    have e₅ : RDemonicExec (B := .standard) w (.op (.store regTmp1 regIdx)) x₄ 1 (· = x₅) := by
      rw [show x₅ = x₄.write (x₄.regs regTmp1) (x₄.regs regIdx) by rfl]
      exact RDemonicExec.store hpos_fr
    have hx₅_bdd : x₅.Bounded w :=
      ((hx₂_bdd.set (fits_one hw_ne)).set hm_fits).write hpos_fr hm_fits
    have hfront5 : x₅.regs regBase + packedWords w (x₅.regs regB) n ≤ x₅.frontier := by
      change x.regs regBase + packedWords w (x.regs regB) n ≤ x.frontier
      rw [hbase, hb_reg]
      exact le_of_eq hinv.frontier_eq.symm
    have e₆ : RDemonicExec w readSubwordCode x₅ 31 fun x₆ =>
        x₆.Bounded w ∧
        x₆.mem = x₅.mem ∧
        x₆.frontier = x₅.frontier ∧
        x₆.regs regVal =
          readSubword w (fun a => x₅.mem (x₅.regs regBase + a))
            (x₅.regs regB) (x₅.regs regIdx) ∧
        x₆.regs regOp = x₅.regs regOp ∧
        x₆.regs regIdx = x₅.regs regIdx ∧
        x₆.regs regRet = x₅.regs regRet ∧
        x₆.regs regBase = x₅.regs regBase ∧
        x₆.regs regB = x₅.regs regB :=
      readSubwordCode_exec hx₅_bdd
        (by change 0 < x.regs regB; rw [hb_reg]; exact hb_pos)
        (by change x.regs regB ≤ w; rw [hb_reg]; exact hb)
        hm_lt
        (by change Fits w (m * x.regs regB); rw [hb_reg]; exact hm_bitOff)
        hfront5
    have e_tail : ∀ x₆,
        (x₆.Bounded w ∧
          x₆.mem = x₅.mem ∧
          x₆.frontier = x₅.frontier ∧
          x₆.regs regVal =
            readSubword w (fun a => x₅.mem (x₅.regs regBase + a))
              (x₅.regs regB) (x₅.regs regIdx) ∧
          x₆.regs regOp = x₅.regs regOp ∧
          x₆.regs regIdx = x₅.regs regIdx ∧
          x₆.regs regRet = x₅.regs regRet ∧
          x₆.regs regBase = x₅.regs regBase ∧
          x₆.regs regB = x₅.regs regB) →
        RDemonicExec w
          (.seq (RCode.ofCode subwordHeaderCode) <|
           .seq (.op (.const regTmp2 1)) <|
           .seq (.op (.const regTmp1 0)) <|
                (.branch (.eq regOff regTmp1)
                  (.shrink regTmp2)
                  (.branch (.lt regLow regB)
                    (.shrink regTmp2)
                    (.op (.const regTmp1 0)))))
          x₆ 13 fun y =>
            y.Bounded w ∧
              Inv w b (toMemState y) ∧
              abs w b (toMemState y) = (abs w b (toMemState x)).dropLast ∧
              y.frontier = 1 + packedWords w b ((abs w b (toMemState x)).length - 1) ∧
              (if (abs w b (toMemState x)).isEmpty then y.regs regRet = 0
               else y.regs regRet = 1 ∧ some (y.regs regVal) = (abs w b (toMemState x)).getLast?) ∧
              y.regs regBase = 1 ∧
              y.regs regB = b := by
      rintro x₆ ⟨hx₆_bdd, hx₆_mem, hx₆_fr, hx₆_val, _, hx₆_idx, hx₆_ret, hx₆_base, hx₆_b⟩
      have hx₆_idx' : x₆.regs regIdx = m := hx₆_idx
      have hx₆_ret' : x₆.regs regRet = 1 := hx₆_ret
      have hx₆_base' : x₆.regs regBase = 1 := hx₆_base.trans hbase
      have hx₆_b' : x₆.regs regB = b := hx₆_b.trans hb_reg
      have haddr0_lt : 1 + (m * b) / w < x.frontier := by
        have hfr_x : x.frontier = 1 + packedWords w b n := hinv.frontier_eq
        rw [hfr_x]
        exact Nat.add_lt_add_left (wordIdx_lt_packedWords_of_pos hw hb_pos hm_lt) 1
      have haddr0_fits : Fits w (x₆.regs regBase + (x₆.regs regIdx * x₆.regs regB) / w) := by
        rw [hx₆_base', hx₆_idx', hx₆_b']
        exact hx.frontier_fits.of_le (le_of_lt haddr0_lt)
      obtain ⟨d₇, hd₇_exec, hd₇_mem, _, _, hd₇_off, hd₇_low, hd₇_pres⟩ :=
        subwordHeaderCode_exec (x := x₆.toData) hw
          (by change Fits w (x₆.regs regIdx * x₆.regs regB); rw [hx₆_idx', hx₆_b']; exact hm_bitOff)
          haddr0_fits
      set x₇ : RData 16 := ⟨d₇.regs, d₇.mem, x₆.frontier⟩
      have e₇ : RDemonicExec w (RCode.ofCode subwordHeaderCode) x₆ 6 (· = x₇) :=
        RDemonicExec.of_exec_regOnly (by decide) hd₇_exec
      have hx₇_bdd : x₇.Bounded w :=
        ⟨hd₇_exec.bounded hx₆_bdd.1, hx₆_bdd.2.1,
          by change ∀ a ≥ x₆.frontier, d₇.mem a = 0; rw [hd₇_mem]; exact hx₆_bdd.2.2⟩
      set x₈ := x₇.set regTmp2 1
      have e₈ : RDemonicExec (B := .standard) w (.op (.const regTmp2 1)) x₇ 1 (· = x₈) :=
        RDemonicExec.const (fits_one hw_ne)
      set x₉ := x₈.set regTmp1 0
      have e₉ : RDemonicExec (B := .standard) w (.op (.const regTmp1 0)) x₈ 1 (· = x₉) :=
        RDemonicExec.const (fits_zero w)
      have hx₉_bdd : x₉.Bounded w := (hx₇_bdd.set (fits_one hw_ne)).set (fits_zero w)
      have hx₉_mem : x₉.mem = Function.update x.mem 0 m := hd₇_mem.trans hx₆_mem
      have hx₉_fr : x₉.frontier = x.frontier := hx₆_fr
      have hx₉_off : x₉.regs regOff = (m * b) % w := by
        change d₇.regs regOff = (m * b) % w
        rw [hd₇_off]
        change (x₆.regs regIdx * x₆.regs regB) % w = (m * b) % w
        rw [hx₆_idx', hx₆_b']
      have hx₉_low : x₉.regs regLow = w - (m * b) % w := by
        change d₇.regs regLow = w - (m * b) % w
        rw [hd₇_low]
        change w - (x₆.regs regIdx * x₆.regs regB) % w = w - (m * b) % w
        rw [hx₆_idx', hx₆_b']
      have hx₉_b : x₉.regs regB = b := (hd₇_pres regB (by decide)).trans hx₆_b'
      have hx₉_base : x₉.regs regBase = 1 := (hd₇_pres regBase (by decide)).trans hx₆_base'
      have hx₉_ret : x₉.regs regRet = 1 := (hd₇_pres regRet (by decide)).trans hx₆_ret'
      have hx₉_val : x₉.regs regVal = readSubword w (shiftMem 1 x.mem) b m := by
        have h1 : x₉.regs regVal = x₆.regs regVal := hd₇_pres regVal (by decide)
        have hshift5 : (fun a => x₅.mem (x₅.regs regBase + a)) = shiftMem 1 x.mem := by
          change (fun a => Function.update x.mem 0 m (x.regs regBase + a)) = shiftMem 1 x.mem
          rw [hbase]
          exact shiftMem_update_lt x.mem Nat.zero_lt_one m
        rw [h1, hx₆_val, hshift5]
        change readSubword w (shiftMem 1 x.mem) (x.regs regB) m = _
        rw [hb_reg]
      have hne_abs : abs w b (toMemState x) ≠ [] := by
        intro hnil
        have := congrArg List.length hnil
        simp only [length_abs, toMemState, List.length_nil] at this
        exact hn0 this
      have hgetLast : (abs w b (toMemState x)).getLast? =
          some (readSubword w (shiftMem 1 x.mem) b m) := by
        rw [List.getLast?_eq_some_getLast hne_abs, Option.some.injEq, List.getLast_eq_getElem]
        simp [m, n, toMemState]
      have hisEmpty : (abs w b (toMemState x)).isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr hne_abs
      have hsucc : packedWords w b (m + 1) ≤ packedWords w b m + 1 := packedWords_succ_le hb
      have hmono : packedWords w b m ≤ packedWords w b (m + 1) := packedWords_mono (Nat.le_succ m)
      let P_pop : RData 16 → Prop := fun y =>
        y.Bounded w ∧
          Inv w b (toMemState y) ∧
          abs w b (toMemState y) = (abs w b (toMemState x)).dropLast ∧
          y.frontier = 1 + packedWords w b ((abs w b (toMemState x)).length - 1) ∧
          (if (abs w b (toMemState x)).isEmpty then y.regs regRet = 0
           else y.regs regRet = 1 ∧
             some (y.regs regVal) = (abs w b (toMemState x)).getLast?) ∧
          y.regs regBase = 1 ∧
          y.regs regB = b
      let y_sh : RData 16 :=
        ⟨x₉.regs, clear x₉.mem (x₉.frontier - x₉.regs regTmp2) (x₉.regs regTmp2),
          x₉.frontier - x₉.regs regTmp2⟩
      have h_shrink_proof : packedWords w b m < packedWords w b (m + 1) → P_pop y_sh := by
        intro hlt_pw
        have hpw_eq : packedWords w b n = packedWords w b m + 1 := by
          rw [← hmn]
          omega
        have hy_bdd : y_sh.Bounded w :=
          hx₉_bdd.shrink (by change 1 ≤ x₉.frontier; rw [hx₉_fr]; exact hpos_fr)
        have hy_fr : y_sh.frontier = 1 + packedWords w b m := by
          change x₉.frontier - 1 = 1 + packedWords w b m
          rw [hx₉_fr, show x.frontier = 1 + packedWords w b n from hinv.frontier_eq, hpw_eq]
          omega
        have hy_mem0 : y_sh.mem 0 = m := by
          change clear x₉.mem (x₉.frontier - 1) 1 0 = m
          have hnot0 : ¬ (Block.mk (x₉.frontier - 1) 1).Owns 0 := by
            rw [hx₉_fr, show x.frontier = 1 + packedWords w b n from hinv.frontier_eq, hpw_eq]
            simp only [Block.Owns]; omega
          rw [clear_of_not_owns hnot0, hx₉_mem, Function.update_self]
        have hinv_y : Inv w b (toMemState y_sh) :=
          ⟨canonical_toMemState hy_bdd,
            by change y_sh.frontier = 1 + packedWords w b (y_sh.mem 0); rw [hy_fr, hy_mem0]⟩
        refine ⟨hy_bdd, hinv_y, ?_, by simpa [toMemState, m, n] using hy_fr, ?_, hx₉_base, hx₉_b⟩
        · apply List.ext_getElem
          · simp [toMemState, hy_mem0, m, n]
          · intro j hj1 hj2
            rw [getElem_abs, List.getElem_dropLast, getElem_abs]
            have hj_m : j < m := by simpa [toMemState, hy_mem0] using hj1
            apply readSubword_congr hw hb hj_m
            intro a ha
            change clear x₉.mem (x₉.frontier - 1) 1 (1 + a) = x.mem (1 + a)
            have hnot : ¬ (Block.mk (x₉.frontier - 1) 1).Owns (1 + a) := by
              rw [hx₉_fr, show x.frontier = 1 + packedWords w b n from hinv.frontier_eq, hpw_eq]
              simp only [Block.Owns]; omega
            rw [clear_of_not_owns hnot, hx₉_mem, Function.update_of_ne (by omega)]
        · rw [hisEmpty]
          refine ⟨hx₉_ret, ?_⟩
          change some (x₉.regs regVal) = _
          rw [hx₉_val, hgetLast]
      by_cases hoff0 : (m * b) % w = 0
      · have hcond1 : (Cond.eq regOff regTmp1).Holds x₉.toData := by
          change x₉.regs regOff = 0
          rw [hx₉_off, hoff0]
        have hlt_pw : packedWords w b m < packedWords w b (m + 1) :=
          (packedWords_lt_succ_iff hw hb_pos hb).mpr (Or.inl hoff0)
        have e_sh := RDemonicExec.shrink (B := .standard) (w := w) (x := x₉) (kReg := regTmp2)
          (P := P_pop)
          (by change 1 ≤ x₉.frontier; rw [hx₉_fr]; exact hpos_fr) (h_shrink_proof hlt_pw)
        exact (e₇.seq_eq (e₈.seq_eq (e₉.seq_eq (RDemonicExec.branch_pos hcond1 e_sh)))).mono
          (by decide) fun _ h => h
      · have hcond1 : ¬ (Cond.eq regOff regTmp1).Holds x₉.toData := by
          change x₉.regs regOff ≠ 0
          rw [hx₉_off]; exact hoff0
        by_cases hlow : w - (m * b) % w < b
        · have hcond2 : (Cond.lt regLow regB).Holds x₉.toData := by
            change x₉.regs regLow < x₉.regs regB
            rw [hx₉_low, hx₉_b]; exact hlow
          have hlt_pw : packedWords w b m < packedWords w b (m + 1) :=
            (packedWords_lt_succ_iff hw hb_pos hb).mpr (Or.inr hlow)
          have e_sh := RDemonicExec.shrink (B := .standard) (w := w) (x := x₉) (kReg := regTmp2)
            (P := P_pop)
            (by change 1 ≤ x₉.frontier; rw [hx₉_fr]; exact hpos_fr) (h_shrink_proof hlt_pw)
          exact (e₇.seq_eq (e₈.seq_eq (e₉.seq_eq
            (RDemonicExec.branch_neg hcond1 (RDemonicExec.branch_pos hcond2 e_sh))))).mono
            (by decide) fun _ h => h
        · have hcond2 : ¬ (Cond.lt regLow regB).Holds x₉.toData := by
            change ¬ (x₉.regs regLow < x₉.regs regB)
            rw [hx₉_low, hx₉_b]; exact hlow
          have hnot_lt : ¬ (packedWords w b m < packedWords w b (m + 1)) := by
            rw [packedWords_lt_succ_iff hw hb_pos hb]
            exact fun h => h.elim hoff0 hlow
          have hpw_eq : packedWords w b n = packedWords w b m := by
            rw [← hmn]
            omega
          have e_sk :=
            RDemonicExec.const (B := .standard) (w := w) (x := x₉) (d := regTmp1) (fits_zero w)
          refine (e₇.seq_eq (e₈.seq_eq (e₉.seq_eq
            (RDemonicExec.branch_neg hcond1 (RDemonicExec.branch_neg hcond2 e_sk))))).mono
            (by decide) ?_
          rintro _ rfl
          have hx₉_fr_eq : (x₉.set regTmp1 0).frontier = 1 + packedWords w b m := by
            change x₉.frontier = 1 + packedWords w b m
            rw [hx₉_fr, show x.frontier = 1 + packedWords w b n from hinv.frontier_eq, hpw_eq]
          have hx₉_mem0 : (x₉.set regTmp1 0).mem 0 = m := by
            change x₉.mem 0 = m
            rw [hx₉_mem, Function.update_self]
          have hinv_x9 : Inv w b (toMemState (x₉.set regTmp1 0)) :=
            ⟨canonical_toMemState (hx₉_bdd.set (fits_zero w)), by
              change (x₉.set regTmp1 0).frontier = 1 + packedWords w b ((x₉.set regTmp1 0).mem 0)
              rw [hx₉_fr_eq, hx₉_mem0]⟩
          refine ⟨hx₉_bdd.set (fits_zero w), hinv_x9, ?_,
            by simpa [toMemState, m, n] using hx₉_fr_eq, ?_, hx₉_base, hx₉_b⟩
          · apply List.ext_getElem
            · simp only [length_abs, List.length_dropLast]
              exact hx₉_mem0
            · intro j hj1 hj2
              rw [getElem_abs, List.getElem_dropLast, getElem_abs]
              have hshift9 : shiftMem 1 (x₉.set regTmp1 0).mem = shiftMem 1 x.mem := by
                change shiftMem 1 x₉.mem = shiftMem 1 x.mem
                rw [hx₉_mem]
                exact shiftMem_update_lt x.mem Nat.zero_lt_one m
              rw [hshift9]
          · rw [hisEmpty]
            refine ⟨hx₉_ret, ?_⟩
            change some (x₉.regs regVal) = _
            rw [hx₉_val, hgetLast]
    have e_branch_neg := e₃.seq_eq (e₄.seq_eq (e₅.seq_eq (e₆.seq e_tail)))
    exact (e₁.seq_eq (e₂.seq_eq (RDemonicExec.branch_neg hcond e_branch_neg))).mono
      (by decide) fun _ h => h

/-! ## Client theorems: subroutine usage and multi-array memory reuse -/

/-- A client program over `spec w b` that uses the resizable array as a subroutine: it appends `x`,
appends `y`, reads index `0`, updates index `0` to `y`, pops the last element, and reads index
`0`. -/
def subroutineClient (w b x y : ℕ) : (spec w b).Client (ℕ × Option ℕ × ℕ) :=
  .liftBind (.append x) fun _ =>
    .liftBind (.append y) fun _ =>
      .liftBind (.read 0) fun r0 =>
        .liftBind (.write 0 y) fun _ =>
          .liftBind .pop fun popped =>
            .liftBind (.read 0) fun r1 =>
              .pure (r0, popped, r1)

/-- **Client Theorem 1 (Subroutine execution over `Refinement`).**
Linking `subroutineClient w b x y` through `refinement w b hb_pos hb` and running it on
`Memory.Resizable.spec w` from `initState` executes validly, returns `(x, some y, y)`, leaves the
concrete memory at `1 + packedWords w b 1 = 2` words (having grown to `1 + packedWords w b 2` words
and shrunk back on `pop`), and costs at most `42` (`= 6 * 7`) memory units. -/
theorem subroutineClient_correct_and_tight {w b x y : ℕ}
    (hb_pos : 0 < b) (hb : b ≤ w)
    (hx : Fits b x) (hy : Fits b y)
    (hw2 : Fits w 3) :
    let R := refinement w b hb_pos hb
    let p := subroutineClient w b x y
    let linked := link R.methods p
    (Resizable.spec w).ValidHistory initState
        ((Resizable.spec w).clientHistory initState linked) ∧
      (Resizable.spec w).clientResult initState linked = (x, some y, y) ∧
      R.abs ((Resizable.spec w).clientState initState linked) = [y] ∧
      ((Resizable.spec w).clientState initState linked).frontier = 1 + packedWords w b 1 ∧
      (Resizable.spec w).totalCost Resizable.charge initState
        ((Resizable.spec w).clientHistory initState linked) ≤ 42 := by
  intro R p linked
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  obtain ⟨hinv0, habs0⟩ := inv_initState (w := w) (b := b) hw
  have hpw1_le : packedWords w b 1 ≤ 1 := by
    have := packedWords_succ_le (w := w) (b := b) (n := 0) hb
    simpa [packedWords_zero] using this
  have hpw2_le : packedWords w b 2 ≤ 2 := by
    have h12 : packedWords w b 2 ≤ packedWords w b 1 + 1 :=
      packedWords_succ_le (w := w) (b := b) (n := 1) hb
    omega
  have hv_client : (spec w b).ValidHistory (R.abs initState)
      ((spec w b).clientHistory (R.abs initState) p) := by
    change (spec w b).ValidHistory (abs w b initState)
      ((spec w b).clientHistory (abs w b initState) p)
    rw [habs0]
    dsimp only [p, subroutineClient, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient, StateTransitionSpec.stepFn, step,
      StateTransitionSpec.ValidHistory]
    dsimp [spec, StateTransitionSpec.ofFn, valid]
    refine ⟨⟨hx, hw2.of_le (by omega), hw2.of_le (by omega)⟩, ?_⟩
    refine ⟨⟨hy, hw2.of_le (by omega), hw2.of_le (by omega)⟩, ?_⟩
    exact ⟨by simp, ⟨⟨by simp, hy⟩, ⟨trivial, ⟨by simp, trivial⟩⟩⟩⟩
  obtain ⟨hvh_linked, hres_linked, habs_linked, hinv_linked⟩ :=
    R.simulates_client p hinv0 hv_client
  have hcost_linked := (amortized w b hb_pos hb).client p hinv0 hv_client
  have hres_spec : (spec w b).clientResult (R.abs initState) p = (x, some y, y) := by
    change (spec w b).clientResult (abs w b initState) p = (x, some y, y)
    rw [habs0]
    rfl
  have hst_spec : (spec w b).clientState (R.abs initState) p = [y] := by
    change (spec w b).clientState (abs w b initState) p = [y]
    rw [habs0]
    rfl
  have hhist_len : ((spec w b).clientHistory (R.abs initState) p).length = 6 := by
    change ((spec w b).clientHistory (abs w b initState) p).length = 6
    rw [habs0]
    rfl
  rw [(spec w b).totalCost_const, hhist_len] at hcost_linked
  have hfr_fin :
      ((Resizable.spec w).clientState initState linked).frontier = 1 + packedWords w b 1 := by
    have hfr := hinv_linked.frontier_eq
    have hlen : ((Resizable.spec w).clientState initState linked).mem 0 = 1 := by
      rw [← length_abs w b, show abs w b _ = R.abs _ from rfl, habs_linked, hst_spec]
      rfl
    rw [hfr, hlen]
  exact ⟨hvh_linked, hres_linked.trans hres_spec, habs_linked.trans hst_spec, hfr_fin,
    by omega⟩

/-- **Client Theorem 2 (Two resizable arrays in one shared memory reusing released words).**
Consider two resizable `b`-bit arrays `s₀, s₁` sharing memory via `Resizable.packTwoWay s₀ s₁`.
1. At any step where `s₀` holds `n₀` items (`PackedInv w b n₀ s₀`) and `s₁` holds `n₁` items
   (`PackedInv w b n₁ s₁`) with `n₀ + n₁ = m`, the combined memory
   `(Resizable.packTwoWay s₀ s₁).frontier` is at most `packedWords w b m + 1` words
   (`≤ m * b + 2 * w - 1` bits) rather than `2 * packedWords w b m` words.
2. When `s₀` pops an item across a word boundary (releasing `1` word via `.shrink 1`) and `s₁`
   appends an item across a word boundary (allocating `1` word via `.grow 1`), `s₁` reuses the
   word released by `s₀` so the combined word count `(Resizable.packTwoWay s₀' s₁').frontier`
   is unchanged. -/
theorem twoArrays_reuse_released_memory {w b n₀ n₁ m : ℕ} {s₀ s₁ : Memory.State}
    (hw : 0 < w)
    (hinv₀ : PackedInv w b n₀ s₀) (hinv₁ : PackedInv w b n₁ s₁)
    (hsum : n₀ + n₁ = m) :
    (Resizable.packTwoWay s₀ s₁).frontier ≤ packedWords w b m + 1 ∧
      Resizable.spaceBits w (Resizable.packTwoWay s₀ s₁) ≤ m * b + 2 * w - 1 ∧
      (∀ (_ : 1 ≤ s₀.frontier),
        (Resizable.packTwoWay
          (Resizable.step s₀ (.shrink 1)).1
          (Resizable.step s₁ (.grow 1)).1).frontier =
          (Resizable.packTwoWay s₀ s₁).frontier) := by
  have hfr : (Resizable.packTwoWay s₀ s₁).frontier =
      packedWords w b n₀ + packedWords w b n₁ := by
    rw [Resizable.packTwoWay_frontier, hinv₀.frontier_eq, hinv₁.frontier_eq]
  have hwords_le : (Resizable.packTwoWay s₀ s₁).frontier ≤ packedWords w b m + 1 := by
    rw [hfr, ← hsum]
    exact packedWords_add_le hw
  have hbits_le : Resizable.spaceBits w (Resizable.packTwoWay s₀ s₁) ≤ m * b + 2 * w - 1 := by
    unfold Resizable.spaceBits
    have h0 : packedWords w b n₀ * w ≤ n₀ * b + (w - 1) := packedWords_mul_le
    have h1 : packedWords w b n₁ * w ≤ n₁ * b + (w - 1) := packedWords_mul_le
    rw [hfr, Nat.mul_add, Nat.mul_comm w (packedWords w b n₀),
      Nat.mul_comm w (packedWords w b n₁)]
    have hmb : n₀ * b + n₁ * b = m * b := by
      rw [← hsum, Nat.add_mul]
    omega
  refine ⟨hwords_le, hbits_le, fun hk => ?_⟩
  exact Resizable.packTwoWay_shrink_grow_frontier s₀ s₁ hk

/-- **Client Theorem 3 (Two resizable arrays in a single linear tape `s : Memory.State` via
`ChunkedTape` without `Ω(n)` shifting).**
Consider two resizable `b`-bit arrays `s₀, s₁` hosted in a **single** linear word-resizable memory
state `s : Memory.State` via `Resizable.ChunkedTape.Realizes 2 1 K_max s ![s₀, s₁]`:
1. At any step where `s₀` holds `n₀` items (`PackedInv w b n₀ s₀`) and `s₁` holds `n₁` items
   (`PackedInv w b n₁ s₁`) with `n₀ + n₁ = m`, the single physical tape `s` has frontier at most
   `Resizable.ChunkedTape.headerWords 2 K_max + packedWords w b m + 1` words.
2. Reading logical word `a < s_i.frontier` of array `i ∈ {0, 1}` on the single physical tape via
   `Resizable.ChunkedTape.readWord 2 1 K_max i a` returns `s_i.mem a` in `2` single-tape operations
   (`O(1)` worst-case time).
3. When array `0` releases `1` word via `releaseWord1` and array `1` allocates `1` word via
   `allocWord1` on the single physical tape `s`, the combined execution runs in `15` single-tape
   operations (`O(1)` worst-case time, with **no** `Ω(n)` shifting) and leaves `s.frontier`
   unchanged (`s_final.frontier = s.frontier`). -/
theorem twoArrays_singleTape_reuse {w b n₀ n₁ m K_max : ℕ} {s s₀ s₁ : Memory.State}
    (hw : 0 < w)
    (hinv₀ : PackedInv w b n₀ s₀) (hinv₁ : PackedInv w b n₁ s₁)
    (hsum : n₀ + n₁ = m)
    (hreal : Resizable.ChunkedTape.Realizes 2 1 K_max s ![s₀, s₁]) :
    s.frontier ≤ Resizable.ChunkedTape.headerWords 2 K_max + packedWords w b m + 1 ∧
      (∀ (i : Fin 2) (a : ℕ), a < (![s₀, s₁] i).frontier →
        (Resizable.spec w).clientResult s (Resizable.ChunkedTape.readWord 2 1 K_max i a) =
          (![s₀, s₁] i).mem a ∧
        ((Resizable.spec w).clientHistory s (Resizable.ChunkedTape.readWord 2 1 K_max i a)).length =
          2) ∧
      (∀ (N_chk : ℕ) (_ : 1 ≤ s.frontier),
        let prog : Resizable.Prog ℕ := do
          Resizable.ChunkedTape.releaseWord1 2 K_max N_chk 0
          Resizable.ChunkedTape.allocWord1 2 K_max (N_chk - 1) 1
        ((Resizable.spec w).clientState s prog).frontier = s.frontier ∧
          ((Resizable.spec w).clientHistory s prog).length = 15) := by
  have hfr_eq := hreal.frontier_eq_of_unitChunk
  have htot : Resizable.MultiSegment.totalWords ![s₀, s₁] =
      packedWords w b n₀ + packedWords w b n₁ := by
    simp [Resizable.MultiSegment.totalWords, Fin.sum_univ_two, hinv₀.frontier_eq, hinv₁.frontier_eq]
  have hpw_le : packedWords w b n₀ + packedWords w b n₁ ≤ packedWords w b m + 1 := by
    rw [← hsum]
    exact packedWords_add_le hw
  refine ⟨by omega, fun i a ha => ?_, fun N_chk hs => ?_⟩
  · obtain ⟨hres, _, hlen⟩ := Resizable.ChunkedTape.readWord_spec w hreal i ha
    exact ⟨hres, hlen⟩
  · exact Resizable.ChunkedTape.releaseWord1_then_allocWord1_spec w 2 K_max N_chk s 0 1 hs

end Cslib.DataStructure.DynamicArray.ResizableWord
