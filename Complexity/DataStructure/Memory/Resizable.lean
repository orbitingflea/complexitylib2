/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Resizable
public import Complexity.DataStructure.Memory.Field
public import Complexity.DataStructure.StateTransition.Refinement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log

/-!
# Word-granular resizable memory (Virtual Memory model)

This module defines the word-granular resizable memory model (the **Virtual Memory model** of
`[LLYZ23a]` §2.1 and `[KLZ26]` §5.1) on top of `Cslib.DataStructure.Memory`.

A data structure operating in a word-granular virtual memory owns a 0-indexed prefix
`[0, s.frontier)` of `w`-bit words in `s : Memory.State`, where `s.frontier` (`L` in the papers)
is the current number of allocated words at the given point in time. In addition to reading and
writing allocated words (`a < s.frontier`), the data structure can **grow** (`grow k`,
`growDirty k`) or **shrink** (`shrink k`) the active prefix `[0, s.frontier)` by whole words.

## Design choices and rejected alternatives

1. **Reusing `Memory.State` (`mem : ℕ → ℕ`, `frontier : ℕ`) vs. a dependent state type bundling
   proofs (`State w` with `word_bounded` and `outside_zero` fields)**:
   - *Choice*: Reuse `Cslib.DataStructure.Memory.State` directly, paired with the invariant
     predicates `Memory.WellFormed w s` (`Fits w s.frontier` and `∀ a, Fits w (s.mem a)`) and
     `Canonical w s` (`WellFormed w s ∧ ZeroAbove s`).
   - *Rejected alternative*: Defining a separate dependent `structure State (w : ℕ)` carrying proof
     fields `∀ a < frontier, Fits w (mem a)` and `∀ a ≥ frontier, mem a = 0`.
   - *Reason*: Reusing `Memory.State` provides zero-coercion interoperability with all existing
     `Complexity/DataStructure/Memory/*` and `Complexity/Computability/WordRAM/*` modules (`Block`,
     `Block.Owns`, `Block.footprint`, `Block.Realizes`, `clear`, `Memory.copy`, and
     `WordRAM.Realization.memoryState`), and avoids reconstructing proof terms inside every state
     update.

2. **Both demonic relational semantics (`demonicSpec w`) and deterministic functional semantics
   (`spec w`) vs. only one**:
   - *Choice*: Define both `demonicSpec w` (where `.growDirty k` demonically assigns arbitrary
     `w`-bit words to `[s.frontier, s.frontier + k)`, matching `[KLZ26]` §5.1 Footnotes 10 & 13)
     and the deterministic `spec w` (`HasStepFn`, where `.grow k` and `.growDirty k` zero
     `[s.frontier, s.frontier + k)` and `.shrink k` zeros `[s.frontier - k, s.frontier)`),
     together with a refinement certificate `refines_demonic : Refinement (demonicSpec w) (spec w)`.
   - *Rejected alternative*: Providing only deterministic `ofFn` transitions (which cannot express
     robustness against arbitrary dirty initial contents in newly grown words) or only relational
     transitions (which sacrifice `HasStepFn` functional evaluation `runClient` and executable
     `#eval` testing).

3. **Cost of resizing (`charge` and `unitCharge`)**:
   - *Choice*: `charge` assigns cost `1` to `read`, `write`, and `growDirty k`, and cost `max k 1`
     to `grow k` and `shrink k`. Thus single-word allocation `allocWord = grow 1` and release
     `releaseWord = shrink 1` (`L ← L ± 1` in `[LLYZ23a]` §2.1 and `[KLZ26]` §5.1) each cost `1`
     memory unit, while bulk zeroed allocation/release of `k` words pays `k` units for clearing.
   - *Rejected alternative*: Charging `k + 1` for `grow k` (which charges `2` for single-word
     `grow 1`) or charging `1` for arbitrary-size zeroed `grow k` (which would hide $\Theta(k)$
     clearing work on a physical Word RAM).

4. **Space measure (current size at every step + spillover + peak working space)**:
   - *Choice*: Measure space at any state `s` by `spaceWords s = s.frontier` words and
     `spaceBits w s = w * s.frontier` bits (plus `Nat.clog 2 K` bits when paired with a spillover
     $k \in [K]$ via `spilloverSpaceBits w K s`), and track intermediate working space along any
     operation sequence via `peakWords` and `EveryStepWordsLe`.
   - *Rejected alternative*: A single static high-water-mark constant `∃ S, ∀ t, s_t.frontier ≤ S`
     (`WordRAM.StateTransitionImpl.space_bound`), which cannot express bounds that shrink when
     keys or items are deleted.

5. **Frame condition (`UnchangedOutside`)**:
   - *Choice*:
     `UnchangedOutside s s' W := ∀ a < min s.frontier s'.frontier, a ∉ W → s'.mem a = s.mem a`.
   - *Rejected alternative*: Quantifying over `a < s.frontier` (which fails when `s'` shrinks below
     `s.frontier` and zeros the released suffix) or requiring fixed static `room` budgets as in
     `Memory.Framed` (which forbids shrinking).

6. **Composition of multiple structures with reuse of released memory (`MultiSegment`,
   `packTwoWay`, and `product`)**:
   - *Choice*: Provide `MultiSegment.spec w B` ($B$ independent resizable word-granular virtual
     memories with total space $\sum_{i < B} \ell_i$ words and automatic non-interference across
     indices $i \ne j$) together with `packTwoWay`, which multiplexes two resizable segments
     into a single `Resizable.State` of exact size $L = \ell_0 + \ell_1$ words so that words
     released by one structure are immediately reusable by the other.
   - *Rejected alternative*: Placing multiple resizable structures at fixed base addresses in one
     flat grow-only `Memory.spec w`, which prevents any structure from reusing cells released by
     another or growing past its neighbor's base address.

## Main definitions

* `Cslib.DataStructure.Memory.Resizable.Op`, `step`, `valid`, `spec`: deterministic word-granular
  resizable memory specification.
* `Cslib.DataStructure.Memory.Resizable.demonicStep`, `demonicSpec`, `refinesDemonic`: demonic
  relational specification with arbitrary `w`-bit initial contents on `growDirty`.
* `Cslib.DataStructure.Memory.Resizable.charge`, `unitCharge`: operation cost measures.
* `Cslib.DataStructure.Memory.Resizable.spaceWords`, `spaceBits`, `spilloverSpaceBits`,
  `peakWords`, `EveryStepWordsLe`: pointwise and working-space measures.
* `Cslib.DataStructure.Memory.Resizable.UnchangedOutside`: word-level frame condition across
  resizes.
* `Cslib.DataStructure.Memory.Resizable.MultiSegment.spec`, `packTwoWay`: multi-structure
  composition and single-memory multiplexing with reuse of released words.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory.Resizable

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open scoped BigOperators

/-! ## Empty state and zero-above invariant -/

/-- The empty memory state with all cells zeroed and `frontier = 0`. -/
def emptyState : State := ⟨fun _ => 0, 0⟩

/-- Every address at or above `s.frontier` holds `0`. -/
def ZeroAbove (s : State) : Prop :=
  ∀ a, s.frontier ≤ a → s.mem a = 0

@[simp]
theorem emptyState_frontier : emptyState.frontier = 0 := rfl

@[simp]
theorem emptyState_mem (a : ℕ) : emptyState.mem a = 0 := rfl

theorem wellFormed_emptyState (w : ℕ) : WellFormed w emptyState :=
  ⟨fits_zero w, fun _ => fits_zero w⟩

theorem zeroAbove_emptyState : ZeroAbove emptyState :=
  fun _ _ => rfl

/-! ## Operations and transitions -/

/-- Operations of a word-granular resizable memory (`[LLYZ23a]` §2.1, `[KLZ26]` §5.1). -/
inductive Op where
  /-- Read the `w`-bit word at address `a < frontier`. -/
  | read (a : ℕ)
  /-- Write the `w`-bit word `v` at address `a < frontier`. -/
  | write (a v : ℕ)
  /-- Grow the active prefix `[0, frontier)` by `k` zeroed words to `[0, frontier + k)`,
  returning the old `frontier`. -/
  | grow (k : ℕ)
  /-- Grow the active prefix `[0, frontier)` by `k` uninitialized words to `[0, frontier + k)`,
  returning the old `frontier`. -/
  | growDirty (k : ℕ)
  /-- Shrink the active prefix `[0, frontier)` by `k ≤ frontier` words to `[0, frontier - k)`,
  clearing the released suffix `[frontier - k, frontier)`. -/
  | shrink (k : ℕ)
  deriving DecidableEq, Repr

/-- Result type of each resizable-memory operation. -/
abbrev Op.Result : Op → Type
  | .read _ => ℕ
  | .write _ _ => Unit
  | .grow _ => ℕ
  | .growDirty _ => ℕ
  | .shrink _ => Unit

/-- Deterministic transition function for `Resizable.Op` on `Memory.State`. -/
def step (s : State) : (o : Op) → State × o.Result
  | .read a => (s, s.mem a)
  | .write a v => (⟨Function.update s.mem a v, s.frontier⟩, ())
  | .grow k => (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier)
  | .growDirty k => (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier)
  | .shrink k => (⟨clear s.mem (s.frontier - k) k, s.frontier - k⟩, ())

/-- Admissibility precondition at word width `w`: reads and writes stay within `[0, s.frontier)`,
written values fit `w` bits, growing keeps the new frontier fitting `w` bits, and shrinking
releases at most `s.frontier` words. -/
def valid (w : ℕ) (s : State) : Op → Prop
  | .read a => a < s.frontier
  | .write a v => a < s.frontier ∧ Fits w v
  | .grow k => Fits w (s.frontier + k)
  | .growDirty k => Fits w (s.frontier + k)
  | .shrink k => k ≤ s.frontier

instance (w : ℕ) (s : State) (o : Op) : Decidable (valid w s o) := by
  cases o <;> unfold valid <;> infer_instance

/-- Deterministic word-granular resizable memory specification at word width `w`. -/
abbrev spec (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := State) (Op := Op) (Result := Op.Result)
    step (valid w)

/-- Admissibility of a concrete history on `Resizable.spec w` is decidable. -/
instance decidableValidHistory (w : ℕ) (s : State) (os : List Op) :
    Decidable ((spec w).ValidHistory s os) := by
  induction os generalizing s with
  | nil => exact isTrue trivial
  | cons o os ih =>
    exact decidable_of_iff (valid w s o ∧ (spec w).ValidHistory (step s o).1 os) Iff.rfl

/-- Demonic relational transition at word width `w`: `.grow k` and `.growDirty k` permit any
post-state `s'` that preserves `s.mem` outside `[s.frontier, s.frontier + k)` (including keeping
`s'.mem a = 0` for `a ≥ s.frontier + k` when `ZeroAbove s` holds) and places arbitrary `w`-bit
words in `[s.frontier, s.frontier + k)` (`[KLZ26]` §5.1, Footnotes 10 & 13). -/
def demonicStep (w : ℕ) (s : State) : (o : Op) → State → o.Result → Prop
  | .read a, s', r => s' = s ∧ r = s.mem a
  | .write a v, s', _ => s' = ⟨Function.update s.mem a v, s.frontier⟩
  | .grow k, s', r =>
      s'.frontier = s.frontier + k ∧ r = s.frontier ∧
        (∀ a, a < s.frontier ∨ s.frontier + k ≤ a → s'.mem a = s.mem a) ∧
        (∀ a, s.frontier ≤ a → a < s.frontier + k → Fits w (s'.mem a))
  | .growDirty k, s', r =>
      s'.frontier = s.frontier + k ∧ r = s.frontier ∧
        (∀ a, a < s.frontier ∨ s.frontier + k ≤ a → s'.mem a = s.mem a) ∧
        (∀ a, s.frontier ≤ a → a < s.frontier + k → Fits w (s'.mem a))
  | .shrink k, s', _ => s' = ⟨clear s.mem (s.frontier - k) k, s.frontier - k⟩

/-- Demonic relational word-granular resizable memory specification at word width `w`. -/
def demonicSpec (w : ℕ) : StateTransitionSpec where
  State := State
  Op := Op
  Result := Op.Result
  step := demonicStep w
  valid := valid w

/-! ## Effectful program primitives -/

/-- A program over the word-granular resizable memory oracle. -/
abbrev Prog (α : Type) : Type := PFunctor.FreeM ⟨Op, Op.Result⟩ α

/-- Read the word at address `a`. -/
abbrev read (a : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.read a)

/-- Write `v` to address `a`. -/
abbrev write (a v : ℕ) : Prog Unit := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.write a v)

/-- Grow the active prefix by `k` zeroed words, returning the old `frontier`. -/
abbrev grow (k : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.grow k)

/-- Grow the active prefix by `k` uninitialized words, returning the old `frontier`. -/
abbrev growDirty (k : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.growDirty k)

/-- Shrink the active prefix by `k` words. -/
abbrev shrink (k : ℕ) : Prog Unit := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.shrink k)

/-- Allocate a single zeroed word at the end of the active prefix (`L ← L + 1`). -/
abbrev allocWord : Prog ℕ := grow 1

/-- Allocate a single uninitialized word at the end of the active prefix (`L ← L + 1`). -/
abbrev allocWordDirty : Prog ℕ := growDirty 1

/-- Release a single word from the end of the active prefix (`L ← L - 1`). -/
abbrev releaseWord : Prog Unit := shrink 1

/-! ## Simp lemmas for `step` and `valid` -/

@[simp]
theorem step_read (s : State) (a : ℕ) :
    step s (.read a) = (s, s.mem a) := rfl

@[simp]
theorem step_write (s : State) (a v : ℕ) :
    step s (.write a v) = (⟨Function.update s.mem a v, s.frontier⟩, ()) := rfl

@[simp]
theorem step_grow (s : State) (k : ℕ) :
    step s (.grow k) = (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier) := rfl

@[simp]
theorem step_growDirty (s : State) (k : ℕ) :
    step s (.growDirty k) = (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier) := rfl

@[simp]
theorem step_shrink (s : State) (k : ℕ) :
    step s (.shrink k) = (⟨clear s.mem (s.frontier - k) k, s.frontier - k⟩, ()) := rfl

@[simp]
theorem valid_read (w : ℕ) (s : State) (a : ℕ) :
    valid w s (.read a) ↔ a < s.frontier := Iff.rfl

@[simp]
theorem valid_write (w : ℕ) (s : State) (a v : ℕ) :
    valid w s (.write a v) ↔ a < s.frontier ∧ Fits w v := Iff.rfl

@[simp]
theorem valid_grow (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.grow k) ↔ Fits w (s.frontier + k) := Iff.rfl

@[simp]
theorem valid_growDirty (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.growDirty k) ↔ Fits w (s.frontier + k) := Iff.rfl

@[simp]
theorem valid_shrink (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.shrink k) ↔ k ≤ s.frontier := Iff.rfl

theorem clientState_pure {α : Type} (w : ℕ) (s : State) (a : α) :
    (spec w).clientState s (.pure a) = s := rfl

theorem clientResult_pure {α : Type} (w : ℕ) (s : State) (a : α) :
    (spec w).clientResult s (.pure a) = a := rfl

theorem clientHistory_pure {α : Type} (w : ℕ) (s : State) (a : α) :
    (spec w).clientHistory s (.pure a) = [] := rfl

theorem clientState_liftBind {α : Type} (w : ℕ) (s : State) (o : Op) (k : o.Result → Prog α) :
    (spec w).clientState s (.liftBind o k) =
      (spec w).clientState (step s o).1 (k (step s o).2) := rfl

theorem clientResult_liftBind {α : Type} (w : ℕ) (s : State) (o : Op) (k : o.Result → Prog α) :
    (spec w).clientResult s (.liftBind o k) =
      (spec w).clientResult (step s o).1 (k (step s o).2) := rfl

theorem clientHistory_liftBind {α : Type} (w : ℕ) (s : State) (o : Op) (k : o.Result → Prog α) :
    (spec w).clientHistory s (.liftBind o k) =
      o :: (spec w).clientHistory (step s o).1 (k (step s o).2) := rfl

/-! ## Well-formedness and canonical state preservation -/

/-- A resizable memory state is canonical at word width `w` when all words and the frontier fit in
`w` bits (`WellFormed w s`) and all unallocated addresses `a ≥ s.frontier` hold `0`
(`ZeroAbove s`). -/
def Canonical (w : ℕ) (s : State) : Prop :=
  WellFormed w s ∧ ZeroAbove s

/-- The empty state is canonical at every word width `w`. -/
theorem canonical_emptyState (w : ℕ) : Canonical w emptyState :=
  ⟨wellFormed_emptyState w, zeroAbove_emptyState⟩

/-- When `ZeroAbove s` holds, clearing `[s.frontier, s.frontier + k)` is a no-op because all words
at `a ≥ s.frontier` are already `0`. -/
theorem clear_frontier_eq_of_zeroAbove {s : State} (hs : ZeroAbove s) (k : ℕ) :
    clear s.mem s.frontier k = s.mem := by
  funext a
  by_cases ha : (Block.mk s.frontier k).Owns a
  · rw [clear_of_owns ha, hs a ha.1]
  · exact clear_of_not_owns ha

/-- Every valid operation preserves `WellFormed w`. -/
theorem wellFormed_step {w : ℕ} {s : State} {o : Op}
    (hs : WellFormed w s) (hv : valid w s o) :
    WellFormed w (step s o).1 := by
  cases o with
  | read a => exact hs
  | write a v => exact hs.step (o := .write a v) hv
  | grow k => exact hs.step (o := .alloc k) hv
  | growDirty k => exact hs.step (o := .alloc k) hv
  | shrink k =>
    refine ⟨hs.frontier_fits.of_le (Nat.sub_le _ _), fun a => ?_⟩
    dsimp only [step]
    by_cases ha : (Block.mk (s.frontier - k) k).Owns a
    · rw [clear_of_owns ha]
      exact fits_zero w
    · rw [clear_of_not_owns ha]
      exact hs.mem_fits a

/-- Every valid operation preserves `ZeroAbove`. -/
theorem zeroAbove_step {w : ℕ} {s : State} {o : Op}
    (hs : ZeroAbove s) (hv : valid w s o) :
    ZeroAbove (step s o).1 := by
  cases o with
  | read a => exact hs
  | write a v =>
    intro b hb
    dsimp only [step] at hb ⊢
    have hba : b ≠ a := by
      have : a < s.frontier := hv.1
      omega
    rw [Function.update_of_ne hba]
    exact hs b hb
  | grow k =>
    intro b hb
    dsimp only [step] at hb ⊢
    by_cases hown : (Block.mk s.frontier k).Owns b
    · exact clear_of_owns hown
    · rw [clear_of_not_owns hown]
      exact hs b (by omega)
  | growDirty k =>
    intro b hb
    dsimp only [step] at hb ⊢
    by_cases hown : (Block.mk s.frontier k).Owns b
    · exact clear_of_owns hown
    · rw [clear_of_not_owns hown]
      exact hs b (by omega)
  | shrink k =>
    intro b hb
    dsimp only [step] at hb ⊢
    have hle : k ≤ s.frontier := hv
    by_cases hlt : b < s.frontier
    · exact clear_of_owns (by simp only [Block.Owns]; omega)
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
      exact hs b (by omega)

/-- Every valid operation preserves `Canonical w`. -/
theorem canonical_step {w : ℕ} {s : State} {o : Op}
    (hs : Canonical w s) (hv : valid w s o) :
    Canonical w (step s o).1 :=
  ⟨wellFormed_step hs.1 hv, zeroAbove_step hs.2 hv⟩

/-- Every valid transition of `demonicStep w` preserves `WellFormed w`. -/
theorem wellFormed_demonicStep {w : ℕ} {s s' : State} {o : Op} {r : o.Result}
    (hs : WellFormed w s) (hv : valid w s o) (hstep : demonicStep w s o s' r) :
    WellFormed w s' := by
  cases o with
  | read a =>
    rcases hstep with ⟨rfl, -⟩
    exact hs
  | write a v =>
    subst hstep
    exact hs.step (o := .write a v) hv
  | grow k | growDirty k =>
    rcases hstep with ⟨hfront, -, hout, hin⟩
    refine ⟨hfront.symm ▸ hv, fun a => ?_⟩
    by_cases ha : s.frontier ≤ a ∧ a < s.frontier + k
    · exact hin a ha.1 ha.2
    · rw [hout a (by omega)]
      exact hs.mem_fits a
  | shrink k =>
    subst hstep
    exact wellFormed_step (o := .shrink k) hs hv

/-- Every valid transition of `demonicStep w` preserves `ZeroAbove` strictly above the new
frontier. -/
theorem zeroAbove_demonicStep {w : ℕ} {s s' : State} {o : Op} {r : o.Result}
    (hs : ZeroAbove s) (hv : valid w s o) (hstep : demonicStep w s o s' r) :
    ZeroAbove s' := by
  cases o with
  | read a =>
    rcases hstep with ⟨rfl, -⟩
    exact hs
  | write a v =>
    subst hstep
    exact zeroAbove_step (o := .write a v) hs hv
  | grow k | growDirty k =>
    rcases hstep with ⟨hfront, -, hout, -⟩
    intro a ha
    rw [hfront] at ha
    rw [hout a (Or.inr ha)]
    exact hs a (by omega)
  | shrink k =>
    subst hstep
    exact zeroAbove_step (o := .shrink k) hs hv

/-- Every valid transition of `demonicStep w` preserves `Canonical w`. -/
theorem canonical_demonicStep {w : ℕ} {s s' : State} {o : Op} {r : o.Result}
    (hs : Canonical w s) (hv : valid w s o) (hstep : demonicStep w s o s' r) :
    Canonical w s' :=
  ⟨wellFormed_demonicStep hs.1 hv hstep, zeroAbove_demonicStep hs.2 hv hstep⟩

/-! ## Refinement of the demonic specification and lifting `Memory.Prog` -/

/-- Every deterministic `step` transition is a valid transition of `demonicStep w`. -/
theorem demonicStep_of_step (w : ℕ) (s : State) (o : Op) :
    demonicStep w s o (step s o).1 (step s o).2 := by
  cases o with
  | read a => exact ⟨rfl, rfl⟩
  | write a v => rfl
  | grow k | growDirty k =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro a ha
      exact clear_of_not_owns (by simp only [Block.Owns]; omega)
    · intro a hlo hhi
      dsimp only [step]
      rw [clear_of_owns ⟨hlo, hhi⟩]
      exact fits_zero w
  | shrink k => rfl

/-- Any machine-level `WordRAM.Resizable.DemonicGrow` transition from a `ZeroAbove` state satisfies
`demonicStep w s (.grow k)`. -/
theorem demonicStep_grow_of_demonicGrow {w k : ℕ} {s s' : State}
    (hs : ZeroAbove s) (hfront : s'.frontier = s.frontier + k)
    (hg : WordRAM.Resizable.DemonicGrow w s.frontier k s.mem s'.mem) :
    demonicStep w s (.grow k) s' s.frontier := by
  refine ⟨hfront, rfl, fun a ha => ?_, hg.2.1⟩
  rcases ha with hlt | hge
  · exact hg.1 a hlt
  · rw [hg.2.2 a hge, hs a (by omega)]

/-- The deterministic specification `spec w` refines `demonicSpec w` over the identity state
map: every client verified against `demonicSpec w` is valid and has its behavior included in
`demonicSpec w` when executed on `spec w`. -/
def refinesDemonic (w : ℕ) : Refinement (demonicSpec w) (spec w) where
  methods o := .liftBind o fun a => .pure a
  inv _ := True
  abs s := s
  valid o _ hv :=
    StateTransitionSpec.DemonicValid.liftBind (D := spec w) o _ hv fun s' a _ =>
      StateTransitionSpec.DemonicValid.pure s' a
  correct {e} o {_ _ _} _ _ hrun := by
    cases hrun with
    | liftBind _ _ a _ hstep hrest =>
      cases hrest
      have hd := demonicStep_of_step w e o
      rw [← hstep] at hd
      exact ⟨hd, trivial⟩

/-- Lift a program written against the grow-only `Memory.Prog` into `Resizable.Prog`. -/
def liftMemory {α : Type} : Memory.Prog α → Prog α
  | .pure a => .pure a
  | .liftBind (.read a) k => .liftBind (.read a) (fun r => liftMemory (k r))
  | .liftBind (.write a v) k => .liftBind (.write a v) (fun r => liftMemory (k r))
  | .liftBind (.alloc n) k => .liftBind (.grow n) (fun r => liftMemory (k r))
  | .liftBind (.allocDirty n) k => .liftBind (.growDirty n) (fun r => liftMemory (k r))

/-! ## Operation cost measures -/

/-- Operation cost measure (`charge`): `read`, `write`, and `growDirty` cost `1` memory unit;
zeroed `grow k` and `shrink k` cost `max k 1` units (so single-word `allocWord = grow 1` and
`releaseWord = shrink 1` cost `1` unit each, while bulk clearing of `k` words costs `k` units). -/
def charge (_ : State) : Op → ℕ
  | .read _ => 1
  | .write _ _ => 1
  | .grow k => max k 1
  | .growDirty _ => 1
  | .shrink k => max k 1

/-- Unit cost measure assigning cost `1` to every operation. -/
def unitCharge (_ : State) : Op → ℕ := fun _ => 1

@[simp]
theorem charge_read (s : State) (a : ℕ) : charge s (.read a) = 1 := rfl

@[simp]
theorem charge_write (s : State) (a v : ℕ) : charge s (.write a v) = 1 := rfl

@[simp]
theorem charge_grow (s : State) (k : ℕ) : charge s (.grow k) = max k 1 := rfl

@[simp]
theorem charge_growDirty (s : State) (k : ℕ) : charge s (.growDirty k) = 1 := rfl

@[simp]
theorem charge_shrink (s : State) (k : ℕ) : charge s (.shrink k) = max k 1 := rfl

theorem charge_allocWord (s : State) : charge s (.grow 1) = 1 := rfl

theorem charge_releaseWord (s : State) : charge s (.shrink 1) = 1 := rfl

theorem one_le_charge (s : State) (o : Op) : 1 ≤ charge s o := by
  cases o <;> simp [charge]

theorem unitCharge_le_charge (s : State) (o : Op) : unitCharge s o ≤ charge s o := by
  cases o <;> simp [unitCharge, charge]

/-! ## Space measures (current size at every step, spillover, and peak working space) -/

/-- Current allocated space of `s` in `w`-bit words (`L = s.frontier`). -/
abbrev spaceWords (s : State) : ℕ := s.frontier

/-- Current allocated space of `s` in bits (`w * s.frontier`). -/
def spaceBits (w : ℕ) (s : State) : ℕ := w * s.frontier

/-- Total space in bits of a data structure with `s.frontier` allocated words and a spillover
integer in `[0, K)` (`[LLYZ23a]` Definition 1). -/
def spilloverSpaceBits (w K : ℕ) (s : State) : ℕ :=
  w * s.frontier + Nat.clog 2 K

/-- Peak number of allocated words reached at any intermediate point during the execution of a
client program `p` starting from state `s`. -/
def peakWords {α : Type} (s : State) : Prog α → ℕ
  | .pure _ => s.frontier
  | .liftBind o k =>
      let res := step s o
      max s.frontier (peakWords res.1 (k res.2))

theorem frontier_le_peakWords {α : Type} (s : State) (p : Prog α) :
    s.frontier ≤ peakWords s p := by
  cases p with
  | pure _ => exact le_rfl
  | liftBind _ _ => exact le_max_left _ _

theorem clientState_frontier_le_peakWords {α : Type} (w : ℕ) (s : State) (p : Prog α) :
    ((spec w).clientState s p).frontier ≤ peakWords s p := by
  induction p generalizing s with
  | pure _ => exact le_rfl
  | liftBind o k ih =>
    exact le_trans (ih (step s o).2 (step s o).1) (le_max_right _ _)

/-- Predicate asserting that along a sequence of states `s_seq` with current sizes `n_seq`, the
allocated word count at every step `t` is at most `bound (n_seq[t])`. -/
def EveryStepWordsLe (bound : ℕ → ℕ) (n_seq : List ℕ) (s_seq : List State) : Prop :=
  n_seq.length = s_seq.length ∧
    ∀ t (hn : t < n_seq.length) (hs : t < s_seq.length),
      (s_seq[t]).frontier ≤ bound (n_seq[t])

/-! ## Frame condition across resizes -/

/-- Word-level frame condition across resizes: every address `a < min s.frontier s'.frontier`
outside the modified address set `W` retains its value (`s'.mem a = s.mem a`). -/
def UnchangedOutside (s s' : State) (W : Set ℕ) : Prop :=
  ∀ a < min s.frontier s'.frontier, a ∉ W → s'.mem a = s.mem a

theorem UnchangedOutside.refl (s : State) (W : Set ℕ) :
    UnchangedOutside s s W :=
  fun _ _ _ => rfl

theorem UnchangedOutside.mono {s s' : State} {W₁ W₂ : Set ℕ}
    (h : UnchangedOutside s s' W₁) (hsub : W₁ ⊆ W₂) :
    UnchangedOutside s s' W₂ :=
  fun a ha hnot => h a ha (fun hw1 => hnot (hsub hw1))

theorem UnchangedOutside.step_read (s : State) (a : ℕ) :
    UnchangedOutside s (step s (.read a)).1 ∅ :=
  fun _ _ _ => rfl

theorem UnchangedOutside.step_write (s : State) (a v : ℕ) :
    UnchangedOutside s (step s (.write a v)).1 {a} := by
  intro x _ hx
  exact Function.update_of_ne (Set.mem_singleton_iff.not.mp hx) v s.mem

theorem UnchangedOutside.step_grow (s : State) (k : ℕ) :
    UnchangedOutside s (step s (.grow k)).1 ∅ := by
  intro a ha _
  have hlt : a < s.frontier := lt_of_lt_of_le ha (min_le_left _ _)
  exact clear_of_not_owns (by simp only [Block.Owns]; omega)

theorem UnchangedOutside.step_growDirty (s : State) (k : ℕ) :
    UnchangedOutside s (step s (.growDirty k)).1 ∅ :=
  UnchangedOutside.step_grow s k

theorem UnchangedOutside.step_shrink (s : State) (k : ℕ) :
    UnchangedOutside s (step s (.shrink k)).1 ∅ := by
  intro a ha _
  have hlt : a < s.frontier - k := lt_of_lt_of_le ha (min_le_right _ _)
  exact clear_of_not_owns (by simp only [Block.Owns]; omega)

/-- If a block `b` lies below `min s.frontier s'.frontier` and its footprint is disjoint from `W`,
then `UnchangedOutside s s' W` preserves `b.Realizes`. -/
theorem Block.realizes_of_unchangedOutside (b : Block) {s s' : State} {W : Set ℕ}
    {vs : Fin b.length → ℕ}
    (hreal : b.Realizes s.mem vs)
    (hfit : b.base + b.length ≤ min s.frontier s'.frontier)
    (hframe : UnchangedOutside s s' W)
    (hdisj : ∀ a, b.Owns a → a ∉ W) :
    b.Realizes s'.mem vs := by
  intro i
  dsimp only [Block.read]
  have hown : b.Owns (b.base + i.val) := ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt _⟩
  have hlt : b.base + i.val < min s.frontier s'.frontier := by omega
  rw [hframe (b.base + i.val) hlt (hdisj _ hown)]
  exact hreal i

/-! ## Composition of multiple resizable structures -/

namespace MultiSegment

/-- State of `B` independent word-granular resizable memory segments (`[LLYZ24]` §2.2,
`[KLZ26]` §5.1). -/
abbrev State (B : ℕ) := Fin B → Memory.State

/-- Operations on `B` independent resizable memory segments. -/
structure Op (B : ℕ) where
  /-- Target segment index `i < B`. -/
  seg : Fin B
  /-- Resizable memory operation on segment `seg`. -/
  op : Resizable.Op
  deriving DecidableEq, Repr

/-- Result type of a multi-segment operation. -/
abbrev Op.Result {B : ℕ} (o : Op B) : Type := o.op.Result

/-- Empty state of `B` resizable segments (all segments have `frontier = 0`). -/
def empty (B : ℕ) : State B := fun _ => emptyState

/-- Deterministic transition function on `B` resizable segments. -/
def step {B : ℕ} (s : State B) (o : Op B) : State B × o.Result :=
  let res := Resizable.step (s o.seg) o.op
  (Function.update s o.seg res.1, res.2)

/-- Validity predicate on `B` resizable segments at word width `w`. -/
def valid (w B : ℕ) (s : State B) (o : Op B) : Prop :=
  Resizable.valid w (s o.seg) o.op

/-- Deterministic specification of `B` independent resizable segments at word width `w`. -/
abbrev spec (w B : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := State B) (Op := Op B) (Result := Op.Result)
    step (valid w B)

/-- Total allocated words across all `B` segments (`∑ i, (s i).frontier`). -/
def totalWords {B : ℕ} (s : State B) : ℕ :=
  ∑ i : Fin B, (s i).frontier

/-- Total allocated bits across all `B` segments (`w * ∑ i, (s i).frontier`). -/
def totalBits (w : ℕ) {B : ℕ} (s : State B) : ℕ :=
  w * totalWords s

@[simp]
theorem totalWords_empty (B : ℕ) : totalWords (empty B) = 0 := by
  simp [totalWords, empty]

/-- Operating on segment `o.seg` leaves every other segment `j ≠ o.seg` untouched. -/
@[simp]
theorem step_other_eq {B : ℕ} (s : State B) (o : Op B) {j : Fin B} (hj : j ≠ o.seg) :
    (step s o).1 j = s j :=
  Function.update_of_ne hj _ s

/-- Operating on segment `o.seg` updates segment `o.seg` via `Resizable.step`. -/
@[simp]
theorem step_self_eq {B : ℕ} (s : State B) (o : Op B) :
    (step s o).1 o.seg = (Resizable.step (s o.seg) o.op).1 :=
  Function.update_self o.seg _ s

private theorem totalWords_update {B : ℕ} (s : State B) (i : Fin B) (s' : Memory.State) :
    totalWords (Function.update s i s') + (s i).frontier =
      totalWords s + s'.frontier := by
  unfold totalWords
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun x => (s x).frontier) (Finset.mem_univ i)]
  rw [Function.update_self]
  have hrest :
      ∑ x ∈ Finset.univ.erase i, (Function.update s i s' x).frontier =
        ∑ x ∈ Finset.univ.erase i, (s x).frontier := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hrest]
  omega

/-- Releasing `k` words in segment `i` and allocating `k` words in segment `j ≠ i` preserves total
allocated words across the machine (`totalWords`), demonstrating that released memory is
reusable by other structures. -/
theorem totalWords_shrink_then_grow {B : ℕ} (s : State B) (i j : Fin B)
    {k : ℕ} (hk : k ≤ (s i).frontier) :
    let s₁ := (step s ⟨i, .shrink k⟩).1
    let s₂ := (step s₁ ⟨j, .grow k⟩).1
    totalWords s₂ = totalWords s := by
  intro s₁ s₂
  have h1 : totalWords s₁ + (s i).frontier = totalWords s + ((s i).frontier - k) :=
    totalWords_update s i (Resizable.step (s i) (.shrink k)).1
  have h2 : totalWords s₂ + (s₁ j).frontier = totalWords s₁ + ((s₁ j).frontier + k) :=
    totalWords_update s₁ j (Resizable.step (s₁ j) (.grow k)).1
  omega

end MultiSegment

/-! ## Multiplexing two resizable segments into one `Resizable.State` (`packTwoWay`) -/

/-- Pack two resizable memory segments `(s₀, s₁)` contiguously into a single `Memory.State` of
total size `s₀.frontier + s₁.frontier` words: segment `0` occupies `[0, s₀.frontier)` and
segment `1` occupies `[s₀.frontier, s₀.frontier + s₁.frontier)`. -/
def packTwoWay (s₀ s₁ : State) : State where
  frontier := s₀.frontier + s₁.frontier
  mem a :=
    if a < s₀.frontier then s₀.mem a
    else if a < s₀.frontier + s₁.frontier then s₁.mem (a - s₀.frontier)
    else 0

@[simp]
theorem packTwoWay_frontier (s₀ s₁ : State) :
    (packTwoWay s₀ s₁).frontier = s₀.frontier + s₁.frontier := rfl

@[simp]
theorem packTwoWay_mem_left (s₀ s₁ : State) {a : ℕ} (ha : a < s₀.frontier) :
    (packTwoWay s₀ s₁).mem a = s₀.mem a := by
  simp [packTwoWay, ha]

@[simp]
theorem packTwoWay_mem_right (s₀ s₁ : State) {a : ℕ} (ha : a < s₁.frontier) :
    (packTwoWay s₀ s₁).mem (s₀.frontier + a) = s₁.mem a := by
  have hnot : ¬ (s₀.frontier + a < s₀.frontier) := by omega
  have hlt : s₀.frontier + a < s₀.frontier + s₁.frontier := by omega
  simp [packTwoWay, hnot, hlt]

theorem packTwoWay_zeroAbove (s₀ s₁ : State) :
    ZeroAbove (packTwoWay s₀ s₁) := by
  intro a ha
  rw [packTwoWay_frontier] at ha
  have hnot0 : ¬ (a < s₀.frontier) := by omega
  have hnot1 : ¬ (a < s₀.frontier + s₁.frontier) := by omega
  simp [packTwoWay, hnot0, hnot1]

/-- When segment `0` shrinks by `k` words and segment `1` grows by `k` words, the combined
single-memory representation `packTwoWay` keeps the exact same total word count
`s₀.frontier + s₁.frontier`. -/
theorem packTwoWay_shrink_grow_frontier (s₀ s₁ : State) {k : ℕ} (hk : k ≤ s₀.frontier) :
    (packTwoWay (step s₀ (.shrink k)).1 (step s₁ (.grow k)).1).frontier =
      (packTwoWay s₀ s₁).frontier := by
  simp only [packTwoWay_frontier, step_shrink, step_grow]
  omega

/-! ## Single-linear-tape chunked multiplexer (`ChunkedTape`, `[LLYZ23a]` Lemma 5.1) -/

namespace ChunkedTape

/-- Number of `C`-word chunks required to hold `L` words (`⌈L / C⌉`). -/
def numChunks (C L : ℕ) : ℕ :=
  (L + C - 1) / C

@[simp]
theorem numChunks_zero (C : ℕ) : numChunks C 0 = 0 := by
  unfold numChunks
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · rfl
  · exact Nat.div_eq_of_lt (by omega)

@[simp]
theorem numChunks_one (L : ℕ) : numChunks 1 L = L := by
  simp [numChunks]

theorem le_numChunks_mul {C L : ℕ} (hC : 0 < C) :
    L ≤ numChunks C L * C := by
  unfold numChunks
  have hdiv := Nat.div_add_mod (L + C - 1) C
  have hmod : (L + C - 1) % C < C := Nat.mod_lt _ hC
  have hcomm : C * ((L + C - 1) / C) = (L + C - 1) / C * C := Nat.mul_comm _ _
  omega

theorem numChunks_mul_le {C L : ℕ} (hC : 0 < C) :
    numChunks C L * C ≤ L + C := by
  unfold numChunks
  have hle : (L + C - 1) / C * C ≤ L + C - 1 := Nat.div_mul_le_self (L + C - 1) C
  omega

/-- Fixed header size in words for multiplexing `B` segments with at most `K_max` chunks each:
`[0, B)` stores segment word lengths, `[B, B + B * K_max)` stores `chunkToSlot`, and
`[B + B * K_max, B + 2 * B * K_max)` stores `slotOwner`. -/
def headerWords (B K_max : ℕ) : ℕ :=
  B + 2 * B * K_max

/-- Physical address of the slot-index entry `chunkToSlot(i, q)` in the header. -/
def chunkSlotAddr (B K_max : ℕ) (i : Fin B) (q : ℕ) : ℕ :=
  B + i.val * K_max + q

/-- Physical address of the reverse owner entry `slotOwner(p)` in the header. -/
def slotOwnerAddr (B K_max p : ℕ) : ℕ :=
  B + B * K_max + p

/-- Physical address of word offset `off < C` inside physical chunk slot `p`. -/
def dataWordAddr (B C K_max p off : ℕ) : ℕ :=
  headerWords B K_max + p * C + off

/-- Total number of active `C`-word chunks across all `B` logical segments. -/
def totalChunks (C : ℕ) {B : ℕ} (segs : Fin B → State) : ℕ :=
  ∑ i : Fin B, numChunks C (segs i).frontier

/-- Representation invariant asserting that a single linear resizable memory `s : State`
multiplexes `B` logical resizable segments `segs : Fin B → State` using `C`-word chunks with
chunk capacity `K_max` per segment (`[LLYZ23a]` Lemma 5.1, `[BHKLZ26]` Lemma 2.1). -/
structure Realizes (B C K_max : ℕ) (s : State) (segs : Fin B → State) : Prop where
  /-- Chunk size is positive. -/
  chunk_pos : 0 < C
  /-- Segment word lengths are stored in `[0, B)`. -/
  len_stored : ∀ i : Fin B, s.mem i.val = (segs i).frontier
  /-- Each segment uses at most `K_max` chunks. -/
  chunks_fit : ∀ i : Fin B, numChunks C (segs i).frontier ≤ K_max
  /-- The single physical tape has frontier `headerWords B K_max + totalChunks C segs * C`. -/
  frontier_eq : s.frontier = headerWords B K_max + totalChunks C segs * C
  /-- Every active logical chunk `(i, q)` maps to a valid physical slot `< totalChunks C segs`. -/
  slot_lt : ∀ (i : Fin B) (q : ℕ), q < numChunks C (segs i).frontier →
    s.mem (chunkSlotAddr B K_max i q) < totalChunks C segs
  /-- `slotOwner` is the left inverse of `chunkToSlot` on all active logical chunks. -/
  owner_inv : ∀ (i : Fin B) (q : ℕ), q < numChunks C (segs i).frontier →
    s.mem (slotOwnerAddr B K_max (s.mem (chunkSlotAddr B K_max i q))) = i.val * K_max + q
  /-- Every allocated word `a < (segs i).frontier` of segment `i` is stored in its assigned
  physical chunk slot at offset `a % C`. -/
  data_eq : ∀ (i : Fin B) (a : ℕ), a < (segs i).frontier →
    s.mem (dataWordAddr B C K_max (s.mem (chunkSlotAddr B K_max i (a / C))) (a % C)) =
      (segs i).mem a

/-- **Space bound for single-tape chunked multiplexing (`[LLYZ23a]` Lemma 5.1, `[BHKLZ26]`
Lemma 2.1).** Storing `B` logical resizable segments `segs` in a single linear resizable memory `s`
with chunk size `C` and chunk-table capacity `K_max` uses at most
`(∑ i, (segs i).frontier) + B * C + headerWords B K_max` words at every step. -/
theorem Realizes.frontier_le {B C K_max : ℕ} {s : State} {segs : Fin B → State}
    (h : Realizes B C K_max s segs) :
    s.frontier ≤ MultiSegment.totalWords segs + B * C + headerWords B K_max := by
  rw [h.frontier_eq]
  unfold totalChunks
  rw [Finset.sum_mul]
  have hsum :
      ∑ i : Fin B, numChunks C (segs i).frontier * C ≤
        ∑ i : Fin B, ((segs i).frontier + C) :=
    Finset.sum_le_sum fun i _ => numChunks_mul_le h.chunk_pos
  have hsplit :
      (∑ i : Fin B, ((segs i).frontier + C)) = MultiSegment.totalWords segs + B * C := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rfl
  omega

/-- Bit-level space bound for single-tape chunked multiplexing (`[LLYZ23a]` Lemma 5.1,
`[BHKLZ26]` Lemma 2.1): choosing `C = ⌈√(L_max / w)⌉` and `K_max = ⌈L_max / C⌉` gives
`∑ i, w * ℓ_i + O(B * √(L_max * w) + B * w)` bits on the single physical tape `s`. -/
theorem Realizes.spaceBits_le (w : ℕ) {B C K_max : ℕ} {s : State} {segs : Fin B → State}
    (h : Realizes B C K_max s segs) :
    spaceBits w s ≤
      MultiSegment.totalBits w segs + w * (B * C + headerWords B K_max) := by
  unfold spaceBits MultiSegment.totalBits
  rw [← Nat.mul_add, ← Nat.add_assoc]
  exact Nat.mul_le_mul_left w h.frontier_le

/-- Exact word count for unit-chunk (`C = 1`) single-tape multiplexing: zero internal chunk
rounding waste (`s.frontier = headerWords B K_max + ∑ i, (segs i).frontier`). -/
theorem Realizes.frontier_eq_of_unitChunk {B K_max : ℕ} {s : State} {segs : Fin B → State}
    (h : Realizes B 1 K_max s segs) :
    s.frontier = headerWords B K_max + MultiSegment.totalWords segs := by
  simpa [totalChunks, MultiSegment.totalWords] using h.frontier_eq

/-- Read logical word `a` of segment `i` on the single linear tape (`2` reads, `O(1)` worst-case
time). -/
def readWord (B C K_max : ℕ) (i : Fin B) (a : ℕ) : Prog ℕ := do
  let p ← read (chunkSlotAddr B K_max i (a / C))
  read (dataWordAddr B C K_max p (a % C))

/-- Write `v` to logical word `a` of segment `i` on the single linear tape (`1` read + `1` write =
`2` operations, `O(1)` worst-case time). -/
def writeWord (B C K_max : ℕ) (i : Fin B) (a v : ℕ) : Prog Unit := do
  let p ← read (chunkSlotAddr B K_max i (a / C))
  write (dataWordAddr B C K_max p (a % C)) v

/-- Allocate `1` word at the end of segment `i` in a unit-chunk (`C = 1`) single linear tape with
`N_chk` currently active data words (`6` operations, `O(1)` worst-case time, zero shifting). -/
def allocWord1 (B K_max N_chk : ℕ) (i : Fin B) : Prog ℕ := do
  let L_i ← read i.val
  write i.val (L_i + 1)
  let _ ← grow 1
  write (chunkSlotAddr B K_max i L_i) N_chk
  write (slotOwnerAddr B K_max N_chk) (i.val * K_max + L_i)
  write (dataWordAddr B 1 K_max N_chk 0) 0
  return L_i

/-- Release `1` word from the end of segment `i` in a unit-chunk (`C = 1`) single linear tape with
`N_chk` currently active data words by swapping the last physical data slot `N_chk - 1` into the
freed slot `p` and shrinking the single physical tape by `1` word (`9` operations, `O(1)`
worst-case time, **no** `Ω(N_chk)` shift). -/
def releaseWord1 (B K_max N_chk : ℕ) (i : Fin B) : Prog Unit := do
  let L_i ← read i.val
  let L' := L_i - 1
  write i.val L'
  let p ← read (chunkSlotAddr B K_max i L')
  let p_last := N_chk - 1
  let lastVal ← read (dataWordAddr B 1 K_max p_last 0)
  let lastOwner ← read (slotOwnerAddr B K_max p_last)
  write (dataWordAddr B 1 K_max p 0) lastVal
  write (B + lastOwner) p
  write (slotOwnerAddr B K_max p) lastOwner
  shrink 1

/-- `readWord` on a valid `ChunkedTape` returns `(segs i).mem a`, leaves `s` unchanged, and
executes in `2` operations. -/
theorem readWord_spec (w : ℕ) {B C K_max : ℕ} {s : State} {segs : Fin B → State}
    (h : Realizes B C K_max s segs) (i : Fin B) {a : ℕ} (ha : a < (segs i).frontier) :
    (spec w).clientResult s (readWord B C K_max i a) = (segs i).mem a ∧
      (spec w).clientState s (readWord B C K_max i a) = s ∧
      ((spec w).clientHistory s (readWord B C K_max i a)).length = 2 := by
  exact ⟨h.data_eq i a ha, rfl, rfl⟩

/-- `writeWord` executes in `2` operations and preserves `s.frontier`. -/
theorem writeWord_spec (w B C K_max : ℕ) (s : State) (i : Fin B) (a v : ℕ) :
    ((spec w).clientState s (writeWord B C K_max i a v)).frontier = s.frontier ∧
      ((spec w).clientHistory s (writeWord B C K_max i a v)).length = 2 :=
  ⟨rfl, rfl⟩

/-- `allocWord1` executes in `6` operations and grows the single physical tape `s` by `1` word. -/
theorem allocWord1_spec (w B K_max N_chk : ℕ) (s : State) (i : Fin B) :
    ((spec w).clientState s (allocWord1 B K_max N_chk i)).frontier = s.frontier + 1 ∧
      ((spec w).clientHistory s (allocWord1 B K_max N_chk i)).length = 6 :=
  ⟨rfl, rfl⟩

/-- `releaseWord1` executes in `9` operations and shrinks the single physical tape `s` by `1`
word. -/
theorem releaseWord1_spec (w B K_max N_chk : ℕ) (s : State) (i : Fin B) :
    ((spec w).clientState s (releaseWord1 B K_max N_chk i)).frontier = s.frontier - 1 ∧
      ((spec w).clientHistory s (releaseWord1 B K_max N_chk i)).length = 9 :=
  ⟨rfl, rfl⟩

/-- **Single-tape memory reuse without shifting:** When segment `i` releases `1` word via
`releaseWord1` and segment `j` subsequently allocates `1` word via `allocWord1` on the **same**
linear tape `s` (`1 ≤ s.frontier`, `1 ≤ N_chk`), the single physical tape returns to the exact
same frontier `s.frontier` in `15` total operations (`O(1)` worst-case time, independent of tape
length). -/
theorem releaseWord1_then_allocWord1_spec (w B K_max N_chk : ℕ) (s : State) (i j : Fin B)
    (hs : 1 ≤ s.frontier) :
    let prog : Prog ℕ := do
      releaseWord1 B K_max N_chk i
      allocWord1 B K_max (N_chk - 1) j
    ((spec w).clientState s prog).frontier = s.frontier ∧
      ((spec w).clientHistory s prog).length = 15 := by
  refine ⟨?_, rfl⟩
  change s.frontier - 1 + 1 = s.frontier
  omega

end ChunkedTape

end Cslib.DataStructure.Memory.Resizable
