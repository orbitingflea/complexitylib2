/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.BranchingProgram.Basic
public import CslibFrontier.Computability.BranchingProgram.MonoidProgram
public import CslibFrontier.Foundations.Data.BitString.Block
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Prod
import CslibFrontier.Foundations.Data.List.FoldlIdx
import Batteries.Data.Fin.Fold
import Mathlib.Data.List.OfFn

/-!
# Read-once branching programs

A *read-once branching program* of length `L` over an alphabet `X`, with states `S`, reads a word
`x : Fin L → X` letter by letter in the standard order: it starts in the state `start`, at time
`i` it moves from its current state `s` to `step i s (x i)`, and it accepts when the final state
satisfies `accept` (`ReadOnceProgram`, `ReadOnceProgram.eval`). Its *width* is the number of
states `Fintype.card S`. Read-once branching programs of width `w` and length `L` model
computations of length `L` with `log w` bits of memory reading a one-way stream of random letters,
the tests fooled by Nisan's generator. These are the standard-order read-once branching programs
of [Hatami and Hoza, Definition 1.5][HatamiHoza2024], the oblivious read-once branching programs of
[Vadhan, Section 8.2.1][Vadhan2012] (with layers of states `S` and edges labelled by letters). A
program of length `m * n` over `X` regroups into a program of length `m` over the blocks
`Fin n → X` with the same states (`ReadOnceProgram.blocks`, `ReadOnceProgram.eval_blocks`); the
words of length `m * n` are the blocks concatenated by `Cslib.BitString.blocksEquiv.symm`.

The run of a time-dependent transition function `δ : ℕ → S → X → S` on a list of letters `l`,
starting at time `t` in state `s`, is the indexed fold `l.foldlIdx δ s t` (`List.foldlIdx_append`
splits runs). A program runs its transition function extended by the identity after time `L`
(`ReadOnceProgram.finalState_eq`).

Read-once branching programs are a sequential form of monoid programs
(`Cslib.BranchingPrograms.MonoidProgram`) over the transformation monoid `Function.End S`. That
model fixes a monoid element for each letter read, but lets instructions read positions in any
order and any number of times, and measures length rather than width. A read-once program is the
monoid program whose `i`-th instruction from the end reads position `i` and selects
`step i · a` on the letter `a`; since the last instruction of a program over `Function.End S` acts
first, it maps the start state to the final state (`ReadOnceProgram.toMonoidProgram`,
`ReadOnceProgram.eval_toMonoidProgram`). The read-once nondeterministic programs
`Cslib.Circuits.Frontier.ReadOnceNBP` instead read sets of coordinates in a layout order, with
nondeterministic transitions.

A read-once program with finitely many states is also a deterministic branching program
(`Cslib.BranchingPrograms.BranchingProgram`), which may query any coordinate at any node: its nodes
are the pairs of a time and a state, so it has `(L + 1) * Fintype.card S` of them
(`ReadOnceProgram.toBranchingProgram`, `ReadOnceProgram.eval_toBranchingProgram`,
`ReadOnceProgram.size_toBranchingProgram`).

## Main definitions

* `Cslib.BranchingPrograms.ReadOnceProgram`: a read-once branching program in standard order.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval`: its output on a word.
* `Cslib.BranchingPrograms.ReadOnceProgram.stepAt`: its transition function extended to all times.
* `Cslib.BranchingPrograms.ReadOnceProgram.runFrom`: the state reached by reading the rest of a
  word from a given time and state.
* `Cslib.BranchingPrograms.ReadOnceProgram.blocks`: the program on blocks of `n` letters.
* `Cslib.BranchingPrograms.ReadOnceProgram.toMonoidProgram`: the program as a monoid program over
  `Function.End S`.
* `Cslib.BranchingPrograms.ReadOnceProgram.toBranchingProgram`: the program as a deterministic
  branching program.

## Main results

* `Cslib.BranchingPrograms.ReadOnceProgram.finalState_eq`: the final state is the run of the
  extended transition function.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_blocks`: regrouping into blocks preserves outputs.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_toMonoidProgram`: the monoid program evaluates to
  the map from start states to final states.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_toBranchingProgram`,
  `Cslib.BranchingPrograms.ReadOnceProgram.size_toBranchingProgram`: the branching program computes
  the same function, with `(L + 1) * Fintype.card S` nodes.

## References

* [P. Hatami, W. Hoza, *Paradigms for Unconditional Pseudorandom Generators*][HatamiHoza2024]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

open Cslib.BitString

variable {S X : Type*}

/-- A *read-once branching program* in standard order, of length `L` over the alphabet `X` with
states `S`: from the state `start`, at time `i` it moves from state `s` to `step i s a` on reading
the `i`-th letter `a`, and it accepts when the final state satisfies `accept`. Its width is
`Fintype.card S` [Hatami and Hoza, Definition 1.5][HatamiHoza2024]. -/
structure ReadOnceProgram (L : ℕ) (S X : Type*) where
  /-- The start state. -/
  start : S
  /-- The transition at each time, on the current state and the letter read. -/
  step : Fin L → S → X → S
  /-- The accepting final states. -/
  accept : S → Bool

namespace ReadOnceProgram

variable {L : ℕ} (P : ReadOnceProgram L S X)

/-- The state of the program after reading the word `x`. -/
def finalState (x : Fin L → X) : S :=
  Fin.foldl L (fun s i => P.step i s (x i)) P.start

/-- The output of the program on the word `x`: whether its final state is accepting. -/
def eval (x : Fin L → X) : Bool :=
  P.accept (P.finalState x)

/-- The transition function of the program at every time, the identity from time `L` on. -/
def stepAt (t : ℕ) (s : S) (a : X) : S :=
  if h : t < L then P.step ⟨t, h⟩ s a else s

/-- The final state is the run of the extended transition function `stepAt` on the word. -/
theorem finalState_eq (x : Fin L → X) :
    P.finalState x = (List.ofFn x).foldlIdx P.stepAt P.start := by
  rw [List.foldlIdx_ofFn]
  simp only [finalState, stepAt, Nat.zero_add, Fin.is_lt, dite_true]

/-- The state reached from the state `s` at time `t` by reading the rest of the word `x`. -/
def runFrom (x : Fin L → X) (t : ℕ) (s : S) : S :=
  ((List.ofFn x).drop t).foldlIdx P.stepAt s t

/-- Reading the whole word from the start gives the final state. -/
theorem runFrom_zero (x : Fin L → X) : P.runFrom x 0 P.start = P.finalState x :=
  (P.finalState_eq x).symm

/-- From time `L` on, no more letters are read. -/
theorem runFrom_of_le (x : Fin L → X) {t : ℕ} (ht : L ≤ t) (s : S) :
    P.runFrom x t s = s := by
  rw [runFrom, List.drop_eq_nil_of_le (by simpa using ht)]
  rfl

/-- Before time `L`, one step of `runFrom` reads `x ⟨t, ht⟩` and advances to `t + 1`. -/
theorem runFrom_step (x : Fin L → X) {t : ℕ} (ht : t < L) (s : S) :
    P.runFrom x t s = P.runFrom x (t + 1) (P.step ⟨t, ht⟩ s (x ⟨t, ht⟩)) := by
  rw [runFrom, List.drop_eq_getElem_cons (by simpa using ht), List.foldlIdx_cons,
    List.getElem_ofFn]
  simp only [stepAt, ht, dite_true]
  rfl

/-! ### Blocks -/

/-- The program of length `m` on blocks of `n` letters: at time `i` it runs `P` on the `i`-th
block, from time `n * i`. It has the same states, hence the same width. -/
def blocks {m n : ℕ} (P : ReadOnceProgram (m * n) S X) : ReadOnceProgram m S (Fin n → X) where
  start := P.start
  step i s y := (List.ofFn y).foldlIdx P.stepAt s (n * i)
  accept := P.accept

/-- **Regrouping into blocks** preserves final states. -/
theorem finalState_blocks {m n : ℕ} (P : ReadOnceProgram (m * n) S X) (x : Fin m → Fin n → X) :
    P.blocks.finalState x = P.finalState (blocksEquiv.symm x) := by
  have hrun := List.foldlIdx_flatten P.stepAt (List.ofFn fun i => List.ofFn (x i))
    (fun l hl => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact List.length_ofFn) P.start 0
  rw [Nat.mul_zero, ← ofFn_blocksEquiv_symm, ← finalState_eq, List.ofFn_comp', List.foldlIdx_map,
    List.foldlIdx_ofFn] at hrun
  rw [hrun]
  simp only [finalState, Nat.zero_add, blocks]

/-- **Regrouping into blocks** preserves outputs. -/
theorem eval_blocks {m n : ℕ} (P : ReadOnceProgram (m * n) S X) (x : Fin m → Fin n → X) :
    P.blocks.eval x = P.eval (blocksEquiv.symm x) := by
  rw [eval, finalState_blocks]
  rfl

/-! ### Monoid programs -/

/-- The program as a monoid program over `Function.End S`: the `i`-th instruction from the end
reads position `i` and selects `step i · a` on the letter `a`. -/
def toMonoidProgram (P : ReadOnceProgram L S X) : MonoidProgram (Fin L) X (Function.End S) :=
  FreeMonoid.ofList <| List.ofFn fun i : Fin L =>
    ⟨i.rev, fun a => (fun s => P.step i.rev s a : Function.End S)⟩

private theorem prod_ofFn_rev_apply {m : ℕ} (g : Fin m → Function.End S) (s : S) :
    (List.ofFn fun i : Fin m => g i.rev).prod s =
      Fin.foldl m (fun s i => g i s) s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
      Fin.foldl_succ]
    simp only [Fin.rev_castSucc, Fin.rev_last]
    exact ih (fun i => g i.succ) (g 0 s)

/-- **Read-once programs are monoid programs**: the monoid program `P.toMonoidProgram` evaluates on
`x` to the map sending the start state to the final state of `P` on `x`. -/
theorem eval_toMonoidProgram (x : Fin L → X) :
    P.toMonoidProgram.eval x P.start = P.finalState x := by
  rw [MonoidProgram.eval_eq_prod, toMonoidProgram, FreeMonoid.toList_ofList, List.map_ofFn]
  exact prod_ofFn_rev_apply (fun i => (fun s => P.step i s (x i) : Function.End S)) P.start

/-! ### Branching programs -/

/-- The program as a graph on the pairs of a time and a state: at a time `t < L` the node `(t, s)`
queries position `t` and moves to `(t + 1, step t s a)` on the letter `a`, and at time `L` it is a
sink returning `accept s`. -/
def toGraph : BranchingProgram.Graph (Fin L) X (Fin (L + 1) × S) where
  start := (0, P.start)
  node p :=
    if h : p.1.val < L then
      .branch ⟨p.1.val, h⟩ fun a => ((⟨p.1.val, h⟩ : Fin L).succ, P.step ⟨p.1.val, h⟩ p.2 a)
    else
      .sink (P.accept p.2)
  rank p := L - p.1.val
  rank_lt p i next a h := by
    by_cases ht : p.1.val < L
    · rw [dite_eq_left ht] at h
      injection h with _ hnext
      subst hnext
      exact Nat.sub_lt_sub_left ht (Nat.lt_succ_self _)
    · rw [dite_eq_right ht] at h
      cases h

variable [Fintype S]

/-- From the node `(t, s)`, the graph of `P` reaches the output of `P` run from time `t` and state
`s`. -/
theorem evalNode_toGraph (x : Fin L → X) :
    ∀ (k : ℕ) (t : Fin (L + 1)) (s : S), L - t.val = k →
      P.toGraph.evalNode x (t, s) = P.accept (P.runFrom x t.val s) := by
  intro k
  induction k with
  | zero =>
    intro t s hk
    have ht : L ≤ t.val := by omega
    have hnode : P.toGraph.node (t, s) = .sink (P.accept s) :=
      dite_eq_right (not_lt.mpr ht)
    rw [BranchingProgram.Graph.evalNode_sink x hnode, P.runFrom_of_le x ht]
  | succ k ih =>
    intro t s hk
    have ht : t.val < L := by omega
    have hnode : P.toGraph.node (t, s) =
        .branch ⟨t.val, ht⟩
          (fun a => ((⟨t.val, ht⟩ : Fin L).succ, P.step ⟨t.val, ht⟩ s a)) :=
      dite_eq_left ht
    rw [BranchingProgram.Graph.evalNode_branch x hnode,
      ih (⟨t.val, ht⟩ : Fin L).succ (P.step ⟨t.val, ht⟩ s (x ⟨t.val, ht⟩))
        (by simp only [Fin.val_succ]; omega),
      Fin.val_succ, ← P.runFrom_step x ht s]

/-- The program as a deterministic branching program, with a node for each time and state. -/
noncomputable def toBranchingProgram : BranchingProgram (Fin L) X :=
  P.toGraph.toBranchingProgram

/-- **Read-once programs are branching programs**: `P.toBranchingProgram` computes the same
function as `P`. -/
@[simp]
theorem eval_toBranchingProgram (x : Fin L → X) :
    P.toBranchingProgram.eval x = P.eval x := by
  rw [toBranchingProgram, BranchingProgram.Graph.eval_toBranchingProgram,
    show P.toGraph.start = (0, P.start) from rfl,
    P.evalNode_toGraph x L 0 P.start (by simp), Fin.val_zero, P.runFrom_zero, eval]

/-- The branching program of a read-once program has `(L + 1) * Fintype.card S` nodes. -/
@[simp]
theorem size_toBranchingProgram :
    P.toBranchingProgram.size = (L + 1) * Fintype.card S := by
  simp [toBranchingProgram]

end ReadOnceProgram

end Cslib.BranchingPrograms
