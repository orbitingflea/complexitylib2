/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnce
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

/-!
# Deterministic branching programs

A *deterministic branching program* over inputs `x : ι → α`, on a type `Node` of nodes, is a
directed acyclic graph with a distinguished start node `start` in which every node is either a
terminal sink returning a Boolean output (`.sink b`) or an internal query node reading an input
coordinate `i : ι` and branching to `next (x i)` (`.branch i next`)
[Arora and Barak, Section 13.4.4][AroraBarak07]. Unlike read-once branching programs
(`Cslib.BranchingPrograms.ReadOnceProgram`), any coordinate may be queried at any node and a
coordinate may be queried multiple times along a path. Acyclicity is witnessed by a topological
rank `rank : Node → ℕ` that strictly decreases along every outgoing edge of a query node. For a
finite node type `Node`, the *size* of the program (`BranchingProgram.size`) is its number of
nodes `Fintype.card Node`. Whereas Arora and Barak's Section 13.4.4 fixes two designated
outdegree-zero nodes (`ACCEPT` and `REJECT`), `BranchingProgram` allows multiple `.sink b` nodes;
coalescing equal-output sinks adds at most one node when only one output value appears, and never
increases `size` when at least two sink nodes exist (as in `MultiTapeTM.toBranchingProgram`).

Evaluation (`BranchingProgram.evalNode`, `BranchingProgram.eval`) is defined by structural
recursion on an upper bound for `rank`, so it unfolds directly by `evalNode_sink` and
`evalNode_branch` and computes by `decide` on concrete finite inputs. Every read-once branching
program of length `L` and state type `S` embeds as a layered general branching program on
`Fin (L + 1) × S` (`ReadOnceProgram.toBranchingProgram`, `ReadOnceProgram.eval_toBranchingProgram`,
`ReadOnceProgram.size_toBranchingProgram`).

## Main definitions

* `Cslib.BranchingPrograms.BranchingProgram.Step`: the action at a node (a terminal `.sink` or a
  coordinate query `.branch`).
* `Cslib.BranchingPrograms.BranchingProgram`: a deterministic acyclic branching program.
* `Cslib.BranchingPrograms.BranchingProgram.evalNode`,
  `Cslib.BranchingPrograms.BranchingProgram.eval`: evaluation from a node and from the start node.
* `Cslib.BranchingPrograms.BranchingProgram.size`: the node count `Fintype.card Node`.
* `Cslib.BranchingPrograms.BranchingProgram.const`,
  `Cslib.BranchingPrograms.BranchingProgram.rename`,
  `Cslib.BranchingPrograms.BranchingProgram.comap`: constant programs and pullbacks along
  coordinate or alphabet maps.
* `Cslib.BranchingPrograms.ReadOnceProgram.toBranchingProgram`: a read-once branching program
  viewed as a general branching program on `Fin (L + 1) × S`.

## Main results

* `Cslib.BranchingPrograms.BranchingProgram.evalNode_sink`,
  `Cslib.BranchingPrograms.BranchingProgram.evalNode_branch`: unfolding equations for evaluation.
* `Cslib.BranchingPrograms.BranchingProgram.induction_on`: well-founded induction along `rank`.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_toBranchingProgram`,
  `Cslib.BranchingPrograms.ReadOnceProgram.size_toBranchingProgram`: semantics and node count of
  the embedded read-once program.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Section 13.4.4][AroraBarak07]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 14][Jukna2012]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

/-- The action at a node of a deterministic branching program over inputs `ι → α` with nodes
`Node`: either a terminal sink returning a Boolean value, or a query node that reads coordinate `i`
and follows `next` on the letter read. -/
inductive BranchingProgram.Step (ι α Node : Type*) where
  /-- A terminal sink returning `b`. -/
  | sink (b : Bool)
  /-- An internal query node reading coordinate `i` and moving to `next a` on letter `a`. -/
  | branch (i : ι) (next : α → Node)

/-- A *deterministic branching program* over inputs `ι → α` on the nodes `Node`: a directed acyclic
graph with a start node `start`, where each node is either a terminal sink or a coordinate query
whose outgoing edges strictly decrease `rank` [Arora and Barak, Section 13.4.4][AroraBarak07].
For finite `Node`, its size is the node count `Fintype.card Node` (`BranchingProgram.size`). -/
structure BranchingProgram (ι α Node : Type*) where
  /-- The start node. -/
  start : Node
  /-- The action at each node: a terminal sink or a coordinate query. -/
  node : Node → BranchingProgram.Step ι α Node
  /-- A topological rank decreasing along every outgoing edge of a query node. -/
  rank : Node → ℕ
  /-- Every outgoing edge of a query node leads to a node of strictly smaller rank. -/
  rank_lt : ∀ v i next a, node v = .branch i next → rank (next a) < rank v

namespace BranchingProgram

variable {ι κ α β Node : Type*} (P : BranchingProgram ι α Node)

/-- Evaluation of `P` on `x` from a node `v` of rank `< k`, by structural recursion on `k`. -/
def evalBelow (x : ι → α) : (k : ℕ) → (v : Node) → P.rank v < k → Bool
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, v, h =>
    match hn : P.node v with
    | .sink b => b
    | .branch i next =>
      evalBelow x k (next (x i))
        (Nat.lt_of_lt_of_le (P.rank_lt v i next (x i) hn) (Nat.le_of_lt_succ h))

theorem evalBelow_congr (x : ι → α) :
    ∀ (k k' : ℕ) (v : Node) (h : P.rank v < k) (h' : P.rank v < k'),
      P.evalBelow x k v h = P.evalBelow x k' v h'
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h' => absurd h' (Nat.not_lt_zero _)
  | k + 1, k' + 1, v, h, h' => by
    simp only [evalBelow]
    split
    · rfl
    · apply evalBelow_congr

/-- The output of `P` on input `x` when started at node `v`. -/
def evalNode (x : ι → α) (v : Node) : Bool :=
  P.evalBelow x (P.rank v + 1) v (Nat.lt_succ_self _)

/-- The output of `P` on input `x`, started at `P.start`. -/
def eval (x : ι → α) : Bool :=
  P.evalNode x P.start

/-- The *size* of a branching program on a finite node type: its number of nodes. -/
@[nolint unusedArguments]
def size (_P : BranchingProgram ι α Node) [Fintype Node] : ℕ :=
  Fintype.card Node

variable {P}

/-- Unfolding `evalNode` at a terminal sink. -/
theorem evalNode_sink (x : ι → α) {v : Node} {b : Bool} (h : P.node v = .sink b) :
    P.evalNode x v = b := by
  conv_lhs => rw [evalNode, evalBelow]
  split
  · rename_i b' heq
    rw [h] at heq
    injection heq with hb
    exact hb.symm
  · rename_i j next' heq
    rw [h] at heq
    cases heq

/-- Unfolding `evalNode` at a coordinate query node. -/
theorem evalNode_branch (x : ι → α) {v : Node} {i : ι} {next : α → Node}
    (h : P.node v = .branch i next) :
    P.evalNode x v = P.evalNode x (next (x i)) := by
  conv_lhs => rw [evalNode, evalBelow]
  split
  · rename_i b heq
    rw [h] at heq
    cases heq
  · rename_i j next' heq
    rw [h] at heq
    injection heq with hij hnext
    subst hij hnext
    exact P.evalBelow_congr x _ _ _ _ _

/-- **Induction on nodes** along the topological rank `P.rank`. -/
theorem induction_on {M : Node → Prop}
    (h : ∀ v, (∀ u, P.rank u < P.rank v → M u) → M v) (v : Node) : M v := by
  obtain ⟨n, hn⟩ : ∃ n, P.rank v = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih => exact h v fun u hu => ih (P.rank u) (hn ▸ hu) u rfl

/-- The one-node branching program returning the constant `b`. -/
def const (ι α : Type*) (b : Bool) : BranchingProgram ι α Unit where
  start := ()
  node _ := .sink b
  rank _ := 0
  rank_lt _ _ _ _ h := by cases h

@[simp]
theorem eval_const (b : Bool) (x : ι → α) : (const ι α b).eval x = b :=
  evalNode_sink x rfl

@[simp]
theorem size_const (b : Bool) : (const ι α b).size = 1 :=
  Fintype.card_unit

/-- A branching program of size at most `1` cannot branch (since any outgoing edge would strictly
decrease `rank` within a subsingleton), so its evaluation is constant across all inputs. -/
theorem eval_eq_of_size_le_one [Fintype Node] (hsize : P.size ≤ 1) (x y : ι → α) :
    P.eval x = P.eval y := by
  have hsub : Subsingleton Node := Fintype.card_le_one_iff_subsingleton.mp hsize
  cases hn : P.node P.start with
  | sink b =>
    rw [eval, evalNode_sink x hn, eval, evalNode_sink y hn]
  | branch i next =>
    exact absurd (Subsingleton.elim (next (x i)) P.start ▸ P.rank_lt P.start i next (x i) hn)
      (Nat.lt_irrefl _)

/-- The branching program that queries `f i` whenever `P` queries `i`. -/
def rename (f : ι → κ) (P : BranchingProgram ι α Node) : BranchingProgram κ α Node where
  start := P.start
  node v := match P.node v with
    | .sink b => .sink b
    | .branch i next => .branch (f i) next
  rank := P.rank
  rank_lt v j next a h := by
    cases hn : P.node v with
    | sink b =>
      rw [hn] at h
      cases h
    | branch i next' =>
      rw [hn] at h
      injection h with _ hnext
      subst hnext
      exact P.rank_lt v i next' a hn

@[simp]
theorem evalNode_rename (f : ι → κ) (P : BranchingProgram ι α Node) (x : κ → α) (v : Node) :
    (P.rename f).evalNode x v = P.evalNode (x ∘ f) v := by
  induction v using P.induction_on with
  | h v ih =>
    cases hn : P.node v with
    | sink b =>
      have hn' : (P.rename f).node v = .sink b := by simp [rename, hn]
      rw [evalNode_sink _ hn', evalNode_sink _ hn]
    | branch i next =>
      have hn' : (P.rename f).node v = .branch (f i) next := by simp [rename, hn]
      rw [evalNode_branch _ hn', evalNode_branch _ hn,
        ih (next (x (f i))) (P.rank_lt v i next (x (f i)) hn)]
      rfl

@[simp]
theorem eval_rename (f : ι → κ) (P : BranchingProgram ι α Node) (x : κ → α) :
    (P.rename f).eval x = P.eval (x ∘ f) :=
  evalNode_rename f P x P.start

@[simp]
theorem size_rename (f : ι → κ) (P : BranchingProgram ι α Node) [Fintype Node] :
    (P.rename f).size = P.size :=
  rfl

/-- The branching program over `β` that translates each input letter along `g : β → α`. -/
def comap (g : β → α) (P : BranchingProgram ι α Node) : BranchingProgram ι β Node where
  start := P.start
  node v := match P.node v with
    | .sink b => .sink b
    | .branch i next => .branch i (next ∘ g)
  rank := P.rank
  rank_lt v i next b h := by
    cases hn : P.node v with
    | sink b' =>
      rw [hn] at h
      cases h
    | branch i' next' =>
      rw [hn] at h
      injection h with hi hnext
      subst hi hnext
      exact P.rank_lt v i' next' (g b) hn

@[simp]
theorem evalNode_comap (g : β → α) (P : BranchingProgram ι α Node) (x : ι → β) (v : Node) :
    (P.comap g).evalNode x v = P.evalNode (g ∘ x) v := by
  induction v using P.induction_on with
  | h v ih =>
    cases hn : P.node v with
    | sink b =>
      have hn' : (P.comap g).node v = .sink b := by simp [comap, hn]
      rw [evalNode_sink _ hn', evalNode_sink _ hn]
    | branch i next =>
      have hn' : (P.comap g).node v = .branch i (next ∘ g) := by simp [comap, hn]
      rw [evalNode_branch _ hn', evalNode_branch _ hn]
      exact ih (next (g (x i))) (P.rank_lt v i next (g (x i)) hn)

@[simp]
theorem eval_comap (g : β → α) (P : BranchingProgram ι α Node) (x : ι → β) :
    (P.comap g).eval x = P.eval (g ∘ x) :=
  evalNode_comap g P x P.start

@[simp]
theorem size_comap (g : β → α) (P : BranchingProgram ι α Node) [Fintype Node] :
    (P.comap g).size = P.size :=
  rfl

end BranchingProgram

/-! ### Embedding read-once branching programs -/

namespace ReadOnceProgram

variable {L : ℕ} {S X : Type*} (P : ReadOnceProgram L S X)

/-- A read-once branching program of length `L` with state type `S` as a general branching program
on `Fin (L + 1) × S`: at layer `t < L` it queries position `t` and steps to layer `t + 1`, and at
layer `L` it is a sink returning `P.accept`. -/
def toBranchingProgram : BranchingProgram (Fin L) X (Fin (L + 1) × S) where
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

/-- Evaluating `P.toBranchingProgram` from `(t, s)` runs `P` from time `t` and state `s`. -/
theorem evalNode_toBranchingProgram (x : Fin L → X) :
    ∀ (k : ℕ) (t : Fin (L + 1)) (s : S), L - t.val = k →
      P.toBranchingProgram.evalNode x (t, s) = P.accept (P.runFrom x t.val s) := by
  intro k
  induction k with
  | zero =>
    intro t s hk
    have ht : L ≤ t.val := by omega
    have hnode : P.toBranchingProgram.node (t, s) = .sink (P.accept s) :=
      dite_eq_right (not_lt.mpr ht)
    rw [BranchingProgram.evalNode_sink x hnode, P.runFrom_of_le x ht]
  | succ k ih =>
    intro t s hk
    have ht : t.val < L := by omega
    have hnode : P.toBranchingProgram.node (t, s) =
        .branch ⟨t.val, ht⟩
          (fun a => ((⟨t.val, ht⟩ : Fin L).succ, P.step ⟨t.val, ht⟩ s a)) :=
      dite_eq_left ht
    rw [BranchingProgram.evalNode_branch x hnode,
      ih (⟨t.val, ht⟩ : Fin L).succ (P.step ⟨t.val, ht⟩ s (x ⟨t.val, ht⟩))
        (by simp only [Fin.val_succ]; omega),
      Fin.val_succ, ← P.runFrom_step x ht s]

/-- **Embedding preserves evaluation**: `P.toBranchingProgram` computes the same function as `P`. -/
@[simp]
theorem eval_toBranchingProgram (x : Fin L → X) :
    P.toBranchingProgram.eval x = P.eval x := by
  rw [BranchingProgram.eval, show P.toBranchingProgram.start = (0, P.start) from rfl,
    P.evalNode_toBranchingProgram x L 0 P.start (by simp), Fin.val_zero, P.runFrom_zero, eval]

/-- The embedded read-once program has `(L + 1) * Fintype.card S` nodes. -/
@[simp]
theorem size_toBranchingProgram [Fintype S] :
    P.toBranchingProgram.size = (L + 1) * Fintype.card S := by
  simp [BranchingProgram.size]

end ReadOnceProgram

end Cslib.BranchingPrograms
