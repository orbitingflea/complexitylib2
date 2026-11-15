/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Deterministic branching programs

A *deterministic branching program* over inputs `x : ι → α` is a directed acyclic graph in which
every node is either a sink returning a Boolean output or a query node that reads a coordinate
`i : ι` and moves to the node chosen by the letter `x i`. Its output on `x` is the sink reached
from a designated start node [Arora and Barak, Section 13.4.4][AroraBarak07],
[Jukna, Section 1.3][Jukna2012]. Any coordinate may be queried at any node, and a coordinate may be
queried several times along a path.

The nodes are listed in a topological order. `BranchingProgram.Nodes ι α n` is a sequence of `n`
nodes in which a query node moves only to earlier nodes, so acyclicity is part of the
representation, as it is for the straight-line programs `Cslib.Circuits.Program`. A
`BranchingProgram` is such a sequence with a start node, and its `size` is its number of nodes, the
measure `BP(f)` of [Jukna, Section 15.1][Jukna2012]. The output (`BranchingProgram.eval`) is
defined by structural recursion on the sequence, so it computes by `decide` on a concrete program.
The sources fix one accepting and one rejecting sink; here any number of nodes may be sinks.

A program is often easier to describe as a graph on a finite type of structured nodes, such as the
configurations of a machine, with a rank that decreases along every edge
(`BranchingProgram.Graph`). Listing the nodes of such a graph by rank gives a branching program
with one node for each node of the graph (`BranchingProgram.Graph.toBranchingProgram`,
`BranchingProgram.Graph.size_toBranchingProgram`), whose outputs unfold along the edges of the
graph (`BranchingProgram.Graph.evalNode_sink`, `BranchingProgram.Graph.evalNode_branch`).

## Main definitions

* `Cslib.BranchingPrograms.BranchingProgram.Step`: the action at a node, a sink or a query.
* `Cslib.BranchingPrograms.BranchingProgram.Nodes`: a sequence of nodes in topological order.
* `Cslib.BranchingPrograms.BranchingProgram`: a deterministic branching program.
* `Cslib.BranchingPrograms.BranchingProgram.eval`: the output of a program on an input.
* `Cslib.BranchingPrograms.BranchingProgram.const`,
  `Cslib.BranchingPrograms.BranchingProgram.rename`,
  `Cslib.BranchingPrograms.BranchingProgram.comap`: constant programs, and change of coordinates
  and of alphabet.
* `Cslib.BranchingPrograms.BranchingProgram.Graph`: a program described as a ranked graph on any
  node type.
* `Cslib.BranchingPrograms.BranchingProgram.Graph.toBranchingProgram`: the branching program of a
  graph on a finite node type.

## Main results

* `Cslib.BranchingPrograms.BranchingProgram.Graph.evalNode_sink`,
  `Cslib.BranchingPrograms.BranchingProgram.Graph.evalNode_branch`: the outputs of the program of
  a graph follow the edges of the graph.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Section 13.4.4][AroraBarak07]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Sections 1.3 and
  15.1][Jukna2012]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

/-- The action at a node of a deterministic branching program over inputs `ι → α` whose successors
lie in `Node`: either a sink returning a Boolean value, or a query that reads coordinate `i` and
moves to `next a` on the letter `a`. -/
inductive BranchingProgram.Step (ι α Node : Type*) where
  /-- A sink returning `b`. -/
  | sink (b : Bool)
  /-- A query reading coordinate `i` and moving to `next a` on the letter `a`. -/
  | branch (i : ι) (next : α → Node)

namespace BranchingProgram

variable {ι κ α β Node : Type*}

/-- The action that queries `f i` wherever `step` queries `i`. -/
def Step.rename (f : ι → κ) : Step ι α Node → Step κ α Node
  | .sink b => .sink b
  | .branch i next => .branch (f i) next

/-- The action over the alphabet `β` that reads each letter `b` as `g b`. -/
def Step.comap (g : β → α) : Step ι α Node → Step ι β Node
  | .sink b => .sink b
  | .branch i next => .branch i (next ∘ g)

/-- A sequence of `n` nodes in topological order: each node is a sink, or queries a coordinate and
moves to an earlier node. -/
inductive Nodes (ι α : Type*) : ℕ → Type _ where
  /-- The empty sequence. -/
  | empty : Nodes ι α 0
  /-- The nodes of `P` followed by a node acting by `step`. -/
  | node {n : ℕ} (P : Nodes ι α n) (step : Step ι α (Fin n)) : Nodes ι α (n + 1)

namespace Nodes

/-- The output reached from each node on the input `x`. -/
def eval (x : ι → α) : {n : ℕ} → Nodes ι α n → Fin n → Bool
  | _, empty, v => v.elim0
  | _, node P step, v =>
    Fin.lastCases
      (match step with
        | .sink b => b
        | .branch i next => P.eval x (next (x i)))
      (P.eval x) v

/-- An earlier node reaches the same output in a longer sequence. -/
@[simp] theorem eval_node_castSucc {n : ℕ} (P : Nodes ι α n) (step : Step ι α (Fin n))
    (x : ι → α) (v : Fin n) : (P.node step).eval x v.castSucc = P.eval x v := by
  simp [eval]

/-- A sink returns its value. -/
@[simp] theorem eval_node_last_sink {n : ℕ} (P : Nodes ι α n) (b : Bool) (x : ι → α) :
    (P.node (.sink b)).eval x (Fin.last n) = b := by
  simp [eval]

/-- A query node reaches the output of the node it moves to. -/
@[simp] theorem eval_node_last_branch {n : ℕ} (P : Nodes ι α n) (i : ι) (next : α → Fin n)
    (x : ι → α) : (P.node (.branch i next)).eval x (Fin.last n) = P.eval x (next (x i)) := by
  simp [eval]

/-- The sequence that queries `f i` wherever `P` queries `i`. -/
def rename (f : ι → κ) : {n : ℕ} → Nodes ι α n → Nodes κ α n
  | _, empty => empty
  | _, node P step => node (P.rename f) (step.rename f)

/-- Renaming the coordinates by `f` evaluates on `x ∘ f`. -/
@[simp] theorem eval_rename (f : ι → κ) (x : κ → α) :
    ∀ {n : ℕ} (P : Nodes ι α n) (v : Fin n), (P.rename f).eval x v = P.eval (x ∘ f) v
  | _, empty, v => v.elim0
  | _, node P step, v => by
    induction v using Fin.lastCases with
    | last => cases step <;> simp [rename, Step.rename, eval_rename f x P]
    | cast v => simp [rename, eval_rename f x P]

/-- The sequence over the alphabet `β` that reads each letter `b` as `g b`. -/
def comap (g : β → α) : {n : ℕ} → Nodes ι α n → Nodes ι β n
  | _, empty => empty
  | _, node P step => node (P.comap g) (step.comap g)

/-- Pulling back along `g` evaluates on `g ∘ x`. -/
@[simp] theorem eval_comap (g : β → α) (x : ι → β) :
    ∀ {n : ℕ} (P : Nodes ι α n) (v : Fin n), (P.comap g).eval x v = P.eval (g ∘ x) v
  | _, empty, v => v.elim0
  | _, node P step, v => by
    induction v using Fin.lastCases with
    | last => cases step <;> simp [comap, Step.comap, eval_comap g x P]
    | cast v => simp [comap, eval_comap g x P]

/-- The sequence whose node `k` acts by `f k`. -/
def ofFn : {n : ℕ} → ((k : ℕ) → k < n → Step ι α (Fin k)) → Nodes ι α n
  | 0, _ => empty
  | n + 1, f => node (ofFn fun k hk => f k (Nat.lt_succ_of_lt hk)) (f n (Nat.lt_succ_self n))

/-- A sink of `ofFn f` returns its value. -/
theorem eval_ofFn_sink (x : ι → α) :
    ∀ {n : ℕ} (f : (k : ℕ) → k < n → Step ι α (Fin k)) (k : ℕ) (hk : k < n) {b : Bool},
      f k hk = .sink b → (ofFn f).eval x ⟨k, hk⟩ = b
  | 0, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, k, hk, b, hf => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact (eval_node_castSucc _ _ x ⟨k, hlt⟩).trans
        (eval_ofFn_sink x (fun k hk => f k (Nat.lt_succ_of_lt hk)) k hlt hf)
    · rw [ofFn, hf]
      exact eval_node_last_sink _ b x

/-- A query node of `ofFn f` reaches the output of the node it moves to. -/
theorem eval_ofFn_branch (x : ι → α) :
    ∀ {n : ℕ} (f : (k : ℕ) → k < n → Step ι α (Fin k)) (k : ℕ) (hk : k < n) {i : ι}
      {next : α → Fin k}, f k hk = .branch i next →
        (ofFn f).eval x ⟨k, hk⟩ = (ofFn f).eval x ((next (x i)).castLE hk.le)
  | 0, _, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, k, hk, i, next, hf => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact (eval_node_castSucc _ _ x ⟨k, hlt⟩).trans
        ((eval_ofFn_branch x (fun k hk => f k (Nat.lt_succ_of_lt hk)) k hlt hf).trans
          (eval_node_castSucc _ _ x _).symm)
    · rw [ofFn, hf]
      exact (eval_node_last_branch _ i next x).trans (eval_node_castSucc _ _ x _).symm

end Nodes

end BranchingProgram

/-- A *deterministic branching program* over inputs `ι → α`: nodes in topological order, each a
sink or a query moving to an earlier node, with a start node
[Arora and Barak, Section 13.4.4][AroraBarak07]. Its size is its number of nodes
[Jukna, Section 15.1][Jukna2012]. -/
structure BranchingProgram (ι α : Type*) where
  /-- The number of nodes. -/
  {size : ℕ}
  /-- The nodes, in topological order. -/
  nodes : BranchingProgram.Nodes ι α size
  /-- The start node. -/
  start : Fin size

namespace BranchingProgram

variable {ι κ α β Node : Type*}

/-- The output of `P` on the input `x`: the value of the sink reached from the start node. -/
def eval (P : BranchingProgram ι α) (x : ι → α) : Bool :=
  P.nodes.eval x P.start

/-- The one-node branching program returning the constant `b`. -/
def const (ι α : Type*) (b : Bool) : BranchingProgram ι α where
  nodes := .node .empty (.sink b)
  start := 0

/-- The constant program returns its value on every input. -/
@[simp] theorem eval_const (b : Bool) (x : ι → α) : (const ι α b).eval x = b :=
  Nodes.eval_node_last_sink .empty b x

/-- The constant program has one node. -/
@[simp] theorem size_const (b : Bool) : (const ι α b).size = 1 :=
  rfl

/-- A branching program with at most one node cannot query its input, so it is constant. -/
theorem eval_eq_of_size_le_one (P : BranchingProgram ι α) (hsize : P.size ≤ 1) (x y : ι → α) :
    P.eval x = P.eval y := by
  obtain ⟨nodes, start⟩ := P
  rename_i size
  obtain rfl : size = 1 := le_antisymm hsize (Nat.one_le_of_lt start.isLt)
  obtain rfl : start = Fin.last 0 := Subsingleton.elim _ _
  cases nodes with
  | node P step =>
    cases step with
    | sink b => rfl
    | branch i next => exact (next (x i)).elim0

/-- The branching program that queries `f i` wherever `P` queries `i`. -/
def rename (f : ι → κ) (P : BranchingProgram ι α) : BranchingProgram κ α where
  nodes := P.nodes.rename f
  start := P.start

/-- Renaming the coordinates by `f` evaluates on `x ∘ f`. -/
@[simp] theorem eval_rename (f : ι → κ) (P : BranchingProgram ι α) (x : κ → α) :
    (P.rename f).eval x = P.eval (x ∘ f) :=
  Nodes.eval_rename f x P.nodes P.start

/-- Renaming the coordinates keeps the nodes. -/
@[simp] theorem size_rename (f : ι → κ) (P : BranchingProgram ι α) : (P.rename f).size = P.size :=
  rfl

/-- The branching program over the alphabet `β` that reads each letter `b` as `g b`. -/
def comap (g : β → α) (P : BranchingProgram ι α) : BranchingProgram ι β where
  nodes := P.nodes.comap g
  start := P.start

/-- Pulling back along `g` evaluates on `g ∘ x`. -/
@[simp] theorem eval_comap (g : β → α) (P : BranchingProgram ι α) (x : ι → β) :
    (P.comap g).eval x = P.eval (g ∘ x) :=
  Nodes.eval_comap g x P.nodes P.start

/-- Pulling back along a map of alphabets keeps the nodes. -/
@[simp] theorem size_comap (g : β → α) (P : BranchingProgram ι α) : (P.comap g).size = P.size :=
  rfl

/-! ### Programs described as graphs -/

/-- A deterministic branching program described as a graph on the nodes `Node`: each node is a sink
or a query, and every edge out of a query node leads to a node of strictly smaller `rank`, which
makes the graph acyclic. For finite `Node`, `Graph.toBranchingProgram` lists the nodes by rank. -/
structure Graph (ι α Node : Type*) where
  /-- The start node. -/
  start : Node
  /-- The action at each node. -/
  node : Node → Step ι α Node
  /-- A rank decreasing along every edge. -/
  rank : Node → ℕ
  /-- Every edge out of a query node leads to a node of strictly smaller rank. -/
  rank_lt : ∀ v i next a, node v = .branch i next → rank (next a) < rank v

namespace Graph

variable [Fintype Node] (G : Graph ι α Node)

/-- A linear order on the nodes in which nodes of smaller rank come first. -/
@[instance_reducible]
private noncomputable def rankOrder : LinearOrder Node :=
  LinearOrder.lift' (fun v => toLex (G.rank v, Fintype.equivFin Node v)) fun _ _ h =>
    (Fintype.equivFin Node).injective (congrArg (fun p => (ofLex p).2) h)

/-- An enumeration of the nodes in which nodes of smaller rank come first. -/
private noncomputable def index : Node ≃ Fin (Fintype.card Node) :=
  letI := G.rankOrder
  (monoEquivOfFin Node rfl).symm.toEquiv

/-- A node of smaller rank has a smaller index. -/
private theorem index_lt_index {u v : Node} (h : G.rank u < G.rank v) : G.index u < G.index v := by
  let := G.rankOrder
  have huv : u < v := Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  exact (monoEquivOfFin Node rfl).symm.strictMono huv

/-- The action at the node of index `k`, on the indices of its successors. -/
private noncomputable def stepAt (k : ℕ) (hk : k < Fintype.card Node) : Step ι α (Fin k) :=
  match h : G.node (G.index.symm ⟨k, hk⟩) with
  | .sink b => .sink b
  | .branch i next => .branch i fun a =>
    ⟨G.index (next a), by
      have hlt := G.index_lt_index (G.rank_lt _ i next a h)
      rw [Equiv.apply_symm_apply] at hlt
      exact hlt⟩

/-- The branching program of a graph on a finite node type: its nodes listed by rank. -/
@[no_expose]
noncomputable def toBranchingProgram : BranchingProgram ι α where
  nodes := Nodes.ofFn G.stepAt
  start := G.index G.start

/-- The branching program of a graph has one node for each node of the graph. -/
@[simp] theorem size_toBranchingProgram : G.toBranchingProgram.size = Fintype.card Node := by
  unfold toBranchingProgram
  rfl

/-- The output the branching program of `G` reaches from the node `v` on the input `x`. -/
@[no_expose]
noncomputable def evalNode (x : ι → α) (v : Node) : Bool :=
  G.toBranchingProgram.nodes.eval x (G.index v)

/-- The output of the branching program of `G` is the output reached from the start node. -/
theorem eval_toBranchingProgram (x : ι → α) :
    G.toBranchingProgram.eval x = G.evalNode x G.start := by
  unfold evalNode BranchingProgram.eval toBranchingProgram
  rfl

variable {G}

/-- A sink of the graph returns its value. -/
theorem evalNode_sink (x : ι → α) {v : Node} {b : Bool} (h : G.node v = .sink b) :
    G.evalNode x v = b := by
  have hk : G.node (G.index.symm ⟨G.index v, (G.index v).isLt⟩) = .sink b := by
    rw [Fin.eta, Equiv.symm_apply_apply, h]
  have hstep : G.stepAt (G.index v) (G.index v).isLt = .sink b := by
    unfold stepAt
    split <;> rename_i heq
    · rw [hk] at heq
      cases heq
      rfl
    · rw [hk] at heq
      cases heq
  exact Nodes.eval_ofFn_sink x G.stepAt _ _ hstep

/-- A query node of the graph reaches the output of the node it moves to. -/
theorem evalNode_branch (x : ι → α) {v : Node} {i : ι} {next : α → Node}
    (h : G.node v = .branch i next) : G.evalNode x v = G.evalNode x (next (x i)) := by
  have hk : G.node (G.index.symm ⟨G.index v, (G.index v).isLt⟩) = .branch i next := by
    rw [Fin.eta, Equiv.symm_apply_apply, h]
  have hstep : ∃ hlt : ∀ a, (G.index (next a) : ℕ) < G.index v,
      G.stepAt (G.index v) (G.index v).isLt = .branch i fun a => ⟨G.index (next a), hlt a⟩ := by
    unfold stepAt
    split <;> rename_i heq
    · rw [hk] at heq
      cases heq
    · rw [hk] at heq
      cases heq
      exact ⟨fun a => G.index_lt_index (G.rank_lt v i next a h), rfl⟩
  obtain ⟨hlt, hstep⟩ := hstep
  exact Nodes.eval_ofFn_branch x G.stepAt _ _ hstep

end Graph

end BranchingProgram

end Cslib.BranchingPrograms
