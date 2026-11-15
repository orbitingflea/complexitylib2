/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup

/-!
# Nondeterministic branching programs

A *nondeterministic branching program* over inputs `x : ι → α` is a directed acyclic multigraph
with a source and a target, in which each wire is either unlabelled (a *rectifier*) or labelled by
a test `x i = a` (a *contact*). An input switches on the rectifiers and the contacts whose tests it
passes, and the program accepts it when some path from the source to the target uses only wires
that are switched on. The size of a program is its number of contacts
[Jukna, Section 1.3][Jukna2012]. Over `Bool` the tests are the literals; tests over a larger
alphabet are those of [Jukna, Section 15.2][Jukna2012].

`NBP ι α n` lists `n` nodes in a topological order, as `BranchingProgram.Nodes` does for
deterministic programs: the first node is the target, each later node is given by the list of
wires leaving it for earlier nodes, and the last node is the source. The number of paths from a
node to the target that an input switches on is defined by structural recursion (`NBP.paths`,
`NBP.pathCount`), so it computes by `decide` on a concrete program. This one count gives the
modes of acceptance: a nondeterministic program accepts when the count is nonzero (`NBP.Accepts`),
and a parity branching program when it is odd (`NBP.AcceptsParity`).

A deterministic branching program is a nondeterministic one in which every input switches on
exactly one way out of each query node: a query node has a contact for each letter and an accepting
sink has a rectifier to the target (`BranchingProgram.toNBP`). Its path count is `1` on the inputs
it accepts and `0` on the others (`BranchingProgram.pathCount_toNBP`), and it has at most
`Fintype.card α` contacts for each node of the deterministic program
(`BranchingProgram.size_toNBP_le`).

## Main definitions

* `Cslib.BranchingPrograms.NBP.Wire`: a wire to an earlier node, a rectifier or a contact.
* `Cslib.BranchingPrograms.NBP`: a nondeterministic branching program.
* `Cslib.BranchingPrograms.NBP.size`: its number of contacts.
* `Cslib.BranchingPrograms.NBP.pathCount`: the number of source-to-target paths an input switches
  on.
* `Cslib.BranchingPrograms.NBP.Accepts`, `Cslib.BranchingPrograms.NBP.AcceptsParity`:
  nondeterministic and parity acceptance.
* `Cslib.BranchingPrograms.BranchingProgram.toNBP`: a deterministic program as a nondeterministic
  one.

## Main results

* `Cslib.BranchingPrograms.BranchingProgram.pathCount_toNBP`: a deterministic program switches on
  one path on the inputs it accepts and none on the others.
* `Cslib.BranchingPrograms.BranchingProgram.size_toNBP_le`: it has at most `Fintype.card α`
  contacts for each of its nodes.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Sections 1.3 and
  15.2][Jukna2012]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

/-- A wire leaving a node of a nondeterministic branching program for one of the `n` earlier
nodes: a rectifier, or a contact testing one coordinate of the input. -/
structure NBP.Wire (ι α : Type*) (n : ℕ) where
  /-- The earlier node the wire leads to. -/
  head : Fin n
  /-- `none` for a rectifier, and `some (i, a)` for a contact testing `x i = a`. -/
  label : Option (ι × α)

/-- A *nondeterministic branching program* over inputs `ι → α`, with `n` nodes in topological
order: the first node is the target, each later node has a list of wires to earlier nodes, and the
last node is the source [Jukna, Section 1.3][Jukna2012]. -/
inductive NBP (ι α : Type*) : ℕ → Type _ where
  /-- The program whose only node is the target. -/
  | target : NBP ι α 1
  /-- The nodes of `P` followed by a node with the given wires to them. -/
  | node {n : ℕ} (P : NBP ι α n) (wires : List (NBP.Wire ι α n)) : NBP ι α (n + 1)

namespace NBP

variable {ι α : Type*}

/-- The size of a program: its number of contacts. -/
def size : {n : ℕ} → NBP ι α n → ℕ
  | _, target => 0
  | _, node P wires => P.size + wires.countP (·.label.isSome)

variable [DecidableEq α]

/-- Whether the input `x` switches the wire on: a rectifier always, and a contact when `x` passes
its test. -/
def Wire.on {n : ℕ} (w : Wire ι α n) (x : ι → α) : Bool :=
  w.label.all fun p => x p.1 = p.2

/-- The number of paths from each node to the target on which `x` switches every wire on. -/
def paths (x : ι → α) : {n : ℕ} → NBP ι α n → Fin n → ℕ
  | _, target, _ => 1
  | _, node P wires, v =>
    Fin.lastCases (((wires.filter (·.on x)).map fun w => P.paths x w.head).sum) (P.paths x) v

/-- An earlier node has the same paths in a longer program. -/
@[simp] theorem paths_node_castSucc {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (x : ι → α) (v : Fin n) : (P.node wires).paths x v.castSucc = P.paths x v := by
  simp [paths]

/-- The paths from the last node go through its wires that are switched on. -/
@[simp] theorem paths_node_last {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (x : ι → α) :
    (P.node wires).paths x (Fin.last n) =
      ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum := by
  simp [paths]

/-- The target has one path to itself, the empty one. -/
@[simp] theorem paths_zero (x : ι → α) : ∀ {n : ℕ} (P : NBP ι α (n + 1)), P.paths x 0 = 1
  | 0, target => rfl
  | _ + 1, node P wires => (paths_node_castSucc P wires x 0).trans (paths_zero x P)

/-- The number of paths from the source to the target on which `x` switches every wire on. -/
def pathCount : {n : ℕ} → NBP ι α n → (ι → α) → ℕ
  | _, target, _ => 1
  | _, node P wires, x => ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum

/-- A nondeterministic branching program *accepts* an input that switches on some path from the
source to the target. -/
def Accepts {n : ℕ} (P : NBP ι α n) (x : ι → α) : Prop :=
  P.pathCount x ≠ 0

instance {n : ℕ} (P : NBP ι α n) (x : ι → α) : Decidable (P.Accepts x) :=
  inferInstanceAs (Decidable (P.pathCount x ≠ 0))

/-- A *parity branching program* accepts an input that switches on an odd number of paths from the
source to the target [Jukna, Section 1.3][Jukna2012]. -/
def AcceptsParity {n : ℕ} (P : NBP ι α n) (x : ι → α) : Prop :=
  Odd (P.pathCount x)

instance {n : ℕ} (P : NBP ι α n) (x : ι → α) : Decidable (P.AcceptsParity x) :=
  inferInstanceAs (Decidable (Odd (P.pathCount x)))

end NBP

namespace BranchingProgram

variable {ι α : Type*} [Fintype α]

/-- The wires of a node of a deterministic program: a contact for each letter at a query node, a
rectifier to the target at an accepting sink, and no wire at a rejecting sink. -/
noncomputable def Step.wires {n : ℕ} : Step ι α (Fin n) → List (NBP.Wire ι α (n + 1))
  | .sink true => [⟨0, none⟩]
  | .sink false => []
  | .branch i next => Finset.univ.toList.map fun a => ⟨(next a).succ, some (i, a)⟩

/-- A sequence of deterministic nodes as a nondeterministic program: a new target, then the same
nodes with the wires `Step.wires`. -/
noncomputable def Nodes.toNBP : {n : ℕ} → Nodes ι α n → NBP ι α (n + 1)
  | _, .empty => .target
  | _, .node P step => .node P.toNBP step.wires

/-- A deterministic program as a nondeterministic one: a new source with a rectifier to the start
node. -/
noncomputable def toNBP (P : BranchingProgram ι α) : NBP ι α (P.size + 2) :=
  .node P.nodes.toNBP [⟨P.start.succ, none⟩]

/-- The nondeterministic program of a sequence of `n` deterministic nodes has at most
`Fintype.card α` contacts for each node. -/
theorem Nodes.size_toNBP_le :
    ∀ {n : ℕ} (P : Nodes ι α n), P.toNBP.size ≤ Fintype.card α * n
  | _, .empty => Nat.zero_le _
  | _, .node P step => by
    have ih := size_toNBP_le P
    have hstep : step.wires.countP (·.label.isSome) ≤ Fintype.card α := by
      cases step with
      | sink b => cases b <;> simp [Step.wires]
      | branch i next =>
        refine (List.countP_le_length).trans ?_
        simp [Step.wires]
    rw [toNBP, NBP.size, Nat.mul_succ]
    exact Nat.add_le_add ih hstep

/-- The nondeterministic program of a deterministic one has at most `Fintype.card α` contacts for
each node: its size, counting contacts, is at most `Fintype.card α` times the size, counting
nodes, of the deterministic program. -/
theorem size_toNBP_le (P : BranchingProgram ι α) :
    P.toNBP.size ≤ Fintype.card α * P.size := by
  simpa [toNBP, NBP.size] using Nodes.size_toNBP_le P.nodes

variable [DecidableEq α]

private theorem filter_on_wires (i : ι) {n : ℕ} (next : α → Fin n) (x : ι → α) :
    ((Finset.univ.toList.map fun a => (⟨(next a).succ, some (i, a)⟩ : NBP.Wire ι α (n + 1))).filter
      (·.on x)) = [⟨(next (x i)).succ, some (i, x i)⟩] := by
  have hon : ((fun w : NBP.Wire ι α (n + 1) => w.on x) ∘
      fun a => (⟨(next a).succ, some (i, a)⟩ : NBP.Wire ι α (n + 1))) =
      fun a => decide (a = x i) := by
    funext a
    simp [NBP.Wire.on, eq_comm]
  rw [List.filter_map, hon, List.filter_eq,
    List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.mpr (Finset.mem_univ _))]
  rfl

/-- From each node, a deterministic program switches on one path to the target when it reaches an
accepting sink, and none otherwise. -/
theorem Nodes.paths_toNBP (x : ι → α) :
    ∀ {n : ℕ} (P : Nodes ι α n) (v : Fin n),
      P.toNBP.paths x v.succ = if P.eval x v then 1 else 0
  | _, .empty, v => v.elim0
  | _, .node P step, v => by
    induction v using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, toNBP, NBP.paths_node_last]
      cases step with
      | sink b => cases b <;> simp [Step.wires, NBP.Wire.on]
      | branch i next =>
        rw [Step.wires, filter_on_wires, eval_node_last_branch]
        simp [paths_toNBP x P]
    | cast v =>
      rw [Fin.succ_castSucc, toNBP, NBP.paths_node_castSucc, eval_node_castSucc]
      exact paths_toNBP x P v

/-- **A deterministic branching program is an unambiguous nondeterministic one**: it switches on
one path from the source to the target on the inputs it accepts, and none on the others. -/
theorem pathCount_toNBP (P : BranchingProgram ι α) (x : ι → α) :
    P.toNBP.pathCount x = if P.eval x then 1 else 0 := by
  rw [eval, ← Nodes.paths_toNBP x P.nodes P.start]
  simp [toNBP, NBP.pathCount, NBP.Wire.on]

end BranchingProgram

end Cslib.BranchingPrograms
