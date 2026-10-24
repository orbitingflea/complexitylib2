/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.DijkstraBridge

/-! # Dijkstra's algorithm: shortest paths in `O((m + 1) log n)` time

Given a directed graph with `n` vertices, `m` edges and natural-number edge weights, and a source
vertex `s`, the single-source shortest-path problem asks for the distance from `s` to every
vertex. Dijkstra's algorithm with a binary heap solves it in `O((m + 1) log n)` time. The theorem
below states this bound for a program on the word RAM, with the graph given by adjacency lists.

The graph, its distances, the input and output layouts and the word-size condition are defined here
from scratch. The machine is the library's word RAM `Cslib.WordRAM` over its standard basis of
operations; the appendix says what a reader needs of it. To check that the theorem says what is
claimed, a reader only needs to inspect the definitions and the theorem statement in this file. Lean
checks the proof through `DijkstraBridge`, which proves that the distance here is the library's and
applies the library theorem `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement`.
`#check_abstract` checks mechanically that every definition and theorem statement here depends only
on this file, Lean, Mathlib, upstream CSLib, and the modules `Defs` and `Basis` of the library's
word RAM.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 24.3.
-/

namespace ComplexityAbstracts.DijkstraAbstract

variable {n : ℕ}

/-! ## Graphs and distances

The vertices are `0, …, n - 1` (the type `Fin n`). A walk is a sequence of edges, each leaving
the vertex the previous one enters; vertices and edges may repeat. Its weight is the sum of the
weights of its edges. The distance from `u` to `v` is the least weight of a walk from `u` to `v`,
in `ℕ∞ = ℕ ∪ {⊤}`, and `⊤` when there is no such walk. Weights are natural numbers, so a least
weight exists whenever a walk does.
-/

/-- A directed graph on the vertices `Fin n` with natural-number edge weights, given by adjacency
lists: `G u` holds a pair `(v, c)` for each edge from `u` to `v` of weight `c`. The same pair of
endpoints may appear more than once (parallel edges), and `v` may be `u` (self-loops). -/
abbrev Graph (n : ℕ) := Fin n → List (Fin n × ℕ)

/-- `IsWalk G u l v`: the list `l` of edges `(target, weight)` is a walk from `u` to `v`. Its
first edge is in the list `G u` of edges out of `u`, each later edge is in the list of edges out
of the target of the edge before it, and the target of its last edge is `v`. The empty walk goes
from `u` to `u`. -/
def IsWalk (G : Graph n) : Fin n → List (Fin n × ℕ) → Fin n → Prop
  | u, [], v => u = v
  | u, e :: l, v => e ∈ G u ∧ IsWalk G e.1 l v

/-- The **distance** from `u` to `v`: the least weight of a walk from `u` to `v`, the weight of
a walk being the sum of the weights of its edges, and `⊤` when there is no walk. -/
noncomputable def dist (G : Graph n) (u v : Fin n) : ℕ∞ :=
  ⨅ (l : List (Fin n × ℕ)) (_ : IsWalk G u l v), ((l.map Prod.snd).sum : ℕ∞)

/-- The number `m` of edges. -/
def numEdges (G : Graph n) : ℕ := ∑ u, (G u).length

/-- The largest edge weight, and `0` when there is no edge. -/
def maxWeight (G : Graph n) : ℕ :=
  Finset.univ.sup fun u => ((G u).map Prod.snd).foldr max 0

/-! ## Input, output and cost

The program reads the graph as a list of natural numbers: `n`, the source `s`, the `n + 1` offsets
of the adjacency lists in an array of edges, and then the `m` edges, each as two numbers, its target
and its weight. When it halts, the memory cell `outAddr G v` of each vertex `v` holds `0` when `v`
is unreachable from `s` and `d + 1` when the distance from `s` to `v` is `d`. The machine is a word
RAM with `w`-bit words, and the theorem asks `8 (n + m + 2) (W + 2) < 2 ^ w`, where `W` is the
largest weight, so a word size of order `log (n + m + W)` suffices. Each instruction costs one unit
of time, whatever its operands; the operations are those of the library's standard basis (`+`,
truncated `-`, `*`, `/`, `%`, bitwise operations and shifts), and a value of `2 ^ w` or more makes
the machine fault. The bound counts the instructions executed, the final `halt` included. The
appendix gives the exact layout (`offset`, `encode`, `outAddr`, `encodeDist`) and the machine.
-/

/-! ## Representation details

The input is a list of natural numbers: `n`, the source, the `n + 1` offsets of the adjacency
lists in the edge array, and the edges, in the order of the lists `G 0, …, G (n - 1)`, each as
two numbers, its target and its weight. This is the usual "compressed" layout: the edges out of
`u` are the edges `j` with `offset G u ≤ j < offset G (u + 1)`.

The machine stores the input of length `k = n + 2 m + 3` at addresses `1, …, k` (see
`Cslib.WordRAM.State.init` below). The output is the `n` memory cells just past it: the cell of
vertex `v` holds `0` when `v` is unreachable from the source and `d + 1` when its distance is `d`.
-/

/-- The offset of the adjacency list of vertex `u` in the edge array: the number of edges out of
the vertices below `u`. The offset of `n` is the number of edges. -/
def offset (G : Graph n) (u : ℕ) : ℕ :=
  (((List.finRange n).take u).map fun x => (G x).length).sum

/-- The input: `n`, the source `s`, the offsets of the vertices `0, …, n`, and then the edges of
`G 0, …, G (n - 1)` in order, each as its target and its weight. -/
def encode (G : Graph n) (s : Fin n) : List ℕ :=
  n :: (s : ℕ) ::
    ((List.range (n + 1)).map (offset G) ++
      (List.finRange n).flatMap fun u => (G u).flatMap fun e => [(e.1 : ℕ), e.2])

/-- The output address of vertex `v`: the input occupies addresses `0, …, n + 2 m + 3` (its length
at `0`), and the outputs follow it. -/
def outAddr (G : Graph n) (v : Fin n) : ℕ := n + 2 * numEdges G + 4 + v

/-- A distance as an output word: `0` for `⊤` (unreachable) and `d + 1` for distance `d`. -/
noncomputable def encodeDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

/-! **The machine.** The statement uses five names of the library's word RAM (`Cslib.WordRAM`, in
the allowlisted modules `Defs` and `Basis`). At word size `w`, a machine has registers `0, …, r - 1`
and a memory cell at every address `a : ℕ`, all holding natural numbers.

`Cslib.WordRAM.Program .standard r` is a program with `r` registers: a list of instructions,
numbered from `0`. The instructions load a constant, copy a register, apply an operation of the
standard basis to registers, load from and store to the memory cell whose address is in a
register, jump, branch on `=` or `<` of two registers, and halt. The standard operations are `+`,
truncated `-`, `*`, `/` and `%` (with Lean's `x / 0 = 0` and `x % 0 = x`), bitwise `and`, `or`,
`xor`, the shifts `x * 2 ^ y` and `x / 2 ^ y`, and reading `w`. A constant or an operation whose
value is not below `2 ^ w` faults: there is no wrap-around.

`Cslib.WordRAM.State.init input` is the start state: instruction `0`, all registers `0`, the
length of the input at address `0`, the input at addresses `1, 2, …`, and `0` elsewhere.

`Cslib.WordRAM.step w p t` is the outcome of executing one instruction from state `t`: a next
state, `.halt v` when the instruction is `halt` with output `v`, or a fault.

`Cslib.WordRAM.Runs w p s t k` says that `k` steps lead from state `s` to state `t`, each
continuing to a next state, none halting or faulting.

Each instruction takes one unit of time, so a run of `k` steps that then halts executes `k + 1`
instructions. `WordRAMAbstract` defines from scratch the same machine over the exact basis, where
`-`, `/` and `%` fault instead of truncating or dividing by zero.
-/

/-! ## Main theorem -/

/-- **Dijkstra's algorithm.** Some word-RAM program `p` over the standard basis, with some
number `r` of registers, and some constant `K` satisfy the following.
For every graph `G` with `n` vertices and `m` edges and largest weight `W`, every source `s`, and
every word size `w` with `8 (n + m + 2) (W + 2) < 2 ^ w`: started on the input `encode G s`, the
program runs for `steps` steps to a state `t` whose next instruction is `halt`, executes
`steps + 1 ≤ K (m + 1) (Nat.log 2 n + 1)` instructions in all, and then holds at `outAddr G v`
the encoded distance from `s` to `v`, for every vertex `v`. Here `Nat.log 2 n` is the integer part
of `log₂ n` (and `0` for `n = 0`). The output of `halt` is not part of the result. -/
theorem dijkstra_logLinear :
    ∃ r, ∃ p : Cslib.WordRAM.Program .standard r, ∃ K, ∀ (n : ℕ) (G : Graph n) (s : Fin n) (w : ℕ),
      8 * (n + numEdges G + 2) * (maxWeight G + 2) < 2 ^ w →
      ∃ t steps, Cslib.WordRAM.Runs w p (Cslib.WordRAM.State.init (encode G s)) t steps ∧
        (∃ v, Cslib.WordRAM.step w p t = .halt v) ∧
        steps + 1 ≤ K * (numEdges G + 1) * (Nat.log 2 n + 1) ∧
        ∀ v : Fin n, t.data.mem (outAddr G v) = encodeDist (dist G s v) :=
  DijkstraBridge.logLinear (W := @IsWalk) ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

/--
info: abstract audit passed for `ComplexityAbstracts.DijkstraAbstract`: 14 root
declarations, 249 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.DijkstraAbstract allowing [
  Complexity.Computability.WordRAM.Defs,
  Complexity.Computability.WordRAM.Basis
]

end ComplexityAbstracts.DijkstraAbstract
