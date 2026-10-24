/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Function
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Data.ENat.Lattice

/-!
# Dijkstra's algorithm on the word RAM: statements

This file states, without proof, what a quadratic-time single-source shortest-path program on
the word RAM must satisfy [Dijkstra][Dijkstra1959] [Cormen et al., Section 24.3][CLRS2009].

An instance (`Cslib.Algorithms.WordRAM.Dijkstra.Instance`) is a directed graph on `Fin n` with
natural-number edge weights, given by its weight matrix, and a source vertex. The distance
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist` is the infimum, in `ℕ∞`, of the weights of the
paths (`Quiver.Path`, `Quiver.Path.addWeight`) between two vertices; it is `⊤` when there is no
path.

The program reads the input words `n`, the source and the matrix row by row, with `0` for a
missing edge and `c + 1` for an edge of weight `c`. When it halts, the `n` memory cells just past
the input hold the distances from the source, with `0` for an unreachable vertex and `d + 1` for
distance `d`. The word size must hold `(n + 2) ^ 2 (W + 2)`, where `W` is the largest weight; this
bounds every address and every distance with room for the program's scratch arrays.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.Instance`: a weighted directed graph with a source.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist`: the shortest-path distance.
* `Cslib.Algorithms.WordRAM.Dijkstra.QuadraticSpec`: a flat program computes every distance from
  the source within `K n ^ 2` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.QuadraticStatement`: some program meets `QuadraticSpec`.
* `Cslib.Algorithms.WordRAM.Dijkstra.QueryStatement`: the distance to one queried vertex is
  uniformly computable in `O(n ^ 2)` instructions, in the sense of
  `Cslib.WordRAM.UniformComputableInO`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist_self`: every vertex is at distance `0` from
  itself.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

/-- An instance of the **single-source shortest-path problem**: a directed graph on `Fin n` with
natural-number edge weights, given by its weight matrix, and a source vertex. The entry
`weight u v` is `some c` for an edge from `u` to `v` of weight `c`, and `none` for no edge. -/
structure Instance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The weight matrix. -/
  weight : Fin n → Fin n → Option ℕ
  /-- The source. -/
  source : Fin n

namespace Instance

variable (I : Instance)

/-- The vertices of an instance, as a quiver: an arrow from `u` to `v` is a weight `c` with
`I.weight u v = some c`, so there is at most one. -/
def Vertex : Type := Fin I.n

instance : Quiver I.Vertex where
  Hom u v := {c : ℕ // I.weight u v = some c}

/-- The weight of an arrow. -/
def arrowWeight {u v : I.Vertex} (e : u ⟶ v) : ℕ∞ :=
  (show {c : ℕ // I.weight u v = some c} from e).1

/-- The **shortest-path distance** from `u` to `v`: the infimum of the weights of the paths from
`u` to `v`, and `⊤` when there is none. -/
noncomputable def dist (u v : Fin I.n) : ℕ∞ :=
  ⨅ p : Quiver.Path (V := I.Vertex) u v, p.addWeight I.arrowWeight

/-- Every vertex is at distance `0` from itself, by the empty path. -/
theorem dist_self (u : Fin I.n) : I.dist u u = 0 :=
  le_antisymm (iInf_le_of_le .nil (Quiver.Path.addWeight_nil _ _).le) (by simp)

/-- The largest edge weight, and `0` when there is no edge. -/
def maxWeight : ℕ :=
  Finset.univ.sup fun uv : Fin I.n × Fin I.n => (I.weight uv.1 uv.2).getD 0

/-- A matrix entry as a word: `0` for no edge and `c + 1` for an edge of weight `c`. -/
def encodeWeight : Option ℕ → ℕ
  | none => 0
  | some c => c + 1

/-- The input words: `n`, the source, and the weight matrix row by row. The entry of row `u` and
column `v` is word `u * n + v + 2`, so `Cslib.WordRAM.Data.init` places it at address
`u * n + v + 3`. -/
def encode : List ℕ :=
  I.n :: (I.source : ℕ) ::
    (List.finRange I.n).flatMap fun u =>
      (List.finRange I.n).map fun v => encodeWeight (I.weight u v)

/-- The output address of vertex `v`: the `n` cells just past the input, which ends at address
`n * n + 2`. -/
def outAddr (v : Fin I.n) : ℕ := I.n * I.n + 3 + v

end Instance

/-- A distance as a word: `0` for an unreachable vertex and `d + 1` for distance `d`. -/
def encodeDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

/-- **Quadratic-time shortest paths.** At every word size `w` that holds `(n + 2) ^ 2 (W + 2)`,
where `W` is the largest weight, the flat program `p`, started on the input words of an instance,
halts within `K n ^ 2` instructions, the final `halt` included, and its memory then holds at
`I.outAddr v` the encoded distance from the source to `v`, for every vertex `v`. The register
value returned by `halt` is not part of the result. -/
def QuadraticSpec {r : ℕ} (p : Program .exact r) (K : ℕ) : Prop :=
  ∀ (I : Instance) (w : ℕ), Fits w ((I.n + 2) ^ 2 * (I.maxWeight + 2)) →
    ∃ t m, Runs w p (.init I.encode) t m ∧ (∃ v, step w p t = .halt v) ∧
      m + 1 ≤ K * I.n ^ 2 ∧
      ∀ v : Fin I.n, t.data.mem (I.outAddr v) = encodeDist (I.dist I.source v)

/-- **Phase 1 main theorem (statement).** Some word-RAM program over the exact basis computes
all shortest-path distances from the source of a weighted directed graph with `n` vertices
within `O(n ^ 2)` instructions. -/
def QuadraticStatement : Prop :=
  ∃ r, ∃ p : Program .exact r, ∃ K, QuadraticSpec p K

/-- A query: an instance and a target vertex. -/
abbrev Query := Σ I : Instance, Fin I.n

/-- **Corollary form, in the library's notion of computation.** The encoded distance from the
source to a queried target is uniformly computable over the exact basis in `O(n ^ 2)`
instructions, on the input words of the instance followed by the target, at every word size that
holds `(n + 2) ^ 2 (W + 2)`. -/
def QueryStatement : Prop :=
  UniformComputableInO .exact (fun q : Query => encodeDist (q.1.dist q.1.source q.2))
    (fun _ q => q.1.encode ++ [(q.2 : ℕ)]) (fun q => q.1.n) (fun n _ => n ^ 2)
    (fun q w => Fits w ((q.1.n + 2) ^ 2 * (q.1.maxWeight + 2)))

end Cslib.Algorithms.WordRAM.Dijkstra
