/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Statement
public import Complexity.Computability.WordRAM.ExactNotation
public import Complexity.Computability.WordRAM.Function

/-!
# Dijkstra's algorithm on the word RAM: the program

This file writes the quadratic-time Dijkstra program as a structured word-RAM program over the
exact basis `Cslib.WordRAM.Basis.exact` [Dijkstra][Dijkstra1959] [Cormen et al., Section
24.3][CLRS2009].

The program reads the instance of `Cslib.Algorithms.WordRAM.Dijkstra.Instance.encode`, whose
weight matrix entry for row `u` and column `v` sits at address `u n + v + 3`. It keeps two arrays
of `n` words just past the input: the tentative distances at `n² + 3 + v`, which are the output
cells `Cslib.Algorithms.WordRAM.Dijkstra.Instance.outAddr`, and the visited flags at
`n² + 3 + n + v`. Both start at `0` because memory past the input is `0`; a distance word `0`
means "no path found yet" and `d + 1` means distance `d`.

Each round scans the unvisited vertices for the least finite tentative distance
(`Cslib.Algorithms.WordRAM.Dijkstra.minScan`). If there is none, the program stops; otherwise it
marks that vertex visited and relaxes the edges of its matrix row
(`Cslib.Algorithms.WordRAM.Dijkstra.relax`). There are at most `n` rounds of `O(n)` instructions.

On the exact basis a subtraction below zero faults. The program's only subtraction is
`best + c - 1` in the relaxation, which runs only for a matrix entry `c ≠ 0`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.encodeWeight`: a matrix entry as a word.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.encode`: the weight-matrix input words.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.outAddr`: the output address of a vertex.
* `Cslib.Algorithms.WordRAM.Dijkstra.QuadraticSpec`: a flat program computes every distance from
  the source within `K n ^ 2` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.QuadraticStatement`: some program meets `QuadraticSpec`.
* `Cslib.Algorithms.WordRAM.Dijkstra.QueryStatement`: the distance to one queried vertex is
  uniformly computable in `O(n ^ 2)` instructions, in the sense of
  `Cslib.WordRAM.UniformComputableInO`.
* `Cslib.Algorithms.WordRAM.Dijkstra.dijkstra`: the program.
* `Cslib.Algorithms.WordRAM.Dijkstra.relaxWord`: one relaxation on encoded words.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

namespace Instance

variable (I : Instance)

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

/-! ### Register names -/

namespace Reg

/-- Register holding `0`, as all registers do initially. -/
abbrev zero : Fin 17 := 0
/-- Register holding `1`. -/
abbrev one : Fin 17 := 1
/-- Register holding `3`, the offset of the matrix. -/
abbrev three : Fin 17 := 2
/-- Register holding the number `n` of vertices. -/
abbrev n : Fin 17 := 3
/-- Register holding the source. -/
abbrev src : Fin 17 := 4
/-- Register holding `n² + 3`, the address of the distance array. -/
abbrev dbase : Fin 17 := 5
/-- Register holding `n² + 3 + n`, the address of the visited flags. -/
abbrev vbase : Fin 17 := 6
/-- The round counter. -/
abbrev k : Fin 17 := 7
/-- The vertex index of the inner loops. -/
abbrev j : Fin 17 := 8
/-- Scratch register for addresses. -/
abbrev tmp : Fin 17 := 9
/-- The visited flag of vertex `j`. -/
abbrev f : Fin 17 := 10
/-- The distance word of vertex `j`. -/
abbrev dj : Fin 17 := 11
/-- The least distance word found by the scan, `0` if none. -/
abbrev best : Fin 17 := 12
/-- The vertex of the least distance word. -/
abbrev bv : Fin 17 := 13
/-- The address of the matrix row of `bv`. -/
abbrev row : Fin 17 := 14
/-- The matrix entry of the edge from `bv` to `j`. -/
abbrev c : Fin 17 := 15
/-- The candidate distance word through `bv`. -/
abbrev cand : Fin 17 := 16

end Reg

open Reg

/-! ### The program -/

/-- Read `n` and the source, compute the addresses of the two arrays, set the distance word of
the source to `1` (distance `0`), and start at round `0`. -/
def setup : Code .exact 17 := ram_exact[
  one ← #1;
  three ← #3;
  n ← *one;
  tmp ← #2;
  src ← *tmp;
  dbase ← n * n;
  dbase ← dbase + three;
  vbase ← dbase + n;
  tmp ← dbase + src;
  *tmp ← one;
  k ← zero ]

/-- Scan the vertices `j < n` that are not visited and have a nonzero distance word, and leave
the least such word in `best` and its vertex in `bv`; `best` stays `0` if there is none. -/
def minScan : Code .exact 17 := ram_exact[
  best ← zero;
  j ← zero;
  while j < n do [
    tmp ← vbase + j;
    f ← *tmp;
    if f = zero then [
      tmp ← dbase + j;
      dj ← *tmp;
      if dj = zero then [ tmp ← tmp ] else [
        if best = zero then [ best ← dj; bv ← j ] else [
          if dj < best then [ best ← dj; bv ← j ] else [ tmp ← tmp ] ] ] ]
    else [ tmp ← tmp ];
    j ← j + one ] ]

/-- Relax every edge out of `bv`, whose distance word is `best`: for each `j < n` with an edge of
matrix entry `c ≠ 0`, the candidate word `best + c - 1` replaces the distance word of `j` if that
word is `0` or larger. -/
def relax : Code .exact 17 := ram_exact[
  row ← bv * n;
  row ← row + three;
  j ← zero;
  while j < n do [
    tmp ← row + j;
    c ← *tmp;
    if c = zero then [ tmp ← tmp ] else [
      cand ← best + c;
      cand ← cand - one;
      tmp ← dbase + j;
      dj ← *tmp;
      if dj = zero then [ *tmp ← cand ] else [
        if cand < dj then [ *tmp ← cand ] else [ tmp ← tmp ] ] ];
    j ← j + one ] ]

/-- One round: find the unvisited vertex of least finite tentative distance; stop if there is
none, and otherwise mark it visited and relax its edges. -/
def round : Code .exact 17 := ram_exact[
  ⟪minScan⟫;
  if best = zero then [ k ← n ] else [
    tmp ← vbase + bv;
    *tmp ← one;
    ⟪relax⟫;
    k ← k + one ] ]

/-- **Dijkstra's algorithm** with a linear-scan minimum, on the weight matrix. -/
def dijkstra : Code .exact 17 := ram_exact[ ⟪setup⟫; while k < n do [ ⟪round⟫ ] ]

/-- One relaxation on encoded words: the new distance word of a vertex with distance word `d`,
through an edge of matrix entry `c` out of a vertex with distance word `b ≠ 0`. -/
def relaxWord (b c d : ℕ) : ℕ :=
  if c = 0 then d else if d = 0 then b + c - 1 else if b + c - 1 < d then b + c - 1 else d

end Cslib.Algorithms.WordRAM.Dijkstra

end
