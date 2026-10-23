/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapStatement
public import Complexity.Algorithms.WordRAM.Dijkstra.Invariant

/-!
# Dijkstra's algorithm with a binary heap: the input words

This file reads the input words `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.encode` of an
adjacency-list instance back from the initial memory of a word RAM: `n`, the source, the offsets
of the adjacency lists and the targets and weights of the edges each sit at the address that
`Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra` reads them from, and memory past the input is
`0`.

It also defines the effect of scanning the edges out of a vertex on one distance word
(`Cslib.Algorithms.WordRAM.Dijkstra.edgesWord`), and shows that it is the relaxation of the
weight-matrix instance (`Cslib.Algorithms.WordRAM.Dijkstra.decode_edgesWord`): the scan of all
parallel edges to a vertex has the effect of the lightest one.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.dbase`: the first address past the input.
* `Cslib.Algorithms.WordRAM.Dijkstra.edgeWord`, `Cslib.Algorithms.WordRAM.Dijkstra.edgesWord`:
  the relaxation of a distance word through one edge, and through a list of edges.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.init_offset`,
  `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.init_target`,
  `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.init_weight`: the input words in the initial
  memory.
* `Cslib.Algorithms.WordRAM.Dijkstra.decode_edgesWord`: the scan of the edges out of a vertex
  relaxes the tentative distances.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

namespace ListInstance

variable (G : ListInstance) {r : ℕ}

/-- The first address past the input words: the base of the distance words. -/
def dbase : ℕ := G.n + 2 * G.m + 4

/-- The input has `n + 2 m + 3` words. -/
theorem encode_length : G.encode.length = G.n + 2 * G.m + 3 := by
  sorry

/-- The offset of `u + 1` is the offset of `u` plus the length of the list of `u`. -/
theorem offset_succ {u : ℕ} (hu : u < G.n) :
    G.offset (u + 1) = G.offset u + (G.adj ⟨u, hu⟩).length := by
  sorry

/-- The offset of `n` is the number of edges. -/
theorem offset_n : G.offset G.n = G.m := by
  sorry

/-- The offsets grow. -/
theorem offset_mono {u v : ℕ} (h : u ≤ v) : G.offset u ≤ G.offset v := by
  sorry

/-- Address `1` initially holds `n`. -/
theorem init_n : (Data.init G.encode : Data r).mem 1 = G.n := rfl

/-- Address `2` initially holds the source. -/
theorem init_source : (Data.init G.encode : Data r).mem 2 = G.source := rfl

/-- Address `u + 3` initially holds the offset of `u`, for `u ≤ n`. -/
theorem init_offset {u : ℕ} (hu : u ≤ G.n) :
    (Data.init G.encode : Data r).mem (u + 3) = G.offset u := by
  sorry

/-- The target of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 4`. -/
theorem init_target (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 4) = ((G.adj u)[i].1 : ℕ) := by
  sorry

/-- The weight of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 5`. -/
theorem init_weight (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 5) = (G.adj u)[i].2 := by
  sorry

/-- Memory past the input is initially `0`. -/
theorem init_past {a : ℕ} (ha : G.dbase ≤ a) : (Data.init G.encode : Data r).mem a = 0 := by
  sorry

/-- Every edge weight is at most the largest weight. -/
theorem le_maxWeight {u : Fin G.n} {e : Fin G.n × ℕ} (he : e ∈ G.adj u) : e.2 ≤ G.maxWeight := by
  sorry

/-- The largest weight of the weight-matrix instance is at most the largest edge weight. -/
theorem toInstance_maxWeight_le : G.toInstance.maxWeight ≤ G.maxWeight := by
  sorry

end ListInstance

/-- The relaxation of the distance word `d` through an edge of weight `c` from a vertex with
distance word `b ≠ 0`. -/
def edgeWord (b c d : ℕ) : ℕ := if d = 0 then b + c else if b + c < d then b + c else d

/-- The relaxation of the distance word `d` of `v` through the edges to `v` in the list `es`, in
order, from a vertex with distance word `b`. -/
def edgesWord {N : ℕ} (b : ℕ) (es : List (Fin N × ℕ)) (v : Fin N) (d : ℕ) : ℕ :=
  es.foldl (fun d e => if e.1 = v then edgeWord b e.2 d else d) d

/-- **The scan of the edges out of `u` relaxes the tentative distances.** If `b ≠ 0` is the
distance word of `u` and `d` that of `v`, the relaxation of `d` through the edges from `u` to `v`
decodes to the relaxation of the tentative distance of `v` in the weight-matrix instance. -/
theorem decode_edgesWord (G : ListInstance) {D : Fin G.n → ℕ∞} {u v : Fin G.n} {b d : ℕ}
    (hb : b ≠ 0) (hu : D u = decodeDist b) (hv : D v = decodeDist d) :
    decodeDist (edgesWord b (G.adj u) v d) = G.toInstance.relax D u v := by
  sorry

end Cslib.Algorithms.WordRAM.Dijkstra

end
