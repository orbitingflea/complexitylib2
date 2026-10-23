/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapRelax

/-!
# Dijkstra's algorithm with a binary heap in `O((m + 1) log n)` time

This file proves that `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra` computes the distances
from the source of an adjacency-list instance within `O((m + 1) log n)` instructions, and so
proves `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearStatement`.

The rounds keep the invariant of Dijkstra's algorithm
(`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv`) of the weight-matrix instance, for the visited
vertices (discovered and out of the heap) and the tentative distances in the output cells, along
with the heap invariant. A round costs `O((deg u + 1) log n)` for its vertex `u`, which is paid by
a potential that counts twice the edges out of the unvisited vertices plus the heap size: the
round visits `u`, so it removes `deg u` edges from the count and one entry from the heap, and it
inserts at most `deg u` entries.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.OuterInv`: the invariant of the rounds.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.potential`: the potential that pays for them.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra_spec`: the structured program leaves the
  encoded distances in the output cells within `200 (m + 1) (⌊log₂ n⌋ + 1) + 27` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.logLinearSpec`: its compiled program meets
  `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec` with `K = 230`.
* `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement`: the phase-2 main theorem.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

namespace ListInstance

variable (G : ListInstance)

/-- The tentative distances held in the distance words of `y`. -/
noncomputable def distOf (y : Data 27) (v : Fin G.n) : ℕ∞ :=
  decodeDist (y.mem (G.dbase + v))

/-- The visited vertices of `y`: those that are discovered, with a nonzero distance word, but
not in the heap, with position `0`. -/
def visitedOf (y : Data 27) : Finset (Fin G.n) :=
  Finset.univ.filter fun v => y.mem (G.dbase + v) ≠ 0 ∧ y.mem (G.dbase + 2 * G.n + 1 + v) = 0

/-- The number of edges out of the unvisited vertices of `y`. -/
def remaining (y : Data 27) : ℕ :=
  ∑ v ∈ Finset.univ.filter (· ∉ G.visitedOf y), (G.adj v).length

/-- **The potential** of `y`, which pays for the remaining rounds: `100 (⌊log₂ n⌋ + 1)` times
twice the number of edges out of the unvisited vertices plus the heap size. -/
def potential (y : Data 27) : ℕ :=
  100 * (Nat.log 2 G.n + 1) * (2 * G.remaining y + y.regs sz)

/-- **The invariant of the rounds.** The constant registers hold their values, the input is
intact, the heap invariant holds, and the memory satisfies the invariant of Dijkstra's algorithm
for the weight-matrix instance. -/
structure OuterInv (y : Data 27) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  two_eq : y.regs two = 2
  three_eq : y.regs three = 3
  eb_eq : y.regs eb = G.n + 4
  db_eq : y.regs db = G.dbase
  hb_eq : y.regs hb = G.dbase + G.n
  pb_eq : y.regs pb = G.dbase + 2 * G.n + 1
  input : ∀ a < G.dbase, y.mem a = (Data.init G.encode : Data 27).mem a
  heap : HeapInv G.n G.dbase (y.regs sz) y.mem
  inv : G.toInstance.Inv (G.visitedOf y) (G.distOf y)

end ListInstance

variable {G : ListInstance} {w : ℕ}

/-- The setup establishes the invariant of the rounds, with the source as the only heap entry. -/
theorem heapSetup_spec (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    ∃ y, ExecWithin w heapSetup (.init G.encode) y 25 ∧ G.OuterInv y ∧
      G.potential y ≤ 100 * (Nat.log 2 G.n + 1) * (2 * G.m + 1) := by
  sorry

/-- **One round** keeps the invariant of the rounds, and its running time and two more
instructions are paid by the drop of the potential. -/
theorem heapRound_spec (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) {y : Data 27}
    (hy : G.OuterInv y) (hsz : (Cond.lt zero sz).Holds y) :
    ∃ y' T, ExecWithin w heapRound y y' T ∧ G.OuterInv y' ∧
      T + 2 + G.potential y' ≤ G.potential y := by
  sorry

/-- When the rounds stop, with an empty heap, the output cells hold the encoded distances. -/
theorem heapExit_spec {y : Data 27} (hy : G.OuterInv y) (hsz : ¬(Cond.lt zero sz).Holds y)
    (v : Fin G.n) : y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  sorry

/-- **Correctness and running time of the structured program.** -/
theorem heapDijkstra_spec (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    ∃ y, ExecWithin w heapDijkstra (.init G.encode) y
        (200 * (G.m + 1) * (Nat.log 2 G.n + 1) + 27) ∧
      ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  sorry

/-- **Dijkstra's algorithm with a binary heap in `O((m + 1) log n)` time.** The compiled program
meets the specification `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec` with `K = 230`. -/
theorem logLinearSpec : LogLinearSpec (heapDijkstra.program zero) 230 := by
  sorry

/-- **Phase 2 main theorem.** Some word-RAM program over the standard basis computes all
shortest-path distances from the source of a weighted directed graph with `n` vertices and `m`
edges, given by adjacency lists, within `O((m + 1) log n)` instructions. -/
theorem logLinearStatement : LogLinearStatement :=
  ⟨27, _, 230, logLinearSpec⟩

end Cslib.Algorithms.WordRAM.Dijkstra

end
