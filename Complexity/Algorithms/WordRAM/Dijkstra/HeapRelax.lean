/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.BinaryHeap
public import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Dijkstra's algorithm with a binary heap: the scan of the edges

This file proves what one run of `Cslib.Algorithms.WordRAM.Dijkstra.relaxEdges` does on the
edges out of a vertex `U` of an adjacency-list instance: within `O(deg U · log n)` instructions
it applies `Cslib.Algorithms.WordRAM.Dijkstra.edgesWord` to every distance word, and keeps the
heap invariant, with the heap holding the discovered vertices that are not visited.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.relaxEdges_spec`: the scan of the edges out of a vertex.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

/-- **The scan of the edges out of `U`.** Started with the index `j` and the end `jend` at the
offsets of `U` and `U + 1`, the distance word `B ≠ 0` of `U` in `best`, the input intact below
`Db = G.dbase` and a heap that holds the discovered vertices other than the visited ones, the
scan runs within `deg U · (30 ⌊log₂ n⌋ + 32) + 2` instructions. It replaces every distance word
by its relaxation through the edges out of `U`, inserts at most `deg U` vertices into the heap and
keeps the heap invariant, the visited vertices, the input and the registers other than its
scratch registers and `sz`.

A vertex is visited when it is discovered (its distance word is nonzero) but not in the heap (its
position is `0`). The scan assumes that no edge out of `U` improves a visited vertex. -/
theorem relaxEdges_spec {G : ListInstance} {w S₀ B : ℕ} (U : Fin G.n) {x : Data 27}
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (heb : x.regs eb = G.n + 4) (hdb : x.regs db = G.dbase) (hhb : x.regs hb = G.dbase + G.n)
    (hpb : x.regs pb = G.dbase + 2 * G.n + 1) (hsz : x.regs sz = S₀) (hbest : x.regs best = B)
    (hB : B ≠ 0) (hj : x.regs j = G.offset U) (hjend : x.regs jend = G.offset ((U : ℕ) + 1))
    (hfit : Fits w (G.dbase + 3 * G.n + 1)) (hfitC : ∀ e ∈ G.adj U, Fits w (B + e.2))
    (hinput : ∀ a < G.dbase, x.mem a = (Data.init G.encode : Data 27).mem a)
    (hheap : HeapInv G.n G.dbase S₀ x.mem)
    (hvis : ∀ v : Fin G.n, x.mem (G.dbase + v) ≠ 0 → x.mem (G.dbase + 2 * G.n + 1 + v) = 0 →
      ∀ c, (v, c) ∈ G.adj U → x.mem (G.dbase + v) ≤ B + c) :
    ∃ y, ExecWithin w relaxEdges x y ((G.adj U).length * (30 * Nat.log 2 G.n + 32) + 2) ∧
      (∀ i ∉ [j, tv, tc, cand, dv, t, k, p, vk, vp, dk, dp, sz], y.regs i = x.regs i) ∧
      y.regs sz ≤ S₀ + (G.adj U).length ∧
      HeapInv G.n G.dbase (y.regs sz) y.mem ∧
      (∀ v : Fin G.n, y.mem (G.dbase + v) = edgesWord B (G.adj U) v (x.mem (G.dbase + v))) ∧
      (∀ v : Fin G.n, (y.mem (G.dbase + v) ≠ 0 ∧ y.mem (G.dbase + 2 * G.n + 1 + v) = 0) ↔
        (x.mem (G.dbase + v) ≠ 0 ∧ x.mem (G.dbase + 2 * G.n + 1 + v) = 0)) ∧
      (∀ a < G.dbase, y.mem a = x.mem a) := by
  sorry

end Cslib.Algorithms.WordRAM.Dijkstra

end
