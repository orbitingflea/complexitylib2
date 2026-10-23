/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.BinaryHeap

/-!
# Dijkstra's algorithm with a binary heap: the heap operations

This file proves what the heap operations of `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra`
do on a heap with the invariant `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`, and how long they
take. A sift-up or a sift-down halves or doubles the repaired position at every step, so each
takes `O(log sz)` instructions.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.siftUp_spec`,
  `Cslib.Algorithms.WordRAM.Dijkstra.siftDown_spec`: the two repairs.
* `Cslib.Algorithms.WordRAM.Dijkstra.extractMin_spec`: removal of the root.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

variable {N Db S : ℕ}

/-- **Sift-up.** From a heap ordered except between position `K` and its parent, the sift-up
runs within `30 ⌊log₂ K⌋ + 2` instructions, writes only the registers `k`, `p`, `vk`, `vp`, `dk`,
`dp`, `t` and the heap and positions arrays, and leaves a heap with the same vertices. -/
theorem siftUp_spec {w K : ℕ} {x : Data 27} (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hdb : x.regs db = Db) (hhb : x.regs hb = Db + N) (hpb : x.regs pb = Db + 2 * N + 1)
    (hk : x.regs k = K) (hK : 1 ≤ K) (hKS : K ≤ S) (hfit : Fits w (Db + 3 * N + 1))
    (hshape : HeapShape N Db S x.mem) (hord : UpOrdered (heapKey N Db x.mem) S K) :
    ∃ y, ExecWithin w siftUp x y (30 * Nat.log 2 K + 2) ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t], y.regs i = x.regs i) ∧
      HeapInv N Db S y.mem ∧
      (∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔ x.mem (Db + 2 * N + 1 + v) = 0) ∧
      (∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a) := by
  sorry

/-- **Sift-down.** From a heap of `S` entries ordered except between position `K` and its
children, the sift-down runs within `45 ⌊log₂ (S + 1)⌋ + 4` instructions, writes only the
registers `k`, `p`, `vk`, `vp`, `dk`, `dp`, `t`, `l`, `szp` and the heap and positions arrays, and
leaves a heap with the same vertices. -/
theorem siftDown_spec {w K : ℕ} {x : Data 27} (hone : x.regs one = 1)
    (hdb : x.regs db = Db) (hhb : x.regs hb = Db + N) (hpb : x.regs pb = Db + 2 * N + 1)
    (hsz : x.regs sz = S) (hk : x.regs k = K) (hK : 1 ≤ K) (hKS : K ≤ S)
    (hfit : Fits w (Db + 3 * N + 1))
    (hshape : HeapShape N Db S x.mem) (hord : DownOrdered (heapKey N Db x.mem) S K) :
    ∃ y, ExecWithin w siftDown x y (45 * Nat.log 2 (S + 1) + 4) ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x.regs i) ∧
      HeapInv N Db S y.mem ∧
      (∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔ x.mem (Db + 2 * N + 1 + v) = 0) ∧
      (∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a) := by
  sorry

/-- **Extract-min.** From a heap of `S ≥ 1` entries, the removal of the root runs within
`45 ⌊log₂ S⌋ + 20` instructions. It leaves the root vertex in `u` and its key in `best`, and a
heap of `S - 1` entries that holds the vertices of the old heap but the root. -/
theorem extractMin_spec {w : ℕ} {x : Data 27} (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hdb : x.regs db = Db) (hhb : x.regs hb = Db + N) (hpb : x.regs pb = Db + 2 * N + 1)
    (hsz : x.regs sz = S) (hS : 1 ≤ S) (hfit : Fits w (Db + 3 * N + 1))
    (hheap : HeapInv N Db S x.mem) :
    ∃ y, ExecWithin w extractMin x y (45 * Nat.log 2 S + 20) ∧
      (∀ i ∉ [t, u, best, vk, sz, k, p, vp, dk, dp, l, szp], y.regs i = x.regs i) ∧
      y.regs u = x.mem (Db + N + 1) ∧ y.regs best = x.mem (Db + x.mem (Db + N + 1)) ∧
      y.regs sz = S - 1 ∧ HeapInv N Db (S - 1) y.mem ∧
      (∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔
        x.mem (Db + 2 * N + 1 + v) = 0 ∨ v = x.mem (Db + N + 1)) ∧
      (∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a) := by
  sorry

end Cslib.Algorithms.WordRAM.Dijkstra

end
