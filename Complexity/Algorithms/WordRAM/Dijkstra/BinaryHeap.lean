/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapProgram

/-!
# Dijkstra's algorithm with a binary heap: the heap

This file states the invariant of the binary min-heap of
`Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra` and proves that its operations keep it. The heap
lives in a memory `mem` with three arrays past a base `Db`, for `N` vertices: the keys
`mem (Db + v)`, the heap entries `mem (Db + N + i)` for the positions `1 ≤ i ≤ sz`, and the
positions `mem (Db + 2 N + 1 + v)`, with `0` for a vertex not in the heap. The key of a position
is the key of the vertex there (`Cslib.Algorithms.WordRAM.Dijkstra.heapKey`).

The invariant (`Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`) has a shape part
(`Cslib.Algorithms.WordRAM.Dijkstra.HeapShape`: the positions array is the inverse of the heap,
and vertices in the heap have nonzero keys) and an order part: the key of every position is at
least the key of its parent. A sift-up from position `k` repairs a heap ordered except between `k`
and its parent (`Cslib.Algorithms.WordRAM.Dijkstra.UpOrdered`), and a sift-down from `k` repairs a
heap ordered except between `k` and its children (`Cslib.Algorithms.WordRAM.Dijkstra.DownOrdered`).
Each takes `O(log sz)` instructions, since every step halves or doubles the position.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.HeapShape`, `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`: the
  heap invariant.
* `Cslib.Algorithms.WordRAM.Dijkstra.UpOrdered`, `Cslib.Algorithms.WordRAM.Dijkstra.DownOrdered`:
  heap order with one defect.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.siftUp_spec`,
  `Cslib.Algorithms.WordRAM.Dijkstra.siftDown_spec`: the two repairs.
* `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.push`,
  `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.decrease`,
  `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.extract`: insertion, decrease-key and removal of the
  root leave a heap with one defect.
* `Cslib.Algorithms.WordRAM.Dijkstra.extractMin_spec`: removal of the root.
* `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.root_le`: the root has the least key.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

/-- The key of heap position `i`: the key of the vertex at position `i`. -/
def heapKey (N Db : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (Db + mem (Db + N + i))

/-- **The shape of the heap.** The positions `1, …, sz` hold vertices below `N`, the positions
array is the inverse of the heap and is `0` off the heap, and vertices in the heap have nonzero
keys. -/
structure HeapShape (N Db sz : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- The heap holds at most `N` entries. -/
  size_le : sz ≤ N
  /-- The heap holds vertices. -/
  vertex_lt : ∀ i, 1 ≤ i → i ≤ sz → mem (Db + N + i) < N
  /-- The position of the vertex at position `i` is `i`. -/
  pos_vertex : ∀ i, 1 ≤ i → i ≤ sz → mem (Db + 2 * N + 1 + mem (Db + N + i)) = i
  /-- Positions are at most the size. -/
  pos_le : ∀ v < N, mem (Db + 2 * N + 1 + v) ≤ sz
  /-- A vertex with a nonzero position is at that position. -/
  vertex_pos : ∀ v < N, mem (Db + 2 * N + 1 + v) ≠ 0 →
    mem (Db + N + mem (Db + 2 * N + 1 + v)) = v
  /-- Vertices in the heap have nonzero keys. -/
  key_ne : ∀ v < N, mem (Db + 2 * N + 1 + v) ≠ 0 → mem (Db + v) ≠ 0

/-- **Heap order**: the key of every position `2 ≤ i ≤ sz` is at least that of its parent. -/
def Ordered (f : ℕ → ℕ) (sz : ℕ) : Prop := ∀ i, 2 ≤ i → i ≤ sz → f (i / 2) ≤ f i

/-- Heap order except between position `k` and its parent, where the parent of `k` is at most
the children of `k`: the state of a sift-up at `k`. -/
def UpOrdered (f : ℕ → ℕ) (sz k : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz → (i ≠ k → f (i / 2) ≤ f i) ∧ (i / 2 = k → 2 ≤ k → f (k / 2) ≤ f i)

/-- Heap order except between position `k` and its children, where the parent of `k` is at most
the children of `k`: the state of a sift-down at `k`. -/
def DownOrdered (f : ℕ → ℕ) (sz k : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz → (i / 2 ≠ k → f (i / 2) ≤ f i) ∧ (i / 2 = k → 2 ≤ k → f (k / 2) ≤ f i)

/-- **The heap invariant**: the shape and the heap order. -/
structure HeapInv (N Db sz : ℕ) (mem : ℕ → ℕ) : Prop extends HeapShape N Db sz mem where
  /-- Heap order. -/
  ordered : Ordered (heapKey N Db mem) sz

variable {N Db S : ℕ} {mem : ℕ → ℕ}

/-- A heap that misses a vertex has room for it. -/
theorem HeapShape.size_lt (h : HeapShape N Db S mem) {v : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) = 0) : S < N := by
  sorry

/-- **The root has the least key** among the vertices in the heap. -/
theorem HeapInv.root_le (h : HeapInv N Db S mem) {v : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) ≠ 0) : mem (Db + mem (Db + N + 1)) ≤ mem (Db + v) := by
  sorry

/-- **Insertion.** Giving a vertex `v` out of the heap the nonzero key `c` and appending it at
position `S + 1` leaves a heap ordered except at `S + 1`, which holds `v`. -/
theorem HeapInv.push (h : HeapInv N Db S mem) {v c : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) = 0) (hc : c ≠ 0) :
    HeapShape N Db (S + 1) (Function.update (Function.update (Function.update mem (Db + v) c)
      (Db + N + (S + 1)) v) (Db + 2 * N + 1 + v) (S + 1)) ∧
    UpOrdered (heapKey N Db (Function.update (Function.update (Function.update mem (Db + v) c)
      (Db + N + (S + 1)) v) (Db + 2 * N + 1 + v) (S + 1))) (S + 1) (S + 1) := by
  sorry

/-- **Decrease-key.** Lowering the key of a vertex `v` in the heap to the nonzero `c` leaves a
heap ordered except at the position of `v`. -/
theorem HeapInv.decrease (h : HeapInv N Db S mem) {v c : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) ≠ 0) (hc : c ≠ 0) (hle : c ≤ mem (Db + v)) :
    HeapShape N Db S (Function.update mem (Db + v) c) ∧
    UpOrdered (heapKey N Db (Function.update mem (Db + v) c)) S (mem (Db + 2 * N + 1 + v)) := by
  sorry

/-- **Removal of the root**, from a heap of at least two entries: clearing the position of the
root `U` and moving the last entry `L` to the root leaves a heap of `S - 1` entries ordered except
between the root and its children, which holds exactly the vertices of the old heap but `U`. -/
theorem HeapInv.extract (h : HeapInv N Db S mem) (hS : 2 ≤ S) :
    HeapShape N Db (S - 1) (Function.update (Function.update
      (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
        (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1) ∧
    DownOrdered (heapKey N Db (Function.update (Function.update
      (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
        (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1)) (S - 1) 1 ∧
    ∀ v < N, (Function.update (Function.update
      (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
        (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1 (Db + 2 * N + 1 + v) = 0 ↔
      mem (Db + 2 * N + 1 + v) = 0 ∨ v = mem (Db + N + 1)) := by
  sorry

/-- **Removal of the only entry**: clearing the position of the root of a heap of one entry
leaves the empty heap. -/
theorem HeapInv.extract_one (h : HeapInv N Db 1 mem) :
    HeapInv N Db 0 (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) := by
  sorry

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
