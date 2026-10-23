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
`Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra` and proves how its operations change it. The heap
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
Insertion and decrease-key leave the first kind of defect, and removal of the root the second.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.HeapShape`, `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`: the
  heap invariant.
* `Cslib.Algorithms.WordRAM.Dijkstra.UpOrdered`, `Cslib.Algorithms.WordRAM.Dijkstra.DownOrdered`:
  heap order with one defect.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.push`,
  `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.decrease`,
  `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.extract`: insertion, decrease-key and removal of the
  root leave a heap with one defect.
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

end Cslib.Algorithms.WordRAM.Dijkstra

end
