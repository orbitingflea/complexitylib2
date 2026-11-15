/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BTree.Comparisons.BinarySearch

/-!
# B-tree binary in-node search examples
-/

public section

namespace CslibFrontierTests.BTreeBinarySearch

open Cslib (FreeM)
open Cslib.DataStructure
open Cslib.DataStructure.BTree
open Cslib.Query (LEQuery)

/-- A root with five keys, the most a node of minimum degree `3` holds. -/
def wide : BTree ℕ String :=
  .node .leaf [(1, "a", .leaf), (3, "b", .leaf), (5, "c", .leaf), (7, "d", .leaf),
    (9, "e", .leaf)]

/-- A tree of height two and minimum degree `2`. -/
def twoLevel : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (2, "b", .leaf)])
    [(3, "c", .node .leaf [(4, "d", .leaf), (5, "e", .leaf)]),
     (6, "f", .node .leaf [(7, "g", .leaf), (8, "h", .leaf), (9, "i", .leaf)])]

private theorem wide_isWF : IsWF 3 wide := isWF_iff.1 (by decide)

private theorem twoLevel_isWF : IsWF 2 twoLevel := isWF_iff.1 (by decide)

/-- An oracle that answers every comparison with `false`. -/
def falseOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun _ _ => false

/-! Binary search finds the last key of the wide node in three probes and one equality test,
where the linear scan needs five probes and the test. Four is the bound
`⌈log₂ (2 * 3)⌉ + 1` of `countQueries_lookupBinQ_le` at height one, so the bound is attained. -/

example : (lookupBinQ 9 wide).eval orderOracle = some "e" := by
  simp [wide, lookupBinQ_def, lookupBinM_node, lookupBinM_leaf, slotBinM_cons]

example : (lookupBinQ 9 wide).countQueries orderOracle = 4 := by
  simp [wide, lookupBinQ_def, lookupBinM_node, lookupBinM_leaf, slotBinM_cons]

example : (lookupQ 9 wide).countQueries orderOracle = 6 := by
  simp [wide, lookupQ_def, lookupM]

example : (lookupBinQ 9 wide).countQueries orderOracle ≤ (Nat.clog 2 (2 * 3) + 1) * wide.height :=
  countQueries_lookupBinQ_le orderOracle wide_isWF 9

example : (Nat.clog 2 (2 * 3) + 1) * wide.height = 4 := by
  simp [wide, Nat.clog_of_two_le]

/-! An absent key, and an oracle unrelated to the order: the count stays within the bound. -/

example : (lookupBinQ 4 wide).eval orderOracle = none := by
  simp [wide, lookupBinQ_def, lookupBinM_node, lookupBinM_leaf, slotBinM_cons]

example : (lookupBinQ 4 wide).countQueries falseOracle = 2 := by
  simp [wide, falseOracle, lookupBinQ_def, lookupBinM_node, lookupBinM_leaf, slotBinM_cons]

/-! Two levels: lookup and rank descend into the child selected by the search. -/

example : (lookupBinQ 8 twoLevel).eval orderOracle = some "h" := by
  simp [twoLevel, lookupBinQ_def, lookupBinM_node, lookupBinM_leaf, slotBinM_cons]

example : (rankBinQ 8 twoLevel).eval orderOracle = 7 := by
  simp [twoLevel, rankBinQ_def, rankBinM_node, rankBinM_leaf, slotBinM_cons, size_node]

example : (rankBinQ 8 twoLevel).countQueries orderOracle = 3 := by
  simp [twoLevel, rankBinQ_def, rankBinM_node, rankBinM_leaf, slotBinM_cons]

example : rankBin 8 twoLevel = rank 8 twoLevel := rankBin_eq_rank twoLevel_isWF.sorted 8

example : lookupBin 8 twoLevel = lookup 8 twoLevel := lookupBin_eq_lookup twoLevel_isWF.sorted 8

/-! Sortedness is needed for agreement with linear search: on the keys `5, 1, 3` the linear scan
stops at `5`, the first key not below `2`, while binary search probes `1` and moves right. -/

example : slot 2 [(5, "a", (.leaf : BTree ℕ String)), (1, "b", .leaf), (3, "c", .leaf)] = 0 := by
  simp

example :
    slotBin 2 [(5, "a", (.leaf : BTree ℕ String)), (1, "b", .leaf), (3, "c", .leaf)] = 2 := by
  simp [slotBin_def, slotBinM_cons]

end CslibFrontierTests.BTreeBinarySearch
