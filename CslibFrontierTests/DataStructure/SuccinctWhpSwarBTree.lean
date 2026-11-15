/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.PackedLane
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpBufferTrie
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpParams
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTree
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTreeInsert
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTreeSpec
public import CslibFrontier.Foundations.Data.Nat.ChooseLog

/-!
# Tests for `SuccinctWhp` Parameters, SWAR B+-Tree, and Buffer Trie

Ordinary-import `module` client exercising the Milestone 3a pure components of `#5356`:
1. **`SuccinctWhpParams` and `Nat.ChooseLog`**:
   - Concrete small-regime parameter evaluations, `Nat.mul_clog_le_add_clog_choose`, and
     `whpSpace_le_succinctWords`.
   - Non-vacuous large-regime witness at `n_max = whpThreshold c` verifying threshold separation,
     Thorup's double-tabulation bound, branching cube bound, and a concrete satisfying load vector
     for the 3-case front-yard/backyard conservation theorem `sum_sub_capFront_le_poolSize`.
2. **`PackedLane` and `SuccinctWhpSwarBTree` (SWAR word-lane primitives)**:
   - Concrete `laneGet`, `eq_of_forall_laneGet_eq_of_lt`, `wordInsertAt`, `wordDeleteAt`,
     `wordUpdateAt`, `swarOnes`, `ltMask`, and `swarRank` evaluations across boundary queries,
     paired with `swarRank_eq_count_lt`.
3. **`SuccinctWhpSwarBTree` / `Spec` / `Insert` (top-down split-only SWAR B+-tree)**:
   - Concrete execution at `(fpBits = 4, W_val = 8, tMin = 3)` verifying `NodeSplit` output of
     `splitFullNode`, proactive root splitting (`splitRootIfFull`), proactive internal child
     splitting (`descendSplitToLeaf`), and a 15-operation unsorted `btreeInsert` / `btreeUpdate` /
     `btreeDelete` trace (`btree_multi_split_overwrite_delete_separator`) proving internal-root
     creation (`metaIsLeaf = false`), in-place `btreeInsert` overwrite, and lazy deletion of
     promoted separator key `8`.
   - Multi-operation fold client over `ValidWhpSlice` preserving invariants across
     `insert → insert → update → delete` and verifying `btreeLookup = mapFn`.
4. **`SuccinctWhpBufferTrie` (`BufTrie`)**:
   - Concrete execution at `(cTab = 3, bChar = 2)` covering shared-prefix node sharing, deletion,
     zero-allocation same-epoch slot reactivation, `bufCheckSlot` scanning, and incremental
     single-pop cleanup (`bufClearSteps`), paired with `ValidBufTrie` theorem composition.
-/

public section

namespace CslibFrontierTests.DataStructure.SuccinctWhpSwarBTree

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Finset
open scoped BigOperators

/-! ## 1. `SuccinctWhpParams`: Small/Large Regimes and Conservation Non-Vacuity -/

example : cEff 0 = 1 ∧ cEff 3 = 3 := by decide
example : Dynamic.logLogFactor 16 = 2 ∧ slabScale 16 = 4 := by decide
example : 64 ≤ nSliceWhp 16 := sixty_four_le_nSliceWhp 16
example (c n_max : ℕ) :
    dTabWhp c = 2 * qTabWhp c * (cTabWhp c + 1) ∧
    kIndepWhp c n_max = 2 * sMaxWhp c n_max ∧
    whpSpace c 64 16 64 16 = smallSpaceWhp 64 16 64 16 ∧
    whpSpace c (whpThreshold c) 16 64 (whpThreshold c) =
      largeSpaceWhp c (whpThreshold c) 16 64 (whpThreshold c) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have hlt : 16 < whpThreshold c := by
      have hbm := le_bMinWhp c
      calc 16 < 2 ^ 5 := by decide
        _ ≤ 2 ^ bMinWhp c := Nat.pow_le_pow_right (by decide) (by omega)
    simp [whpSpace, hlt]
  · simp [whpSpace]

/-- Concrete small-regime instantiation of `whpSpace_le_succinctWords` at
`(c = 1, U = 64, V = 16, w = 64, n_max = 16)`. -/
theorem small_regime_whpSpace_le :
    whpSpace 1 64 16 64 16 ≤
      Dynamic.succinctWords (whpSpaceFactor 1) whpSpaceConst 64 16 64 16 :=
  whpSpace_le_succinctWords (by decide : 16 ≤ 64)

/-- Ordinary-import check of `Nat.mul_clog_le_add_clog_choose` across `n = 0` and `0 < n ≤ U`. -/
example :
    0 * Nat.clog 2 10 ≤ 0 + 0 * 3 + Nat.clog 2 (Nat.choose 10 0) ∧
    5 * Nat.clog 2 12 ≤ 5 + 5 * 3 + Nat.clog 2 (Nat.choose 12 5) :=
  ⟨Nat.mul_clog_le_add_clog_choose Nat.one_lt_two (by decide) (by decide),
   Nat.mul_clog_le_add_clog_choose Nat.one_lt_two (by decide) (by decide)⟩

/-- Concrete non-vacuous bucket-load profile `X b = capFrontWhp n_max + deltaWhp n_max` satisfying
all hypotheses of `sum_sub_capFront_le_poolSize` at every `n_max ≥ whpThreshold c`. -/
def uniformOverflowLoad (n_max : ℕ) : Fin (numBucketsWhp n_max) → ℕ :=
  fun _ => capFrontWhp n_max + deltaWhp n_max

/-- Verifies that `uniformOverflowLoad` satisfies all hypotheses and conclusions of
`sum_sub_capFront_le_poolSize` at `n_max = whpThreshold c`. -/
theorem sum_sub_capFront_nonvacuous (c : ℕ) :
    let n_max := whpThreshold c
    let X := uniformOverflowLoad n_max
    (∑ b, X b ≤ n_max) ∧
    (∀ b, X b - capFrontWhp n_max < capBackWhp n_max) ∧
    (∀ b, X b ≤ capMaxWhp n_max) ∧
    (∑ b, (X b - capFrontWhp n_max) ≤ poolSizeWhp n_max) := by
  set n_max := whpThreshold c
  have hth : whpThreshold c ≤ n_max := le_rfl
  set M := numBucketsWhp n_max
  have hM_pos : 0 < M := by dsimp [M, numBucketsWhp]; positivity
  have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
  have hL2 := two_le_slabScale n_max
  have h4δ_le : 4 * deltaWhp n_max ≤ n_max / M := by
    have h1 : 4 * deltaWhp n_max * M ≤ n_max := by
      calc 4 * deltaWhp n_max * M
          ≤ deltaWhp n_max * (M * (8 * slabScale n_max)) := by
            have : 4 * deltaWhp n_max * M * (2 * slabScale n_max) =
                deltaWhp n_max * (M * (8 * slabScale n_max)) := by ring
            rw [← this]
            exact Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ n_max := Nat.div_mul_le_self n_max _
    rwa [Nat.le_div_iff_mul_le hM_pos]
  have hsum_eq : (∑ b : Fin M, uniformOverflowLoad n_max b) =
      M * (capFrontWhp n_max + deltaWhp n_max) := by
    simp [uniformOverflowLoad, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum_le : (∑ b : Fin M, uniformOverflowLoad n_max b) ≤ n_max := by
    rw [hsum_eq]
    have hcf : capFrontWhp n_max + deltaWhp n_max ≤ n_max / M := by
      unfold capFrontWhp
      change n_max / M - 4 * deltaWhp n_max + deltaWhp n_max ≤ n_max / M
      omega
    exact (Nat.mul_le_mul_left M hcf).trans (Nat.mul_div_le n_max M)
  have hupper : ∀ b : Fin M,
      M * uniformOverflowLoad n_max b ≤
        (∑ b', uniformOverflowLoad n_max b') + M * deltaWhp n_max := by
    intro b
    rw [hsum_eq]
    dsimp [uniformOverflowLoad]
    omega
  have hlower : ∀ b : Fin M,
      (∑ b', uniformOverflowLoad n_max b') ≤
        M * uniformOverflowLoad n_max b + M * deltaWhp n_max := by
    intro b
    rw [hsum_eq]
    dsimp [uniformOverflowLoad]
    omega
  exact ⟨hsum_le, sum_sub_capFront_le_poolSize hth _ hsum_le hupper hlower⟩

/-- Concrete large-regime witness at `n_max = U = whpThreshold c` exercising all major parameter
bounds (including single-word SWAR B+-tree node bit-widths) simultaneously. -/
theorem large_regime_threshold_witness (c w : ℕ) :
    let n_max := whpThreshold c
    codeExpWhp c * Dynamic.logLogFactor n_max ≤ bCharWhp n_max ∧
    2 * Cslib.Probability.doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c n_max) ≤ 2 ^ bCharWhp n_max ∧
    8 ≤ tMinWhp n_max ∧
    slabScale n_max ≤ (tMinWhp n_max) ^ 3 ∧
    keysWordBitsWhp n_max + keyLaneBitsWhp n_max < Nat.log 2 n_max ∧
    valsWordBitsWhp n_max + valLaneBitsWhp n_max < Nat.log 2 n_max ∧
    whpSpace c n_max 16 w n_max ≤
      Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst n_max 16 w n_max :=
  ⟨codeExpWhp_mul_ell_le_bCharWhp le_rfl,
   two_mul_doubleTabCodeBound_le_pow_bCharWhp le_rfl,
   eight_le_tMinWhp le_rfl,
   slabScale_le_tMinWhp_cubed le_rfl,
   keysWordBitsWhp_lt_log le_rfl,
   valsWordBitsWhp_lt_log le_rfl,
   whpSpace_le_succinctWords le_rfl⟩

/-! ## 2. SWAR Word-Lane Primitives and Parallel Rank -/

/-- Pack four 6-bit lanes `[2, 5, 9, 13]` (`fpBits = 4`, `W = 6`) via `wordInsertAt`. -/
def sampleKeysWord : ℕ :=
  wordInsertAt 6 1 5 (wordInsertAt 6 0 2 (wordInsertAt 6 0 9 (wordInsertAt 6 0 13 0)))

example : laneGet 6 sampleKeysWord 0 = 2 ∧
    laneGet 6 sampleKeysWord 1 = 5 ∧
    laneGet 6 sampleKeysWord 2 = 9 ∧
    laneGet 6 sampleKeysWord 3 = 13 := by decide

example : laneGet 6 (wordUpdateAt 6 2 11 sampleKeysWord) 2 = 11 ∧
    laneGet 6 (wordUpdateAt 6 2 11 sampleKeysWord) 1 = 5 ∧
    laneGet 6 (wordDeleteAt 6 1 sampleKeysWord) 1 = 9 := by decide

example : swarRank 4 6 4 1 sampleKeysWord = 0 ∧
    swarRank 4 6 4 2 sampleKeysWord = 0 ∧
    swarRank 4 6 4 7 sampleKeysWord = 2 ∧
    swarRank 4 6 4 13 sampleKeysWord = 3 ∧
    swarRank 4 6 4 15 sampleKeysWord = 4 := by decide

example : swarRank 4 6 4 7 sampleKeysWord =
    #((range 4).filter fun j => laneGet 6 sampleKeysWord j < 7) :=
  swarRank_eq_count_lt (by decide) (by decide) (by decide) (by decide) (by decide)

example {a b : ℕ} (ha : a < 2 ^ (3 * 2)) (hb : b < 2 ^ (3 * 2))
    (hd : ∀ d < 3, laneGet 2 a d = laneGet 2 b d) : a = b :=
  eq_of_forall_laneGet_eq_of_lt ha hb hd

/-! ## 3. Concrete SWAR B+-Tree Splits, Descent, and Entry-Point Reduction -/

/-- Uninitialized empty slice (`alloc = 0`). -/
def uninitSlice : BTreeSlice := ⟨0, 0, fun _ => ⟨0, 0, 0⟩⟩

/-- Pack a list of `W`-bit lane values into a single word (head at lane `0`). -/
def packLanes (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + (packLanes W xs <<< W)

/-- Full 5-key leaf (`2 * 3 - 1 = 5` keys `[2, 5, 8, 11, 14]`, values `[20, 50, 80, 110, 140]`) at
`(fpBits = 4, W_val = 8, tMin = 3)`. -/
def fullLeafNode : BTreeNode :=
  ⟨mkNodeMeta true 5, packLanes 6 [2, 5, 8, 11, 14], packLanes 8 [20, 50, 80, 110, 140]⟩

/-- `splitFullNode` returns a `NodeSplit` record with median separator `8`, 3 left keys `[2, 5, 8]`,
and 2 right keys `[11, 14]`. -/
example :
    let sp := splitFullNode 4 8 3 fullLeafNode
    sp.sep = 8 ∧
    metaIsLeaf sp.left.metaWord = true ∧
    metaCount sp.left.metaWord = 3 ∧
    laneGet 6 sp.left.keysWord 2 = 8 ∧
    metaIsLeaf sp.right.metaWord = true ∧
    metaCount sp.right.metaWord = 2 ∧
    laneGet 6 sp.right.keysWord 0 = 11 := by decide

/-- `splitRootIfFull` promotes separator `8` into an internal root (`alloc = 3`) whose children `1`
and `2` are reached by `descendToLeaf`. -/
def slRootSplit : BTreeSlice :=
  splitRootIfFull 4 8 3 ⟨1, 0, fun _ => fullLeafNode⟩

example : slRootSplit.alloc = 3 ∧
    metaIsLeaf (slRootSplit.nodes slRootSplit.root).metaWord = false ∧
    metaCount (slRootSplit.nodes slRootSplit.root).metaWord = 1 ∧
    laneGet 6 (slRootSplit.nodes slRootSplit.root).keysWord 0 = 8 ∧
    descendToLeaf 4 8 3 slRootSplit.nodes 2 slRootSplit.root 5 = 1 ∧
    descendToLeaf 4 8 3 slRootSplit.nodes 2 slRootSplit.root 8 = 1 ∧
    descendToLeaf 4 8 3 slRootSplit.nodes 2 slRootSplit.root 11 = 2 := by decide

/-- Filling right child `2` to 5 keys `[9, 10, 11, 12, 14]` and descending for `q = 13` triggers a
proactive internal child split inside `descendSplitToLeaf`, growing `alloc` to `4` and root
separators to `[8, 11]`. -/
def slWithFullRight : BTreeSlice :=
  let rightFull : BTreeNode :=
    ⟨mkNodeMeta true 5, packLanes 6 [9, 10, 11, 12, 14], packLanes 8 [90, 100, 110, 120, 140]⟩
  { slRootSplit with nodes := Function.update slRootSplit.nodes 2 rightFull }

example :
    let p := descendSplitToLeaf 4 8 3 2 slWithFullRight slWithFullRight.root 13
    p.1.alloc = 4 ∧
    p.2 = 3 ∧
    metaCount (p.1.nodes p.1.root).metaWord = 2 ∧
    laneGet 6 (p.1.nodes p.1.root).keysWord 0 = 8 ∧
    laneGet 6 (p.1.nodes p.1.root).keysWord 1 = 11 ∧
    descendToLeaf 4 8 3 p.1.nodes 2 p.1.root 5 = 1 ∧
    descendToLeaf 4 8 3 p.1.nodes 2 p.1.root 10 = 2 ∧
    descendToLeaf 4 8 3 p.1.nodes 2 p.1.root 13 = 3 := by decide

/-- Direct specification check for `btreeInsert`, `btreeUpdate`, `btreeDelete`, and `btreeLookup`
on a `(fpBits = 4, W_val = 8, tMin = 3)` slice via `btreeInsert_subtree_spec`,
`btreeUpdate_subtree_spec`, `btreeDelete_subtree_spec`, and `btreeLookup_eq_of_subtree`. -/
theorem btree_fixed_params_roundtrip :
    let s0 := emptyBTreeSlice
    let s1 := btreeInsert 4 8 3 s0 8 80
    let s2 := btreeUpdate 4 8 3 s1 8 88
    let s3 := btreeDelete 4 8 3 s2 8
    btreeLookup 4 8 3 s1 8 = some 80 ∧
    btreeLookup 4 8 3 s2 8 = some 88 ∧
    btreeLookup 4 8 3 s3 8 = none := by
  have ht3 : (3 : ℕ) ≤ 3 := le_rfl
  have ht2 : (2 : ℕ) ≤ 3 := by decide
  have hcap : 2 * 3 < 2 ^ (4 + 2) := by decide
  have hv0 : ValidSubtree true 4 8 3 emptyBTreeSlice.alloc emptyBTreeSlice.nodes
      0 (2 ^ 4 - 1) (fun _ => none) (.leaf 0 0) := by
    refine ⟨by decide, rfl, by decide, by decide, by decide,
      fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ => Or.inr ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩⟩
  have halloc0 : emptyBTreeSlice.alloc + hMaxBTree + 2 < 2 ^ 8 := by
    rw [hMaxBTree_eq]; decide
  obtain ⟨ha1_pos, _, T1, hrt1, hht1, _, hv1⟩ :=
    btreeInsert_subtree_spec ht3 hcap (by decide) halloc0 rfl hv0
      (by simp [BTreeTree.height, hMaxBTree_eq]) (by decide : 8 < 2 ^ 4) (by decide : 80 < 2 ^ 8)
  have hht1_le : T1.height ≤ hMaxBTree := by
    simp only [BTreeTree.height] at hht1
    rw [hMaxBTree_eq]; omega
  obtain ⟨ha2_eq, T2, hrt2, hht2, _, hv2⟩ :=
    btreeUpdate_subtree_spec ht2 hcap ha1_pos hrt1 hv1 hht1_le
      (by decide : 8 < 2 ^ 4) (by decide : 88 < 2 ^ 8)
  have ha2_pos : 1 ≤ (btreeUpdate 4 8 3 (btreeInsert 4 8 3 emptyBTreeSlice 8 80) 8 88).alloc := by
    omega
  have hht2_le : T2.height ≤ hMaxBTree := by omega
  obtain ⟨ha3_eq, T3, hrt3, hht3, _, hv3⟩ :=
    btreeDelete_subtree_spec ht2 hcap ha2_pos hrt2 hv2 hht2_le (by decide : 8 < 2 ^ 4)
  have ha3_pos : 1 ≤
      (btreeDelete 4 8 3
        (btreeUpdate 4 8 3 (btreeInsert 4 8 3 emptyBTreeSlice 8 80) 8 88) 8).alloc := by
    omega
  have hht3_le : T3.height ≤ hMaxBTree := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [btreeLookup_eq_of_subtree ht2 hcap ha1_pos hrt1 hv1 hht1_le (by decide)]; decide
  · rw [btreeLookup_eq_of_subtree ht2 hcap ha2_pos hrt2 hv2 hht2_le (by decide)]; decide
  · rw [btreeLookup_eq_of_subtree ht2 hcap ha3_pos hrt3 hv3 hht3_le (by decide)]; decide

/-! ## 4. `ValidWhpSlice` Multi-Step Client (`insert → insert → update → delete`) -/

/-- Operations exercised by the `ValidWhpSlice` client. -/
inductive SliceOp
  | insert (q val : ℕ)
  | update (q val : ℕ)
  | delete (q : ℕ)

/-- Pure slice interpreter at `n_max`. -/
def stepWhpSlice (n_max : ℕ) (sl : BTreeSlice) : SliceOp → BTreeSlice
  | .insert q v => btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q v
  | .update q v => btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q v
  | .delete q => btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q

/-- Pure abstract map interpreter. -/
def stepMapFn (mapFn : ℕ → Option ℕ) : SliceOp → (ℕ → Option ℕ)
  | .insert q v => Function.update mapFn q (some v)
  | .update q v => if (mapFn q).isSome then Function.update mapFn q (some v) else mapFn
  | .delete q => Function.update mapFn q none

/-- Count insertions in a `SliceOp` list. -/
def countInserts : List SliceOp → ℕ
  | [] => 0
  | .insert _ _ :: ops => 1 + countInserts ops
  | .update _ _ :: ops => countInserts ops
  | .delete _ :: ops => countInserts ops

/-- Operand fit condition for a `SliceOp` at `n_max`. -/
def ValidSliceOp (n_max : ℕ) : SliceOp → Prop
  | .insert q v => q < 2 ^ fpBitsWhp n_max ∧ v < 2 ^ valLaneBitsWhp n_max
  | .update q v => q < 2 ^ fpBitsWhp n_max ∧ v < 2 ^ valLaneBitsWhp n_max
  | .delete q => q < 2 ^ fpBitsWhp n_max

/-- Pure slice interpreter at `(fpBits = 4, W_val = 8, tMin = 3)`. -/
def stepSlice3 (sl : BTreeSlice) : SliceOp → BTreeSlice
  | .insert q v => btreeInsert 4 8 3 sl q v
  | .update q v => btreeUpdate 4 8 3 sl q v
  | .delete q => btreeDelete 4 8 3 sl q

/-- Operand fit condition at `(fpBits = 4, W_val = 8)`. -/
def ValidSliceOp3 : SliceOp → Prop
  | .insert q v => q < 16 ∧ v < 256
  | .update q v => q < 16 ∧ v < 256
  | .delete q => q < 16

/-- Potential-bounded subtree invariant for `(fpBits = 4, W_val = 8, tMin = 3)`. -/
def ValidSubtree3 (ins : ℕ) (sl : BTreeSlice) (mapFn : ℕ → Option ℕ) : Prop :=
  1 ≤ sl.alloc ∧
    ∃ T : BTreeTree,
      T.rootIdx = sl.root ∧
      T.height ≤ ins ∧
      (sl.alloc - 1) + 2 * T.potential 3 ≤ 2 * ins ∧
      ValidSubtree true 4 8 3 sl.alloc sl.nodes 0 15 mapFn T

/-- Folding up to `40` insertions at `(fpBits = 4, W_val = 8, tMin = 3)` preserves `ValidSubtree3`
without ever overflowing `2 ^ 8 = 256` node indices or `hMaxBTree = 42` height. -/
theorem validSubtree3_foldl {ins₀ : ℕ} {sl₀ : BTreeSlice} {map₀ : ℕ → Option ℕ}
    (ops : List SliceOp) (hv₀ : ValidSubtree3 ins₀ sl₀ map₀)
    (hins : ins₀ + countInserts ops ≤ 40)
    (hops : ∀ op ∈ ops, ValidSliceOp3 op) :
    ValidSubtree3 (ins₀ + countInserts ops)
      (ops.foldl stepSlice3 sl₀) (ops.foldl stepMapFn map₀) := by
  have ht3 : (3 : ℕ) ≤ 3 := le_rfl
  have ht2 : (2 : ℕ) ≤ 3 := by decide
  have hcap : 2 * 3 < 2 ^ (4 + 2) := by decide
  induction ops generalizing ins₀ sl₀ map₀ with
  | nil =>
    simpa [countInserts] using hv₀
  | cons op rest ih =>
    have hop : ValidSliceOp3 op := hops op (List.mem_cons_self ..)
    have hrest : ∀ o ∈ rest, ValidSliceOp3 o :=
      fun o ho => hops o (List.mem_cons_of_mem _ ho)
    obtain ⟨ha_pos, T, hrt, hht_le, hpot, hv⟩ := hv₀
    cases op with
    | insert q v =>
      dsimp only [countInserts] at hins ⊢
      have halloc_val : sl₀.alloc + hMaxBTree + 2 < 2 ^ 8 := by
        rw [hMaxBTree_eq]; omega
      have hht_lt : T.height < hMaxBTree := by
        rw [hMaxBTree_eq]; omega
      obtain ⟨ha1_pos, _, T1, hrt1, hht1, hpot1, hv1⟩ :=
        btreeInsert_subtree_spec ht3 hcap ha_pos halloc_val hrt hv hht_lt hop.1 hop.2
      have hv₁ : ValidSubtree3 (ins₀ + 1) (btreeInsert 4 8 3 sl₀ q v)
          (Function.update map₀ q (some v)) :=
        ⟨ha1_pos, T1, hrt1, by omega, by omega, hv1⟩
      have hih := ih hv₁ (by omega) hrest
      simpa only [List.foldl_cons, stepSlice3, stepMapFn,
        Nat.add_assoc, Nat.add_comm 1 (countInserts rest)] using hih
    | update q v =>
      dsimp only [countInserts, List.foldl_cons, stepSlice3, stepMapFn] at hins ⊢
      have hfuel : T.height ≤ hMaxBTree := by rw [hMaxBTree_eq]; omega
      obtain ⟨ha1_eq, T1, hrt1, hht1, hpot1, hv1⟩ :=
        btreeUpdate_subtree_spec ht2 hcap ha_pos hrt hv hfuel hop.1 hop.2
      exact ih ⟨by omega, T1, hrt1, by omega, by omega, hv1⟩ hins hrest
    | delete q =>
      dsimp only [countInserts, List.foldl_cons, stepSlice3, stepMapFn] at hins ⊢
      have hfuel : T.height ≤ hMaxBTree := by rw [hMaxBTree_eq]; omega
      obtain ⟨ha1_eq, T1, hrt1, hht1, hpot1, hv1⟩ :=
        btreeDelete_subtree_spec ht2 hcap ha_pos hrt hv hfuel hop
      exact ih ⟨by omega, T1, hrt1, by omega, by omega, hv1⟩ hins hrest

/-- 15-operation workload at `(fpBits = 4, W_val = 8, tMin = 3)`: 10 unsorted `btreeInsert`s
(filling the root leaf on the first 5 keys `[8, 2, 14, 5, 11]`, promoting median `8` on key `6`,
and filling/splitting the right child on `[9, 10, 12, 13]`), an in-place `btreeInsert` overwrite of
`8`, `btreeUpdate` on present `13` and absent `1`, and `btreeDelete` of promoted separator `8` and
leaf key `2`. -/
def sampleTrace3 : List SliceOp :=
  [ .insert 8 80, .insert 2 20, .insert 14 140, .insert 5 50, .insert 11 110,
    .insert 6 60, .insert 9 90, .insert 10 100, .insert 12 120, .insert 13 130,
    .insert 8 88, .update 13 133, .update 1 99, .delete 8, .delete 2 ]

/-- End-to-end verification of `sampleTrace3` proving that the resulting root is an internal node
(`metaIsLeaf = false`, since `8 > 5` live keys exceed single-leaf capacity `2 * 3 - 1 = 5`), meets
packed word-width bounds (`ValidSubtree.node_bits_lt`), and returns exact `btreeLookup` answers on
all present/overwritten/deleted keys. -/
theorem btree_multi_split_overwrite_delete_separator :
    let slFinal := sampleTrace3.foldl stepSlice3 emptyBTreeSlice
    metaIsLeaf (slFinal.nodes slFinal.root).metaWord = false ∧
    (slFinal.nodes slFinal.root).metaWord < 2 ^ 4 ∧
    (slFinal.nodes slFinal.root).keysWord < 2 ^ 36 ∧
    (slFinal.nodes slFinal.root).valsWord < 2 ^ 48 ∧
    btreeLookup 4 8 3 slFinal 8 = none ∧
    btreeLookup 4 8 3 slFinal 2 = none ∧
    btreeLookup 4 8 3 slFinal 1 = none ∧
    btreeLookup 4 8 3 slFinal 5 = some 50 ∧
    btreeLookup 4 8 3 slFinal 6 = some 60 ∧
    btreeLookup 4 8 3 slFinal 9 = some 90 ∧
    btreeLookup 4 8 3 slFinal 10 = some 100 ∧
    btreeLookup 4 8 3 slFinal 11 = some 110 ∧
    btreeLookup 4 8 3 slFinal 12 = some 120 ∧
    btreeLookup 4 8 3 slFinal 13 = some 133 ∧
    btreeLookup 4 8 3 slFinal 14 = some 140 := by
  have hv0 : ValidSubtree3 0 emptyBTreeSlice (fun _ => none) := by
    refine ⟨by decide, .leaf 0 0, rfl, le_rfl, by simp [BTreeTree.potential]; rfl,
      by decide, rfl, by decide, by decide, by decide,
      fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ => Or.inr ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩⟩
  have hops : ∀ op ∈ sampleTrace3, ValidSliceOp3 op := by simp [sampleTrace3, ValidSliceOp3]
  have hins : 0 + countInserts sampleTrace3 ≤ 40 := by decide
  obtain ⟨ha_pos, T, hrt, hht_le, _, hv⟩ := validSubtree3_foldl sampleTrace3 hv0 hins hops
  obtain ⟨hmeta_lt, hkeys_lt, hvals_lt⟩ :=
    hv.node_bits_lt (metaBits := 4) (by decide) (by decide) _ (hrt ▸ T.rootIdx_mem_nodeSet)
  have hfuel : T.height ≤ hMaxBTree := by
    have : 0 + countInserts sampleTrace3 = 11 := by decide
    rw [hMaxBTree_eq]; omega
  have hlk : ∀ q < 16,
      btreeLookup 4 8 3 (sampleTrace3.foldl stepSlice3 emptyBTreeSlice) q =
        (sampleTrace3.foldl stepMapFn (fun _ => none)) q :=
    fun q hq => btreeLookup_eq_of_subtree (by decide) (by decide) ha_pos hrt hv hfuel hq
  have hnot_leaf : metaIsLeaf
      ((sampleTrace3.foldl stepSlice3 emptyBTreeSlice).nodes
        (sampleTrace3.foldl stepSlice3 emptyBTreeSlice).root).metaWord = false := by
    cases T with
    | branch idx cnt cs =>
      dsimp only [BTreeTree.rootIdx] at hrt
      rw [← hrt, hv.2.1, metaIsLeaf_mkNodeMeta]
    | leaf idx cnt =>
      exfalso
      obtain ⟨_, _, hcnt_le, _, _, _, hmono, href⟩ := hv
      have hhit (q : ℕ) (hq15 : q ≤ 15)
          (hsome : (sampleTrace3.foldl stepMapFn (fun _ => none) q).isSome = true) :
          ∃ j < cnt, laneGet (4 + 2)
            ((sampleTrace3.foldl stepSlice3 emptyBTreeSlice).nodes idx).keysWord j = q := by
        rcases href q (Nat.zero_le q) hq15 with ⟨j, hj, hkj, _⟩ | ⟨_, hnone⟩
        · exact ⟨j, hj, hkj⟩
        · rw [hnone] at hsome; cases hsome
      obtain ⟨j0, hj0, hk0⟩ := hhit 5 (by decide) (by decide)
      obtain ⟨j1, hj1, hk1⟩ := hhit 6 (by decide) (by decide)
      obtain ⟨j2, hj2, hk2⟩ := hhit 9 (by decide) (by decide)
      obtain ⟨j3, hj3, hk3⟩ := hhit 10 (by decide) (by decide)
      obtain ⟨j4, hj4, hk4⟩ := hhit 11 (by decide) (by decide)
      obtain ⟨j5, hj5, hk5⟩ := hhit 12 (by decide) (by decide)
      have hlt_idx {a b : ℕ} (ha : a < cnt) (hb : b < cnt)
          (hab : laneGet (4 + 2)
              ((sampleTrace3.foldl stepSlice3 emptyBTreeSlice).nodes idx).keysWord a <
            laneGet (4 + 2)
              ((sampleTrace3.foldl stepSlice3 emptyBTreeSlice).nodes idx).keysWord b) :
          a < b := by
        rcases lt_trichotomy a b with h | rfl | h
        · exact h
        · omega
        · have := hmono b a h ha; omega
      have h01 : j0 < j1 := hlt_idx hj0 hj1 (by omega)
      have h12 : j1 < j2 := hlt_idx hj1 hj2 (by omega)
      have h23 : j2 < j3 := hlt_idx hj2 hj3 (by omega)
      have h34 : j3 < j4 := hlt_idx hj3 hj4 (by omega)
      have h45 : j4 < j5 := hlt_idx hj4 hj5 (by omega)
      omega
  refine ⟨hnot_leaf, hmeta_lt, hkeys_lt, hvals_lt,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hlk _ (by decide)]; decide)

/-- Folding any valid `SliceOp` sequence preserves `ValidWhpSlice`. -/
theorem validWhpSlice_foldl {c n_max ins₀ : ℕ} {sl₀ : BTreeSlice} {map₀ : ℕ → Option ℕ}
    (hth : whpThreshold c ≤ n_max) (ops : List SliceOp)
    (hv₀ : ValidWhpSlice n_max ins₀ sl₀ map₀)
    (hins : ins₀ + countInserts ops ≤ 8 * (slabScale n_max) ^ 12)
    (hops : ∀ op ∈ ops, ValidSliceOp n_max op) :
    ValidWhpSlice n_max (ins₀ + countInserts ops)
      (ops.foldl (stepWhpSlice n_max) sl₀) (ops.foldl stepMapFn map₀) := by
  induction ops generalizing ins₀ sl₀ map₀ with
  | nil =>
    simpa [countInserts] using hv₀
  | cons op rest ih =>
    have hop : ValidSliceOp n_max op := hops op (List.mem_cons_self ..)
    have hrest : ∀ o ∈ rest, ValidSliceOp n_max o :=
      fun o ho => hops o (List.mem_cons_of_mem _ ho)
    cases op with
    | insert q v =>
      dsimp only [countInserts] at hins ⊢
      have hv₁ := (hv₀.insert_spec hth (by omega) hop.1 hop.2).2
      have hih := ih hv₁ (by omega) hrest
      simpa only [List.foldl_cons, stepWhpSlice, stepMapFn,
        Nat.add_assoc, Nat.add_comm 1 (countInserts rest)] using hih
    | update q v =>
      dsimp only [countInserts] at hins ⊢
      exact ih (hv₀.update_spec hth (by omega) hop.1 hop.2) hins hrest
    | delete q =>
      dsimp only [countInserts] at hins ⊢
      exact ih (hv₀.delete_spec hth (by omega) hop) hins hrest

/-- Concrete 4-step sequence `insert 3 30 → insert 9 90 → update 3 33 → delete 9` verified via
`validWhpSlice_foldl`, `ValidWhpSlice.lookup_eq`, and `ValidWhpSlice.alloc_and_height_lt` at
`n_max = whpThreshold c` (including single-word packed bit-width fit `< 2 ^ ⌊log₂ n_max⌋`). -/
theorem validWhpSlice_sequence_lookup (c : ℕ) :
    let n_max := whpThreshold c
    let ops : List SliceOp := [.insert 3 30, .insert 9 90, .update 3 33, .delete 9]
    let slFinal := ops.foldl (stepWhpSlice n_max) uninitSlice
    slFinal.alloc < nSliceWhp n_max ∧
    (slFinal.nodes slFinal.root).keysWord < 2 ^ Nat.log 2 n_max ∧
    (slFinal.nodes slFinal.root).valsWord < 2 ^ Nat.log 2 n_max ∧
    btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) slFinal 3 = some 33 ∧
    btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) slFinal 9 = none ∧
    btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) slFinal 5 = none := by
  intro n_max ops slFinal
  have hth : whpThreshold c ≤ n_max := le_rfl
  have hell := Dynamic.one_le_logLogFactor n_max
  have hL2 := two_le_slabScale n_max
  have hfp_ge : 16 ≤ 2 ^ fpBitsWhp n_max := by
    calc 16 = 2 ^ 4 := by decide
      _ ≤ 2 ^ (36 * Dynamic.logLogFactor n_max) := Nat.pow_le_pow_right (by decide) (by omega)
  have hval_ge : 128 ≤ 2 ^ valLaneBitsWhp n_max := by
    calc 128 = 2 ^ 7 := by decide
      _ ≤ 2 ^ (12 * Dynamic.logLogFactor n_max + 8) := Nat.pow_le_pow_right (by decide) (by omega)
  have hL12_ge : 2 ≤ 8 * (slabScale n_max) ^ 12 := by
    have : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (by omega)
    omega
  have hv₀ : ValidWhpSlice n_max 0 uninitSlice (fun _ => none) :=
    validWhpSlice_zero n_max 0 uninitSlice.nodes
  have hops : ∀ op ∈ ops, ValidSliceOp n_max op := by
    intro op hop
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl <;>
      dsimp only [ValidSliceOp] <;> omega
  have hvFinal := validWhpSlice_foldl hth ops hv₀
    (by dsimp [ops, countInserts]; omega) hops
  have hins_final : 0 + countInserts ops ≤ 8 * (slabScale n_max) ^ 12 := by
    dsimp [ops, countInserts]; omega
  dsimp only [slFinal]
  have hlk3 : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (ops.foldl (stepWhpSlice n_max) uninitSlice) 3 = some 33 := by
    rw [hvFinal.lookup_eq hth hins_final (by omega)]; rfl
  obtain ⟨halloc_lt, ⟨_, hmap0⟩ | ⟨_, T, hrt, _, _, hbits, _⟩⟩ :=
    hvFinal.alloc_and_height_lt hth hins_final
  · have h3_eq : (ops.foldl stepMapFn (fun _ => none)) 3 = some 33 := rfl
    rw [hmap0] at h3_eq
    cases h3_eq
  · obtain ⟨_, hkw_lt, hvw_lt⟩ := hbits _ (hrt ▸ T.rootIdx_mem_nodeSet)
    have hkw_log : keysWordBitsWhp n_max < Nat.log 2 n_max :=
      (Nat.le_add_right _ _).trans_lt (keysWordBitsWhp_lt_log hth)
    have hvw_log : valsWordBitsWhp n_max < Nat.log 2 n_max :=
      (Nat.le_add_right _ _).trans_lt (valsWordBitsWhp_lt_log hth)
    refine ⟨by omega,
      hkw_lt.trans (Nat.pow_lt_pow_right (by decide) hkw_log),
      hvw_lt.trans (Nat.pow_lt_pow_right (by decide) hvw_log),
      hlk3, ?_, ?_⟩
    · rw [hvFinal.lookup_eq hth hins_final (by omega)]; rfl
    · rw [hvFinal.lookup_eq hth hins_final (by omega)]; rfl

/-! ## 5. `BufTrie`: Shared-Prefix Sharing, Slot Reactivation, Scan, and Cleanup -/

/-- Insert keys `5` (digits `[1, 1, 0]`), `21` (digits `[1, 1, 1]`), and `42` (digits `[2, 2, 2]`)
into `emptyBufTrie` at `(cTab = 3, bChar = 2)`. -/
def sampleBuf3 : BufTrie :=
  let t1 := bufInsert 3 2 emptyBufTrie 5 2 20
  let t2 := bufInsert 3 2 t1 21 4 40
  bufInsert 3 2 t2 42 7 70

/-- Keys `5` and `21` share a 2-digit prefix `[1, 1]`, allocating `8` total nodes (`1` root + `3 +
1 + 3`) rather than `1 + 3 * 3 = 10`. -/
example : sampleBuf3.nodeAlloc = 8 ∧
    sampleBuf3.itemAlloc = 3 ∧
    bufLookup 3 2 sampleBuf3 5 = some (2, 20) ∧
    bufLookup 3 2 sampleBuf3 21 = some (4, 40) ∧
    bufLookup 3 2 sampleBuf3 42 = some (7, 70) ∧
    bufLookup 3 2 sampleBuf3 9 = none ∧
    bufCheckSlot sampleBuf3 0 = some (2, 20) ∧
    bufCheckSlot sampleBuf3 1 = some (4, 40) ∧
    bufCheckSlot sampleBuf3 2 = some (7, 70) := by decide

/-- Deleting `21` clears `bufLookup` and `bufCheckSlot 1` while retaining `bufEverPresent = true`,
and re-inserting `21` in the same epoch allocates zero new trie nodes or item slots. -/
def sampleBufReactivated : BufTrie :=
  let td := bufDelete 3 2 sampleBuf3 21
  bufInsert 3 2 td 21 9 99

example :
    let td := bufDelete 3 2 sampleBuf3 21
    bufLookup 3 2 td 21 = none ∧
    bufCheckSlot td 1 = none ∧
    bufEverPresent 3 2 td 21 = true ∧
    sampleBufReactivated.nodeAlloc = 8 ∧
    sampleBufReactivated.itemAlloc = 3 ∧
    bufLookup 3 2 sampleBufReactivated 21 = some (9, 99) ∧
    bufCheckSlot sampleBufReactivated 1 = some (9, 99) := by decide

/-- `bufClearSteps` restores `nodeAlloc = 1`, `itemAlloc = 0`, and empty lookups/flags in `8`
elementary steps. -/
example :
    let tc := bufClearSteps 8 sampleBufReactivated
    tc.nodeAlloc = 1 ∧
    tc.itemAlloc = 0 ∧
    bufLookup 3 2 tc 5 = none ∧
    bufLookup 3 2 tc 21 = none ∧
    bufLookup 3 2 tc 42 = none ∧
    bufEverPresent 3 2 tc 21 = false := by decide

/-- Symbolic composition of `validBufTrie_empty`, `insert_spec`, `insert_nodeAlloc_le`,
`delete_spec`, `exists_checkSlot_of_map_some`, single-step `toClearable` / `clearOne_step`, and
`clearSteps_spec`. -/
theorem bufTrie_lifecycle_spec :
    let t1 := bufInsert 3 2 emptyBufTrie 5 2 20
    let t2 := bufDelete 3 2 t1 5
    let t3 := bufInsert 3 2 t2 5 6 60
    let tc1 := bufClearOne t3
    let tc := bufClearSteps tc1.nodeAlloc tc1
    t1.itemAlloc = 1 ∧
    t3.nodeAlloc = t1.nodeAlloc ∧
    t3.itemAlloc = t1.itemAlloc ∧
    t3.nodeAlloc ≤ 1 + 3 * t3.itemAlloc ∧
    (∃ id < t3.itemAlloc, bufCheckSlot t3 id = some (6, 60)) ∧
    ClearableBufTrie tc1 ∧
    tc1.nodeAlloc = max 1 (t3.nodeAlloc - 1) ∧
    ValidBufTrie 3 2 tc (fun _ => none) ∧
    tc.nodeAlloc = 1 ∧
    tc.itemAlloc = 0 := by
  have hk : 5 < 2 ^ (3 * 2) := by decide
  have hv0 := validBufTrie_empty 3 2
  obtain ⟨hv1, _, _, hia1, hev1, _, _⟩ := hv0.insert_spec (b := 2) (loc := 20) hk
  have hia1_eq : (bufInsert 3 2 emptyBufTrie 5 2 20).itemAlloc = 1 := by
    have hev0 : bufEverPresent 3 2 emptyBufTrie 5 = false := by decide
    rw [hev0] at hia1
    simpa [emptyBufTrie] using hia1
  have hlin1 : (bufInsert 3 2 emptyBufTrie 5 2 20).nodeAlloc ≤
      1 + 3 * (bufInsert 3 2 emptyBufTrie 5 2 20).itemAlloc :=
    hv0.insert_nodeAlloc_le hk (by decide)
  obtain ⟨hv2, hna2, hia2, hev2, _⟩ := hv1.delete_spec hk
  have hev_t2 : bufEverPresent 3 2 (bufDelete 3 2 (bufInsert 3 2 emptyBufTrie 5 2 20) 5) 5 =
      true := by
    rw [hev2]
    simpa using hev1 5 hk
  obtain ⟨hv3, _, _, _, _, hreuse, _⟩ := hv2.insert_spec (b := 6) (loc := 60) hk
  obtain ⟨hna3, hia3⟩ := hreuse hev_t2
  have hlin3 := hv2.insert_nodeAlloc_le (b := 6) (loc := 60) hk (by rw [hna2, hia2]; exact hlin1)
  have hscan := hv3.exists_checkSlot_of_map_some (k := 5) (b := 6) (loc := 60)
    (by simp [Function.update_self])
  obtain ⟨hc1, hnac1⟩ := hv3.toClearable.clearOne_step
  obtain ⟨hvc, hnac, hiac⟩ := hc1.clearSteps_spec 3 2 _ le_rfl
  exact ⟨hia1_eq, hna3.trans hna2, hia3.trans hia2, hlin3, hscan, hc1, hnac1, hvc, hnac, hiac⟩

end CslibFrontierTests.DataStructure.SuccinctWhpSwarBTree

end
