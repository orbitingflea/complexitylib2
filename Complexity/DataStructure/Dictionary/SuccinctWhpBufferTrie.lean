/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.SuccinctWhpParams
import Mathlib.Tactic.Ring

/-!
# Bounded-Depth Character Trie Buffer (`BufTrie`) for Deamortized Salt Collisions

This module formalizes the pure model and exact invariants of the constant-depth character trie
(`BufTrie`) used for the two epoch collision buffers (`BufCur` and `BufOld`) in the
with-high-probability succinct dynamic dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Section 5][BenderFarachColtonKuszmaulKuszmaul2024]).

Each Stage-1 reduced key `rKey < 2 ^ (cTab * bChar)` is decomposed into `cTab` digits in base
`2 ^ bChar` (`trieDigit`). A `BufTrie` stores:
* A rooted `2 ^ bChar`-ary trie (root at node `0`, allocated non-root nodes `1 .. nodeAlloc - 1`)
  recording `(nodeParent u, nodeChar u)` for each `1 ≤ u < nodeAlloc` so all dirty child entries can
  be re-zeroed incrementally in `O(1)` writes per step (`bufClearOne`, `bufClearSteps`) without
  scanning `2 ^ bChar` children.
* A sequential append log `0 .. itemAlloc - 1` (`itemLeaf`, `itemBucket`, `itemLoc`), where item
  `id < itemAlloc` is active iff `nodeLeafItem (itemLeaf id) = id + 1`. Deletion clears
  `nodeLeafItem leaf := 0` in one write, and the background rebuilder scans `0 .. itemAlloc - 1`
  via `bufCheckSlot` in `O(1)` time per step without doubly-linked list pointers.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.trieDigit`: base-`2 ^ bChar` digit extraction.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.BufTrie`, `emptyBufTrie`: pure buffer-trie state.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.bufLookup`, `bufInsert`, `bufDelete`,
  `bufCheckSlot`, `bufClearOne`, `bufClearSteps`: constant-time (`O(cTab)`) buffer operations.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidBufTrie`: structural, map-refinement,
  active-slot, and parent-log invariant for `BufTrie`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.eq_of_forall_trieDigit_eq`: digit tuple injectivity on
  `< 2 ^ (cTab * bChar)`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.validBufTrie_empty`,
  `ValidBufTrie.lookup_eq`, `ValidBufTrie.delete_spec`, `ValidBufTrie.insert_spec`,
  `ValidBufTrie.checkSlot_some`, `ValidBufTrie.exists_checkSlot_of_map_some`,
  `ClearableBufTrie.clearSteps_spec`: exact map, active-slot scan, and cleanup specifications.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Section 5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

/-! ## Section 1: Base-`2 ^ bChar` digit extraction and injectivity -/

/-- Extract the `d`-th base-`2 ^ bChar` digit `(rKey / 2 ^ (d * bChar)) % 2 ^ bChar`. -/
@[expose] def trieDigit (bChar d rKey : ℕ) : ℕ :=
  (rKey / 2 ^ (d * bChar)) % 2 ^ bChar

theorem trieDigit_lt (bChar d rKey : ℕ) : trieDigit bChar d rKey < 2 ^ bChar :=
  Nat.mod_lt _ (Nat.two_pow_pos bChar)

theorem trieDigit_zero (bChar rKey : ℕ) : trieDigit bChar 0 rKey = rKey % 2 ^ bChar := by
  simp [trieDigit]

theorem trieDigit_succ (bChar d rKey : ℕ) :
    trieDigit bChar (d + 1) rKey = trieDigit bChar d (rKey / 2 ^ bChar) := by
  unfold trieDigit
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  ring

/-- Keys `< 2 ^ (cTab * bChar)` are uniquely determined by their first `cTab` base-`2 ^ bChar`
digits. -/
theorem eq_of_forall_trieDigit_eq {cTab bChar k₁ k₂ : ℕ}
    (hk₁ : k₁ < 2 ^ (cTab * bChar)) (hk₂ : k₂ < 2 ^ (cTab * bChar))
    (hd : ∀ d < cTab, trieDigit bChar d k₁ = trieDigit bChar d k₂) :
    k₁ = k₂ := by
  induction cTab generalizing k₁ k₂ with
  | zero =>
    simp only [Nat.zero_mul, Nat.pow_zero, Nat.lt_one_iff] at hk₁ hk₂
    omega
  | succ c ih =>
    have h0 := hd 0 (Nat.zero_lt_succ c)
    rw [trieDigit_zero, trieDigit_zero] at h0
    have hpow : 2 ^ ((c + 1) * bChar) = 2 ^ bChar * 2 ^ (c * bChar) := by
      rw [Nat.add_mul, one_mul, add_comm, Nat.pow_add]
    have hdiv₁ : k₁ / 2 ^ bChar < 2 ^ (c * bChar) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos bChar), mul_comm, ← hpow]
      exact hk₁
    have hdiv₂ : k₂ / 2 ^ bChar < 2 ^ (c * bChar) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos bChar), mul_comm, ← hpow]
      exact hk₂
    have hq_eq : k₁ / 2 ^ bChar = k₂ / 2 ^ bChar :=
      ih hdiv₁ hdiv₂ fun d hdc => by
        have hs := hd (d + 1) (Nat.succ_lt_succ hdc)
        rwa [trieDigit_succ, trieDigit_succ] at hs
    rw [← Nat.div_add_mod k₁ (2 ^ bChar), ← Nat.div_add_mod k₂ (2 ^ bChar), hq_eq, h0]

/-! ## Section 2: Pure `BufTrie` state and `O(cTab)` operations -/

/-- Pure state of a bounded-depth character trie buffer with append-only item log and parent-edge
log for incremental `O(1)`-per-step re-zeroing. -/
structure BufTrie where
  /-- Number of allocated trie nodes (`1` initially; node `0` is the root). -/
  nodeAlloc : ℕ
  /-- Number of allocated item log slots (`0 .. itemAlloc - 1`). -/
  itemAlloc : ℕ
  /-- Child pointer table: `0` denotes absent, `u ≥ 1` denotes child node `u`. -/
  trieChild : ℕ → ℕ → ℕ
  /-- Parent node of allocated non-root trie node `u ≥ 1`. -/
  nodeParent : ℕ → ℕ
  /-- Character edge from `nodeParent u` to `u`. -/
  nodeChar : ℕ → ℕ
  /-- Active item slot `+ 1` at leaf node `u` (`0` if never allocated in this epoch). -/
  nodeLeafItem : ℕ → ℕ
  /-- Active flag (`0` if deleted/inactive, non-zero if currently active) at leaf node `u`. -/
  nodeActive : ℕ → ℕ
  /-- Leaf trie node associated with item log slot `id`. -/
  itemLeaf : ℕ → ℕ
  /-- Stored bucket index `b` for item log slot `id`. -/
  itemBucket : ℕ → ℕ
  /-- Stored local coordinate `loc` for item log slot `id`. -/
  itemLoc : ℕ → ℕ

/-- Clean empty `BufTrie` (`nodeAlloc = 1`, `itemAlloc = 0`, all tables zero). -/
@[expose] def emptyBufTrie : BufTrie where
  nodeAlloc := 1
  itemAlloc := 0
  trieChild := fun _ _ => 0
  nodeParent := fun _ => 0
  nodeChar := fun _ => 0
  nodeLeafItem := fun _ => 0
  nodeActive := fun _ => 0
  itemLeaf := fun _ => 0
  itemBucket := fun _ => 0
  itemLoc := fun _ => 0

/-- Walk `rem` digits starting at digit offset `off` from trie node `cur`, returning `some leaf` or
`none` if a zero child pointer is met. -/
@[expose] def bufWalk (bChar : ℕ) (child : ℕ → ℕ → ℕ) (rKey : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, cur => some cur
  | rem + 1, off, cur =>
    let ch := trieDigit bChar off rKey
    let nxt := child cur ch
    if nxt = 0 then none
    else bufWalk bChar child rKey rem (off + 1) nxt

/-- Lookup `rKey` in `tr`, returning `some (b, loc)` if present or `none` if absent. -/
@[expose] def bufLookup (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) : Option (ℕ × ℕ) :=
  match bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => none
  | some leaf =>
    let id1 := tr.nodeLeafItem leaf
    if id1 = 0 ∨ tr.nodeActive leaf = 0 then none
    else some (tr.itemBucket (id1 - 1), tr.itemLoc (id1 - 1))

/-- Whether `rKey` has ever been assigned a leaf item slot in `tr` during the current epoch. -/
@[expose] def bufEverPresent (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) : Bool :=
  match bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => false
  | some leaf => tr.nodeLeafItem leaf != 0

/-- Walk and allocate missing trie nodes along `rem` digits starting at `off` from `cur`, returning
`(tr', leaf)`. -/
@[expose] def bufEnsurePath (bChar rKey : ℕ) : ℕ → ℕ → BufTrie → ℕ → BufTrie × ℕ
  | 0, _, tr, cur => (tr, cur)
  | rem + 1, off, tr, cur =>
    let ch := trieDigit bChar off rKey
    let nxt := tr.trieChild cur ch
    if nxt = 0 then
      let u := tr.nodeAlloc
      let child' := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
      let tr1 : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := child'
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      bufEnsurePath bChar rKey rem (off + 1) tr1 u
    else
      bufEnsurePath bChar rKey rem (off + 1) tr nxt

/-- Insert or overwrite `rKey ↦ (b, loc)` in `tr`:
* If `rKey`'s leaf already has an allocated epoch slot `id = id1 - 1` (active or previously
  deleted), reactivates and updates `(itemBucket, itemLoc)` in place without incrementing
  `itemAlloc` or `nodeAlloc`.
* Otherwise allocates `id := tr1.itemAlloc` (`itemAlloc + 1`) and links `leaf ↔ id`. -/
@[expose] def bufInsert (cTab bChar : ℕ) (tr : BufTrie) (rKey b loc : ℕ) : BufTrie :=
  let p := bufEnsurePath bChar rKey cTab 0 tr 0
  let tr1 := p.1
  let leaf := p.2
  let id1 := tr1.nodeLeafItem leaf
  if id1 = 0 then
    let id := tr1.itemAlloc
    { tr1 with
      itemAlloc := id + 1
      nodeLeafItem := Function.update tr1.nodeLeafItem leaf (id + 1)
      nodeActive := Function.update tr1.nodeActive leaf 1
      itemLeaf := Function.update tr1.itemLeaf id leaf
      itemBucket := Function.update tr1.itemBucket id b
      itemLoc := Function.update tr1.itemLoc id loc }
  else
    let id := id1 - 1
    { tr1 with
      nodeActive := Function.update tr1.nodeActive leaf 1
      itemBucket := Function.update tr1.itemBucket id b
      itemLoc := Function.update tr1.itemLoc id loc }

/-- Delete `rKey` from `tr` in `O(cTab)` steps (clearing `nodeActive leaf := 0` while preserving
its epoch slot `nodeLeafItem leaf` so re-insertions of `rKey` allocate zero new slots). -/
@[expose] def bufDelete (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) : BufTrie :=
  match bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => tr
  | some leaf =>
    if tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0 then tr
    else { tr with nodeActive := Function.update tr.nodeActive leaf 0 }

/-- Constant-time (`O(1)`) scan probe at item slot `id < tr.itemAlloc`: returns `some (b, loc)` iff
item `id` is still active (`nodeLeafItem (itemLeaf id) = id + 1 ∧ nodeActive (itemLeaf id) ≠ 0`). -/
@[expose] def bufCheckSlot (tr : BufTrie) (id : ℕ) : Option (ℕ × ℕ) :=
  if id < tr.itemAlloc then
    let leaf := tr.itemLeaf id
    if tr.nodeLeafItem leaf = id + 1 ∧ tr.nodeActive leaf ≠ 0 then
      some (tr.itemBucket id, tr.itemLoc id)
    else none
  else none

/-- One elementary `O(1)` cleanup step: pops one allocated non-root node `u = nodeAlloc - 1` and
re-zeroes both `trieChild (nodeParent u) (nodeChar u)` and `nodeLeafItem u` (setting
`itemAlloc := 0` and `nodeLeafItem 0 := 0` once `nodeAlloc ≤ 1`). -/
@[expose] def bufClearOne (tr : BufTrie) : BufTrie :=
  if 1 < tr.nodeAlloc then
    let u := tr.nodeAlloc - 1
    let p := tr.nodeParent u
    let ch := tr.nodeChar u
    let child' := Function.update tr.trieChild p (Function.update (tr.trieChild p) ch 0)
    { tr with
      nodeAlloc := u
      itemAlloc := 0
      trieChild := child'
      nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
  else
    { tr with
      nodeAlloc := 1
      itemAlloc := 0
      nodeLeafItem := Function.update tr.nodeLeafItem 0 0 }

/-- Execute `k` elementary `bufClearOne` steps. -/
@[expose] def bufClearSteps : ℕ → BufTrie → BufTrie
  | 0, tr => tr
  | k + 1, tr => bufClearSteps k (bufClearOne tr)

/-! ## Section 3: Exact structural and map invariant (`ValidBufTrie`) -/

/-- Structural, parent-log, and map-refinement invariant for `BufTrie` at character count `cTab ≥ 1`
and character bit-width `bChar`. -/
@[expose] def ValidBufTrie (cTab bChar : ℕ) (tr : BufTrie)
    (mapFn : ℕ → Option (ℕ × ℕ)) : Prop :=
  1 ≤ tr.nodeAlloc ∧
  (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) ∧
  (∀ k, 2 ^ (cTab * bChar) ≤ k → mapFn k = none) ∧
  (∀ k < 2 ^ (cTab * bChar), mapFn k = bufLookup cTab bChar tr k) ∧
  ∃ depth : ℕ → ℕ,
    depth 0 = 0 ∧
    (∀ u, 1 ≤ u → u < tr.nodeAlloc →
      tr.nodeParent u < u ∧
      tr.nodeChar u < 2 ^ bChar ∧
      depth u = depth (tr.nodeParent u) + 1 ∧
      depth u ≤ cTab ∧
      tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u) ∧
    (∀ v ch, tr.trieChild v ch ≠ 0 ↔
      (1 ≤ tr.trieChild v ch ∧
       tr.trieChild v ch < tr.nodeAlloc ∧
       tr.nodeParent (tr.trieChild v ch) = v ∧
       tr.nodeChar (tr.trieChild v ch) = ch)) ∧
    (∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 →
      depth u = cTab ∧
      tr.nodeLeafItem u ≤ tr.itemAlloc ∧
      tr.itemLeaf (tr.nodeLeafItem u - 1) = u ∧
      ∃ k < 2 ^ (cTab * bChar), bufWalk bChar tr.trieChild k cTab 0 0 = some u)

/-- `emptyBufTrie` satisfies `ValidBufTrie` for the empty map. -/
theorem validBufTrie_empty (cTab bChar : ℕ) :
    ValidBufTrie cTab bChar emptyBufTrie (fun _ => none) := by
  refine ⟨le_rfl, fun _ _ => rfl, fun _ _ => rfl, fun k _ => ?_, fun _ => 0, rfl, ?_, ?_, ?_⟩
  · cases cTab with
    | zero => simp [bufLookup, bufWalk, emptyBufTrie]
    | succ c => simp [bufLookup, bufWalk, emptyBufTrie]
  · intro u h1 hlt; dsimp only [emptyBufTrie] at hlt; omega
  · intro v ch; simp [emptyBufTrie]
  · intro u _ hnz; simp [emptyBufTrie] at hnz

/-- Lookup on a `ValidBufTrie` agrees with `mapFn` on `< 2 ^ (cTab * bChar)`. -/
theorem ValidBufTrie.lookup_eq {cTab bChar rKey : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) :
    bufLookup cTab bChar tr rKey = mapFn rKey :=
  (hv.2.2.2.1 rKey hk).symm

/-- Walk depth and injectivity lemma: under `ValidBufTrie`'s edge invariant, `bufWalk` from a node
`cur < nodeAlloc` of depth `off` reaches a node `< nodeAlloc` of depth `off + rem`, and any two
walks of length `rem` from depth `off` reaching the same node started at the same `cur` and read
the exact same `rem` digits. -/
private theorem bufWalk_props {bChar nodeAlloc : ℕ} {child : ℕ → ℕ → ℕ}
    {nodeParent nodeChar depth : ℕ → ℕ}
    (hp_edge : ∀ u, 1 ≤ u → u < nodeAlloc → depth u = depth (nodeParent u) + 1)
    (hiff : ∀ v ch, child v ch ≠ 0 ↔
      (1 ≤ child v ch ∧ child v ch < nodeAlloc ∧
       nodeParent (child v ch) = v ∧ nodeChar (child v ch) = ch)) :
    ∀ (rem off cur leaf : ℕ) (k : ℕ),
      cur < nodeAlloc → depth cur = off →
      bufWalk bChar child k rem off cur = some leaf →
      leaf < nodeAlloc ∧ depth leaf = off + rem ∧
      ∀ (cur₂ k₂ : ℕ), cur₂ < nodeAlloc → depth cur₂ = off →
        bufWalk bChar child k₂ rem off cur₂ = some leaf →
        cur = cur₂ ∧ (∀ j < rem, trieDigit bChar (off + j) k = trieDigit bChar (off + j) k₂) := by
  intro rem
  induction rem with
  | zero =>
    intro off cur leaf k hcur hdep hw
    simp only [bufWalk, Option.some.injEq] at hw
    subst hw
    refine ⟨hcur, by omega, fun cur₂ k₂ _ _ hw₂ => ?_⟩
    simp only [bufWalk, Option.some.injEq] at hw₂
    exact ⟨hw₂.symm, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ rem ih =>
    intro off cur leaf k hcur hdep hw
    dsimp only [bufWalk] at hw
    set ch₁ := trieDigit bChar off k
    set nxt₁ := child cur ch₁
    by_cases h0 : nxt₁ = 0
    · simp [h0] at hw
    · simp only [h0, ↓reduceIte] at hw
      obtain ⟨h1_ge, h1_lt, hp1, hc1⟩ := (hiff cur ch₁).mp h0
      have hd1 : depth nxt₁ = off + 1 := by rw [hp_edge nxt₁ h1_ge h1_lt, hp1, hdep]
      obtain ⟨hleaf_lt, hleaf_dep, huniq⟩ := ih (off + 1) nxt₁ leaf k h1_lt hd1 hw
      refine ⟨hleaf_lt, by omega, fun cur₂ k₂ hcur₂ hdep₂ hw₂ => ?_⟩
      dsimp only [bufWalk] at hw₂
      set ch₂ := trieDigit bChar off k₂
      set nxt₂ := child cur₂ ch₂
      by_cases h0₂ : nxt₂ = 0
      · simp [h0₂] at hw₂
      · simp only [h0₂, ↓reduceIte] at hw₂
        obtain ⟨h2_ge, h2_lt, hp2, hc2⟩ := (hiff cur₂ ch₂).mp h0₂
        have hd2' : depth nxt₂ = off + 1 := by rw [hp_edge nxt₂ h2_ge h2_lt, hp2, hdep₂]
        obtain ⟨hnxt_eq, hdigits⟩ := huniq nxt₂ k₂ h2_lt hd2' hw₂
        have hch_eq_node : child cur ch₁ = child cur₂ ch₂ := hnxt_eq
        have hcur_eq : cur = cur₂ := by rw [← hp1, hch_eq_node, hp2]
        have hch_eq : ch₁ = ch₂ := by rw [← hc1, hch_eq_node, hc2]
        refine ⟨hcur_eq, fun j hj => ?_⟩
        rcases j with _ | j'
        · simpa only [Nat.add_zero] using hch_eq
        · have hj' : j' < rem := by omega
          simpa only [Nat.add_assoc, Nat.add_comm 1 j'] using hdigits j' hj'


/-- Monotonicity of `bufWalk`: adding new edges (without changing non-zero child pointers) preserves
every successful walk. -/
private theorem bufWalk_mono {bChar : ℕ} {child₁ child₂ : ℕ → ℕ → ℕ}
    (hmono : ∀ v ch, child₁ v ch ≠ 0 → child₂ v ch = child₁ v ch) :
    ∀ rem off cur leaf k,
      bufWalk bChar child₁ k rem off cur = some leaf →
      bufWalk bChar child₂ k rem off cur = some leaf := by
  intro rem
  induction rem with
  | zero =>
    intro off cur leaf k hw
    exact hw
  | succ rem ih =>
    intro off cur leaf k hw
    dsimp only [bufWalk] at hw ⊢
    set ch := trieDigit bChar off k
    by_cases h0 : child₁ cur ch = 0
    · simp [h0] at hw
    · simp only [h0, ↓reduceIte] at hw
      have heq := hmono cur ch h0
      rw [heq]
      simp only [h0, ↓reduceIte]
      exact ih (off + 1) (child₁ cur ch) leaf k hw

/-- When every non-zero child pointer strictly increases node index (`v < child v ch`), `bufWalk`
never decreases the node index (`cur ≤ leaf`). -/
private theorem bufWalk_le_leaf {bChar : ℕ} {child : ℕ → ℕ → ℕ}
    (hinc : ∀ v ch, child v ch ≠ 0 → v < child v ch) :
    ∀ rem off cur leaf k,
      bufWalk bChar child k rem off cur = some leaf →
      cur ≤ leaf := by
  intro rem
  induction rem with
  | zero =>
    intro off cur leaf k hw
    simp only [bufWalk, Option.some.injEq] at hw
    omega
  | succ rem ih =>
    intro off cur leaf k hw
    dsimp only [bufWalk] at hw
    set ch := trieDigit bChar off k
    by_cases h0 : child cur ch = 0
    · simp [h0] at hw
    · simp only [h0, ↓reduceIte] at hw
      have hlt := hinc cur ch h0
      have hle := ih (off + 1) (child cur ch) leaf k hw
      omega

/-- If `bufWalk` fails in `child₁` (`= none`) and succeeds in an extension `child₂` (`= some leaf`)
where every newly added edge points to a node `≥ bound` and `child₂` strictly increases node
indices, then `bound ≤ leaf`. -/
private theorem bufWalk_ge_of_none {bChar bound : ℕ} {child₁ child₂ : ℕ → ℕ → ℕ}
    (hnew : ∀ v ch, child₂ v ch ≠ child₁ v ch → bound ≤ child₂ v ch)
    (hinc : ∀ v ch, child₂ v ch ≠ 0 → v < child₂ v ch) :
    ∀ rem off cur leaf k,
      bufWalk bChar child₁ k rem off cur = none →
      bufWalk bChar child₂ k rem off cur = some leaf →
      bound ≤ leaf := by
  intro rem
  induction rem with
  | zero =>
    intro off cur leaf k hw₁ _
    simp [bufWalk] at hw₁
  | succ rem ih =>
    intro off cur leaf k hw₁ hw₂
    dsimp only [bufWalk] at hw₁ hw₂
    set ch := trieDigit bChar off k
    by_cases h0₂ : child₂ cur ch = 0
    · simp [h0₂] at hw₂
    · simp only [h0₂, ↓reduceIte] at hw₂
      by_cases h0₁ : child₁ cur ch = 0
      · have hne : child₂ cur ch ≠ child₁ cur ch := by omega
        have hb : bound ≤ child₂ cur ch := hnew cur ch hne
        have hle := bufWalk_le_leaf hinc rem (off + 1) (child₂ cur ch) leaf k hw₂
        omega
      · simp only [h0₁, ↓reduceIte] at hw₁
        by_cases heq : child₂ cur ch = child₁ cur ch
        · rw [heq] at hw₂
          exact ih (off + 1) (child₁ cur ch) leaf k hw₁ hw₂
        · have hb : bound ≤ child₂ cur ch := hnew cur ch heq
          have hle := bufWalk_le_leaf hinc rem (off + 1) (child₂ cur ch) leaf k hw₂
          omega

/-- Exact specification of `bufDelete`: preserves `ValidBufTrie` for
`Function.update mapFn rKey none`, leaves `nodeAlloc`, `itemAlloc`, and `bufEverPresent` unchanged,
and never activates an inactive item slot. -/
theorem ValidBufTrie.delete_spec {cTab bChar rKey : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) :
    let tr' := bufDelete cTab bChar tr rKey
    ValidBufTrie cTab bChar tr' (Function.update mapFn rKey none) ∧
    tr'.nodeAlloc = tr.nodeAlloc ∧
    tr'.itemAlloc = tr.itemAlloc ∧
    bufEverPresent cTab bChar tr' = bufEverPresent cTab bChar tr ∧
    (∀ id, bufCheckSlot tr id = none → bufCheckSlot tr' id = none) := by
  obtain ⟨halloc, hzero, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  have hp_edge : ∀ u, 1 ≤ u → u < tr.nodeAlloc → depth u = depth (tr.nodeParent u) + 1 :=
    fun u h1 h2 => (hedge u h1 h2).2.2.1
  dsimp only [bufDelete]
  cases hw : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none =>
    dsimp only
    have hmr : mapFn rKey = none := by
      rw [hmap rKey hk]
      simp [bufLookup, hw]
    have hupd : Function.update mapFn rKey none = mapFn := by
      funext x; by_cases hx : x = rKey <;> simp [hx, hmr]
    rw [hupd]
    exact ⟨⟨halloc, hzero, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩,
      rfl, rfl, rfl, fun _ h => h⟩
  | some leaf =>
    dsimp only
    by_cases hcond : tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0
    · simp only [hcond, ↓reduceIte]
      have hmr : mapFn rKey = none := by
        rw [hmap rKey hk]
        simp [bufLookup, hw, hcond]
      have hupd : Function.update mapFn rKey none = mapFn := by
        funext x; by_cases hx : x = rKey <;> simp [hx, hmr]
      rw [hupd]
      exact ⟨⟨halloc, hzero, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩,
        trivial, trivial, trivial, fun _ h => h⟩
    · simp only [hcond, ↓reduceIte]
      push Not at hcond
      obtain ⟨hli, _⟩ := hcond
      refine ⟨?_, trivial, trivial, ?_, ?_⟩
      · refine ⟨halloc, hzero, ?_, ?_, depth, hd0, hedge, hiff, hleaf⟩
        · intro k hk_ge
          have hne : k ≠ rKey := by omega
          rw [Function.update_of_ne hne]
          exact hout k hk_ge
        · intro k hk_lt
          by_cases heq : k = rKey
          · subst heq
            simp [bufLookup, hw]
          · rw [Function.update_of_ne heq, hmap k hk_lt]
            dsimp only [bufLookup]
            cases hwk : bufWalk bChar tr.trieChild k cTab 0 0 with
            | none => rfl
            | some leaf_k =>
              have hne_leaf : leaf_k ≠ leaf := by
                intro hl_eq
                subst hl_eq
                have hwp := bufWalk_props hp_edge hiff cTab 0 0 leaf_k rKey halloc hd0 hw
                have hdig := (hwp.2.2 0 k halloc hd0 hwk).2
                exact heq (eq_of_forall_trieDigit_eq hk_lt hk
                  (fun d hd => by
                    have h := hdig d hd
                    simpa only [Nat.zero_add] using h.symm))
              dsimp only
              simp only [Function.update_of_ne hne_leaf]
      · rfl
      · intro id hnone
        dsimp only [bufCheckSlot] at hnone ⊢
        by_cases hid : id < tr.itemAlloc
        · simp only [hid, ↓reduceIte] at hnone ⊢
          by_cases hleaf_eq : tr.itemLeaf id = leaf
          · simp [hleaf_eq]
          · simp only [Function.update_of_ne hleaf_eq]
            exact hnone
        · simp [hid]

/-- Structural invariant preserved along `bufEnsurePath`. -/
private theorem bufEnsurePath_props {cTab bChar rKey : ℕ} :
    ∀ (rem off : ℕ) (tr : BufTrie) (cur : ℕ) (depth : ℕ → ℕ),
      off + rem = cTab →
      1 ≤ tr.nodeAlloc →
      (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) →
      depth 0 = 0 →
      (∀ u, 1 ≤ u → u < tr.nodeAlloc →
        tr.nodeParent u < u ∧
        tr.nodeChar u < 2 ^ bChar ∧
        depth u = depth (tr.nodeParent u) + 1 ∧
        depth u ≤ cTab ∧
        tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u) →
      (∀ v ch, tr.trieChild v ch ≠ 0 ↔
        (1 ≤ tr.trieChild v ch ∧
         tr.trieChild v ch < tr.nodeAlloc ∧
         tr.nodeParent (tr.trieChild v ch) = v ∧
         tr.nodeChar (tr.trieChild v ch) = ch)) →
      (∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 →
        depth u = cTab ∧
        tr.nodeLeafItem u ≤ tr.itemAlloc ∧
        tr.itemLeaf (tr.nodeLeafItem u - 1) = u ∧
        ∃ k < 2 ^ (cTab * bChar), bufWalk bChar tr.trieChild k cTab 0 0 = some u) →
      cur < tr.nodeAlloc →
      depth cur = off →
      let p := bufEnsurePath bChar rKey rem off tr cur
      let tr1 := p.1
      let leaf := p.2
      tr.nodeAlloc ≤ tr1.nodeAlloc ∧
      tr1.nodeAlloc ≤ tr.nodeAlloc + rem ∧
      tr1.itemAlloc = tr.itemAlloc ∧
      tr1.itemLeaf = tr.itemLeaf ∧
      tr1.itemBucket = tr.itemBucket ∧
      tr1.itemLoc = tr.itemLoc ∧
      tr1.nodeActive = tr.nodeActive ∧
      (∀ u, tr1.nodeAlloc ≤ u → tr1.nodeLeafItem u = 0) ∧
      (∀ u < tr.nodeAlloc, tr1.nodeLeafItem u = tr.nodeLeafItem u) ∧
      (∀ u, tr.nodeAlloc ≤ u → tr1.nodeLeafItem u = 0) ∧
      (∀ v ch, tr.trieChild v ch ≠ 0 → tr1.trieChild v ch = tr.trieChild v ch) ∧
      (∀ v ch, tr1.trieChild v ch ≠ tr.trieChild v ch → tr.nodeAlloc ≤ tr1.trieChild v ch) ∧
      ((bufWalk bChar tr.trieChild rKey rem off cur = some leaf ∧ tr1 = tr) ∨
       (bufWalk bChar tr.trieChild rKey rem off cur = none ∧ tr.nodeAlloc ≤ leaf)) ∧
      leaf < tr1.nodeAlloc ∧
      bufWalk bChar tr1.trieChild rKey rem off cur = some leaf ∧
      ∃ depth1 : ℕ → ℕ,
        depth1 0 = 0 ∧
        depth1 leaf = cTab ∧
        (∀ u, 1 ≤ u → u < tr1.nodeAlloc →
          tr1.nodeParent u < u ∧
          tr1.nodeChar u < 2 ^ bChar ∧
          depth1 u = depth1 (tr1.nodeParent u) + 1 ∧
          depth1 u ≤ cTab ∧
          tr1.trieChild (tr1.nodeParent u) (tr1.nodeChar u) = u) ∧
        (∀ v ch, tr1.trieChild v ch ≠ 0 ↔
          (1 ≤ tr1.trieChild v ch ∧
           tr1.trieChild v ch < tr1.nodeAlloc ∧
           tr1.nodeParent (tr1.trieChild v ch) = v ∧
           tr1.nodeChar (tr1.trieChild v ch) = ch)) ∧
        (∀ u < tr1.nodeAlloc, tr1.nodeLeafItem u ≠ 0 →
          depth1 u = cTab ∧
          tr1.nodeLeafItem u ≤ tr1.itemAlloc ∧
          tr1.itemLeaf (tr1.nodeLeafItem u - 1) = u ∧
          ∃ k < 2 ^ (cTab * bChar), bufWalk bChar tr1.trieChild k cTab 0 0 = some u) := by
  intro rem
  induction rem with
  | zero =>
    intro off tr cur depth hsum halloc hzero hd0 hedge hiff hleaf hcur hdep
    dsimp only [bufEnsurePath]
    refine ⟨le_rfl, by omega, rfl, rfl, rfl, rfl, rfl, hzero, fun _ _ => rfl, hzero,
      fun _ _ _ => rfl, fun _ _ hne => absurd rfl hne,
      Or.inl ⟨by simp [bufWalk], rfl⟩, hcur, by simp [bufWalk],
      depth, hd0, by omega, hedge, hiff, hleaf⟩
  | succ rem ih =>
    intro off tr cur depth hsum halloc hzero hd0 hedge hiff hleaf hcur hdep
    dsimp only [bufEnsurePath]
    set ch := trieDigit bChar off rKey
    set nxt := tr.trieChild cur ch
    by_cases h0 : nxt = 0
    · simp only [h0, ↓reduceIte]
      set u := tr.nodeAlloc
      set child' := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
      set tr_step : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := child'
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      set depth_step := Function.update depth u (off + 1)
      have hu_ge1 : 1 ≤ u := halloc
      have hch_lt : ch < 2 ^ bChar := trieDigit_lt bChar off rKey
      have hmono_step : ∀ v c, tr.trieChild v c ≠ 0 → tr_step.trieChild v c = tr.trieChild v c := by
        intro v c hnz
        dsimp only [tr_step, child']
        by_cases hv : v = cur
        · subst hv
          have hc : c ≠ ch := by intro heq; subst heq; exact hnz h0
          simp [hc]
        · simp [hv]
      have hd0_step : depth_step 0 = 0 := by
        dsimp only [depth_step]
        rw [Function.update_of_ne (by omega)]
        exact hd0
      have hedge_step : ∀ w, 1 ≤ w → w < tr_step.nodeAlloc →
          tr_step.nodeParent w < w ∧
          tr_step.nodeChar w < 2 ^ bChar ∧
          depth_step w = depth_step (tr_step.nodeParent w) + 1 ∧
          depth_step w ≤ cTab ∧
          tr_step.trieChild (tr_step.nodeParent w) (tr_step.nodeChar w) = w := by
        intro w hw1 hw_lt
        dsimp only [tr_step] at hw_lt ⊢
        by_cases hw_eq : w = u
        · subst hw_eq
          simp only [Function.update_self]
          have hcur_ne : cur ≠ u := by omega
          have hd_cur : depth_step cur = off := by
            dsimp only [depth_step]; rw [Function.update_of_ne hcur_ne]; exact hdep
          refine ⟨hcur, hch_lt, ?_, ?_, ?_⟩
          · dsimp only [depth_step]
            rw [Function.update_self, Function.update_of_ne hcur_ne, hdep]
          · dsimp only [depth_step]; simp; omega
          · dsimp only [child']; simp
        · have hw_lt_u : w < u := by omega
          obtain ⟨hp_lt, hc_lt, hd_eq, hd_le, hchild_eq⟩ := hedge w hw1 hw_lt_u
          have hp_ne_u : tr.nodeParent w ≠ u := by omega
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne hw_eq]; exact hp_lt
          · rw [Function.update_of_ne hw_eq]; exact hc_lt
          · dsimp only [depth_step]
            rw [Function.update_of_ne hw_eq, Function.update_of_ne hw_eq,
              Function.update_of_ne hp_ne_u]
            exact hd_eq
          · dsimp only [depth_step]; rw [Function.update_of_ne hw_eq]; exact hd_le
          · rw [Function.update_of_ne hw_eq, Function.update_of_ne hw_eq]
            have hnz : tr.trieChild (tr.nodeParent w) (tr.nodeChar w) ≠ 0 := by omega
            change tr_step.trieChild (tr.nodeParent w) (tr.nodeChar w) = w
            rw [hmono_step _ _ hnz]
            exact hchild_eq
      have hiff_step : ∀ v c, tr_step.trieChild v c ≠ 0 ↔
          (1 ≤ tr_step.trieChild v c ∧
           tr_step.trieChild v c < tr_step.nodeAlloc ∧
           tr_step.nodeParent (tr_step.trieChild v c) = v ∧
           tr_step.nodeChar (tr_step.trieChild v c) = c) := by
        intro v c
        dsimp only [tr_step, child']
        by_cases hv : v = cur
        · subst hv
          by_cases hc : c = ch
          · subst hc
            simp only [Function.update_self]
            exact ⟨fun _ => ⟨hu_ge1, by omega, trivial, trivial⟩, fun _ => by omega⟩
          · simp only [Function.update_self, Function.update_of_ne hc]
            constructor
            · intro hnz
              obtain ⟨h1, h2, h3, h4⟩ := (hiff v c).mp hnz
              have hne_u : tr.trieChild v c ≠ u := by omega
              rw [Function.update_of_ne hne_u, Function.update_of_ne hne_u]
              exact ⟨h1, by omega, h3, h4⟩
            · intro ⟨h1, _, _, _⟩
              omega
        · simp only [Function.update_of_ne hv]
          constructor
          · intro hnz
            obtain ⟨h1, h2, h3, h4⟩ := (hiff v c).mp hnz
            have hne_u : tr.trieChild v c ≠ u := by omega
            rw [Function.update_of_ne hne_u, Function.update_of_ne hne_u]
            exact ⟨h1, by omega, h3, h4⟩
          · intro ⟨h1, _, _, _⟩
            omega
      have hzero_step : ∀ w, tr_step.nodeAlloc ≤ w → tr_step.nodeLeafItem w = 0 := by
        intro w hw_ge
        dsimp only [tr_step] at hw_ge ⊢
        rw [Function.update_of_ne (by omega)]
        exact hzero w (by omega)
      have hleaf_step : ∀ w < tr_step.nodeAlloc, tr_step.nodeLeafItem w ≠ 0 →
          depth_step w = cTab ∧
          tr_step.nodeLeafItem w ≤ tr_step.itemAlloc ∧
          tr_step.itemLeaf (tr_step.nodeLeafItem w - 1) = w ∧
          ∃ k < 2 ^ (cTab * bChar), bufWalk bChar tr_step.trieChild k cTab 0 0 = some w := by
        intro w hw_lt hnz
        dsimp only [tr_step] at hw_lt hnz ⊢
        have hw_ne_u : w ≠ u := by
          intro heq; subst heq; simp at hnz
        have hw_lt_u : w < u := by omega
        rw [Function.update_of_ne hw_ne_u] at hnz ⊢
        obtain ⟨hd_w, hle_item, hil_w, k, hk_lt, hwk⟩ := hleaf w hw_lt_u hnz
        dsimp only [depth_step]
        rw [Function.update_of_ne hw_ne_u]
        exact ⟨hd_w, hle_item, hil_w, k, hk_lt, bufWalk_mono hmono_step cTab 0 0 w k hwk⟩
      have hna_step : tr_step.nodeAlloc = u + 1 := rfl
      have hih := ih (off + 1) tr_step u depth_step (by omega) (by rw [hna_step]; omega)
        hzero_step hd0_step hedge_step hiff_step hleaf_step (by rw [hna_step]; omega)
        (by dsimp only [depth_step]; simp)
      change (let p := bufEnsurePath bChar rKey rem (off + 1) tr_step u; _)
      dsimp only
      rcases hih with ⟨ha_le, ha_ub, hia, hil, hib, hiloc, hact, hz1, hpres1, hz_ge1,
        hmono1, hnew1, hwalk_or, hleaf_lt, hw_rem, depth1, hd1_0, hd1_leaf,
        hedge1, hiff1, hleaf1⟩
      rw [hna_step] at ha_le ha_ub
      refine ⟨by omega, by omega,
        hia, hil, hib, hiloc, hact, hz1, ?_, ?_, ?_, ?_, ?_, hleaf_lt, ?_,
        depth1, hd1_0, hd1_leaf, hedge1, hiff1, hleaf1⟩
      · intro w hw_lt
        have hwu : w ≠ u := by omega
        rw [hpres1 w (by rw [hna_step]; omega)]
        dsimp only [tr_step]
        rw [Function.update_of_ne hwu]
      · intro w hw_ge
        by_cases hw_eq : w = u
        · subst hw_eq
          rw [hpres1 u (by rw [hna_step]; omega)]
          dsimp only [tr_step]; simp
        · exact hz_ge1 w (by rw [hna_step]; omega)
      · intro v c hnz
        rw [hmono1 v c (by rw [hmono_step v c hnz]; exact hnz)]
        exact hmono_step v c hnz
      · intro v c hne
        by_cases hne1 : (bufEnsurePath bChar rKey rem (off + 1) tr_step u).1.trieChild v c ≠
            tr_step.trieChild v c
        · have hb := hnew1 v c hne1
          rw [hna_step] at hb; omega
        · push Not at hne1
          rw [hne1] at hne ⊢
          by_cases hnz_old : tr.trieChild v c ≠ 0
          · exact absurd (hmono_step v c hnz_old) hne
          · push Not at hnz_old
            dsimp only [tr_step, child'] at hne ⊢
            by_cases hv : v = cur
            · subst hv
              by_cases hc : c = ch
              · subst hc; simp
              · simp [hc, hnz_old] at hne
            · simp [hv, hnz_old] at hne
      · refine Or.inr ⟨by simp [bufWalk, ch, nxt, h0], ?_⟩
        have hinc1 : ∀ v c,
            (bufEnsurePath bChar rKey rem (off + 1) tr_step u).1.trieChild v c ≠ 0 →
            v < (bufEnsurePath bChar rKey rem (off + 1) tr_step u).1.trieChild v c := by
          intro v c hnz
          obtain ⟨h1, h2, h3, _⟩ := (hiff1 v c).mp hnz
          have hp := (hedge1 _ h1 h2).1
          omega
        exact bufWalk_le_leaf hinc1 rem (off + 1) u _ rKey hw_rem
      · dsimp only [bufWalk]
        have hch_u : (bufEnsurePath bChar rKey rem (off + 1) tr_step u).1.trieChild cur ch = u := by
          have hstep_eq : tr_step.trieChild cur ch = u := by dsimp [tr_step, child']; simp
          rw [hmono1 cur ch (by omega), hstep_eq]
        rw [hch_u]
        simp only [show u ≠ 0 by omega, ↓reduceIte]
        exact hw_rem
    · simp only [h0, ↓reduceIte]
      obtain ⟨h1_ge, h1_lt, hp1, _⟩ := (hiff cur ch).mp h0
      have hd_nxt : depth nxt = off + 1 := by
        rw [(hedge nxt h1_ge h1_lt).2.2.1, hp1, hdep]
      have hih := ih (off + 1) tr nxt depth (by omega) halloc hzero hd0 hedge hiff hleaf
        h1_lt hd_nxt
      rcases hih with ⟨ha_le, ha_ub, hia, hil, hib, hiloc, hact, hz1, hpres1, hz_ge1,
        hmono1, hnew1, hwalk_or, hleaf_lt, hw_rem, depth1, hd1_0, hd1_leaf,
        hedge1, hiff1, hleaf1⟩
      refine ⟨ha_le, by omega, hia, hil, hib, hiloc, hact, hz1, hpres1, hz_ge1, hmono1, hnew1, ?_,
        hleaf_lt, ?_, depth1, hd1_0, hd1_leaf, hedge1, hiff1, hleaf1⟩
      · rcases hwalk_or with ⟨hw_ok, htr_eq⟩ | ⟨hw_none, hge_leaf⟩
        · exact Or.inl ⟨by simp [bufWalk, ch, nxt, h0, hw_ok], htr_eq⟩
        · exact Or.inr ⟨by simp [bufWalk, ch, nxt, h0, hw_none], hge_leaf⟩
      · dsimp only [bufWalk]
        have hch_nxt : (bufEnsurePath bChar rKey rem (off + 1) tr nxt).1.trieChild cur ch = nxt :=
          hmono1 cur ch h0
        rw [hch_nxt]
        simp only [h0, ↓reduceIte]
        exact hw_rem

/-- Exact specification of `bufInsert`:
* Preserves `ValidBufTrie` for `Function.update mapFn rKey (some (b, loc))`;
* Allocates at most `cTab` trie nodes and at most `1` item slot;
* Sets `bufEverPresent` at `rKey` to `true` and preserves `bufEverPresent` on all other keys
  `< 2 ^ (cTab * bChar)`;
* Whenever `bufEverPresent cTab bChar tr rKey = true` (including re-insertion of a previously
  deleted key in the same epoch!), leaves `nodeAlloc` and `itemAlloc` completely unchanged;
* When `mapFn rKey ≠ none` (updating an active item's `(b, loc)` in place), also leaves inactive
  scan slots (`bufCheckSlot _ id = none`) unchanged. -/
theorem ValidBufTrie.insert_spec {cTab bChar rKey b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) :
    let tr' := bufInsert cTab bChar tr rKey b loc
    ValidBufTrie cTab bChar tr' (Function.update mapFn rKey (some (b, loc))) ∧
    tr.nodeAlloc ≤ tr'.nodeAlloc ∧
    tr'.nodeAlloc ≤ tr.nodeAlloc + cTab ∧
    tr.itemAlloc ≤ tr'.itemAlloc ∧
    tr'.itemAlloc ≤ tr.itemAlloc + 1 ∧
    (∀ k < 2 ^ (cTab * bChar),
      bufEverPresent cTab bChar tr' k =
        if k = rKey then true else bufEverPresent cTab bChar tr k) ∧
    (bufEverPresent cTab bChar tr rKey = true →
      tr'.nodeAlloc = tr.nodeAlloc ∧ tr'.itemAlloc = tr.itemAlloc) ∧
    (mapFn rKey ≠ none →
      tr'.nodeAlloc = tr.nodeAlloc ∧
      tr'.itemAlloc = tr.itemAlloc ∧
      ∀ id, bufCheckSlot tr id = none → bufCheckSlot tr' id = none) := by
  obtain ⟨halloc, hzero, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  dsimp only [bufInsert]
  have hens := bufEnsurePath_props (cTab := cTab) (bChar := bChar) (rKey := rKey)
    cTab 0 tr 0 depth (Nat.zero_add cTab) halloc hzero hd0 hedge hiff hleaf halloc hd0
  dsimp only at hens
  generalize bufEnsurePath bChar rKey cTab 0 tr 0 = p at hens ⊢
  rcases p with ⟨tr1, leaf⟩
  dsimp only at hens ⊢
  rcases hens with ⟨ha_le, ha_ub, hia, hil, hib, hiloc, hact1, hz1, hpres1, hz_ge1,
    hmono1, hnew1, hwalk_or, hleaf_lt, hw_rKey, depth1, hd1_0, hd1_leaf,
    hedge1, hiff1, hleaf1⟩
  have hp_edge1 : ∀ u, 1 ≤ u → u < tr1.nodeAlloc → depth1 u = depth1 (tr1.nodeParent u) + 1 :=
    fun u h1 h2 => (hedge1 u h1 h2).2.2.1
  have hinc1 : ∀ v c, tr1.trieChild v c ≠ 0 → v < tr1.trieChild v c := by
    intro v c hnz
    obtain ⟨h1, h2, h3, _⟩ := (hiff1 v c).mp hnz
    have hp := (hedge1 _ h1 h2).1
    omega
  by_cases hid1 : tr1.nodeLeafItem leaf = 0
  · simp only [hid1, ↓reduceIte]
    have hever_false : bufEverPresent cTab bChar tr rKey = false := by
      rcases hwalk_or with ⟨hw_old, htr_eq⟩ | ⟨hw_none, _⟩
      · have hli_old : tr.nodeLeafItem leaf = 0 := by rw [← htr_eq]; exact hid1
        simp [bufEverPresent, hw_old, hli_old]
      · simp [bufEverPresent, hw_none]
    have hmap_none : mapFn rKey = none := by
      rw [hmap rKey hk]
      rcases hwalk_or with ⟨hw_old, htr_eq⟩ | ⟨hw_none, _⟩
      · have hli_old : tr.nodeLeafItem leaf = 0 := by rw [← htr_eq]; exact hid1
        simp [bufLookup, hw_old, hli_old]
      · simp [bufLookup, hw_none]
    refine ⟨?_, ha_le, ha_ub, by omega, by omega, ?_, ?_,
      fun hne => absurd hmap_none hne⟩
    · refine ⟨by dsimp only; omega, ?_, ?_, ?_, depth1, hd1_0, hedge1, hiff1, ?_⟩
      · intro u hu_ge
        dsimp only at hu_ge ⊢
        rw [Function.update_of_ne (by omega)]
        exact hz1 u hu_ge
      · intro k hk_ge
        rw [Function.update_of_ne (by omega)]
        exact hout k hk_ge
      · intro k hk_lt
        by_cases heq : k = rKey
        · subst heq
          simp [bufLookup, hw_rKey]
        · rw [Function.update_of_ne heq, hmap k hk_lt]
          dsimp only [bufLookup]
          cases hwk_old : bufWalk bChar tr.trieChild k cTab 0 0 with
          | some leaf_k =>
            have hwk1 := bufWalk_mono hmono1 cTab 0 0 leaf_k k hwk_old
            rw [hwk1]
            have hne_leaf : leaf_k ≠ leaf := by
              intro hl_eq; subst hl_eq
              have hwp := bufWalk_props hp_edge1 hiff1 cTab 0 0 leaf_k rKey (by omega) hd1_0 hw_rKey
              have hdig := (hwp.2.2 0 k (by omega) hd1_0 hwk1).2
              exact heq (eq_of_forall_trieDigit_eq hk_lt hk
                (fun d hd => by
                  have h := hdig d hd
                  simpa only [Nat.zero_add] using h.symm))
            have hlk_lt_old : leaf_k < tr.nodeAlloc :=
              (bufWalk_props (fun u h1 h2 => (hedge u h1 h2).2.2.1) hiff
                cTab 0 0 leaf_k k halloc hd0 hwk_old).1
            simp only [Function.update_of_ne hne_leaf, hpres1 leaf_k hlk_lt_old, hact1]
            by_cases hcond_k : tr.nodeLeafItem leaf_k = 0 ∨ tr.nodeActive leaf_k = 0
            · simp [hcond_k]
            · simp only [hcond_k, ↓reduceIte]
              push Not at hcond_k
              have hle_ia := (hleaf leaf_k hlk_lt_old hcond_k.1).2.1
              have hid_ne : tr.nodeLeafItem leaf_k - 1 ≠ tr1.itemAlloc := by omega
              simp only [Function.update_of_ne hid_ne, hib, hiloc]
          | none =>
            cases hwk1 : bufWalk bChar tr1.trieChild k cTab 0 0 with
            | none => rfl
            | some leaf_k =>
              have hne_leaf : leaf_k ≠ leaf := by
                intro hl_eq; subst hl_eq
                have hwp := bufWalk_props hp_edge1 hiff1 cTab 0 0 leaf_k rKey
                  (by omega) hd1_0 hw_rKey
                have hdig := (hwp.2.2 0 k (by omega) hd1_0 hwk1).2
                exact heq (eq_of_forall_trieDigit_eq hk_lt hk
                  (fun d hd => by
                    have h := hdig d hd
                    simpa only [Nat.zero_add] using h.symm))
              have hge_old : tr.nodeAlloc ≤ leaf_k :=
                bufWalk_ge_of_none hnew1 hinc1 cTab 0 0 leaf_k k hwk_old hwk1
              simp [Function.update_of_ne hne_leaf, hz_ge1 leaf_k hge_old]
      · intro u hu_lt hnz'
        dsimp only at hu_lt hnz' ⊢
        by_cases hu_eq : u = leaf
        · subst hu_eq
          simp only [Function.update_self, Nat.add_sub_cancel]
          exact ⟨hd1_leaf, le_rfl, trivial, rKey, hk, hw_rKey⟩
        · rw [Function.update_of_ne hu_eq] at hnz' ⊢
          obtain ⟨hd_u, hle_u, hil_u, k, hk_lt, hwk⟩ := hleaf1 u hu_lt hnz'
          have hid_ne : tr1.nodeLeafItem u - 1 ≠ tr1.itemAlloc := by omega
          refine ⟨hd_u, by omega, ?_, k, hk_lt, hwk⟩
          rw [Function.update_of_ne hid_ne]
          exact hil_u
    · intro k hk_lt
      by_cases heq : k = rKey
      · subst heq
        simp [bufEverPresent, hw_rKey]
      · simp only [heq, ↓reduceIte]
        dsimp only [bufEverPresent]
        cases hwk_old : bufWalk bChar tr.trieChild k cTab 0 0 with
        | some leaf_k =>
          have hwk1 := bufWalk_mono hmono1 cTab 0 0 leaf_k k hwk_old
          rw [hwk1]
          have hne_leaf : leaf_k ≠ leaf := by
            intro hl_eq; subst hl_eq
            have hwp := bufWalk_props hp_edge1 hiff1 cTab 0 0 leaf_k rKey (by omega) hd1_0 hw_rKey
            have hdig := (hwp.2.2 0 k (by omega) hd1_0 hwk1).2
            exact heq (eq_of_forall_trieDigit_eq hk_lt hk
              (fun d hd => by
                have h := hdig d hd
                simpa only [Nat.zero_add] using h.symm))
          have hlk_lt_old : leaf_k < tr.nodeAlloc :=
            (bufWalk_props (fun u h1 h2 => (hedge u h1 h2).2.2.1) hiff
              cTab 0 0 leaf_k k halloc hd0 hwk_old).1
          simp only [Function.update_of_ne hne_leaf, hpres1 leaf_k hlk_lt_old]
        | none =>
          cases hwk1 : bufWalk bChar tr1.trieChild k cTab 0 0 with
          | none => rfl
          | some leaf_k =>
            have hne_leaf : leaf_k ≠ leaf := by
              intro hl_eq; subst hl_eq
              have hwp := bufWalk_props hp_edge1 hiff1 cTab 0 0 leaf_k rKey (by omega) hd1_0 hw_rKey
              have hdig := (hwp.2.2 0 k (by omega) hd1_0 hwk1).2
              exact heq (eq_of_forall_trieDigit_eq hk_lt hk
                (fun d hd => by
                  have h := hdig d hd
                  simpa only [Nat.zero_add] using h.symm))
            have hge_old : tr.nodeAlloc ≤ leaf_k :=
              bufWalk_ge_of_none hnew1 hinc1 cTab 0 0 leaf_k k hwk_old hwk1
            simp [Function.update_of_ne hne_leaf, hz_ge1 leaf_k hge_old]
    · intro hev
      rw [hever_false] at hev
      cases hev
  · simp only [hid1, ↓reduceIte]
    have htr1_eq : tr1 = tr := by
      rcases hwalk_or with ⟨_, htr_eq⟩ | ⟨_, hge_leaf⟩
      · exact htr_eq
      · exact absurd (hz_ge1 leaf hge_leaf) hid1
    obtain ⟨_, hle_id1, hil_leaf, _⟩ := hleaf1 leaf hleaf_lt hid1
    refine ⟨?_, ha_le, ha_ub, by omega, by omega, ?_,
      fun _ => ⟨by rw [htr1_eq], hia⟩, ?_⟩
    · refine ⟨by dsimp only; omega, hz1, ?_, ?_, depth1, hd1_0, hedge1, hiff1, ?_⟩
      · intro k hk_ge
        rw [Function.update_of_ne (by omega)]
        exact hout k hk_ge
      · intro k hk_lt
        by_cases heq : k = rKey
        · subst heq
          simp [bufLookup, hw_rKey, hid1]
        · rw [Function.update_of_ne heq, hmap k hk_lt, ← htr1_eq]
          dsimp only [bufLookup]
          cases hwk1 : bufWalk bChar tr1.trieChild k cTab 0 0 with
          | none => rfl
          | some leaf_k =>
            have hne_leaf : leaf_k ≠ leaf := by
              intro hl_eq; subst hl_eq
              have hwp := bufWalk_props hp_edge1 hiff1 cTab 0 0 leaf_k rKey
                (by omega) hd1_0 hw_rKey
              have hdig := (hwp.2.2 0 k (by omega) hd1_0 hwk1).2
              exact heq (eq_of_forall_trieDigit_eq hk_lt hk
                (fun d hd => by
                  have h := hdig d hd
                  simpa only [Nat.zero_add] using h.symm))
            dsimp only
            simp only [Function.update_of_ne hne_leaf]
            by_cases hcond_k : tr1.nodeLeafItem leaf_k = 0 ∨ tr1.nodeActive leaf_k = 0
            · simp [hcond_k]
            · simp only [hcond_k, ↓reduceIte]
              push Not at hcond_k
              have hlk_lt : leaf_k < tr1.nodeAlloc :=
                (bufWalk_props hp_edge1 hiff1 cTab 0 0 leaf_k k (by omega) hd1_0 hwk1).1
              have hil_k := (hleaf1 leaf_k hlk_lt hcond_k.1).2.2.1
              have hid_ne : tr1.nodeLeafItem leaf_k - 1 ≠ tr1.nodeLeafItem leaf - 1 := by
                intro heq_id
                apply hne_leaf
                rw [← hil_k, heq_id, hil_leaf]
              simp only [Function.update_of_ne hid_ne]
      · intro u hu_lt hnz'
        dsimp only at hu_lt hnz' ⊢
        exact hleaf1 u hu_lt hnz'
    · intro k hk_lt
      by_cases heq : k = rKey
      · subst heq
        simp [bufEverPresent, hw_rKey, hid1]
      · simp only [heq, ↓reduceIte]
        rw [← htr1_eq]
        rfl
    · intro hmap_ne
      have hact_nz : tr1.nodeActive leaf ≠ 0 := by
        intro hact0
        apply hmap_ne
        rw [hmap rKey hk, ← htr1_eq]
        simp [bufLookup, hw_rKey, hact0]
      refine ⟨by rw [htr1_eq], hia, ?_⟩
      intro id hnone
      rw [← htr1_eq] at hnone
      dsimp only [bufCheckSlot] at hnone ⊢
      by_cases hid : id < tr1.itemAlloc
      · simp only [hid, ↓reduceIte] at hnone ⊢
        by_cases hleaf_eq : tr1.itemLeaf id = leaf
        · rw [hleaf_eq] at hnone ⊢
          simp only [Function.update_self]
          by_cases hli_eq : tr1.nodeLeafItem leaf = id + 1
          · simp [hli_eq, hact_nz] at hnone
          · simp [hli_eq]
        · simp only [Function.update_of_ne hleaf_eq]
          split_ifs at hnone ⊢
          exact rfl
      · simp [hid]

/-- Forward scan specification: if `bufCheckSlot tr id = some (b, loc)`, then `id < tr.itemAlloc`
and some active key `k < 2 ^ (cTab * bChar)` maps to `(b, loc)` in `mapFn` (with leaf
`tr.itemLeaf id`). -/
theorem ValidBufTrie.checkSlot_some {cTab bChar id b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hchk : bufCheckSlot tr id = some (b, loc)) :
    id < tr.itemAlloc ∧
    ∃ k < 2 ^ (cTab * bChar),
      bufWalk bChar tr.trieChild k cTab 0 0 = some (tr.itemLeaf id) ∧
      mapFn k = some (b, loc) := by
  obtain ⟨_, hzero, _, hmap, _, _, _, _, hleaf⟩ := hv
  dsimp only [bufCheckSlot] at hchk
  by_cases hid : id < tr.itemAlloc
  · simp only [hid, ↓reduceIte] at hchk
    set leaf := tr.itemLeaf id
    by_cases hcond : tr.nodeLeafItem leaf = id + 1 ∧ tr.nodeActive leaf ≠ 0
    · obtain ⟨hli, hact⟩ := hcond
      simp only [hli, hact, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at hchk
      have hleaf_lt : leaf < tr.nodeAlloc := by
        by_contra hge
        have hz := hzero leaf (Nat.not_lt.mp hge)
        omega
      obtain ⟨_, _, _, k, hk_lt, hwk⟩ := hleaf leaf hleaf_lt (by omega)
      refine ⟨hid, k, hk_lt, hwk, ?_⟩
      rw [hmap k hk_lt]
      simp [bufLookup, hwk, hli, hact, hchk.1, hchk.2]
    · simp [hcond] at hchk
  · simp [hid] at hchk

/-- Converse scan specification: every active key `mapFn k = some (b, loc)` has an active scan slot
`id < tr.itemAlloc` with `bufCheckSlot tr id = some (b, loc)`. In particular, once
`∀ id < tr.itemAlloc, bufCheckSlot tr id = none`, `mapFn` is identically `none`. -/
theorem ValidBufTrie.exists_checkSlot_of_map_some {cTab bChar k b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hmk : mapFn k = some (b, loc)) :
    ∃ id < tr.itemAlloc, bufCheckSlot tr id = some (b, loc) := by
  obtain ⟨halloc, _, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  have hk_lt : k < 2 ^ (cTab * bChar) := by
    by_contra hge
    rw [hout k (Nat.not_lt.mp hge)] at hmk
    simp at hmk
  rw [hmap k hk_lt] at hmk
  dsimp only [bufLookup] at hmk
  cases hwk : bufWalk bChar tr.trieChild k cTab 0 0 with
  | none => simp [hwk] at hmk
  | some leaf =>
    rw [hwk] at hmk
    dsimp only at hmk
    by_cases hcond : tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0
    · simp [hcond] at hmk
    · simp only [hcond, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hmk
      push Not at hcond
      obtain ⟨hli, hact⟩ := hcond
      have hleaf_lt : leaf < tr.nodeAlloc :=
        (bufWalk_props (fun u h1 h2 => (hedge u h1 h2).2.2.1) hiff cTab 0 0 leaf k halloc hd0 hwk).1
      obtain ⟨_, hle_ia, hil_eq, _⟩ := hleaf leaf hleaf_lt hli
      set id := tr.nodeLeafItem leaf - 1
      have hid_lt : id < tr.itemAlloc := by omega
      refine ⟨id, hid_lt, ?_⟩
      dsimp only [bufCheckSlot]
      have hli_eq : tr.nodeLeafItem (tr.itemLeaf id) = id + 1 := by
        rw [hil_eq]
        omega
      have hact_eq : tr.nodeActive (tr.itemLeaf id) ≠ 0 := by
        rwa [hil_eq]
      simp [hid_lt, hli_eq, hact_eq, hmk.1, hmk.2]

/-! ## Section 4: Incremental `O(1)`-per-step cleanup (`ClearableBufTrie`, `clearSteps_spec`) -/

/-- Structural parent-log invariant maintained across intermediate `bufClearOne` steps while
re-zeroing `BufOld` in the second half of an epoch. -/
@[expose] def ClearableBufTrie (tr : BufTrie) : Prop :=
  1 ≤ tr.nodeAlloc ∧
  (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) ∧
  (∀ u, 1 ≤ u → u < tr.nodeAlloc →
    tr.nodeParent u < u ∧ tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u) ∧
  (∀ v ch, tr.trieChild v ch ≠ 0 →
    1 ≤ tr.trieChild v ch ∧ tr.trieChild v ch < tr.nodeAlloc ∧
    tr.nodeParent (tr.trieChild v ch) = v ∧ tr.nodeChar (tr.trieChild v ch) = ch)

/-- Every `ValidBufTrie` satisfies `ClearableBufTrie`. -/
theorem ValidBufTrie.toClearable {cTab bChar : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn) :
    ClearableBufTrie tr := by
  obtain ⟨halloc, hzero, _, _, _, _, hedge, hiff, _⟩ := hv
  refine ⟨halloc, hzero, fun u h1 h2 => ?_, fun v ch hnz => (hiff v ch).mp hnz⟩
  exact ⟨(hedge u h1 h2).1, (hedge u h1 h2).2.2.2.2⟩

/-- One step of `bufClearOne` preserves `ClearableBufTrie` and decrements `nodeAlloc` toward `1`. -/
theorem ClearableBufTrie.clearOne_step {tr : BufTrie} (hc : ClearableBufTrie tr) :
    ClearableBufTrie (bufClearOne tr) ∧
    (bufClearOne tr).nodeAlloc = max 1 (tr.nodeAlloc - 1) := by
  obtain ⟨halloc, hzero, hedge, hchild⟩ := hc
  dsimp only [bufClearOne]
  by_cases hgt : 1 < tr.nodeAlloc
  · simp only [hgt, ↓reduceIte]
    set u := tr.nodeAlloc - 1
    set p := tr.nodeParent u
    set ch := tr.nodeChar u
    refine ⟨⟨by dsimp only; omega, ?_, ?_, ?_⟩, by omega⟩
    · intro w hw_ge
      dsimp only at hw_ge ⊢
      by_cases hw_eq : w = u
      · subst hw_eq; simp
      · rw [Function.update_of_ne hw_eq]
        exact hzero w (by omega)
    · intro w hw1 hw_lt
      dsimp only at hw_lt ⊢
      obtain ⟨hp_w, hc_w⟩ := hedge w hw1 (by omega)
      refine ⟨hp_w, ?_⟩
      by_cases hvp : tr.nodeParent w = p
      · by_cases hvc : tr.nodeChar w = ch
        · have hu_eq : tr.trieChild p ch = u := (hedge u (by omega) (by omega)).2
          have hw_eq_u : w = u := by rw [← hc_w, hvp, hvc, hu_eq]
          omega
        · rw [hvp] at hc_w ⊢
          simp only [Function.update_self, Function.update_of_ne hvc, hc_w]
      · simp [hvp, hc_w]
    · intro v c hnz
      dsimp only at hnz ⊢
      by_cases hv : v = p
      · subst hv
        by_cases hcc : c = ch
        · subst hcc; simp at hnz
        · simp only [Function.update_self, Function.update_of_ne hcc] at hnz ⊢
          obtain ⟨h1, h2, h3, h4⟩ := hchild p c hnz
          have hne_u : tr.trieChild p c ≠ u := by
            intro heq
            apply hcc
            rw [← h4, heq]
          exact ⟨h1, by omega, h3, h4⟩
      · simp only [Function.update_of_ne hv] at hnz ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hchild v c hnz
        have hne_u : tr.trieChild v c ≠ u := by
          intro heq
          apply hv
          rw [← h3, heq]
        exact ⟨h1, by omega, h3, h4⟩
  · simp only [hgt, ↓reduceIte]
    have ha1 : tr.nodeAlloc = 1 := by omega
    refine ⟨⟨le_rfl, ?_, fun u h1 h2 => by dsimp only at h2; omega, ?_⟩, by omega⟩
    · intro w hw_ge
      dsimp only at hw_ge ⊢
      rw [Function.update_of_ne (by omega)]
      exact hzero w (by omega)
    · intro v c hnz
      dsimp only at hnz ⊢
      obtain ⟨h1, h2, _⟩ := hchild v c hnz
      omega

/-- When `ClearableBufTrie tr` holds with `tr.nodeAlloc = 1`, one final `bufClearOne` step yields a
completely clean `ValidBufTrie cTab bChar _ (fun _ => none)` with `nodeAlloc = 1` and
`itemAlloc = 0`. -/
theorem ClearableBufTrie.clearOne_of_one (cTab bChar : ℕ) {tr : BufTrie}
    (hc : ClearableBufTrie tr) (ha1 : tr.nodeAlloc = 1) :
    let tr' := bufClearOne tr
    ValidBufTrie cTab bChar tr' (fun _ => none) ∧
    tr'.nodeAlloc = 1 ∧
    tr'.itemAlloc = 0 := by
  obtain ⟨_, hzero, _, hchild⟩ := hc
  have hchild0 : ∀ v c, tr.trieChild v c = 0 := by
    intro v c
    by_contra hnz
    obtain ⟨h1, h2, _⟩ := hchild v c hnz
    omega
  have hgt : ¬ (1 < tr.nodeAlloc) := by omega
  dsimp only [bufClearOne]
  simp only [hgt, ↓reduceIte]
  have hz_all : ∀ w, Function.update tr.nodeLeafItem 0 0 w = 0 := by
    intro w
    by_cases hw0 : w = 0
    · subst hw0; simp
    · rw [Function.update_of_ne hw0]
      exact hzero w (by omega)
  refine ⟨⟨le_rfl, fun w _ => hz_all w, fun _ _ => rfl, ?_, fun _ => 0, rfl,
    fun _ h1 h2 => by dsimp only at h2; omega, ?_, ?_⟩, trivial, trivial⟩
  · intro k _
    cases cTab with
    | zero => simp [bufLookup, bufWalk]
    | succ c => simp [bufLookup, bufWalk, hchild0]
  · intro v ch
    dsimp only
    simp [hchild0 v ch]
  · intro u _ hnz
    dsimp only at hnz
    exact absurd (hz_all u) hnz

/-- Executing `k ≥ tr.nodeAlloc` elementary `bufClearOne` steps on any `ClearableBufTrie` produces a
clean empty `ValidBufTrie` (`mapFn = fun _ => none`, `nodeAlloc = 1`, `itemAlloc = 0`). -/
theorem ClearableBufTrie.clearSteps_spec (cTab bChar : ℕ) :
    ∀ (k : ℕ) {tr : BufTrie},
      ClearableBufTrie tr →
      tr.nodeAlloc ≤ k →
      let tr' := bufClearSteps k tr
      ValidBufTrie cTab bChar tr' (fun _ => none) ∧
      tr'.nodeAlloc = 1 ∧
      tr'.itemAlloc = 0 := by
  intro k
  induction k with
  | zero =>
    intro tr hc hle
    have := hc.1
    omega
  | succ k ih =>
    intro tr hc hle
    dsimp only [bufClearSteps]
    by_cases ha1 : tr.nodeAlloc = 1
    · obtain ⟨hv1, ha1', hi0'⟩ := hc.clearOne_of_one cTab bChar ha1
      cases k with
      | zero => exact ⟨hv1, ha1', hi0'⟩
      | succ k' =>
        exact ih hv1.toClearable (by omega)
    · obtain ⟨hc1, ha_nxt⟩ := hc.clearOne_step
      have hgt1 : 1 < tr.nodeAlloc := by have := hc.1; omega
      have hle_nxt : (bufClearOne tr).nodeAlloc ≤ k := by omega
      exact ih hc1 hle_nxt

/-- Corollary for `ValidBufTrie`: `bufClearSteps k tr` (for `tr.nodeAlloc ≤ k`) yields a clean
empty `ValidBufTrie` with `nodeAlloc = 1` and `itemAlloc = 0`. -/
theorem ValidBufTrie.clearSteps_spec {cTab bChar k : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hle : tr.nodeAlloc ≤ k) :
    let tr' := bufClearSteps k tr
    ValidBufTrie cTab bChar tr' (fun _ => none) ∧
    tr'.nodeAlloc = 1 ∧
    tr'.itemAlloc = 0 :=
  hv.toClearable.clearSteps_spec cTab bChar k hle

/-- Whenever `ValidBufTrie` holds with `tr.itemAlloc = 0`, `bufEverPresent` is identically
`false`. -/
theorem ValidBufTrie.everPresent_eq_false_of_itemAlloc_zero {cTab bChar : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hia0 : tr.itemAlloc = 0) (k : ℕ) :
    bufEverPresent cTab bChar tr k = false := by
  obtain ⟨_, hzero, _, _, _, _, _, _, hleaf⟩ := hv
  dsimp only [bufEverPresent]
  cases hw : bufWalk bChar tr.trieChild k cTab 0 0 with
  | none => rfl
  | some leaf =>
    have hli0 : tr.nodeLeafItem leaf = 0 := by
      by_cases hlt : leaf < tr.nodeAlloc
      · by_contra hnz
        have hle := (hleaf leaf hlt hnz).2.1
        omega
      · exact hzero leaf (Nat.not_lt.mp hlt)
    simp [hli0]

/-- `bufInsert` preserves the linear bound `nodeAlloc ≤ 1 + cTab * itemAlloc` across all
insertions, overwrites, and reactivations. -/
theorem ValidBufTrie.insert_nodeAlloc_le {cTab bChar rKey b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) (hlin : tr.nodeAlloc ≤ 1 + cTab * tr.itemAlloc) :
    let tr' := bufInsert cTab bChar tr rKey b loc
    tr'.nodeAlloc ≤ 1 + cTab * tr'.itemAlloc := by
  dsimp only
  by_cases hev : bufEverPresent cTab bChar tr rKey = true
  · obtain ⟨ha_eq, hia_eq⟩ := (hv.insert_spec (b := b) (loc := loc) hk).2.2.2.2.2.2.1 hev
    rw [ha_eq, hia_eq]
    exact hlin
  · obtain ⟨halloc, hzero, _, _, depth, hd0, hedge, hiff, hleaf⟩ := hv
    have hens := bufEnsurePath_props (cTab := cTab) (bChar := bChar) (rKey := rKey)
      cTab 0 tr 0 depth (Nat.zero_add cTab) halloc hzero hd0 hedge hiff hleaf halloc hd0
    dsimp only [bufInsert]
    generalize bufEnsurePath bChar rKey cTab 0 tr 0 = p at hens ⊢
    rcases p with ⟨tr1, leaf⟩
    dsimp only at hens ⊢
    rcases hens with ⟨_, ha_ub, hia, _, _, _, _, _, _, hz_ge1, _, _, hwalk_or, _, _, _⟩
    by_cases hid1 : tr1.nodeLeafItem leaf = 0
    · simp only [hid1, ↓reduceIte]
      rw [hia, Nat.mul_add, Nat.mul_one]
      omega
    · exfalso
      apply hev
      rcases hwalk_or with ⟨hw_old, htr_eq⟩ | ⟨_, hge_leaf⟩
      · rw [← htr_eq] at hw_old
        have htr_eq' : tr = tr1 := htr_eq.symm
        subst htr_eq'
        simp [bufEverPresent, hw_old, hid1]
      · exact absurd (hz_ge1 leaf hge_leaf) hid1

/-- Any slot active after `bufDelete` was already active at the exact same `(b', loc')` before
`bufDelete`. -/
theorem bufDelete_checkSlot_some {cTab bChar rKey id b' loc' : ℕ} {tr : BufTrie}
    (h : bufCheckSlot (bufDelete cTab bChar tr rKey) id = some (b', loc')) :
    bufCheckSlot tr id = some (b', loc') := by
  dsimp only [bufDelete] at h
  cases hw : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => rw [hw] at h; exact h
  | some leaf =>
    rw [hw] at h
    dsimp only at h
    split_ifs at h with hc
    · exact h
    · dsimp only [bufCheckSlot] at h ⊢
      by_cases hid : id < tr.itemAlloc
      · simp only [hid, ↓reduceIte] at h ⊢
        by_cases hleaf : tr.itemLeaf id = leaf
        · simp [hleaf] at h
        · simp only [Function.update_of_ne hleaf] at h
          exact h
      · simp [hid] at h

/-- Relocating an already-active key `rKey` (`mapFn rKey = some (b, loc_old)`) within the same
bucket `b` (`bufInsert cTab bChar tr rKey b loc_new`) preserves active bucket membership at every
scan slot `id`. -/
theorem ValidBufTrie.insert_same_bucket_checkSlot_some {cTab bChar rKey b loc_old loc_new id b'
    loc' : ℕ} {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie cTab bChar tr mapFn) (hk : rKey < 2 ^ (cTab * bChar))
    (hm : mapFn rKey = some (b, loc_old))
    (hchk : bufCheckSlot (bufInsert cTab bChar tr rKey b loc_new) id = some (b', loc')) :
    ∃ loc₀, bufCheckSlot tr id = some (b', loc₀) := by
  obtain ⟨halloc, hzero, _, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  have hens := bufEnsurePath_props (cTab := cTab) (bChar := bChar) (rKey := rKey)
    cTab 0 tr 0 depth (Nat.zero_add cTab) halloc hzero hd0 hedge hiff hleaf halloc hd0
  dsimp only [bufInsert] at hchk
  generalize bufEnsurePath bChar rKey cTab 0 tr 0 = p at hens hchk
  rcases p with ⟨tr1, leaf⟩
  dsimp only at hens hchk
  rcases hens with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hwalk_or, hleaf_lt, _, _, _, _, _, _, _⟩
  have hlk := (hmap rKey hk).symm.trans hm
  dsimp only [bufLookup] at hlk
  rcases hwalk_or with ⟨hw_old, rfl⟩ | ⟨hw_none, _⟩
  · rw [hw_old] at hlk
    dsimp only at hlk
    by_cases hcond : tr1.nodeLeafItem leaf = 0 ∨ tr1.nodeActive leaf = 0
    · simp [hcond] at hlk
    · simp only [hcond, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hlk
      push Not at hcond
      obtain ⟨hli_nz, hact_nz⟩ := hcond
      simp only [hli_nz, ↓reduceIte] at hchk
      obtain ⟨_, hle_ia, hil_leaf, _⟩ := hleaf leaf hleaf_lt hli_nz
      dsimp only [bufCheckSlot] at hchk ⊢
      by_cases hid : id < tr1.itemAlloc
      · simp only [hid, ↓reduceIte] at hchk ⊢
        by_cases hid_eq : id = tr1.nodeLeafItem leaf - 1
        · subst hid_eq
          have hb_eq : b = b' := by
            simp only [hil_leaf, Function.update_self,
              show tr1.nodeLeafItem leaf - 1 + 1 = tr1.nodeLeafItem leaf by omega] at hchk
            simp only [ne_eq, one_ne_zero, not_false_eq_true, and_self, ↓reduceIte,
              Option.some.injEq, Prod.mk.injEq] at hchk
            exact hchk.1
          subst hb_eq
          refine ⟨loc_old, ?_⟩
          simp [hil_leaf, show tr1.nodeLeafItem leaf - 1 + 1 = tr1.nodeLeafItem leaf by omega,
            hact_nz, hlk.1, hlk.2]
        · simp only [Function.update_of_ne hid_eq] at hchk
          by_cases hleaf_id : tr1.itemLeaf id = leaf
          · have hne1 : tr1.nodeLeafItem leaf ≠ id + 1 := by omega
            simp [hleaf_id, hne1] at hchk
          · simp only [Function.update_of_ne hleaf_id] at hchk
            exact ⟨loc', hchk⟩
      · simp [hid] at hchk
  · rw [hw_none] at hlk; simp at hlk

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
