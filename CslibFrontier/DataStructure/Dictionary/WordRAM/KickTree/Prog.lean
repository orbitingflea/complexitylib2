/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.Tactic.Realize
public import CslibFrontier.DataStructure.Dictionary.WordRAM.KickTree.Layout
public import CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm
public import CslibFrontier.DataStructure.Dictionary.KickTree.Metadata
public import CslibFrontier.DataStructure.Dictionary.KickTree.Facility
public import CslibFrontier.DataStructure.BallsToSlots.KickTree

/-!
# Word-RAM `Memory.Prog` Subroutines and Realization for STOC 2022 KickTree

This module formalizes the core Word-RAM `Memory.Prog` subroutines and their width-free
`Realizes .exact` (`¬ReadsWidth`) realization certificates for the STOC 2022 `k`-kick tree
dynamic dictionary ([BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`):

1. **Initialization (`initProg`)**: initializes seed words at `offSeeds` and zeroes metadata
   roots at `offFreeSlot`.
2. **Query Routing (`queryProg`)**: queries cubby metadata at `offFacility` and quotient matching
   at `offQuot`, retrieving stored values from `offVal` when present.
3. **Bounded Kick Loop (`kickStepProg`, `kickLoopProg`)**: executes the bounded switching sequence
   using `Realization.iterate`, bounded by `kickLimit ≤ k + 1` steps per Lemma 1 / Theorem 2.
4. **Deletion via Tail Replacement (`deleteProg`)**: implements non-hash tail replacement
   (Section 5.2 / `Facility.tailReplace`) and free-slot reclamation.

## Source attribution

* [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 3.1 (printed pp. 8–10 / PDF pp. 9–11): $k$-kick tree structure and switching paths.
  - Section 5.1 (printed pp. 27–29 / PDF pp. 28–30): free-slot tree and cubby routing.
  - Section 5.2 (printed pp. 30–32 / PDF pp. 31–33): non-hash tail replacement on deletion.
  - Section 5.3 (printed pp. 34–36 / PDF pp. 33–35): quotienting and word-space layout.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.initProg`: initialize dictionary state.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.queryProg`: query routing with cubby check.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.kickStepProg`: single kick displacement step.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.kickLoopProg`: bounded kick loop via `iterate`.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.deleteProg`: deletion via tail replacement.

## Main results

* `realize_init`, `not_readsWidth_init`: realization and width-freedom of `initProg`.
* `realize_query`, `not_readsWidth_query`: realization and width-freedom of `queryProg`.
* `realize_kickStep`: realization of single kick step.
* `realize_kickLoop`, `not_readsWidth_kickLoop`: realization and width-freedom of `kickLoopProg`.
* `realize_delete`, `not_readsWidth_delete`: realization and width-freedom of `deleteProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.KickTree

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open scoped Cslib.WordRAM
open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.KickTree
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ### 1. Initialization Subroutine -/

/-- Word-RAM `Memory.Prog` subroutine initializing the kick-tree dictionary at `base`.
Writes seed words to `base + offSeeds` and zeroes the free-slot tree header at
`base + offFreeSlot`. -/
@[expose] def initProg (base offFreeSlot seed : ℕ) : Memory.Prog Unit := do
  Memory.write (base + offSeeds) seed
  Memory.write (base + offSeeds + 1) seed
  Memory.write (base + offFreeSlot) 0

/-- Uniform `Realizes .exact` certificate for `initProg`. -/
theorem realize_init :
    Realizes .exact (fun (((base, offFreeSlot), seed) : (ℕ × ℕ) × ℕ) =>
      initProg base offFreeSlot seed)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((base, offFreeSlot), seed) : (ℕ × ℕ) × ℕ) _ =>
        Fits w (base + offSeeds) ∧
        Fits w (base + offSeeds + 1) ∧
        Fits w (base + offFreeSlot) ∧
        Fits w seed)
      (fun _ _ => 0) := by
  realize
  · exact h.2.1
  · exact h.2.2.1

/-- `initProg` emitted code does not read machine word width. -/
theorem not_readsWidth_init {r : ℕ} (frontier : Fin r) (src : Fin 3 → Fin r)
    (tmp : Fin (0 + realize_init.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(realize_init.code frontier src tmp).ReadsWidth :=
  (realize_init.code_spec frontier src tmp hi hd hf hs).1

/-! ### 2. Query Routing Subroutine -/

/-- Word-RAM `Memory.Prog` subroutine querying the kick tree at `base`.
Checks the cubby metadata at `base + offFacility + slot`; if non-zero, compares
the stored quotient at `base + offQuot + slot` against target quotient `q`.
If equal, retrieves and returns stored value `val` from `base + offVal + slot`,
otherwise returns `0` (not found). -/
@[expose] def queryProg (base offFacility offVal slot q : ℕ) : Memory.Prog ℕ := do
  let cubbyMeta ← Memory.read (base + offFacility + slot)
  if 0 < cubbyMeta then do
    let storedQuot ← Memory.read (base + offQuot + slot)
    if storedQuot = q then do
      let val ← Memory.read (base + offVal + slot)
      pure val
    else
      pure 0
  else
    pure 0

/-- Uniform `Realizes .exact` certificate for `queryProg`. -/
theorem realize_query :
    Realizes .exact
      (fun (((((base, offFacility), offVal), slot), q) : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
        queryProg base offFacility offVal slot q)
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((((base, offFacility), offVal), slot), q) : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) _ =>
        Fits w (base + offFacility + slot) ∧
        Fits w (base + offQuot + slot) ∧
        Fits w (base + offVal + slot) ∧
        Fits w q)
      (fun _ _ => 0) := by
  realize
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

/-- `queryProg` emitted code does not read machine word width. -/
theorem not_readsWidth_query {r : ℕ} (frontier : Fin r) (src : Fin 5 → Fin r)
    (tmp : Fin (1 + realize_query.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(realize_query.code frontier src tmp).ReadsWidth :=
  (realize_query.code_spec frontier src tmp hi hd hf hs).1

/-! ### 3. Bounded Kick Loop Subroutine -/

/-- State of one kick transition: `(slot, item, status)` where `status = 1` indicates
an active kick in progress, and `status = 0` indicates the item has been placed. -/
abbrev KickState := ℕ × ℕ × ℕ

/-- Single switching step of the bounded kick loop (Lemma 1 / Theorem 2):
Inspects candidate slot `slot`. If vacant (quotient `0`), writes `item`,
marks cubby metadata active, and terminates (`status = 0`). If occupied, displaces
the incumbent quotient, writes `item`, and transitions to alternate slot
`slot ^^^ 1` with displaced occupant as new item (`status = 1`). -/
@[expose] def kickStepProg (base offFacility : ℕ) : KickState → Memory.Prog KickState
  | (slot, item, status) => do
      if 0 < status then do
        let occupant ← Memory.read (base + offQuot + slot)
        if occupant = 0 then do
          Memory.write (base + offQuot + slot) item
          Memory.write (base + offFacility + slot) 1
          pure (slot, 0, 0)
        else do
          Memory.write (base + offQuot + slot) item
          let nextSlot := slot ^^^ 1
          pure (nextSlot, occupant, 1)
      else
        pure (slot, item, status)

/-- Uniform `Realizes .exact` certificate for `kickStepProg`. -/
theorem realize_kickStep :
    Realizes .exact
      (fun (((base, offFacility), (slot, item, status)) : (ℕ × ℕ) × KickState) =>
        kickStepProg base offFacility (slot, item, status))
      (appendWords (WordEncoding.encode (α := ℕ × ℕ))
        (WordEncoding.encode (α := KickState)))
      (WordEncoding.encode (α := KickState))
      (fun w (((base, offFacility), (slot, item, _status)) : (ℕ × ℕ) × KickState) _ =>
        Fits w (base + offQuot + slot) ∧
        Fits w (base + offFacility + slot) ∧
        Fits w item ∧
        Fits w (slot ^^^ 1) ∧
        Fits w 1)
      (fun _ _ => 0) := by
  realize
  · exact h.1
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.2
  · exact h.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- Bounded kick loop insertion subroutine executing at most `fuel` steps
using `Realization.iterate` (bounded by `k + 1` steps per Lemma 1 / Theorem 2). -/
@[expose] def kickLoopIterProg : ((ℕ × ℕ) × KickState) × ℕ → Memory.Prog KickState
  | (((base, offFacility), state), fuel) =>
      iterate (fun (((b, off), s) : (ℕ × ℕ) × KickState) => kickStepProg b off s)
        (base, offFacility) fuel state

/-- Uniform `Realizes .exact` certificate for `kickLoopIterProg`. -/
theorem realize_kickLoop :
    Realizes .exact kickLoopIterProg
      (((appendWords (WordEncoding.encode (α := ℕ × ℕ))
        (WordEncoding.encode (α := KickState))).prodMap
          (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
            (Fin.appendEquiv (2 + 3) 1).toEmbedding)
      (WordEncoding.encode (α := KickState))
      (fun w ((d, a), fuel) s =>
        iterationSafe
          (fun (((b, off), state) : (ℕ × ℕ) × KickState) => kickStepProg b off state)
          (fun w (((base, offFacility), (slot, item, _status)) : (ℕ × ℕ) × KickState) _ =>
            Fits w (base + offQuot + slot) ∧
            Fits w (base + offFacility + slot) ∧
            Fits w item ∧
            Fits w (slot ^^^ 1) ∧
            Fits w 1)
          w d fuel a s)
      (fun ((d, a), fuel) s =>
        iterationWork
          (fun (((b, off), state) : (ℕ × ℕ) × KickState) => kickStepProg b off state)
          (fun _ _ => 0)
          d fuel a s) :=
  Realizes.iterateRuntime (WordEncoding.encode (α := ℕ × ℕ))
    (WordEncoding.encode (α := KickState)) realize_kickStep

/-- `kickLoopIterProg` emitted code does not read machine word width. -/
theorem not_readsWidth_kickLoop {r : ℕ} (frontier : Fin r) (src : Fin 6 → Fin r)
    (tmp : Fin (3 + realize_kickLoop.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(realize_kickLoop.code frontier src tmp).ReadsWidth :=
  (realize_kickLoop.code_spec frontier src tmp hi hd hf hs).1

/-- Bounded kick loop insertion with canonical initial state `(slot, item, 1)`. -/
@[expose] def kickLoopProg (base offFacility kickLimit slot item : ℕ) :
    Memory.Prog KickState :=
  kickLoopIterProg (((base, offFacility), (slot, item, 1)), kickLimit)

/-! ### 4. Deletion Subroutine via Tail Replacement -/

/-- Word-RAM `Memory.Prog` subroutine deleting an item via non-hash tail replacement
(STOC 2022 Section 5.2 / `Facility.tailReplace`) and free-slot reclamation.
Copies the quotient and value from `tailSlot` into `slot`, clears `tailSlot`,
and marks `tailSlot` available in the free-slot tree bitmap. -/
@[expose] def deleteProg (base offVal offFreeSlot slot tailSlot : ℕ) :
    Memory.Prog Unit := do
  let tailQuot ← Memory.read (base + offQuot + tailSlot)
  let tailVal ← Memory.read (base + offVal + tailSlot)
  Memory.write (base + offQuot + slot) tailQuot
  Memory.write (base + offVal + slot) tailVal
  Memory.write (base + offQuot + tailSlot) 0
  Memory.write (base + offVal + tailSlot) 0
  Memory.write (base + offFreeSlot + tailSlot) 0

/-- Uniform `Realizes .exact` certificate for `deleteProg`. -/
theorem realize_delete :
    Realizes .exact
      (fun (((((base, offVal), offFreeSlot), slot), tailSlot) :
          (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
        deleteProg base offVal offFreeSlot slot tailSlot)
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((((base, offVal), offFreeSlot), slot), tailSlot) :
          (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) _ =>
        Fits w (base + offQuot + tailSlot) ∧
        Fits w (base + offVal + tailSlot) ∧
        Fits w (base + offQuot + slot) ∧
        Fits w (base + offVal + slot) ∧
        Fits w (base + offFreeSlot + tailSlot))
      (fun _ _ => 0) := by
  realize
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- `deleteProg` emitted code does not read machine word width. -/
theorem not_readsWidth_delete {r : ℕ} (frontier : Fin r) (src : Fin 5 → Fin r)
    (tmp : Fin (0 + realize_delete.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(realize_delete.code frontier src tmp).ReadsWidth :=
  (realize_delete.code_spec frontier src tmp hi hd hf hs).1

end Cslib.DataStructure.Dictionary.WordRAM.KickTree
