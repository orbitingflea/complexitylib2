/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module

public import CslibFrontier.Crypto.Primitives.PRF.Invertible
public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Plinko

@[expose] public section

/-! # Tests for Invertible PRFs and the Plinko Preprocessing PIR Scheme

Concrete smoke tests exercising:
1. `idealInvertiblePRF`, `isCorrect_idealInvertiblePRF`, `InvertiblePRF.composePerm`,
   `InvertiblePRF.isCorrect_composePerm`, and an iPRF that is not inversion-correct.
2. Single-pass database streaming (`streamEntry`, `foldr_streamEntry_univ`) and
   `PlinkoState.Valid` on a concrete `2 × 2` database (`c = 2`, `w = 2`, `nReg = 2`, `nBackup = 1`).
3. Hint lookup (`findHintSlotScan`, `findHintSlot_eq_findHintSlotScan`, `getHintScan`),
   state transition (`PlinkoState.nextState`, `PlinkoState.valid_nextState`), and single/multi-query
   correctness (`PlinkoState.eval_step_plinkoScheme`,
   `PlinkoState.isCorrectFrom_plinkoScheme_of_canAnswerSeq`), including regular hint consumption,
   backup hint promotion, and cache hits.
4. The query map on a conditioned uniform hint (`eval_buildQuery_conditioned_eq_plinkoSim`) and
   perfect privacy of the idealized stand-in `plinkoHybridScheme`
   (`isPerfectlyPrivateWith_plinkoHybridScheme`, `privacyAdvantage_plinkoHybridScheme_eq_zero`,
   `eval_queryTranscript_plinkoHybridScheme`); neither is privacy of `plinkoScheme`.
5. Database and hint updates (`updateDB`, `updateHint`, `updateState`, `applyUpdates`,
   `PlinkoState.valid_updateHint`, `PlinkoState.valid_updateState`).
6. A non-degenerate instance (`c = 4`, `w = 2`, `nReg = 3`, `nBackup = 2`), where regular hints
   are proper `3`-block subsets: a query sequence that consumes a regular hint, then consumes the
   promoted backup hint it created, then hits the cache; every preprocessed state satisfies the
   correctness hypotheses (`PlinkoState.valid_of_mem_support_preprocess`); and the query map and the
   idealized stand-in at `c = 4`, `w = 3`, against a server whose queries depend on the messages it
   has seen.
-/

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko.Tests

open Cslib.Crypto.PRF
open Cslib.Crypto.Protocols.PIR.Preprocessing
open Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko

/-! ### 1. Invertible PRF and permutation composition smoke tests -/

/-- Canonical ideal iPRF on `Fin 3 → Fin 2` with key space `Fin 3 → Fin 2`. -/
noncomputable abbrev exampleIPRF : InvertiblePRF (Fin 3 → Fin 2) (Fin 3) (Fin 2) :=
  idealInvertiblePRF (Fin 3) (Fin 2)

example : exampleIPRF.IsCorrect := isCorrect_idealInvertiblePRF

example : exampleIPRF.IsCorrectOnGen := isCorrectOnGen_idealInvertiblePRF

/-- Composing `idealInvertiblePRF (Fin 3) (Fin 2)` with a keyed permutation family on `Fin 3`
yields a correct iPRF (Theorem 4.4 / Corollary 4.5). -/
noncomputable def examplePermIPRF :
    InvertiblePRF (Equiv.Perm (Fin 3) × (Fin 3 → Fin 2)) (Fin 3) (Fin 2) :=
  exampleIPRF.composePerm (ProbComp.uniform (Equiv.Perm (Fin 3))) id

example : examplePermIPRF.IsCorrect :=
  InvertiblePRF.isCorrect_composePerm (ProbComp.uniform (Equiv.Perm (Fin 3))) id
    isCorrect_idealInvertiblePRF

/-- An iPRF on `Fin 2` whose inverse is always empty: it is not inversion-correct at its key. -/
def emptyInverseIPRF : InvertiblePRF Unit (Fin 2) (Fin 2) where
  gen := pure ()
  eval _ x := x
  inv _ _ := ∅

example : ¬ emptyInverseIPRF.IsCorrectKey () := fun h => by
  simpa [emptyInverseIPRF] using (h 0 0).mpr rfl

/-! ### 2. Concrete 4-bit database (`c = 2` blocks × `w = 2` entries) -/

/-- Concrete 4-bit database on `Fin 2 × Fin 2`:
`db (0, 0) = true`, `db (0, 1) = false`, `db (1, 0) = true`, `db (1, 1) = true`. -/
def exampleDB : Fin 2 × Fin 2 → Bool
  | (0, 0) => true
  | (0, 1) => false
  | (1, 0) => true
  | (1, 1) => true

/-- Concrete iPRF keys for the two blocks (`nReg = 2`, `nBackup = 1`, total `3` slots). -/
def exampleKeys : Fin 2 → Fin 3 → Fin 2
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 1

/-- Regular block subsets of size `c / 2 + 1 = 2` (i.e. `Finset.univ : Finset (Fin 2)`). -/
def exampleRegBlocks : Fin 3 → Finset (Fin 2)
  | _ => Finset.univ

/-- Backup block subsets of size `c / 2 = 1` (`{0}`). -/
def exampleBackupBlocks : Fin 3 → Finset (Fin 2)
  | _ => {0}

/-- Offline preprocessing state for `exampleDB` with `nReg = 2` regular hints and `nBackup = 1`
backup hint. -/
noncomputable abbrev exampleState : PlinkoState 2 2 2 1 (Fin 3 → Fin 2) :=
  streamPreprocess exampleIPRF exampleDB exampleKeys exampleRegBlocks exampleBackupBlocks

/-- Single-pass entry streaming over `Finset.univ` produces `exampleState`. -/
example :
    (Finset.univ : Finset (Fin 2 × Fin 2)).toList.foldr
      (fun x st => streamEntry exampleIPRF x (exampleDB x) st)
      (initPlinkoState exampleKeys exampleRegBlocks exampleBackupBlocks) =
      exampleState :=
  foldr_streamEntry_univ (nReg := 2) (nBackup := 1) exampleDB exampleKeys
    exampleRegBlocks exampleBackupBlocks
    (fun α => isCorrectKey_idealInvertiblePRF (exampleKeys α))

/-- `exampleState` satisfies `PlinkoState.Valid exampleIPRF exampleDB`. -/
theorem exampleState_valid : exampleState.Valid exampleIPRF exampleDB :=
  PlinkoState.valid_streamPreprocess (nReg := 2) (nBackup := 1) exampleIPRF exampleDB exampleKeys
    exampleRegBlocks exampleBackupBlocks

/-- Slot `0` matches query `(0, 0)` and slot `1` matches query `(0, 1)`. -/
example : findHintSlotScan exampleIPRF exampleState (0, 0) = some 0 := by decide
example : findHintSlotScan exampleIPRF exampleState (0, 1) = some 1 := by decide

example : findHintSlot exampleIPRF exampleState (0, 0) = some 0 := by
  rw [findHintSlot_eq_findHintSlotScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

/-! ### 3. Online execution, backup promotion, and cache hits -/

/-- After answering `(0, 0)`, backup slot `2` is promoted into active hint slot `2` and `(0, 0)`
is cached with value `exampleDB (0, 0) = true`. -/
example : (exampleState.nextState exampleIPRF exampleDB (0, 0)).cache (0, 0) =
    some (true, 2) := by
  dsimp only [PlinkoState.nextState]
  rw [getHint_eq_getHintScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

theorem exampleState_canAnswer_00 : exampleState.CanAnswer exampleIPRF (0, 0) := by
  right
  rw [getHint_eq_getHintScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

/-- Single-step exact evaluation of `plinkoScheme` on `exampleState` and query `(0, 0)` outputs
`(exampleState.nextState exampleIPRF exampleDB (0, 0), exampleDB (0, 0))` with probability one. -/
example :
    ProbComp.eval ((plinkoScheme 2 2 2 1 exampleIPRF).step exampleDB exampleState (0, 0)) =
      PMF.pure (exampleState.nextState exampleIPRF exampleDB (0, 0), exampleDB (0, 0)) :=
  PlinkoState.eval_step_plinkoScheme exampleState_valid
    (isCorrectKey_idealInvertiblePRF _) exampleState_canAnswer_00

/-- Re-querying `(0, 0)` after it has been cached is answered directly from the cache, so the
2-query sequence `[(0, 0), (0, 0)]` satisfies `IsCorrectFrom`. -/
theorem exampleState_canAnswerSeq_00_00 :
    exampleState.CanAnswerSeq exampleIPRF exampleDB [(0, 0), (0, 0)] := by
  refine ⟨exampleState_canAnswer_00, ⟨Or.inl ?_, trivial⟩⟩
  dsimp only [PlinkoState.nextState]
  rw [getHint_eq_getHintScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

example :
    (plinkoScheme 2 2 2 1 exampleIPRF).IsCorrectFrom exampleDB exampleState [(0, 0), (0, 0)] :=
  (PlinkoState.isCorrectFrom_plinkoScheme_of_canAnswerSeq exampleState_valid
    (fun α => isCorrectKey_idealInvertiblePRF (exampleState.keys α))
    exampleState_canAnswerSeq_00_00).1

/-! ### 4. Single-query and multi-query privacy tests -/

instance : Fact (Even 2) := ⟨⟨1, rfl⟩⟩

/-- On `Fin 2 × Fin 2`, `buildQuery` sends a conditioned uniform regular hint to `plinkoSim 2 2`. -/
example (x : Fin 2 × Fin 2) :
    ProbComp.eval (do
      let P ← ProbComp.uniform (RegBlocksContaining 2 x.1)
      let o ← ProbComp.uniform (OffsetsContaining 2 2 x)
      let b ← ProbComp.uniform Bool
      let r ← ProbComp.uniform (Fin 2)
      pure (buildQuery x P.1 o.1 b r)) =
      ProbComp.eval (plinkoSim 2 2) :=
  eval_buildQuery_conditioned_eq_plinkoSim x

/-- Perfect privacy of the idealized stand-in `plinkoHybridScheme 2 2`. -/
example : (plinkoHybridScheme 2 2).IsPerfectlyPrivateWith (plinkoSim 2 2) :=
  isPerfectlyPrivateWith_plinkoHybridScheme

/-- Concrete adaptive server logging Plinko queries and maintaining a step counter. -/
def plinkoTranscriptServer : AdaptiveServer (Fin 2 × Fin 2) (PlinkoQuery 2 2) (Bool × Bool)
    (ℕ × List (PlinkoQuery 2 2)) where
  chooseQuery st := pure ((st.1 + 1, st.2), (0, 0))
  onQuery st q := pure ((st.1, q :: st.2), (decide (0 ∈ q.blocks), decide (q.offsets 0 = 0)))

example (db : Fin 2 × Fin 2 → Bool) :
    (plinkoHybridScheme 2 2).privacyAdvantage (plinkoSim 2 2) plinkoTranscriptServer
      (fun st => decide (st.2.length = 2)) db 2 (0, []) = 0 :=
  privacyAdvantage_plinkoHybridScheme_eq_zero plinkoTranscriptServer
    (fun st => decide (st.2.length = 2)) db 2 (0, [])

/-- Query transcripts of the idealized stand-in `plinkoHybridScheme 2 2` on a 3-query sequence. -/
example :
    ProbComp.eval
      ((plinkoHybridScheme 2 2).queryTranscript exampleDB [(0, 0), (1, 1), (0, 1)]) =
      ProbComp.eval (simTranscript (plinkoSim 2 2) 3) :=
  eval_queryTranscript_plinkoHybridScheme exampleDB [(0, 0), (1, 1), (0, 1)]

/-! ### 5. Database and hint updates (`UpdateDB` / `UpdateHint`) -/

/-- Updating entry `(0, 0)` of `exampleDB` to `false` via `updateDB` and `updateHint` preserves
`PlinkoState.Valid`. -/
example :
    (updateHint exampleIPRF (updateDB exampleDB (0, 0) false).1 exampleState).Valid
      exampleIPRF (updateDB exampleDB (0, 0) false).2 :=
  PlinkoState.valid_updateHint (0, 0) false exampleState_valid
    (isCorrectKey_idealInvertiblePRF (exampleState.keys 0))

/-- Batch updates via `updateState` preserve `PlinkoState.Valid` for `applyUpdates`. -/
example (updates : List (UpdateSummary 2 2)) :
    (updateState exampleIPRF updates exampleState).Valid
      exampleIPRF (applyUpdates updates exampleDB) :=
  PlinkoState.valid_updateState updates exampleState_valid
    (fun α => isCorrectKey_idealInvertiblePRF (exampleState.keys α))

/--
info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko.applyUpdates_nil' does not depend on any axioms
-/
#guard_msgs in
#print axioms applyUpdates_nil

/-! ### 6. A non-degenerate instance: `c = 4` blocks, `w = 2` offsets, `3 + 2` hint slots -/

/-- The ideal iPRF from the `5` hint slots to the `2` offsets. -/
noncomputable abbrev exampleIPRF4 : InvertiblePRF (Fin 5 → Fin 2) (Fin 5) (Fin 2) :=
  idealInvertiblePRF (Fin 5) (Fin 2)

/-- With the ideal iPRF, `getHint` agrees with the linear scan on every state and index. -/
theorem getHint_exampleIPRF4 (st : PlinkoState 4 2 3 2 (Fin 5 → Fin 2)) (x : Fin 4 × Fin 2) :
    getHint exampleIPRF4 st x = getHintScan exampleIPRF4 st x :=
  getHint_eq_getHintScan st x (isCorrectKey_idealInvertiblePRF _)

/-- A non-constant `8`-bit database on `Fin 4 × Fin 2`. -/
def exampleDB4 (x : Fin 4 × Fin 2) : Bool :=
  ![![true, false], ![false, true], ![true, true], ![false, true]] x.1 x.2

/-- Per-block iPRF keys (functions from the `5` slots to the `2` offsets). -/
def exampleKeys4 : Fin 4 → Fin 5 → Fin 2 :=
  ![![0, 1, 0, 1, 0], ![1, 0, 1, 0, 1], ![0, 0, 1, 1, 0], ![1, 1, 1, 0, 1]]

/-- Regular block sets of size `c / 2 + 1 = 3` (used in slots `0, 1, 2`). -/
def exampleRegBlocks4 : Fin 5 → Finset (Fin 4) :=
  ![{0, 1, 2}, {1, 2, 3}, {0, 2, 3}, {0, 1, 2}, {0, 1, 2}]

/-- Backup block sets of size `c / 2 = 2` (used in slots `3, 4`). -/
def exampleBackupBlocks4 : Fin 5 → Finset (Fin 4) :=
  ![{0, 1}, {0, 1}, {0, 1}, {0, 1}, {2, 3}]

/-- Offline preprocessing state with `3` regular and `2` backup hints. -/
noncomputable abbrev exampleState4 : PlinkoState 4 2 3 2 (Fin 5 → Fin 2) :=
  streamPreprocess exampleIPRF4 exampleDB4 exampleKeys4 exampleRegBlocks4 exampleBackupBlocks4

theorem exampleState4_valid : exampleState4.Valid exampleIPRF4 exampleDB4 :=
  PlinkoState.valid_streamPreprocess (nReg := 3) (nBackup := 2) exampleIPRF4 exampleDB4
    exampleKeys4 exampleRegBlocks4 exampleBackupBlocks4

/-- The block sets used by `streamPreprocess` have the sizes that `plinkoScheme` samples:
`c / 2 + 1 = 3` in the regular slots and `c / 2 = 2` in the backup slots. -/
example : (∀ j : Fin 5, j.val < 3 → (exampleRegBlocks4 j).card = 3) ∧
    (∀ j : Fin 5, 3 ≤ j.val → (exampleBackupBlocks4 j).card = 2) := by decide

/-- Query `(0, 0)` uses regular slot `0`; slot `2` also contains block `0` at offset `0`. -/
example : (getHintScan exampleIPRF4 exampleState4 (0, 0)).map MatchedHint.slot = some 0 := by decide

/-- After `(0, 0)`, backup slot `3` is promoted with `(0, 0)` and caches `exampleDB4 (0, 0)`. -/
example : (exampleState4.nextState exampleIPRF4 exampleDB4 (0, 0)).cache (0, 0) =
    some (true, 3) := by
  dsimp only [PlinkoState.nextState]
  simp only [getHint_exampleIPRF4]
  decide

/-- The second query `(3, 0)` is answered by the promoted hint in slot `3`, whose effective block
set is `{0, 2, 3}`. -/
example :
    (getHintScan exampleIPRF4 (exampleState4.nextState exampleIPRF4 exampleDB4 (0, 0))
      (3, 0)).map (fun t => (t.slot, t.blocks)) = some (3, {0, 2, 3}) := by
  dsimp only [PlinkoState.nextState]
  simp only [getHint_exampleIPRF4]
  decide

/-- The sequence `[(0, 0), (3, 0), (0, 0)]` is answerable: a regular hint, then the promoted hint
created by the first query, then the cache. -/
theorem exampleState4_canAnswerSeq :
    exampleState4.CanAnswerSeq exampleIPRF4 exampleDB4 [(0, 0), (3, 0), (0, 0)] := by
  refine ⟨Or.inr ?_, Or.inr ?_, Or.inl ?_, trivial⟩ <;>
    simp only [PlinkoState.nextState, getHint_exampleIPRF4] <;> decide

example :
    (plinkoScheme 4 2 3 2 exampleIPRF4).IsCorrectFrom exampleDB4 exampleState4
      [(0, 0), (3, 0), (0, 0)] :=
  (PlinkoState.isCorrectFrom_plinkoScheme_of_canAnswerSeq exampleState4_valid
    (fun α => isCorrectKey_idealInvertiblePRF (exampleState4.keys α))
    exampleState4_canAnswerSeq).1

/-- Every state that `plinkoScheme` preprocesses with the ideal iPRF is `Valid` and has
inversion-correct keys. -/
example (db : Fin 4 × Fin 2 → Bool) (st : PlinkoState 4 2 3 2 (Fin 5 → Fin 2))
    (hmem : st ∈ (ProbComp.eval ((plinkoScheme 4 2 3 2 exampleIPRF4).preprocess db)).support) :
    st.Valid exampleIPRF4 db ∧ ∀ α, exampleIPRF4.IsCorrectKey (st.keys α) :=
  let h := PlinkoState.valid_of_mem_support_preprocess hmem
  ⟨h.1, h.2 isCorrectOnGen_idealInvertiblePRF⟩

instance : Fact (Even 4) := ⟨⟨2, rfl⟩⟩

/-- At `c = 4`, `w = 3`, `buildQuery` sends a conditioned uniform regular hint (one of three
`3`-block sets containing the queried block) to `plinkoSim 4 3`. -/
example (x : Fin 4 × Fin 3) :
    ProbComp.eval (do
      let P ← ProbComp.uniform (RegBlocksContaining 4 x.1)
      let o ← ProbComp.uniform (OffsetsContaining 4 3 x)
      let b ← ProbComp.uniform Bool
      let r ← ProbComp.uniform (Fin 3)
      pure (buildQuery x P.1 o.1 b r)) =
      ProbComp.eval (plinkoSim 4 3) :=
  eval_buildQuery_conditioned_eq_plinkoSim x

/-- An adaptive server for `c = 4`, `w = 3` that picks its next index from the last query message
it saw and logs every message. -/
def plinkoAdaptiveServer4 : AdaptiveServer (Fin 4 × Fin 3) (PlinkoQuery 4 3) (Bool × Bool)
    (List (PlinkoQuery 4 3)) where
  chooseQuery st :=
    match st with
    | [] => pure (st, (0, 0))
    | q :: _ => pure (st, if 0 ∈ q.blocks then (1, q.offsets 1) else (3, q.offsets 2))
  onQuery st q := pure (q :: st, (decide (2 ∈ q.blocks), decide (q.offsets 3 = 1)))

example (db : Fin 4 × Fin 3 → Bool) :
    (plinkoHybridScheme 4 3).privacyAdvantage (plinkoSim 4 3) plinkoAdaptiveServer4
      (fun st => match st with
        | q :: _ => decide (0 ∈ q.blocks)
        | [] => false) db 3 [] = 0 :=
  privacyAdvantage_plinkoHybridScheme_eq_zero plinkoAdaptiveServer4 _ db 3 []

end Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko.Tests

end
