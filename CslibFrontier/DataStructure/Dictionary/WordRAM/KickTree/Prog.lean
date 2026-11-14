/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
public import CslibFrontier.DataStructure.Dictionary.WordRAM.KickTree.Layout
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctProg
import CslibFrontier.Tactic.Realize

/-!
# Bit-Packed Word-RAM `Memory.Prog` Subroutines and Realizations for `k`-Kick Tree Slots

This module implements bit-packed Word-RAM `Memory.Prog` slot subroutines over the parameterized
`Layout.lean` arrays (`Quotients`, `Values`, `Occupancy`, `SlotMeta`), certifies each subroutine
with a uniform width-free `Realizes .exact` (`¬ReadsWidth`) certificate via `realize`, and proves
exact pure array-level specifications:

1. **Zeroed Table Allocation (`allocKickTableGenProg`, `allocKickTableProg`)**: allocates
   `totalSpace p` zeroed words at the memory frontier and establishes `quotAt = 0`, `valAt = 0`,
   `occAt = 0`, and `metaAt = 0` (`allocKickTableProg_spec`).
2. **Bit-Packed Slot Query (`querySlotGenProg`, `querySlotProg`)**: inspects 1-bit `Occupancy`
   before comparing `Quotients[slot]` against target quotient `q`, returning `Option ℕ` (`some val`
   on a hit, `none` on an empty or mismatched slot so stored value `0` and `none` stay distinct;
   `querySlotProg_spec`).
3. **Bounded Bit-Packed Kick Displacement Loop (`kickStepGenProg`, `kickLoopIterGenProg`,
   `kickLoopProg`)**: steps along a caller-supplied switching-path buffer `[pathBase, pathBase +
   fuel)` using `Realization.iterate` (`fuel ≤ k + 1` per Section 3.1 / Theorem 2), checking
   vacancy via 1-bit `Occupancy` (so zero quotients are preserved) and displacing
   `(quot, val, metaTag)` atomically (`kickStepProg_vacant_spec`, `kickStepProg_displace_spec`).
4. **Bit-Packed Tail-Replacement Deletion (`deleteSlotGenProg`, `deleteSlotProg`)**: copies
   `(quot, val, meta, occ)` from `tailSlot` to `slot` and clears all four bit-packed fields
   (including `occ := 0`) at `tailSlot`, handling both `slot ≠ tailSlot` and self-deletion
   `slot = tailSlot` (`deleteSlotProg_spec`).

## Source attribution

* [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 3.1 (printed pp. 8–10 / PDF pp. 9–11) and Theorem 2 (printed p. 11 / PDF p. 12):
    `k`-kick tree priority displacement chains of length at most `k + 1`.
  - Section 5.1–5.3 (printed pp. 27–35 / PDF pp. 34–36): occupancy/free-slot bitmaps, non-hash
    tail replacement on deletion (`Facility.tailReplace`), and bit-packed quotiented slots.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickRuntimeParams`, `mkKickRuntimeParams`,
  `KickEnv`, `KickEnvGen`: 10-word runtime layout parameter record and safety envelope.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.allocKickTableGenProg`, `allocKickTableProg`:
  zeroed `totalSpace` block allocation.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickQueryInput`, `querySlotGenProg`,
  `querySlotProg`: bit-packed slot lookup returning `Option ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickStepEnv`, `KickStepState`,
  `kickStepGenProg`, `kickStepProg`, `kickLoopIterGenProg`, `kickLoopProg`: bounded bit-packed
  switching-path displacement step and `iterate` loop.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickDeleteInput`, `deleteSlotGenProg`,
  `deleteSlotProg`: bit-packed tail-replacement slot deletion.

## Main results

* `allocKickTableProg_spec`, `realizes_allocKickTableGen`: zero-initialized array specification and
  `Realizes .exact` certificate for `allocKickTableGenProg`.
* `querySlotProg_spec`, `realizes_querySlotGen`: `Option ℕ` lookup specification and
  `Realizes .exact` certificate for `querySlotGenProg`.
* `kickStepProg_vacant_spec`, `kickStepProg_displace_spec`, `realizes_kickStepGen`,
  `realizes_kickLoopGen`: pure array-update specifications and `Realizes .exact` certificates for
  `kickStepGenProg` and `kickLoopIterGenProg`.
* `deleteSlotProg_spec`, `realizes_deleteSlotGen`: pure array-update specification (covering both
  `slot ≠ tailSlot` and `slot = tailSlot`) and `Realizes .exact` certificate for
  `deleteSlotGenProg`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022],
  STOC 2022, pp. 1284–1297 (`arXiv:2111.00602v2`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.KickTree

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open scoped Cslib.WordRAM
open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.KickTree
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ### 1. Runtime layout parameter record and safety envelope -/

/-- 10-word precomputed runtime parameter record for bit-packed kick-tree `Memory.Prog` methods. -/
structure KickRuntimeParams where
  /-- Machine word width `w`. -/
  w : ℕ
  /-- Primary slot capacity `nMax`. -/
  nMax : ℕ
  /-- Word offset `offQuot p`. -/
  offQuot : ℕ
  /-- Quotient bit width `fullQuotBits p.U p.nMax`. -/
  quotBits : ℕ
  /-- Word offset `offVal p`. -/
  offVal : ℕ
  /-- Value bit width `valBits p.V`. -/
  valBits : ℕ
  /-- Word offset `offOcc p`. -/
  offOcc : ℕ
  /-- Word offset `offMeta p`. -/
  offMeta : ℕ
  /-- Metadata bit width `metaBits p`. -/
  metaBits : ℕ
  /-- Total word footprint `totalSpace p`. -/
  totalSpace : ℕ
deriving Repr, DecidableEq

/-- Tuple equivalence for `KickRuntimeParams` used by `WordEncoding.ofEquiv`. -/
@[expose] def KickRuntimeParams.equiv :
    KickRuntimeParams ≃
      ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun r :=
    (((((((((r.w, r.nMax), r.offQuot), r.quotBits), r.offVal), r.valBits),
      r.offOcc), r.offMeta), r.metaBits), r.totalSpace)
  invFun := fun (((((((((w, nMax), oQ), qB), oV), vB), oO), oM), mB), tot) =>
    ⟨w, nMax, oQ, qB, oV, vB, oO, oM, mB, tot⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickRuntimeParams := .ofEquiv KickRuntimeParams.equiv

/-- Populate `KickRuntimeParams` from a layout configuration `p : KickTreeParams`. -/
@[expose] def mkKickRuntimeParams (p : KickTreeParams) : KickRuntimeParams where
  w := p.w
  nMax := p.nMax
  offQuot := offQuot p
  quotBits := fullQuotBits p.U p.nMax
  offVal := offVal p
  valBits := valBits p.V
  offOcc := offOcc p
  offMeta := offMeta p
  metaBits := metaBits p
  totalSpace := totalSpace p

/-- Word-width, bit-width, metadata-multiplicity, and address-fit invariant for `p` at `base`. -/
@[expose] def KickEnv (p : KickTreeParams) (w' base : ℕ) : Prop :=
  w' = p.w ∧
    0 < p.w ∧
    fullQuotBits p.U p.nMax ≤ p.w ∧
    valBits p.V ≤ p.w ∧
    metaBits p ≤ p.w ∧
    1 ≤ p.cMeta ∧
    Fits p.w (base + totalSpace p)

/-- Parameter-free runtime envelope pairing `rp : KickRuntimeParams` with `KickTreeParams`. -/
@[expose] def KickEnvGen (w' : ℕ) (rp : KickRuntimeParams) (base : ℕ) : Prop :=
  ∃ p : KickTreeParams, rp = mkKickRuntimeParams p ∧ KickEnv p w' base

private theorem fits_one_of_pos {w : ℕ} (hw : 0 < w) : Fits w 1 :=
  Nat.one_lt_two_pow (by omega)

private theorem fits_one_of_env {w' base : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) : Fits w' 1 := by
  obtain ⟨_, _, rfl, hw, _⟩ := henv
  exact fits_one_of_pos hw

private theorem slot_lt_occLen {p : KickTreeParams} {slot : ℕ} (hs : slot < p.nMax) :
    slot < occLen p := by
  unfold occLen; omega

private theorem slot_lt_metaLen {p : KickTreeParams} {slot : ℕ} (hc : 1 ≤ p.cMeta)
    (hs : slot < p.nMax) : slot < metaLen p := by
  unfold metaLen
  calc slot < 1 * p.nMax := by omega
    _ ≤ p.cMeta * p.nMax := Nat.mul_le_mul_right _ hc

private theorem readPacked_quot_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ rp.quotBits ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offQuot + packedWords N rp.quotBits w') := by
  obtain ⟨p, rfl, rfl, hw, hq, _, _, _, hfit⟩ := henv
  refine ⟨p.nMax, rfl, hw, hq, hslot, hfit.of_le ?_⟩
  have := quot_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, quotWords] at this ⊢
  omega

private theorem readPacked_val_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ rp.valBits ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offVal + packedWords N rp.valBits w') := by
  obtain ⟨p, rfl, rfl, hw, _, hv, _, _, hfit⟩ := henv
  refine ⟨p.nMax, rfl, hw, hv, hslot, hfit.of_le ?_⟩
  have := val_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, valWords] at this ⊢
  omega

private theorem readPacked_occ_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ 1 ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offOcc + packedWords N 1 w') := by
  obtain ⟨p, rfl, rfl, hw, _, _, _, _, hfit⟩ := henv
  refine ⟨occLen p, rfl, hw, hw, slot_lt_occLen hslot, hfit.of_le ?_⟩
  have := occ_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, occWords] at this ⊢
  omega

private theorem readPacked_meta_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ rp.metaBits ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offMeta + packedWords N rp.metaBits w') := by
  obtain ⟨p, rfl, rfl, hw, _, _, hm, hc, hfit⟩ := henv
  refine ⟨metaLen p, rfl, hw, hm, slot_lt_metaLen hc hslot, hfit.of_le ?_⟩
  have := meta_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, metaWords] at this ⊢
  omega

/-! ### 2. Zeroed Table Allocation Subroutine -/

/-- Parameter-free `Memory.Prog` subroutine allocating `rp.totalSpace` zeroed words. -/
@[expose] def allocKickTableGenProg (rp : KickRuntimeParams) : Memory.Prog ℕ :=
  Memory.alloc rp.totalSpace

/-- Allocate `totalSpace p` zeroed words for `p : KickTreeParams`. -/
@[expose] def allocKickTableProg (p : KickTreeParams) : Memory.Prog ℕ :=
  allocKickTableGenProg (mkKickRuntimeParams p)

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `allocKickTableGenProg`. -/
theorem realizes_allocKickTableGen :
    Realizes .exact allocKickTableGenProg
      (WordEncoding.encode (α := KickRuntimeParams))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  realize

/-- Allocating a kick-tree table returns `base = s.frontier`, advances the frontier by
`totalSpace p`, and zero-initializes all four bit-packed arrays (`quotAt`, `valAt`, `occAt`,
`metaAt`). -/
theorem allocKickTableProg_spec (p : KickTreeParams) (hw : 0 < p.w) (s : Memory.State) :
    let base := (Memory.spec 0).clientResult s (allocKickTableProg p)
    let s' := (Memory.spec 0).clientState s (allocKickTableProg p)
    base = s.frontier ∧
      s'.frontier = s.frontier + totalSpace p ∧
      quotAt base p s'.mem = (fun _ => 0) ∧
      valAt base p s'.mem = (fun _ => 0) ∧
      occAt base p s'.mem = (fun _ => 0) ∧
      metaAt base p s'.mem = (fun _ => 0) := by
  have hzero : ∀ a, s.frontier + p.hSpace ≤ a → a < s.frontier + totalSpace p →
      clear s.mem s.frontier (totalSpace p) a = 0 := fun a ha1 ha2 =>
    clear_of_owns ⟨by dsimp; omega, ha2⟩
  exact ⟨rfl, rfl,
    quotAt_zero_of_init p hw hzero,
    valAt_zero_of_init p hw hzero,
    occAt_zero_of_init p hw hzero,
    metaAt_zero_of_init p hw hzero⟩

/-! ### 3. Bit-Packed Slot Query Subroutine (`Option ℕ`) -/

/-- Input record for `querySlotGenProg`. -/
structure KickQueryInput where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Primary slot index `slot < rp.nMax`. -/
  slot : ℕ
  /-- Target quotient `q`. -/
  q : ℕ

/-- Tuple equivalence for `KickQueryInput` used by `WordEncoding.ofEquiv`. -/
@[expose] def KickQueryInput.equiv :
    KickQueryInput ≃ ((KickRuntimeParams × ℕ) × ℕ) × ℕ where
  toFun d := (((d.rp, d.base), d.slot), d.q)
  invFun := fun (((rp, base), slot), q) => ⟨rp, base, slot, q⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickQueryInput := .ofEquiv KickQueryInput.equiv

/-- Parameter-free bit-packed slot lookup returning `Option ℕ`. Checks `Occupancy[slot]` first so
that an empty slot (`none`) and a stored value `0` (`some 0`, even at quotient `0`) are distinct. -/
@[expose] def querySlotGenProg (d : KickQueryInput) : Memory.Prog (Option ℕ) := do
  let occ ← readPackedGenProg (((d.base, d.rp.offOcc), (1, d.rp.w)), d.slot)
  if occ = 0 then
    pure none
  else do
    let sq ← readPackedGenProg (((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.slot)
    if sq = d.q then do
      let v ← readPackedGenProg (((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.slot)
      pure (some v)
    else
      pure none

/-- Bit-packed slot lookup for `p : KickTreeParams` at `base`. -/
@[expose] def querySlotProg (p : KickTreeParams) (base slot q : ℕ) : Memory.Prog (Option ℕ) :=
  querySlotGenProg ⟨mkKickRuntimeParams p, base, slot, q⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `querySlotGenProg`. -/
theorem realizes_querySlotGen :
    Realizes .exact querySlotGenProg
      (WordEncoding.encode (α := KickQueryInput))
      (WordEncoding.encode (α := Option ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax ∧ Fits w d.q)
      (fun _ _ => 0) := by
  realize [realizes_readPackedGen]
  · exact fits_one_of_env h.1
  · exact readPacked_occ_safe h.1 h.2.1
  · exact readPacked_quot_safe h.1 h.2.1
  · exact readPacked_val_safe h.1 h.2.1
  · exact fits_one_of_env h.1

/-- Pure array-level specification for `querySlotProg`: preserves memory state and returns
`some (valAt base p s.mem slot)` iff `occAt base p s.mem slot ≠ 0` and
`quotAt base p s.mem slot = q`. -/
theorem querySlotProg_spec (p : KickTreeParams) {base slot q : ℕ} (hslot : slot < p.nMax)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (querySlotProg p base slot q) = s ∧
      (Memory.spec 0).clientResult s (querySlotProg p base slot q) =
        if occAt base p s.mem slot = 0 then none
        else if quotAt base p s.mem slot = q then some (valAt base p s.mem slot)
        else none := by
  have hocc_lt : slot < occLen p := slot_lt_occLen hslot
  unfold querySlotProg querySlotGenProg readPackedGenProg
  dsimp only [mkKickRuntimeParams]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    clientState_readPackedProg, clientResult_readPackedProg]
  have hocc : readPacked (base + offOcc p) 1 p.w s.mem slot = occAt base p s.mem slot := by
    simp [occAt, hocc_lt]
  rw [hocc]
  by_cases ho : occAt base p s.mem slot = 0
  · rw [ite_eq_left ho, ite_eq_left ho]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right ho, ite_eq_right ho,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    have hq : readPacked (base + offQuot p) (fullQuotBits p.U p.nMax) p.w s.mem slot =
        quotAt base p s.mem slot := by
      simp [quotAt, hslot]
    rw [hq]
    by_cases hqe : quotAt base p s.mem slot = q
    · rw [ite_eq_left hqe, ite_eq_left hqe,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        clientState_readPackedProg, clientResult_readPackedProg]
      have hv : readPacked (base + offVal p) (valBits p.V) p.w s.mem slot =
          valAt base p s.mem slot := by
        simp [valAt, hslot]
      rw [hv]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hqe, ite_eq_right hqe]
      exact ⟨rfl, rfl⟩

/-! ### 4. Bounded Bit-Packed Kick Displacement Loop -/

/-- Loop-invariant environment for `kickStepGenProg`. -/
structure KickStepEnv where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Base word address of the switching-path buffer `[pathBase, pathBase + fuel)`. -/
  pathBase : ℕ

/-- Tuple equivalence for `KickStepEnv` used by `WordEncoding.ofEquiv`. -/
@[expose] def KickStepEnv.equiv :
    KickStepEnv ≃ (KickRuntimeParams × ℕ) × ℕ where
  toFun e := ((e.rp, e.base), e.pathBase)
  invFun := fun ((rp, base), pathBase) => ⟨rp, base, pathBase⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickStepEnv := .ofEquiv KickStepEnv.equiv

/-- Loop state carried across bounded kick displacement steps (`active > 0` while an item remains
in flight; `active = 0` once placed into a vacant slot). -/
structure KickStepState where
  /-- Current index into the switching-path buffer `pathBase`. -/
  stepIdx : ℕ
  /-- Quotient of the item currently being placed. -/
  quot : ℕ
  /-- Value of the item currently being placed. -/
  val : ℕ
  /-- Per-slot kick-depth / metadata tag of the item currently being placed. -/
  metaTag : ℕ
  /-- Activity flag (`1` = active displacement in progress, `0` = item placed). -/
  active : ℕ
deriving Repr, DecidableEq

/-- Tuple equivalence for `KickStepState` used by `WordEncoding.ofEquiv`. -/
@[expose] def KickStepState.equiv :
    KickStepState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun st := ((((st.stepIdx, st.quot), st.val), st.metaTag), st.active)
  invFun := fun ((((stepIdx, quot), val), metaTag), active) =>
    ⟨stepIdx, quot, val, metaTag, active⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickStepState := .ofEquiv KickStepState.equiv

/-- Precondition for one step of `kickStepGenProg`. -/
@[expose] def KickStepSafe (w : ℕ) (d : KickStepEnv × KickStepState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  KickEnvGen w env.rp env.base ∧
    (0 < st.active →
      Fits w (env.pathBase + st.stepIdx) ∧
        Fits w (st.stepIdx + 1) ∧
        s.mem (env.pathBase + st.stepIdx) < env.rp.nMax)

/-- Single bit-packed displacement step along `env.pathBase`:
checks 1-bit `Occupancy[slot]` (never confusing zero quotients with empty slots). If vacant, writes
`(quot, val, metaTag)` and sets `Occupancy[slot] := 1`, terminating (`active := 0`). If occupied,
atomically reads incumbent `(oldQuot, oldVal, oldMeta)`, writes `(quot, val, metaTag)` into `slot`,
and advances to `stepIdx + 1` carrying `(oldQuot, oldVal, oldMeta)`. -/
@[expose] def kickStepGenProg (d : KickStepEnv × KickStepState) : Memory.Prog KickStepState := do
  let env := d.1
  let st := d.2
  if 0 < st.active then do
    let slot ← Memory.read (env.pathBase + st.stepIdx)
    let occ ← readPackedGenProg (((env.base, env.rp.offOcc), (1, env.rp.w)), slot)
    if occ = 0 then do
      writePackedGenProg ((((env.base, env.rp.offQuot), (env.rp.quotBits, env.rp.w)), slot),
        st.quot)
      writePackedGenProg ((((env.base, env.rp.offVal), (env.rp.valBits, env.rp.w)), slot),
        st.val)
      writePackedGenProg ((((env.base, env.rp.offMeta), (env.rp.metaBits, env.rp.w)), slot),
        st.metaTag)
      writePackedGenProg ((((env.base, env.rp.offOcc), (1, env.rp.w)), slot), 1)
      pure ⟨st.stepIdx + 1, 0, 0, 0, 0⟩
    else do
      let oldQuot ← readPackedGenProg (((env.base, env.rp.offQuot), (env.rp.quotBits, env.rp.w)),
        slot)
      let oldVal ← readPackedGenProg (((env.base, env.rp.offVal), (env.rp.valBits, env.rp.w)),
        slot)
      let oldMeta ← readPackedGenProg (((env.base, env.rp.offMeta), (env.rp.metaBits, env.rp.w)),
        slot)
      writePackedGenProg ((((env.base, env.rp.offQuot), (env.rp.quotBits, env.rp.w)), slot),
        st.quot)
      writePackedGenProg ((((env.base, env.rp.offVal), (env.rp.valBits, env.rp.w)), slot),
        st.val)
      writePackedGenProg ((((env.base, env.rp.offMeta), (env.rp.metaBits, env.rp.w)), slot),
        st.metaTag)
      pure ⟨st.stepIdx + 1, oldQuot, oldVal, oldMeta, 1⟩
  else
    pure st

/-- Typed wrapper for `kickStepGenProg`. -/
@[expose] def kickStepProg (p : KickTreeParams) (base pathBase : ℕ) (st : KickStepState) :
    Memory.Prog KickStepState :=
  kickStepGenProg (⟨mkKickRuntimeParams p, base, pathBase⟩, st)

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `kickStepGenProg`. -/
theorem realizes_kickStepGen :
    Realizes .exact kickStepGenProg
      (appendWords (WordEncoding.encode (α := KickStepEnv))
        (WordEncoding.encode (α := KickStepState)))
      (WordEncoding.encode (α := KickStepState))
      KickStepSafe
      (fun _ _ => 0) := by
  realize [realizes_readPackedGen, realizes_writePackedGen]
  all_goals
    obtain ⟨henv, hact⟩ := h
  · exact (hact (by assumption)).1
  · exact fits_one_of_env henv
  · exact readPacked_occ_safe henv (hact (by assumption)).2.2
  · exact readPacked_quot_safe henv (hact (by assumption)).2.2
  · exact readPacked_val_safe henv (hact (by assumption)).2.2
  · exact readPacked_meta_safe henv (hact (by assumption)).2.2
  · exact fits_one_of_env henv
  · exact readPacked_occ_safe henv (hact (by assumption)).2.2
  · exact (hact (by assumption)).2.1
  · exact readPacked_quot_safe henv (hact (by assumption)).2.2
  · exact readPacked_val_safe henv (hact (by assumption)).2.2
  · exact readPacked_meta_safe henv (hact (by assumption)).2.2
  · exact (hact (by assumption)).2.1
  · exact fits_one_of_env henv

/-- Bounded bit-packed kick displacement loop executing `fuel` steps via `Realization.iterate`
(`fuel ≤ k + 1` per Section 3.1 / Theorem 2). -/
@[expose] def kickLoopIterGenProg : (KickStepEnv × KickStepState) × ℕ → Memory.Prog KickStepState
  | ((env, st), fuel) => iterate kickStepGenProg env fuel st

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `kickLoopIterGenProg`. -/
theorem realizes_kickLoopGen :
    Realizes .exact kickLoopIterGenProg
      (((appendWords (WordEncoding.encode (α := KickStepEnv))
        (WordEncoding.encode (α := KickStepState))).prodMap
          (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
            (Fin.appendEquiv _ 1).toEmbedding)
      (WordEncoding.encode (α := KickStepState))
      (fun w ((env, st), fuel) s =>
        iterationSafe kickStepGenProg KickStepSafe w env fuel st s)
      (fun ((env, st), fuel) s =>
        iterationWork kickStepGenProg (fun _ _ => 0) env fuel st s) :=
  Realizes.iterateRuntime (WordEncoding.encode (α := KickStepEnv))
    (WordEncoding.encode (α := KickStepState)) realizes_kickStepGen

/-- Bounded bit-packed kick loop starting from step `0` with active item `(quot, val, metaTag)`. -/
@[expose] def kickLoopProg (p : KickTreeParams) (base pathBase fuel quot val metaTag : ℕ) :
    Memory.Prog KickStepState :=
  kickLoopIterGenProg ((⟨mkKickRuntimeParams p, base, pathBase⟩, ⟨0, quot, val, metaTag, 1⟩), fuel)

private theorem not_in_quot_of_outside {p : KickTreeParams} {base a : ℕ}
    (ha : ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p)) :
    ¬(base + offQuot p ≤ a ∧ a < base + offQuot p + quotWords p) := by
  have hle := quot_end_le_totalSpace p
  unfold offQuot at hle ⊢; omega

private theorem not_in_val_of_outside {p : KickTreeParams} {base a : ℕ}
    (ha : ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p)) :
    ¬(base + offVal p ≤ a ∧ a < base + offVal p + valWords p) := by
  have hle := val_end_le_totalSpace p
  unfold offVal offQuot at hle ⊢; omega

private theorem not_in_occ_of_outside {p : KickTreeParams} {base a : ℕ}
    (ha : ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p)) :
    ¬(base + offOcc p ≤ a ∧ a < base + offOcc p + occWords p) := by
  have hle := occ_end_le_totalSpace p
  unfold offOcc offVal offQuot at hle ⊢; omega

private theorem not_in_meta_of_outside {p : KickTreeParams} {base a : ℕ}
    (ha : ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p)) :
    ¬(base + offMeta p ≤ a ∧ a < base + offMeta p + metaWords p) := by
  have hle := meta_end_le_totalSpace p
  unfold offMeta offOcc offVal offQuot at hle ⊢; omega

/-- When `st.active = 0`, `kickStepProg` is a no-op returning `st` and preserving `s`. -/
theorem kickStepProg_inactive_spec (p : KickTreeParams) {base pathBase : ℕ} {st : KickStepState}
    (hact : st.active = 0) (s : Memory.State) :
    (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) = st ∧
      (Memory.spec 0).clientState s (kickStepProg p base pathBase st) = s := by
  unfold kickStepProg kickStepGenProg
  dsimp only
  rw [ite_eq_right (by omega)]
  exact ⟨rfl, rfl⟩

/-- Pure array-update specification for `kickStepProg` when the candidate slot `slot` is vacant
(`occAt base p s.mem slot = 0`): places `(quot, val, metaTag)` into `slot`, sets
`occAt ... slot = 1`, frames memory outside `[base + p.hSpace, base + totalSpace p)`, and
terminates (`active = 0`). -/
theorem kickStepProg_vacant_spec (p : KickTreeParams) (hw : 0 < p.w) (hc : 1 ≤ p.cMeta)
    {base pathBase : ℕ} {st : KickStepState} {s : Memory.State}
    (hact : 0 < st.active)
    (hslot : s.mem (pathBase + st.stepIdx) < p.nMax)
    (hq : st.quot < 2 ^ fullQuotBits p.U p.nMax)
    (hv : st.val < 2 ^ valBits p.V)
    (hm : st.metaTag < 2 ^ metaBits p)
    (hvac : occAt base p s.mem (s.mem (pathBase + st.stepIdx)) = 0) :
    let slot := s.mem (pathBase + st.stepIdx)
    let s' := (Memory.spec 0).clientState s (kickStepProg p base pathBase st)
    (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
        ⟨st.stepIdx + 1, 0, 0, 0, 0⟩ ∧
      s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = Function.update (quotAt base p s.mem) slot st.quot ∧
      valAt base p s'.mem = Function.update (valAt base p s.mem) slot st.val ∧
      metaAt base p s'.mem = Function.update (metaAt base p s.mem) slot st.metaTag ∧
      occAt base p s'.mem = Function.update (occAt base p s.mem) slot 1 := by
  intro slot s'
  change slot < p.nMax at hslot
  change occAt base p s.mem slot = 0 at hvac
  have hocc_lt : slot < occLen p := slot_lt_occLen hslot
  have hmeta_lt : slot < metaLen p := slot_lt_metaLen hc hslot
  have hocc_read : readPacked (base + offOcc p) 1 p.w s.mem slot = 0 := by
    simpa [occAt, hocc_lt] using hvac
  set m1 := writeQuotMem base p s.mem slot st.quot
  set m2 := writeValMem base p m1 slot st.val
  set m3 := writeMetaMem base p m2 slot st.metaTag
  set m4 := writeOccMem base p m3 slot 1
  have hr_mem : (Memory.spec 0).clientState s (Memory.read (pathBase + st.stepIdx)) = s := rfl
  have hr_res : (Memory.spec 0).clientResult s (Memory.read (pathBase + st.stepIdx)) = slot := rfl
  have hres : (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
      ⟨st.stepIdx + 1, 0, 0, 0, 0⟩ := by
    unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    rw [ite_eq_left hact, StateTransitionSpec.clientResult_bind, hr_mem, hr_res,
      StateTransitionSpec.clientResult_bind, clientState_readPackedProg,
      clientResult_readPackedProg, hocc_read, ite_eq_left rfl]
    iterate 4 rw [StateTransitionSpec.clientResult_bind, clientState_writePackedProg]
    rfl
  have hst : s' = { mem := m4, frontier := s.frontier } := by
    change (Memory.spec 0).clientState s (kickStepProg p base pathBase st) = _
    unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    rw [ite_eq_left hact, StateTransitionSpec.clientState_bind, hr_mem, hr_res,
      StateTransitionSpec.clientState_bind, clientState_readPackedProg,
      clientResult_readPackedProg, hocc_read, ite_eq_left rfl]
    iterate 4 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
    rfl
  have heQ := writeQuotMem_effects (base := base) p hw s.mem hslot hq
  have heV := writeValMem_effects (base := base) p hw m1 hslot hv
  have heM := writeMetaMem_effects (base := base) p hw m2 hmeta_lt hm
  have heO := writeOccMem_effects (base := base) p hw m3 hocc_lt (by decide : 1 < 2 ^ 1)
  rw [hst]
  refine ⟨hres, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · exact (heO.2.2.2.2 a (not_in_occ_of_outside ha)).trans
      ((heM.2.2.2.2 a (not_in_meta_of_outside ha)).trans
        ((heV.2.2.2.2 a (not_in_val_of_outside ha)).trans
          (heQ.2.2.2.2 a (not_in_quot_of_outside ha))))
  · exact heO.1.trans (heM.1.trans (heV.1.trans heQ.1))
  · exact heO.2.1.trans (heM.2.1.trans (heV.2.1.trans (by rw [heQ.2.1])))
  · exact heO.2.2.2.1.trans (heM.2.2.2.1.trans (by rw [heV.2.2.2.1, heQ.2.2.2.1]))
  · exact heO.2.2.1.trans (by rw [heM.2.2.1, heV.2.2.1, heQ.2.2.1])

/-- Pure array-update specification for `kickStepProg` when the candidate slot `slot` is occupied
(`occAt base p s.mem slot ≠ 0`): atomically displaces `(oldQuot, oldVal, oldMeta)`, writes
`(quot, val, metaTag)` into `slot`, preserves `occAt` and memory outside
`[base + p.hSpace, base + totalSpace p)`, and advances to `stepIdx + 1` with `active = 1`. -/
theorem kickStepProg_displace_spec (p : KickTreeParams) (hw : 0 < p.w) (hc : 1 ≤ p.cMeta)
    {base pathBase : ℕ} {st : KickStepState} {s : Memory.State}
    (hact : 0 < st.active)
    (hslot : s.mem (pathBase + st.stepIdx) < p.nMax)
    (hq : st.quot < 2 ^ fullQuotBits p.U p.nMax)
    (hv : st.val < 2 ^ valBits p.V)
    (hm : st.metaTag < 2 ^ metaBits p)
    (hocc_ne : occAt base p s.mem (s.mem (pathBase + st.stepIdx)) ≠ 0) :
    let slot := s.mem (pathBase + st.stepIdx)
    let s' := (Memory.spec 0).clientState s (kickStepProg p base pathBase st)
    (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
        ⟨st.stepIdx + 1, quotAt base p s.mem slot, valAt base p s.mem slot,
          metaAt base p s.mem slot, 1⟩ ∧
      s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = Function.update (quotAt base p s.mem) slot st.quot ∧
      valAt base p s'.mem = Function.update (valAt base p s.mem) slot st.val ∧
      metaAt base p s'.mem = Function.update (metaAt base p s.mem) slot st.metaTag ∧
      occAt base p s'.mem = occAt base p s.mem := by
  intro slot s'
  change slot < p.nMax at hslot
  change occAt base p s.mem slot ≠ 0 at hocc_ne
  have hocc_lt : slot < occLen p := slot_lt_occLen hslot
  have hmeta_lt : slot < metaLen p := slot_lt_metaLen hc hslot
  have hocc_read : readPacked (base + offOcc p) 1 p.w s.mem slot ≠ 0 := by
    simpa [occAt, hocc_lt] using hocc_ne
  set m1 := writeQuotMem base p s.mem slot st.quot
  set m2 := writeValMem base p m1 slot st.val
  set m3 := writeMetaMem base p m2 slot st.metaTag
  have hr_mem : (Memory.spec 0).clientState s (Memory.read (pathBase + st.stepIdx)) = s := rfl
  have hr_res : (Memory.spec 0).clientResult s (Memory.read (pathBase + st.stepIdx)) = slot := rfl
  have hres : (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
      ⟨st.stepIdx + 1, quotAt base p s.mem slot, valAt base p s.mem slot,
        metaAt base p s.mem slot, 1⟩ := by
    unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    rw [ite_eq_left hact, StateTransitionSpec.clientResult_bind, hr_mem, hr_res,
      StateTransitionSpec.clientResult_bind, clientState_readPackedProg,
      clientResult_readPackedProg, ite_eq_right hocc_read]
    iterate 3 rw [StateTransitionSpec.clientResult_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    iterate 3 rw [StateTransitionSpec.clientResult_bind, clientState_writePackedProg]
    change KickStepState.mk _ _ _ _ _ = _
    simp [quotAt, valAt, metaAt, hslot, hmeta_lt]
  have hst : s' = { mem := m3, frontier := s.frontier } := by
    change (Memory.spec 0).clientState s (kickStepProg p base pathBase st) = _
    unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    rw [ite_eq_left hact, StateTransitionSpec.clientState_bind, hr_mem, hr_res,
      StateTransitionSpec.clientState_bind, clientState_readPackedProg,
      clientResult_readPackedProg, ite_eq_right hocc_read]
    iterate 3 rw [StateTransitionSpec.clientState_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    iterate 3 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
    rfl
  have heQ := writeQuotMem_effects (base := base) p hw s.mem hslot hq
  have heV := writeValMem_effects (base := base) p hw m1 hslot hv
  have heM := writeMetaMem_effects (base := base) p hw m2 hmeta_lt hm
  rw [hst]
  refine ⟨hres, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · exact (heM.2.2.2.2 a (not_in_meta_of_outside ha)).trans
      ((heV.2.2.2.2 a (not_in_val_of_outside ha)).trans
        (heQ.2.2.2.2 a (not_in_quot_of_outside ha)))
  · exact heM.1.trans (heV.1.trans heQ.1)
  · exact heM.2.1.trans (heV.2.1.trans (by rw [heQ.2.1]))
  · exact heM.2.2.2.1.trans (by rw [heV.2.2.2.1, heQ.2.2.2.1])
  · exact heM.2.2.1.trans (heV.2.2.1.trans heQ.2.2.1)

/-! ### 5. Bit-Packed Deletion Subroutine via Tail Replacement -/

/-- Input record for `deleteSlotGenProg`. -/
structure KickDeleteInput where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Primary slot index `slot < rp.nMax` being deleted. -/
  slot : ℕ
  /-- Tail slot index `tailSlot < rp.nMax` supplying the replacement item. -/
  tailSlot : ℕ

/-- Tuple equivalence for `KickDeleteInput` used by `WordEncoding.ofEquiv`. -/
@[expose] def KickDeleteInput.equiv :
    KickDeleteInput ≃ ((KickRuntimeParams × ℕ) × ℕ) × ℕ where
  toFun d := (((d.rp, d.base), d.slot), d.tailSlot)
  invFun := fun (((rp, base), slot), tailSlot) => ⟨rp, base, slot, tailSlot⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickDeleteInput := .ofEquiv KickDeleteInput.equiv

/-- Parameter-free bit-packed deletion subroutine implementing non-hash tail replacement
([BenderFarachColtonKuszmaulKuszmaulLiu2022], Section 5.2 / `Facility.tailReplace`).
Copies `(quot, val, meta, occ)` from `tailSlot` to `slot` and then clears all four bit-packed
fields (including `occ := 0`) at `tailSlot`, cleanly handling both `slot ≠ tailSlot` and
self-deletion `slot = tailSlot`. -/
@[expose] def deleteSlotGenProg (d : KickDeleteInput) : Memory.Prog Unit := do
  let tailQuot ← readPackedGenProg (((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.tailSlot)
  let tailVal ← readPackedGenProg (((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.tailSlot)
  let tailMeta ← readPackedGenProg (((d.base, d.rp.offMeta), (d.rp.metaBits, d.rp.w)), d.tailSlot)
  let tailOcc ← readPackedGenProg (((d.base, d.rp.offOcc), (1, d.rp.w)), d.tailSlot)
  writePackedGenProg ((((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.slot), tailQuot)
  writePackedGenProg ((((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.slot), tailVal)
  writePackedGenProg ((((d.base, d.rp.offMeta), (d.rp.metaBits, d.rp.w)), d.slot), tailMeta)
  writePackedGenProg ((((d.base, d.rp.offOcc), (1, d.rp.w)), d.slot), tailOcc)
  writePackedGenProg ((((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.tailSlot), 0)
  writePackedGenProg ((((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.tailSlot), 0)
  writePackedGenProg ((((d.base, d.rp.offMeta), (d.rp.metaBits, d.rp.w)), d.tailSlot), 0)
  writePackedGenProg ((((d.base, d.rp.offOcc), (1, d.rp.w)), d.tailSlot), 0)

/-- Typed wrapper for `deleteSlotGenProg`. -/
@[expose] def deleteSlotProg (p : KickTreeParams) (base slot tailSlot : ℕ) : Memory.Prog Unit :=
  deleteSlotGenProg ⟨mkKickRuntimeParams p, base, slot, tailSlot⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `deleteSlotGenProg`. -/
theorem realizes_deleteSlotGen :
    Realizes .exact deleteSlotGenProg
      (WordEncoding.encode (α := KickDeleteInput))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax ∧ d.tailSlot < d.rp.nMax)
      (fun _ _ => 0) := by
  realize [realizes_readPackedGen, realizes_writePackedGen]
  · exact readPacked_quot_safe h.1 h.2.2
  · exact readPacked_val_safe h.1 h.2.2
  · exact readPacked_meta_safe h.1 h.2.2
  · exact fits_one_of_env h.1
  · exact readPacked_occ_safe h.1 h.2.2
  · exact readPacked_quot_safe h.1 h.2.1
  · exact readPacked_val_safe h.1 h.2.1
  · exact readPacked_meta_safe h.1 h.2.1
  · exact readPacked_occ_safe h.1 h.2.1

/-- Exact pure array-update specification for `deleteSlotProg` (valid for both `slot ≠ tailSlot`
and `slot = tailSlot`): copies `tailSlot`'s fields to `slot` and clears `tailSlot` (including
`occAt base p s'.mem tailSlot = 0`, so reclaimed or self-deleted tail slots return `none` under
`querySlotProg` for every key, including quotient `0`). -/
theorem deleteSlotProg_spec (p : KickTreeParams) (hw : 0 < p.w) (hc : 1 ≤ p.cMeta)
    {base slot tailSlot : ℕ} (hslot : slot < p.nMax) (htail : tailSlot < p.nMax)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (deleteSlotProg p base slot tailSlot)
    s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem =
        Function.update
          (Function.update (quotAt base p s.mem) slot (quotAt base p s.mem tailSlot))
          tailSlot 0 ∧
      valAt base p s'.mem =
        Function.update
          (Function.update (valAt base p s.mem) slot (valAt base p s.mem tailSlot))
          tailSlot 0 ∧
      metaAt base p s'.mem =
        Function.update
          (Function.update (metaAt base p s.mem) slot (metaAt base p s.mem tailSlot))
          tailSlot 0 ∧
      occAt base p s'.mem =
        Function.update
          (Function.update (occAt base p s.mem) slot (occAt base p s.mem tailSlot))
          tailSlot 0 := by
  intro s'
  have hsO : slot < occLen p := slot_lt_occLen hslot
  have htO : tailSlot < occLen p := slot_lt_occLen htail
  have hsM : slot < metaLen p := slot_lt_metaLen hc hslot
  have htM : tailSlot < metaLen p := slot_lt_metaLen hc htail
  have hq_eq : readPacked (base + offQuot p) (fullQuotBits p.U p.nMax) p.w s.mem tailSlot =
      quotAt base p s.mem tailSlot := by simp [quotAt, htail]
  have hv_eq : readPacked (base + offVal p) (valBits p.V) p.w s.mem tailSlot =
      valAt base p s.mem tailSlot := by simp [valAt, htail]
  have hm_eq : readPacked (base + offMeta p) (metaBits p) p.w s.mem tailSlot =
      metaAt base p s.mem tailSlot := by simp [metaAt, htM]
  have ho_eq : readPacked (base + offOcc p) 1 p.w s.mem tailSlot =
      occAt base p s.mem tailSlot := by simp [occAt, htO]
  set m1 := writeQuotMem base p s.mem slot (quotAt base p s.mem tailSlot)
  set m2 := writeValMem base p m1 slot (valAt base p s.mem tailSlot)
  set m3 := writeMetaMem base p m2 slot (metaAt base p s.mem tailSlot)
  set m4 := writeOccMem base p m3 slot (occAt base p s.mem tailSlot)
  set m5 := writeQuotMem base p m4 tailSlot 0
  set m6 := writeValMem base p m5 tailSlot 0
  set m7 := writeMetaMem base p m6 tailSlot 0
  set m8 := writeOccMem base p m7 tailSlot 0
  have hst : s' = { mem := m8, frontier := s.frontier } := by
    change (Memory.spec 0).clientState s (deleteSlotProg p base slot tailSlot) = _
    unfold deleteSlotProg deleteSlotGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    iterate 4 rw [StateTransitionSpec.clientState_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    rw [hq_eq, hv_eq, hm_eq, ho_eq]
    iterate 7 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
    rw [clientState_writePackedProg]
    rfl
  have hq_lt := quotAt_lt base p s.mem tailSlot
  have hv_lt := valAt_lt base p s.mem tailSlot
  have hm_lt := metaAt_lt base p s.mem tailSlot
  have ho_lt := occAt_lt base p s.mem tailSlot
  have he1 := writeQuotMem_effects (base := base) p hw s.mem hslot hq_lt
  have he2 := writeValMem_effects (base := base) p hw m1 hslot hv_lt
  have he3 := writeMetaMem_effects (base := base) p hw m2 hsM hm_lt
  have he4 := writeOccMem_effects (base := base) p hw m3 hsO ho_lt
  have he5 := writeQuotMem_effects (base := base) p hw m4 htail (by positivity)
  have he6 := writeValMem_effects (base := base) p hw m5 htail (by positivity)
  have he7 := writeMetaMem_effects (base := base) p hw m6 htM (by positivity)
  have he8 := writeOccMem_effects (base := base) p hw m7 htO (by positivity)
  rw [hst]
  refine ⟨rfl, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · have hoQ := not_in_quot_of_outside ha
    have hoV := not_in_val_of_outside ha
    have hoM := not_in_meta_of_outside ha
    have hoO := not_in_occ_of_outside ha
    exact (he8.2.2.2.2 a hoO).trans
      ((he7.2.2.2.2 a hoM).trans
        ((he6.2.2.2.2 a hoV).trans
          ((he5.2.2.2.2 a hoQ).trans
            ((he4.2.2.2.2 a hoO).trans
              ((he3.2.2.2.2 a hoM).trans
                ((he2.2.2.2.2 a hoV).trans (he1.2.2.2.2 a hoQ)))))))
  · rw [he8.1, he7.1, he6.1, he5.1, he4.1, he3.1, he2.1, he1.1]
  · rw [he8.2.1, he7.2.1, he6.2.1, he5.2.1, he4.2.1, he3.2.1, he2.2.1, he1.2.1]
  · rw [he8.2.2.2.1, he7.2.2.2.1, he6.2.2.2.1, he5.2.2.2.1,
      he4.2.2.2.1, he3.2.2.2.1, he2.2.2.2.1, he1.2.2.2.1]
  · rw [he8.2.2.1, he7.2.2.1, he6.2.2.1, he5.2.2.1,
      he4.2.2.1, he3.2.2.1, he2.2.2.1, he1.2.2.1]

end Cslib.DataStructure.Dictionary.WordRAM.KickTree
