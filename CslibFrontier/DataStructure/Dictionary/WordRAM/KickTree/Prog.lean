/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArrayProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.KickTree.Layout
import CslibFrontier.Tactic.Realize

/-!
# Bit-Packed Word-RAM `Memory.Prog` Subroutines and Realizations for `k`-Kick Tree Slots

This module implements bit-packed Word-RAM `Memory.Prog` slot subroutines over the parameterized
`Layout.lean` arrays (`Quotients`, `Values`, `Occupancy`, `Elevated`, `SlotMeta`), certifies each
subroutine with a uniform width-free `Realizes .exact` (`¬ReadsWidth`) certificate via `realize`,
and proves exact pure array-level specifications:

1. **Zeroed Table Allocation (`allocKickTableGenProg`, `allocKickTableProg`)**: allocates
   `totalSpace p` zeroed words at the memory frontier, frames memory outside `[base, base +
   totalSpace p)`, zeroes `[base, base + totalSpace p)`, and establishes `quotAt = 0`, `valAt = 0`,
   `occAt = 0`, `elevAt = 0`, and `metaAt = 0` (`allocKickTableProg_spec`).
2. **Bit-Packed Slot Query (`querySlotGenProg`, `querySlotProg`)**: inspects 1-bit `Occupancy`
   before comparing `Quotients[slot]` against target quotient `q`, returning `Option ℕ` (`some val`
   on a hit, `none` on an empty or mismatched slot so stored value `0` and `none` stay distinct;
   `querySlotProg_spec`).
3. **Bit-Packed Sparse `SlotMeta` Accessors (`readMetaGenProg`, `readMetaProg`, `writeMetaGenProg`,
   `writeMetaProg`)**: bit-packed `metaBits p`-wide reads and writes into `SlotMeta[idx]` (`idx <
   metaLen p`) for sparse auxiliary bin/router/cubby metadata (`readMetaProg_spec`,
   `writeMetaProg_spec`).
4. **Bounded Bit-Packed Kick Displacement Loop (`kickStepGenProg`, `kickLoopIterGenProg`,
   `kickLoopProg`)**: steps along a caller-supplied switching-path buffer `[pathBase, pathBase +
   p.kickLimit)` using `Realization.iterate` (`p.kickLimit = k + 1` per Section 3.1 / Theorem 2),
   checking vacancy via 1-bit `Occupancy` (so zero quotients are preserved) and displacing
   `(quot, val, elevated)` atomically using the local formalization adaptation's 1-bit per-slot
   `Elevated` indicator (`elevated < 2 ^ 1`, preserving priority-depth status under kicks without
   multi-bit tag truncation; `kickStepProg_vacant_spec`, `kickStepProg_displace_spec`,
   `kickStepProg_inactive_spec`, `kickLoopProg_spec`, `validHistory_kickStepProg`,
   `validHistory_kickLoopProg`).
5. **Bit-Packed Slot Vacating & Unindexed Tail-Cubby Compaction (`clearSlotGenProg`,
   `clearSlotProg`, `popUnindexedSlotGenProg`, `popUnindexedSlotProg`)**: for Section 5.2 deletion,
   `clearSlotProg` vacates a deleted slot in a hashed kick-tree without overwriting hashed bins in
   place (`clearSlotProg_spec`), while `popUnindexedSlotProg` is a local formalization adaptation
   that pops and swap-compacts an item from an unindexed `[0, len)` tail-cubby slot array
   (`Facility.TailCubby`, reusing `clearSlotGenProg` to clear `lastSlot` and handling both
   `slot ≠ lastSlot` and `slot = lastSlot`) and returns its `((quot, val), elevated)` payload for
   subsequent `kickLoopProg` re-insertion (`popUnindexedSlotProg_spec`).

## Source attribution and formalization adaptations

* **Primary source** — [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 3.1 (printed pp. 8–12 / PDF pp. 9–13) and Theorem 2 (printed p. 12 / PDF p. 13):
    `k`-kick tree priority displacement chains of length at most `k + 1` and kick-depth invariance.
  - Section 5.1–5.2 (printed pp. 27–32 / PDF pp. 28–33): occupancy/free-slot bitmaps, sparse
    `SlotMeta` (`O(n_max log^(k + 1) n_max)` bits), and full-cubby deletion refilled by popping an
    item from a tail cubby.
  - Section 5.3 and Theorem 21 (printed pp. 33–35 / PDF pp. 34–36): bit-packed quotiented slot
    payloads (`quotAt`, `valAt`, `querySlotGenProg`).
* **Local formalization adaptations**:
  - Dedicated 1-bit per-slot `Elevated` (`depth ≥ 1`) bitmap (`elevAt`, `KickStepState.elevated`)
    carried across displacements to track elevated priority status per primary slot alongside
    sparse `SlotMeta`.
  - Unindexed `[0, len)` swap-compacted tail-cubby array (`popUnindexedSlotGenProg`,
    `popUnindexedSlotProg`), pairing `Facility.TailCubby` with `clearSlotProg` and `kickLoopProg`
    re-insertion.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickRuntimeParams`, `mkKickRuntimeParams`,
  `KickEnv`, `KickEnvGen`: 12-word runtime layout parameter record and safety envelope.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.allocKickTableGenProg`, `allocKickTableProg`:
  zeroed `totalSpace` block allocation.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickQueryInput`, `querySlotGenProg`,
  `querySlotProg`: bit-packed slot lookup returning `Option ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickMetaReadInput`, `readMetaGenProg`,
  `readMetaProg`, `KickMetaWriteInput`, `writeMetaGenProg`, `writeMetaProg`: bit-packed sparse
  `SlotMeta` accessors.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickStepEnv`, `KickStepState`,
  `kickStepGenProg`, `kickStepProg`, `kickLoopIterGenProg`, `kickLoopProg`: bounded bit-packed
  switching-path displacement step and `p.kickLimit`-bounded `iterate` loop.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickClearInput`, `clearSlotGenProg`,
  `clearSlotProg`, `KickPopInput`, `popUnindexedSlotGenProg`, `popUnindexedSlotProg`: bit-packed
  hashed-slot clear and unindexed tail-cubby pop/compaction subroutines.

## Main results

* `allocKickTableProg_spec`, `validHistory_allocKickTableProg`, `memoryCost_allocKickTableProg`,
  `realizes_allocKickTableGen`: zero-initialized array and frame specification, admissibility,
  memory charge, and `Realizes .exact` certificate for `allocKickTableGenProg`.
* `querySlotProg_spec`, `validHistory_querySlotProg`, `memoryCost_querySlotProg_le`,
  `realizes_querySlotGen`: `Option ℕ` lookup specification, admissibility, memory-charge bound, and
  `Realizes .exact` certificate for `querySlotGenProg`.
* `readMetaProg_spec`, `validHistory_readMetaProg`, `memoryCost_readMetaProg`,
  `realizes_readMetaGen`, `writeMetaProg_spec`, `validHistory_writeMetaProg`,
  `memoryCost_writeMetaProg`, `realizes_writeMetaGen`: `SlotMeta` accessor specifications,
  admissibility, memory charges, and `Realizes .exact` certificates.
* `kickStepProg_inactive_spec`, `kickStepProg_vacant_spec`, `kickStepProg_displace_spec`,
  `validHistory_kickStepProg`, `memoryCost_kickStepProg_le`, `kickLoopProg_spec`,
  `validHistory_kickLoopProg`, `memoryCost_kickLoopProg_le`, `realizes_kickStepGen`,
  `realizes_kickLoopGen`: pure array-update and parametric bounded-loop specifications,
  admissibility, memory-charge bounds, and `Realizes .exact` certificates for `kickStepGenProg` and
  `kickLoopIterGenProg`.
* `clearSlotProg_spec`, `validHistory_clearSlotProg`, `memoryCost_clearSlotProg`,
  `realizes_clearSlotGen`, `popUnindexedSlotProg_spec`, `validHistory_popUnindexedSlotProg`,
  `memoryCost_popUnindexedSlotProg`, `realizes_popUnindexedSlotGen`: pure array-update
  specifications, admissibility, memory charges, and `Realizes .exact` certificates for
  `clearSlotGenProg` and `popUnindexedSlotGenProg`.

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

/-! ### 1. Runtime layout parameter record and safety envelope -/

/-- 12-word precomputed runtime parameter record for bit-packed kick-tree `Memory.Prog` methods. -/
structure KickRuntimeParams where
  /-- Machine word width `w`. -/
  w : ℕ
  /-- Primary slot capacity `nMax`. -/
  nMax : ℕ
  /-- Word offset `offQuot p`. -/
  offQuot : ℕ
  /-- Quotient bit width `quotBits p`. -/
  quotBits : ℕ
  /-- Word offset `offVal p`. -/
  offVal : ℕ
  /-- Value bit width `valBits p.V`. -/
  valBits : ℕ
  /-- Word offset `offOcc p`. -/
  offOcc : ℕ
  /-- Word offset `offElev p`. -/
  offElev : ℕ
  /-- Word offset `offMeta p`. -/
  offMeta : ℕ
  /-- Metadata bit width `metaBits p`. -/
  metaBits : ℕ
  /-- Metadata entry count `metaLen p`. -/
  metaLen : ℕ
  /-- Total word footprint `totalSpace p`. -/
  totalSpace : ℕ
deriving Repr, DecidableEq

/-- Tuple equivalence for `KickRuntimeParams` used by `WordEncoding.ofEquiv`. -/
def KickRuntimeParams.equiv :
    KickRuntimeParams ≃
      ((((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun r :=
    (((((((((((r.w, r.nMax), r.offQuot), r.quotBits), r.offVal), r.valBits),
      r.offOcc), r.offElev), r.offMeta), r.metaBits), r.metaLen), r.totalSpace)
  invFun := fun (((((((((((w, nMax), oQ), qB), oV), vB), oO), oE), oM), mB), mL), tot) =>
    ⟨w, nMax, oQ, qB, oV, vB, oO, oE, oM, mB, mL, tot⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickRuntimeParams := .ofEquiv KickRuntimeParams.equiv

private theorem fits_encode_nat {w x : ℕ} (hx : Fits w x) :
    ∀ i, Fits w (WordEncoding.encode x i) :=
  fun _ => hx

private theorem fits_encode_prod {α β : Type} [WordEncoding α] [WordEncoding β]
    {w : ℕ} {a : α} {b : β}
    (ha : ∀ i, Fits w (WordEncoding.encode a i))
    (hb : ∀ j, Fits w (WordEncoding.encode b j)) :
    ∀ k, Fits w (WordEncoding.encode (a, b) k) :=
  Fin.addCases
    (fun i => by
      change Fits w
        (Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.castAdd _ i))
      simpa only [Fin.append_left] using ha i)
    (fun j => by
      change Fits w
        (Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.natAdd _ j))
      simpa only [Fin.append_right] using hb j)

/-- Populate `KickRuntimeParams` from a layout configuration `p : KickTreeParams`. -/
@[expose] def mkKickRuntimeParams (p : KickTreeParams) : KickRuntimeParams where
  w := p.w
  nMax := p.nMax
  offQuot := offQuot p
  quotBits := quotBits p
  offVal := offVal p
  valBits := valBits p.V
  offOcc := offOcc p
  offElev := offElev p
  offMeta := offMeta p
  metaBits := metaBits p
  metaLen := metaLen p
  totalSpace := totalSpace p

/-- Word-width, bit-width, and address-fit invariant for `p` at `base`. -/
@[expose] def KickEnv (p : KickTreeParams) (w' base : ℕ) : Prop :=
  w' = p.w ∧
    0 < p.w ∧
    quotBits p ≤ p.w ∧
    valBits p.V ≤ p.w ∧
    metaBits p ≤ p.w ∧
    Fits p.w (base + totalSpace p)

/-- Parameter-free runtime envelope pairing `rp : KickRuntimeParams` with `KickTreeParams`. -/
@[expose] def KickEnvGen (w' : ℕ) (rp : KickRuntimeParams) (base : ℕ) : Prop :=
  ∃ p : KickTreeParams, rp = mkKickRuntimeParams p ∧ KickEnv p w' base

/-- Every encoded word of `mkKickRuntimeParams p` fits in `w` bits under `KickEnv p w base`,
`Fits w p.nMax`, and `Fits w (metaLen p)`. -/
theorem fits_encode_mkKickRuntimeParams {w base : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) (hn : Fits w p.nMax) (hm : Fits w (metaLen p)) :
    ∀ i, Fits w (WordEncoding.encode (mkKickRuntimeParams p) i) := by
  obtain ⟨rfl, _, hq, hv, hmb, hfit⟩ := henv
  have hw_fit : Fits p.w p.w := Nat.lt_two_pow_self
  have hQ := quot_end_le_totalSpace p
  have hV := val_end_le_totalSpace p
  have hO := occ_end_le_totalSpace p
  have hE := elev_end_le_totalSpace p
  have hM := meta_end_le_totalSpace p
  change ∀ i, Fits p.w (WordEncoding.encode (KickRuntimeParams.equiv (mkKickRuntimeParams p)) i)
  dsimp [KickRuntimeParams.equiv, mkKickRuntimeParams]
  refine fits_encode_prod (fits_encode_prod (fits_encode_prod (fits_encode_prod
    (fits_encode_prod (fits_encode_prod (fits_encode_prod (fits_encode_prod
      (fits_encode_prod (fits_encode_prod (fits_encode_prod
        (fits_encode_nat hw_fit) (fits_encode_nat hn))
        (fits_encode_nat (hfit.of_le (by omega))))
        (fits_encode_nat (hw_fit.of_le hq)))
        (fits_encode_nat (hfit.of_le (by omega))))
        (fits_encode_nat (hw_fit.of_le hv)))
        (fits_encode_nat (hfit.of_le (by omega))))
        (fits_encode_nat (hfit.of_le (by omega))))
        (fits_encode_nat (hfit.of_le (by omega))))
        (fits_encode_nat (hw_fit.of_le hmb)))
        (fits_encode_nat hm))
        (fits_encode_nat (hfit.of_le (by omega)))

private theorem fits_one_of_pos {w : ℕ} (hw : 0 < w) : Fits w 1 :=
  Nat.one_lt_two_pow (by omega)

private theorem fits_one_of_env {w' base : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) : Fits w' 1 := by
  obtain ⟨_, _, rfl, hw, _⟩ := henv
  exact fits_one_of_pos hw

private theorem slot_lt_occLen {p : KickTreeParams} {slot : ℕ} (hs : slot < p.nMax) :
    slot < occLen p := by
  unfold occLen; omega

private theorem readPacked_quot_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ rp.quotBits ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offQuot + packedWords N rp.quotBits w') := by
  obtain ⟨p, rfl, rfl, hw, hq, _, _, hfit⟩ := henv
  refine ⟨p.nMax, rfl, hw, hq, hslot, hfit.of_le ?_⟩
  have := quot_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, quotWords] at this ⊢
  omega

private theorem readPacked_val_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ rp.valBits ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offVal + packedWords N rp.valBits w') := by
  obtain ⟨p, rfl, rfl, hw, _, hv, _, hfit⟩ := henv
  refine ⟨p.nMax, rfl, hw, hv, hslot, hfit.of_le ?_⟩
  have := val_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, valWords] at this ⊢
  omega

private theorem readPacked_occ_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ 1 ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offOcc + packedWords N 1 w') := by
  obtain ⟨p, rfl, rfl, hw, _, _, _, hfit⟩ := henv
  refine ⟨occLen p, rfl, hw, hw, slot_lt_occLen hslot, hfit.of_le ?_⟩
  have := occ_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, occWords] at this ⊢
  omega

private theorem readPacked_elev_safe {w' base slot : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hslot : slot < rp.nMax) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ 1 ≤ w' ∧ slot < N ∧
      Fits w' (base + rp.offElev + packedWords N 1 w') := by
  obtain ⟨p, rfl, rfl, hw, _, _, _, hfit⟩ := henv
  refine ⟨p.nMax, rfl, hw, hw, hslot, hfit.of_le ?_⟩
  have := elev_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, elevWords] at this ⊢
  omega

private theorem readPacked_meta_safe {w' base idx : ℕ} {rp : KickRuntimeParams}
    (henv : KickEnvGen w' rp base) (hidx : idx < rp.metaLen) :
    ∃ N, w' = rp.w ∧ 0 < w' ∧ rp.metaBits ≤ w' ∧ idx < N ∧
      Fits w' (base + rp.offMeta + packedWords N rp.metaBits w') := by
  obtain ⟨p, rfl, rfl, hw, _, _, hm, hfit⟩ := henv
  refine ⟨metaLen p, rfl, hw, hm, hidx, hfit.of_le ?_⟩
  have := meta_end_le_totalSpace p
  dsimp [mkKickRuntimeParams, metaWords] at this ⊢
  omega

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

private theorem not_in_elev_of_outside {p : KickTreeParams} {base a : ℕ}
    (ha : ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p)) :
    ¬(base + offElev p ≤ a ∧ a < base + offElev p + elevWords p) := by
  have hle := elev_end_le_totalSpace p
  unfold offElev offOcc offVal offQuot at hle ⊢; omega

private theorem not_in_meta_of_outside {p : KickTreeParams} {base a : ℕ}
    (ha : ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p)) :
    ¬(base + offMeta p ≤ a ∧ a < base + offMeta p + metaWords p) := by
  have hle := meta_end_le_totalSpace p
  unfold offMeta offElev offOcc offVal offQuot at hle ⊢; omega

/-! ### 2. Zeroed Table Allocation Subroutine -/

/-- Parameter-free `Memory.Prog` subroutine allocating `rp.totalSpace` zeroed words. -/
def allocKickTableGenProg (rp : KickRuntimeParams) : Memory.Prog ℕ :=
  Memory.alloc rp.totalSpace

/-- Allocate `totalSpace p` zeroed words for `p : KickTreeParams`. -/
abbrev allocKickTableProg (p : KickTreeParams) : Memory.Prog ℕ :=
  allocKickTableGenProg (mkKickRuntimeParams p)

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `allocKickTableGenProg`. -/
theorem realizes_allocKickTableGen :
    Realizes .exact allocKickTableGenProg
      (WordEncoding.encode (α := KickRuntimeParams))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold allocKickTableGenProg
  realize

/-- Admissible memory history for `allocKickTableProg` when `s.frontier + totalSpace p` fits in
`w` bits. -/
theorem validHistory_allocKickTableProg {w : ℕ} (p : KickTreeParams) {s : Memory.State}
    (hfit : Fits w (s.frontier + totalSpace p)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (allocKickTableProg p)) :=
  ⟨hfit, trivial⟩

/-- Exact memory charge of `allocKickTableProg` (`totalSpace p + 1`). -/
theorem memoryCost_allocKickTableProg (p : KickTreeParams) (s : Memory.State) :
    memoryCost (allocKickTableProg p) s = totalSpace p + 1 := by
  unfold allocKickTableProg allocKickTableGenProg
  exact Nat.add_zero _

/-- Allocating a kick-tree table returns `base = s.frontier`, advances the frontier by
`totalSpace p`, zeroes `[base, base + totalSpace p)`, frames memory outside `[base, base +
totalSpace p)`, and zero-initializes all five bit-packed arrays (`quotAt`, `valAt`, `occAt`,
`elevAt`, `metaAt`). -/
theorem allocKickTableProg_spec (p : KickTreeParams) (hw : 0 < p.w) (s : Memory.State) :
    let base := (Memory.spec 0).clientResult s (allocKickTableProg p)
    let s' := (Memory.spec 0).clientState s (allocKickTableProg p)
    base = s.frontier ∧
      s'.frontier = s.frontier + totalSpace p ∧
      (∀ a, base ≤ a ∧ a < base + totalSpace p → s'.mem a = 0) ∧
      (∀ a, ¬(base ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = (fun _ => 0) ∧
      valAt base p s'.mem = (fun _ => 0) ∧
      occAt base p s'.mem = (fun _ => 0) ∧
      elevAt base p s'.mem = (fun _ => 0) ∧
      metaAt base p s'.mem = (fun _ => 0) := by
  have hzero_all : ∀ a, s.frontier ≤ a ∧ a < s.frontier + totalSpace p →
      clear s.mem s.frontier (totalSpace p) a = 0 := fun a ⟨ha1, ha2⟩ =>
    clear_of_owns ⟨ha1, ha2⟩
  have hout_all : ∀ a, ¬(s.frontier ≤ a ∧ a < s.frontier + totalSpace p) →
      clear s.mem s.frontier (totalSpace p) a = s.mem a := fun a ha =>
    clear_of_not_owns ha
  have hzero : ∀ a, s.frontier + p.hSpace ≤ a → a < s.frontier + totalSpace p →
      clear s.mem s.frontier (totalSpace p) a = 0 := fun a ha1 ha2 =>
    hzero_all a ⟨by omega, ha2⟩
  exact ⟨rfl, rfl, hzero_all, hout_all,
    quotAt_zero_of_init p hw hzero,
    valAt_zero_of_init p hw hzero,
    occAt_zero_of_init p hw hzero,
    elevAt_zero_of_init p hw hzero,
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
def KickQueryInput.equiv :
    KickQueryInput ≃ ((KickRuntimeParams × ℕ) × ℕ) × ℕ where
  toFun d := (((d.rp, d.base), d.slot), d.q)
  invFun := fun (((rp, base), slot), q) => ⟨rp, base, slot, q⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickQueryInput := .ofEquiv KickQueryInput.equiv

/-- Every encoded word of `d : KickQueryInput` fits in `w` bits when its fields do. -/
theorem fits_encode_kickQueryInput {w : ℕ} {d : KickQueryInput}
    (hrp : ∀ i, Fits w (WordEncoding.encode d.rp i))
    (hbase : Fits w d.base) (hslot : Fits w d.slot) (hq : Fits w d.q) :
    ∀ i, Fits w (WordEncoding.encode d i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickQueryInput.equiv d) i)
  dsimp only [KickQueryInput.equiv]
  exact fits_encode_prod (fits_encode_prod (fits_encode_prod hrp
    (fits_encode_nat hbase)) (fits_encode_nat hslot)) (fits_encode_nat hq)

/-- Parameter-free bit-packed slot lookup returning `Option ℕ`. Checks `Occupancy[slot]` first so
that an empty slot (`none`) and a stored value `0` (`some 0`, even at quotient `0`) are distinct. -/
def querySlotGenProg (d : KickQueryInput) : Memory.Prog (Option ℕ) := do
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
abbrev querySlotProg (p : KickTreeParams) (base slot q : ℕ) : Memory.Prog (Option ℕ) :=
  querySlotGenProg ⟨mkKickRuntimeParams p, base, slot, q⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `querySlotGenProg`. -/
theorem realizes_querySlotGen :
    Realizes .exact querySlotGenProg
      (WordEncoding.encode (α := KickQueryInput))
      (WordEncoding.encode (α := Option ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax)
      (fun _ _ => 0) := by
  unfold querySlotGenProg
  realize [realizes_readPackedGen]
  · exact fits_one_of_env h.1
  · exact readPacked_occ_safe h.1 h.2
  · exact readPacked_quot_safe h.1 h.2
  · exact readPacked_val_safe h.1 h.2
  · exact fits_one_of_env h.1

private theorem array_ends_le_frontier {base frontier : ℕ} (p : KickTreeParams)
    (ha : base + totalSpace p ≤ frontier) :
    base + offQuot p + packedWords p.nMax (quotBits p) p.w ≤ frontier ∧
      base + offVal p + packedWords p.nMax (valBits p.V) p.w ≤ frontier ∧
      base + offElev p + packedWords p.nMax 1 p.w ≤ frontier ∧
      base + offOcc p + packedWords (occLen p) 1 p.w ≤ frontier := by
  have hq := quot_end_le_totalSpace p; dsimp [quotWords] at hq
  have hv := val_end_le_totalSpace p; dsimp [valWords] at hv
  have he := elev_end_le_totalSpace p; dsimp [elevWords] at he
  have ho := occ_end_le_totalSpace p; dsimp [occWords] at ho
  omega

private theorem validHistory_readPackedProg_bind {α : Type} {base off len k w idx : ℕ}
    {f : ℕ → Memory.Prog α} {s : Memory.State} (hw : 0 < w) (hidx : idx < len)
    (ha : base + off + packedWords len k w ≤ s.frontier)
    (hk : ∀ r, (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (f r))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readPackedProg base off k w idx >>= f)) := by
  rw [validHistory_bind']
  refine ⟨validHistory_readPackedProg hw hidx ha, ?_⟩
  rw [clientState_readPackedProg]
  exact hk _

private theorem validHistory_writePackedProg_bind {α : Type} {base off len k w idx val : ℕ}
    {f : Unit → Memory.Prog α} {s : Memory.State} (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < len)
    (hwf : Memory.WellFormed w s) (ha : base + off + packedWords len k w ≤ s.frontier)
    (hk : ∀ s' : Memory.State, Memory.WellFormed w s' → s'.frontier = s.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (f ()))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writePackedProg base off k w idx val >>= f)) := by
  rw [validHistory_bind']
  exact ⟨validHistory_writePackedProg hw hkw hidx hwf ha,
    hk _ (BitPackedArray.wellFormed_clientState_writePackedProg hw hkw hwf) rfl⟩

/-- Admissible memory history for `querySlotProg` when `[base, base + totalSpace p)` lies below
`s.frontier`. -/
theorem validHistory_querySlotProg {w base slot q : ℕ} (p : KickTreeParams)
    (hw_eq : w = p.w) (hw : 0 < p.w) (hslot : slot < p.nMax) {s : Memory.State}
    (ha : base + totalSpace p ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (querySlotProg p base slot q)) := by
  subst hw_eq
  obtain ⟨hQ, hV, _, hO⟩ := array_ends_le_frontier p ha
  unfold querySlotProg querySlotGenProg readPackedGenProg
  dsimp only [mkKickRuntimeParams]
  refine validHistory_readPackedProg_bind hw (slot_lt_occLen hslot) hO fun _ => ?_
  split_ifs
  · trivial
  · refine validHistory_readPackedProg_bind hw hslot hQ fun _ => ?_
    split_ifs
    · exact validHistory_readPackedProg_bind hw hslot hV fun _ => trivial
    · trivial

/-- `querySlotProg` issues at most three bit-packed reads (`memoryCost ≤ 6`). -/
theorem memoryCost_querySlotProg_le (p : KickTreeParams) (base slot q : ℕ) (s : Memory.State) :
    memoryCost (querySlotProg p base slot q) s ≤ 6 := by
  unfold querySlotProg querySlotGenProg readPackedGenProg
  dsimp only [mkKickRuntimeParams]
  rw [memoryCost_bind', memoryCost_readPackedProg, clientState_readPackedProg]
  split_ifs
  · simp only [memoryCost_pure]; omega
  · rw [memoryCost_bind', memoryCost_readPackedProg, clientState_readPackedProg]
    split_ifs
    · rw [memoryCost_bind', memoryCost_readPackedProg, memoryCost_pure]
    · simp only [memoryCost_pure]; omega

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
    have hq : readPacked (base + offQuot p) (quotBits p) p.w s.mem slot =
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

/-! ### 4. Bit-Packed Sparse `SlotMeta` Accessors -/

/-- Input record for `readMetaGenProg`. -/
structure KickMetaReadInput where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Metadata index `idx < rp.metaLen`. -/
  idx : ℕ

/-- Tuple equivalence for `KickMetaReadInput` used by `WordEncoding.ofEquiv`. -/
def KickMetaReadInput.equiv :
    KickMetaReadInput ≃ (KickRuntimeParams × ℕ) × ℕ where
  toFun d := ((d.rp, d.base), d.idx)
  invFun := fun ((rp, base), idx) => ⟨rp, base, idx⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickMetaReadInput := .ofEquiv KickMetaReadInput.equiv

/-- Every encoded word of `d : KickMetaReadInput` fits in `w` bits when its fields do. -/
theorem fits_encode_kickMetaReadInput {w : ℕ} {d : KickMetaReadInput}
    (hrp : ∀ i, Fits w (WordEncoding.encode d.rp i))
    (hbase : Fits w d.base) (hidx : Fits w d.idx) :
    ∀ i, Fits w (WordEncoding.encode d i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickMetaReadInput.equiv d) i)
  dsimp only [KickMetaReadInput.equiv]
  exact fits_encode_prod (fits_encode_prod hrp (fits_encode_nat hbase)) (fits_encode_nat hidx)

/-- Parameter-free bit-packed read from `SlotMeta[d.idx]`. -/
def readMetaGenProg (d : KickMetaReadInput) : Memory.Prog ℕ :=
  readPackedGenProg (((d.base, d.rp.offMeta), (d.rp.metaBits, d.rp.w)), d.idx)

/-- Typed wrapper reading `SlotMeta[idx]` for `p : KickTreeParams` at `base`. -/
abbrev readMetaProg (p : KickTreeParams) (base idx : ℕ) : Memory.Prog ℕ :=
  readMetaGenProg ⟨mkKickRuntimeParams p, base, idx⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `readMetaGenProg`. -/
theorem realizes_readMetaGen :
    Realizes .exact readMetaGenProg
      (WordEncoding.encode (α := KickMetaReadInput))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.idx < d.rp.metaLen)
      (fun _ _ => 0) := by
  unfold readMetaGenProg
  realize [realizes_readPackedGen]
  exact readPacked_meta_safe h.1 h.2

/-- Admissible memory history for `readMetaProg` when `[base, base + totalSpace p)` lies below
`s.frontier`. -/
theorem validHistory_readMetaProg {w base idx : ℕ} (p : KickTreeParams)
    (hw_eq : w = p.w) (hw : 0 < p.w) (hidx : idx < metaLen p) {s : Memory.State}
    (ha : base + totalSpace p ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readMetaProg p base idx)) := by
  subst hw_eq
  have hM : base + offMeta p + packedWords (metaLen p) (metaBits p) p.w ≤ s.frontier := by
    have := meta_end_le_totalSpace p; dsimp [metaWords] at this; omega
  exact validHistory_readPackedProg hw hidx hM

/-- Exact memory charge of `readMetaProg` (`2` word reads). -/
theorem memoryCost_readMetaProg (p : KickTreeParams) (base idx : ℕ) (s : Memory.State) :
    memoryCost (readMetaProg p base idx) s = 2 := by
  unfold readMetaProg readMetaGenProg readPackedGenProg
  exact memoryCost_readPackedProg _ _ _ _ _ _

/-- Pure array-level specification for `readMetaProg`. -/
theorem readMetaProg_spec (p : KickTreeParams) {base idx : ℕ} (hidx : idx < metaLen p)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (readMetaProg p base idx) = s ∧
      (Memory.spec 0).clientResult s (readMetaProg p base idx) = metaAt base p s.mem idx := by
  unfold readMetaProg readMetaGenProg readPackedGenProg
  dsimp only [mkKickRuntimeParams]
  rw [clientState_readPackedProg, clientResult_readPackedProg]
  exact ⟨rfl, by simp [metaAt, hidx]⟩

/-- Input record for `writeMetaGenProg`. -/
structure KickMetaWriteInput where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Metadata index `idx < rp.metaLen`. -/
  idx : ℕ
  /-- Metadata entry value `val < 2 ^ rp.metaBits`. -/
  val : ℕ

/-- Tuple equivalence for `KickMetaWriteInput` used by `WordEncoding.ofEquiv`. -/
def KickMetaWriteInput.equiv :
    KickMetaWriteInput ≃ ((KickRuntimeParams × ℕ) × ℕ) × ℕ where
  toFun d := (((d.rp, d.base), d.idx), d.val)
  invFun := fun (((rp, base), idx), val) => ⟨rp, base, idx, val⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickMetaWriteInput := .ofEquiv KickMetaWriteInput.equiv

/-- Every encoded word of `d : KickMetaWriteInput` fits in `w` bits when its fields do. -/
theorem fits_encode_kickMetaWriteInput {w : ℕ} {d : KickMetaWriteInput}
    (hrp : ∀ i, Fits w (WordEncoding.encode d.rp i))
    (hbase : Fits w d.base) (hidx : Fits w d.idx) (hval : Fits w d.val) :
    ∀ i, Fits w (WordEncoding.encode d i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickMetaWriteInput.equiv d) i)
  dsimp only [KickMetaWriteInput.equiv]
  exact fits_encode_prod (fits_encode_prod (fits_encode_prod hrp
    (fits_encode_nat hbase)) (fits_encode_nat hidx)) (fits_encode_nat hval)

/-- Parameter-free bit-packed write to `SlotMeta[d.idx]`. -/
def writeMetaGenProg (d : KickMetaWriteInput) : Memory.Prog Unit :=
  writePackedGenProg ((((d.base, d.rp.offMeta), (d.rp.metaBits, d.rp.w)), d.idx), d.val)

/-- Typed wrapper writing `val` into `SlotMeta[idx]` for `p : KickTreeParams` at `base`. -/
abbrev writeMetaProg (p : KickTreeParams) (base idx val : ℕ) : Memory.Prog Unit :=
  writeMetaGenProg ⟨mkKickRuntimeParams p, base, idx, val⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `writeMetaGenProg`. -/
theorem realizes_writeMetaGen :
    Realizes .exact writeMetaGenProg
      (WordEncoding.encode (α := KickMetaWriteInput))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.idx < d.rp.metaLen)
      (fun _ _ => 0) := by
  unfold writeMetaGenProg
  realize [realizes_writePackedGen]
  exact readPacked_meta_safe h.1 h.2

/-- Admissible memory history for `writeMetaProg` on a well-formed machine state with
`[base, base + totalSpace p)` below `s.frontier`. -/
theorem validHistory_writeMetaProg {w base idx val : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) (hidx : idx < metaLen p) {s : Memory.State}
    (hwf : Memory.WellFormed w s) (ha : base + totalSpace p ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeMetaProg p base idx val)) := by
  obtain ⟨rfl, hw, _, _, hm, _⟩ := henv
  have hM : base + offMeta p + packedWords (metaLen p) (metaBits p) p.w ≤ s.frontier := by
    have := meta_end_le_totalSpace p; dsimp [metaWords] at this; omega
  exact validHistory_writePackedProg hw hm hidx hwf hM

/-- Exact memory charge of `writeMetaProg` (`2` reads and `2` writes). -/
theorem memoryCost_writeMetaProg (p : KickTreeParams) (base idx val : ℕ)
    (s : Memory.State) :
    memoryCost (writeMetaProg p base idx val) s = 4 := by
  unfold writeMetaProg writeMetaGenProg writePackedGenProg
  exact memoryCost_writePackedProg _ _ _ _ _ _ _

/-- Pure array-update specification for `writeMetaProg`. -/
theorem writeMetaProg_spec (p : KickTreeParams) (hw : 0 < p.w) {base idx val : ℕ}
    (hidx : idx < metaLen p) (hval : val < 2 ^ metaBits p) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (writeMetaProg p base idx val)
    s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = quotAt base p s.mem ∧
      valAt base p s'.mem = valAt base p s.mem ∧
      occAt base p s'.mem = occAt base p s.mem ∧
      elevAt base p s'.mem = elevAt base p s.mem ∧
      metaAt base p s'.mem = Function.update (metaAt base p s.mem) idx val := by
  intro s'
  have hst : s' = { mem := writeMetaMem base p s.mem idx val, frontier := s.frontier } := by
    change (Memory.spec 0).clientState s (writeMetaProg p base idx val) = _
    unfold writeMetaProg writeMetaGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    rw [clientState_writePackedProg]
    rfl
  have heM := writeMetaMem_effects (base := base) p hw s.mem hidx hval
  rw [hst]
  exact ⟨rfl, fun a ha => heM.2.2.2.2.2 a (not_in_meta_of_outside ha),
    heM.1, heM.2.1, heM.2.2.1, heM.2.2.2.1, heM.2.2.2.2.1⟩

/-! ### 5. Bounded Bit-Packed Kick Displacement Loop -/

/-- Loop-invariant environment for `kickStepGenProg`. -/
structure KickStepEnv where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Base word address of the switching-path buffer `[pathBase, pathBase + fuel)`. -/
  pathBase : ℕ

/-- Tuple equivalence for `KickStepEnv` used by `WordEncoding.ofEquiv`. -/
def KickStepEnv.equiv :
    KickStepEnv ≃ (KickRuntimeParams × ℕ) × ℕ where
  toFun e := ((e.rp, e.base), e.pathBase)
  invFun := fun ((rp, base), pathBase) => ⟨rp, base, pathBase⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickStepEnv := .ofEquiv KickStepEnv.equiv

/-- Every encoded word of `e : KickStepEnv` fits in `w` bits when its fields do. -/
theorem fits_encode_kickStepEnv {w : ℕ} {e : KickStepEnv}
    (hrp : ∀ i, Fits w (WordEncoding.encode e.rp i))
    (hbase : Fits w e.base) (hpath : Fits w e.pathBase) :
    ∀ i, Fits w (WordEncoding.encode e i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickStepEnv.equiv e) i)
  dsimp only [KickStepEnv.equiv]
  exact fits_encode_prod (fits_encode_prod hrp (fits_encode_nat hbase)) (fits_encode_nat hpath)

/-- Loop state carried across bounded kick displacement steps (`active > 0` while an item remains
in flight; `active = 0` once placed into a vacant slot). -/
structure KickStepState where
  /-- Current index into the switching-path buffer `pathBase`. -/
  stepIdx : ℕ
  /-- Quotient of the item currently being placed. -/
  quot : ℕ
  /-- Value of the item currently being placed. -/
  val : ℕ
  /-- 1-bit per-slot priority-depth indicator (`0` = priority depth `0`, `1` = elevated priority
  depth `≥ 1`; local formalization adaptation), preserved by kick-depth invariance. -/
  elevated : ℕ
  /-- Activity flag (`1` = active displacement in progress, `0` = item placed). -/
  active : ℕ
deriving Repr, DecidableEq

/-- Tuple equivalence for `KickStepState` used by `WordEncoding.ofEquiv`. -/
def KickStepState.equiv :
    KickStepState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun st := ((((st.stepIdx, st.quot), st.val), st.elevated), st.active)
  invFun := fun ((((stepIdx, quot), val), elevated), active) =>
    ⟨stepIdx, quot, val, elevated, active⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickStepState := .ofEquiv KickStepState.equiv

/-- Every encoded word of `st : KickStepState` fits in `w` bits when its fields do. -/
theorem fits_encode_kickStepState {w : ℕ} {st : KickStepState}
    (hs : Fits w st.stepIdx) (hq : Fits w st.quot) (hv : Fits w st.val)
    (he : Fits w st.elevated) (ha : Fits w st.active) :
    ∀ i, Fits w (WordEncoding.encode st i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickStepState.equiv st) i)
  dsimp only [KickStepState.equiv]
  exact fits_encode_prod (fits_encode_prod (fits_encode_prod (fits_encode_prod
    (fits_encode_nat hs) (fits_encode_nat hq)) (fits_encode_nat hv))
    (fits_encode_nat he)) (fits_encode_nat ha)

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
`(quot, val, elevated)` into `(Quotients[slot], Values[slot], Elevated[slot])` and sets
`Occupancy[slot] := 1`, terminating (`active := 0`). If occupied, atomically reads incumbent
`(oldQuot, oldVal, oldElev)`, writes `(quot, val, elevated)` into `slot`, and advances to
`stepIdx + 1` carrying `(oldQuot, oldVal, oldElev)`. -/
def kickStepGenProg (d : KickStepEnv × KickStepState) : Memory.Prog KickStepState := do
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
      writePackedGenProg ((((env.base, env.rp.offElev), (1, env.rp.w)), slot),
        st.elevated)
      writePackedGenProg ((((env.base, env.rp.offOcc), (1, env.rp.w)), slot), 1)
      pure ⟨st.stepIdx + 1, 0, 0, 0, 0⟩
    else do
      let oldQuot ← readPackedGenProg (((env.base, env.rp.offQuot), (env.rp.quotBits, env.rp.w)),
        slot)
      let oldVal ← readPackedGenProg (((env.base, env.rp.offVal), (env.rp.valBits, env.rp.w)),
        slot)
      let oldElev ← readPackedGenProg (((env.base, env.rp.offElev), (1, env.rp.w)), slot)
      writePackedGenProg ((((env.base, env.rp.offQuot), (env.rp.quotBits, env.rp.w)), slot),
        st.quot)
      writePackedGenProg ((((env.base, env.rp.offVal), (env.rp.valBits, env.rp.w)), slot),
        st.val)
      writePackedGenProg ((((env.base, env.rp.offElev), (1, env.rp.w)), slot),
        st.elevated)
      pure ⟨st.stepIdx + 1, oldQuot, oldVal, oldElev, 1⟩
  else
    pure st

/-- Typed wrapper for `kickStepGenProg`. -/
abbrev kickStepProg (p : KickTreeParams) (base pathBase : ℕ) (st : KickStepState) :
    Memory.Prog KickStepState :=
  kickStepGenProg (⟨mkKickRuntimeParams p, base, pathBase⟩, st)

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `kickStepGenProg`. -/
theorem realizes_kickStepGen :
    Realizes .exact kickStepGenProg
      (WordEncoding.encode (α := KickStepEnv × KickStepState))
      (WordEncoding.encode (α := KickStepState))
      KickStepSafe
      (fun _ _ => 0) := by
  unfold kickStepGenProg
  realize [realizes_readPackedGen, realizes_writePackedGen]
  all_goals
    obtain ⟨henv, hact⟩ := h
  all_goals first
    | exact (hact (by assumption)).1
    | exact (hact (by assumption)).2.1
    | exact readPacked_occ_safe henv (hact (by assumption)).2.2
    | exact readPacked_quot_safe henv (hact (by assumption)).2.2
    | exact readPacked_val_safe henv (hact (by assumption)).2.2
    | exact readPacked_elev_safe henv (hact (by assumption)).2.2
    | exact fits_one_of_env henv

/-- Bounded bit-packed kick displacement loop executing `fuel` steps via `Realization.iterate`
(`fuel ≤ k + 1` per Section 3.1 / Theorem 2). -/
def kickLoopIterGenProg : (KickStepEnv × KickStepState) × ℕ → Memory.Prog KickStepState
  | ((env, st), fuel) => iterate kickStepGenProg env fuel st

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `kickLoopIterGenProg`. -/
theorem realizes_kickLoopGen :
    Realizes .exact kickLoopIterGenProg
      (WordEncoding.encode (α := (KickStepEnv × KickStepState) × ℕ))
      (WordEncoding.encode (α := KickStepState))
      (fun w ((env, st), fuel) s =>
        iterationSafe kickStepGenProg KickStepSafe w env fuel st s)
      (fun ((env, st), fuel) s =>
        iterationWork kickStepGenProg (fun _ _ => 0) env fuel st s) :=
  Realizes.iterateRuntime (WordEncoding.encode (α := KickStepEnv))
    (WordEncoding.encode (α := KickStepState)) realizes_kickStepGen

/-- Bounded bit-packed kick loop executing `p.kickLimit` steps starting from step `0` with active
item `(quot, val, elevated)`. -/
abbrev kickLoopProg (p : KickTreeParams) (base pathBase quot val elevated : ℕ) :
    Memory.Prog KickStepState :=
  kickLoopIterGenProg
    ((⟨mkKickRuntimeParams p, base, pathBase⟩, ⟨0, quot, val, elevated, 1⟩), p.kickLimit)

/-- `kickStepProg` issues at most one path-word read, four bit-packed reads, and three bit-packed
writes (`memoryCost ≤ 21`; the vacant branch costs `19` and the inactive branch costs `0`). -/
theorem memoryCost_kickStepProg_le (p : KickTreeParams) (base pathBase : ℕ)
    (st : KickStepState) (s : Memory.State) :
    memoryCost (kickStepProg p base pathBase st) s ≤ 21 := by
  unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
  dsimp only [mkKickRuntimeParams]
  split_ifs with hact
  · have hread_cost : ∀ addr s', memoryCost (Memory.read addr) s' = 1 := fun _ _ => rfl
    rw [memoryCost_bind', hread_cost,
      show (Memory.spec 0).clientState s (Memory.read (pathBase + st.stepIdx)) = s from rfl,
      memoryCost_bind', memoryCost_readPackedProg, clientState_readPackedProg]
    split_ifs
    · iterate 4 rw [memoryCost_bind', memoryCost_writePackedProg]
      rw [memoryCost_pure]; omega
    · iterate 3 rw [memoryCost_bind', memoryCost_readPackedProg, clientState_readPackedProg]
      iterate 3 rw [memoryCost_bind', memoryCost_writePackedProg]
      rw [memoryCost_pure]
  · rw [memoryCost_pure]; omega

/-- When `st.active = 0`, `kickStepProg` is a no-op returning `st` and preserving `s`. -/
theorem kickStepProg_inactive_spec (p : KickTreeParams) {base pathBase : ℕ} {st : KickStepState}
    (hact : st.active = 0) (s : Memory.State) :
    (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) = st ∧
      (Memory.spec 0).clientState s (kickStepProg p base pathBase st) = s := by
  unfold kickStepProg kickStepGenProg
  dsimp only
  rw [ite_eq_right (by omega)]
  exact ⟨rfl, rfl⟩

/-- Admissible memory history for `kickStepProg` on a well-formed machine state when
`[base, base + totalSpace p)` lies below `s.frontier` and, if `0 < st.active`, the path entry
`pathBase + st.stepIdx` is allocated and holds a slot `< p.nMax`. -/
theorem validHistory_kickStepProg {w base pathBase : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) {st : KickStepState} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (ha : base + totalSpace p ≤ s.frontier)
    (hact : 0 < st.active →
      pathBase + st.stepIdx < s.frontier ∧ s.mem (pathBase + st.stepIdx) < p.nMax) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (kickStepProg p base pathBase st)) := by
  obtain ⟨rfl, hw, hq, hv, _, _⟩ := henv
  obtain ⟨hQ, hV, hE, hO⟩ := array_ends_le_frontier p ha
  unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
  dsimp only [mkKickRuntimeParams]
  split_ifs with ha_pos
  · obtain ⟨hp_lt, hslot⟩ := hact ha_pos
    have hocc_lt : s.mem (pathBase + st.stepIdx) < occLen p := slot_lt_occLen hslot
    have hr_st : (Memory.spec 0).clientState s (Memory.read (pathBase + st.stepIdx)) = s := rfl
    have hr_res : (Memory.spec 0).clientResult s (Memory.read (pathBase + st.stepIdx)) =
        s.mem (pathBase + st.stepIdx) := rfl
    rw [validHistory_bind']
    refine ⟨⟨hp_lt, trivial⟩, ?_⟩
    rw [hr_st, hr_res]
    refine validHistory_readPackedProg_bind hw hocc_lt hO fun _ => ?_
    split_ifs
    · refine validHistory_writePackedProg_bind hw hq hslot hwf hQ fun s1 hwf1 hfr1 => ?_
      refine validHistory_writePackedProg_bind hw hv hslot hwf1 (hfr1 ▸ hV) fun s2 hwf2 hfr2 => ?_
      refine validHistory_writePackedProg_bind hw hw hslot hwf2 (hfr2 ▸ hfr1 ▸ hE)
        fun s3 hwf3 hfr3 => ?_
      exact validHistory_writePackedProg_bind hw hw hocc_lt hwf3 (hfr3 ▸ hfr2 ▸ hfr1 ▸ hO)
        fun _ _ _ => trivial
    · refine validHistory_readPackedProg_bind hw hslot hQ fun _ => ?_
      refine validHistory_readPackedProg_bind hw hslot hV fun _ => ?_
      refine validHistory_readPackedProg_bind hw hslot hE fun _ => ?_
      refine validHistory_writePackedProg_bind hw hq hslot hwf hQ fun s1 hwf1 hfr1 => ?_
      refine validHistory_writePackedProg_bind hw hv hslot hwf1 (hfr1 ▸ hV) fun s2 hwf2 hfr2 => ?_
      exact validHistory_writePackedProg_bind hw hw hslot hwf2 (hfr2 ▸ hfr1 ▸ hE)
        fun _ _ _ => trivial
  · trivial

private theorem kickStepProg_step_frame (p : KickTreeParams) (hw : 0 < p.w)
    {base pathBase : ℕ} {st : KickStepState} {s : Memory.State}
    (hslot : 0 < st.active → s.mem (pathBase + st.stepIdx) < p.nMax) :
    let st' := (Memory.spec 0).clientResult s (kickStepProg p base pathBase st)
    let s' := (Memory.spec 0).clientState s (kickStepProg p base pathBase st)
    s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      (0 < st'.active → 0 < st.active ∧ st'.stepIdx = st.stepIdx + 1) := by
  intro st' s'
  by_cases ha_pos : 0 < st.active
  · have hs := hslot ha_pos
    have hsO : s.mem (pathBase + st.stepIdx) < occLen p := slot_lt_occLen hs
    set slot := s.mem (pathBase + st.stepIdx)
    have hr_mem : (Memory.spec 0).clientState s (Memory.read (pathBase + st.stepIdx)) = s := rfl
    have hr_res : (Memory.spec 0).clientResult s (Memory.read (pathBase + st.stepIdx)) = slot := rfl
    by_cases hocc : readPacked (base + offOcc p) 1 p.w s.mem slot = 0
    · have hres : st' = ⟨st.stepIdx + 1, 0, 0, 0, 0⟩ := by
        change (Memory.spec 0).clientResult s _ = _
        unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
        dsimp only [mkKickRuntimeParams]
        rw [ite_eq_left ha_pos, StateTransitionSpec.clientResult_bind, hr_mem, hr_res,
          StateTransitionSpec.clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hocc, ite_eq_left rfl]
        iterate 4 rw [StateTransitionSpec.clientResult_bind, clientState_writePackedProg]
        rfl
      have hst : s' = {
          mem := writeOccMem base p
            (writeElevMem base p
              (writeValMem base p (writeQuotMem base p s.mem slot st.quot) slot st.val)
              slot st.elevated)
            slot 1
          frontier := s.frontier } := by
        change (Memory.spec 0).clientState s _ = _
        unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
        dsimp only [mkKickRuntimeParams]
        rw [ite_eq_left ha_pos, StateTransitionSpec.clientState_bind, hr_mem, hr_res,
          StateTransitionSpec.clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hocc, ite_eq_left rfl]
        iterate 4 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
        rfl
      rw [hres, hst]
      refine ⟨rfl, fun a ha => ?_, fun h => nomatch h⟩
      exact (writePacked_outside hw _ hsO 1 (not_in_occ_of_outside ha)).trans
        ((writePacked_outside hw _ hs st.elevated (not_in_elev_of_outside ha)).trans
          ((writePacked_outside hw _ hs st.val (not_in_val_of_outside ha)).trans
            (writePacked_outside hw _ hs st.quot (not_in_quot_of_outside ha))))
    · have hres_step : st'.stepIdx = st.stepIdx + 1 := by
        change KickStepState.stepIdx
          ((Memory.spec 0).clientResult s (kickStepProg p base pathBase st)) = _
        unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
        dsimp only [mkKickRuntimeParams]
        rw [ite_eq_left ha_pos, StateTransitionSpec.clientResult_bind, hr_mem, hr_res,
          StateTransitionSpec.clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, ite_eq_right hocc]
        iterate 3 rw [StateTransitionSpec.clientResult_bind,
          clientState_readPackedProg, clientResult_readPackedProg]
        iterate 3 rw [StateTransitionSpec.clientResult_bind, clientState_writePackedProg]
        rfl
      have hst : s' = {
          mem := writeElevMem base p
            (writeValMem base p (writeQuotMem base p s.mem slot st.quot) slot st.val)
            slot st.elevated
          frontier := s.frontier } := by
        change (Memory.spec 0).clientState s _ = _
        unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
        dsimp only [mkKickRuntimeParams]
        rw [ite_eq_left ha_pos, StateTransitionSpec.clientState_bind, hr_mem, hr_res,
          StateTransitionSpec.clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, ite_eq_right hocc]
        iterate 3 rw [StateTransitionSpec.clientState_bind,
          clientState_readPackedProg, clientResult_readPackedProg]
        iterate 3 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
        rfl
      rw [hst]
      refine ⟨rfl, fun a ha => ?_, fun _ => ⟨ha_pos, hres_step⟩⟩
      exact (writePacked_outside hw _ hs st.elevated (not_in_elev_of_outside ha)).trans
        ((writePacked_outside hw _ hs st.val (not_in_val_of_outside ha)).trans
          (writePacked_outside hw _ hs st.quot (not_in_quot_of_outside ha)))
  · have hinact := kickStepProg_inactive_spec p (base := base) (pathBase := pathBase)
      (st := st) (by omega) s
    change st' = st ∧ s' = s at hinact
    rw [hinact.1, hinact.2]
    exact ⟨rfl, fun _ _ => rfl, fun h => (ha_pos h).elim⟩

/-- Parametric bounded-loop specification for `kickLoopIterGenProg` / `kickLoopProg` across
arbitrary `fuel` (including `fuel = p.kickLimit` at `st₀ = ⟨0, quot, val, elevated, 1⟩`), proved
via `Realization.iterate_spec`. Establishes `iterationSafe`, `ValidHistory`, `memoryCost ≤
21 * fuel`, frontier preservation, memory frame outside `[base + p.hSpace, base + totalSpace p)`,
and any step invariant `inv` along `[pathBase + st₀.stepIdx, pathBase + st₀.stepIdx + fuel)`. -/
theorem kickLoopProg_spec {w base pathBase fuel : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) {st₀ : KickStepState}
    (inv : ℕ → KickStepState → Memory.State → Prop)
    {s₀ : Memory.State} (hwf : Memory.WellFormed w s₀)
    (ha : base + totalSpace p ≤ s₀.frontier)
    (hpath_lt : pathBase + st₀.stepIdx + fuel ≤ s₀.frontier)
    (hpath_disj : ∀ i < fuel,
      ¬(base + p.hSpace ≤ pathBase + (st₀.stepIdx + i) ∧
        pathBase + (st₀.stepIdx + i) < base + totalSpace p))
    (hpath_slots : ∀ i < fuel, s₀.mem (pathBase + (st₀.stepIdx + i)) < p.nMax)
    (h₀ : inv 0 st₀ s₀)
    (hstep : ∀ i < fuel, ∀ st s,
      (0 < st.active → st.stepIdx = st₀.stepIdx + i) →
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s.mem a = s₀.mem a) →
      inv i st s →
      inv (i + 1)
        ((Memory.spec 0).clientResult s (kickStepProg p base pathBase st))
        ((Memory.spec 0).clientState s (kickStepProg p base pathBase st))) :
    let prog := kickLoopIterGenProg ((⟨mkKickRuntimeParams p, base, pathBase⟩, st₀), fuel)
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe kickStepGenProg KickStepSafe w
      ⟨mkKickRuntimeParams p, base, pathBase⟩ fuel st₀ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 21 * fuel ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s₀.mem a) ∧
    inv fuel ((Memory.spec 0).clientResult s₀ prog) s' := by
  have hw : 0 < p.w := henv.2.1
  let env : KickStepEnv := ⟨mkKickRuntimeParams p, base, pathBase⟩
  let fullInv (i : ℕ) (st : KickStepState) (s : Memory.State) : Prop :=
    Memory.WellFormed w s ∧
      s.frontier = s₀.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s.mem a = s₀.mem a) ∧
      (0 < st.active → st.stepIdx = st₀.stepIdx + i) ∧
      inv i st s
  obtain ⟨hsafe, hv, hcost, hfr, hmod, _, _, _, _, hinv_f⟩ :=
    iterate_spec kickStepGenProg KickStepSafe w env 21 fuel fullInv
      (fun a => base + p.hSpace ≤ a ∧ a < base + totalSpace p)
      (fun i hi st s ⟨hwf_s, hfr_s, hout_s, hidx_s, hinv_s⟩ => by
        have hp_info : 0 < st.active →
            pathBase + st.stepIdx < s.frontier ∧ s.mem (pathBase + st.stepIdx) < p.nMax := by
          intro ha_pos
          have hidx := hidx_s ha_pos
          have hmem_eq := hout_s (pathBase + (st₀.stepIdx + i)) (hpath_disj i hi)
          have hsl := hpath_slots i hi
          exact ⟨by omega, by rw [hidx]; omega⟩
        have hsafe_step : KickStepSafe w (env, st) s := by
          refine ⟨⟨p, rfl, henv⟩, fun ha_pos => ?_⟩
          dsimp only [env]
          have hidx := hidx_s ha_pos
          obtain ⟨hp_lt, hsl⟩ := hp_info ha_pos
          exact ⟨hwf_s.fits_of_lt_frontier hp_lt, hwf_s.1.of_le (by omega), hsl⟩
        have hv_step := validHistory_kickStepProg p henv hwf_s (by rw [hfr_s]; exact ha) hp_info
        have hcost_step := memoryCost_kickStepProg_le p base pathBase st s
        obtain ⟨hfr_step, hout_step, hact_step⟩ :=
          kickStepProg_step_frame p hw (base := base) (pathBase := pathBase)
            (fun ha_pos => (hp_info ha_pos).2)
        have hwf_next :
            Memory.WellFormed w ((Memory.spec 0).clientState s (kickStepGenProg (env, st))) := by
          rw [← clientState_width w, ← StateTransitionSpec.run_runClient]
          exact hwf_s.run hv_step
        refine ⟨hsafe_step, hv_step, hcost_step, hfr_step, hout_step,
          hwf_next, hfr_step.trans hfr_s,
          fun a ha_out => (hout_step a ha_out).trans (hout_s a ha_out),
          fun ha_next => by
            obtain ⟨ha_prev, hstep_eq⟩ := hact_step ha_next
            rw [hstep_eq, hidx_s ha_prev, Nat.add_assoc],
          hstep i hi st s hidx_s hout_s hinv_s⟩)
      st₀ s₀ ⟨hwf, rfl, fun _ _ => rfl, fun _ => (Nat.add_zero _).symm, h₀⟩
  exact ⟨hsafe, hv, hcost, hfr, hmod, hinv_f⟩

/-- Admissibility and `iterationSafe` certificate for `kickLoopProg` from static entry bounds on
`s₀`. -/
theorem validHistory_kickLoopProg {w base pathBase quot val elevated : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) {s₀ : Memory.State} (hwf : Memory.WellFormed w s₀)
    (ha : base + totalSpace p ≤ s₀.frontier)
    (hpath_lt : pathBase + p.kickLimit ≤ s₀.frontier)
    (hpath_disj : ∀ i < p.kickLimit,
      ¬(base + p.hSpace ≤ pathBase + i ∧ pathBase + i < base + totalSpace p))
    (hpath_slots : ∀ i < p.kickLimit, s₀.mem (pathBase + i) < p.nMax) :
    iterationSafe kickStepGenProg KickStepSafe w ⟨mkKickRuntimeParams p, base, pathBase⟩
      p.kickLimit ⟨0, quot, val, elevated, 1⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (kickLoopProg p base pathBase quot val elevated)) := by
  obtain ⟨hsafe, hv, _⟩ := kickLoopProg_spec p henv (st₀ := ⟨0, quot, val, elevated, 1⟩)
    (fuel := p.kickLimit) (fun _ _ _ => True) hwf ha
    (by simpa only [Nat.add_zero] using hpath_lt)
    (fun i hi => by simpa only [Nat.zero_add] using hpath_disj i hi)
    (fun i hi => by simpa only [Nat.zero_add] using hpath_slots i hi)
    trivial (fun _ _ _ _ _ _ _ => trivial)
  exact ⟨hsafe, hv⟩

/-- Unconditional memory-charge bound for `kickLoopIterGenProg` / `kickLoopProg` (`≤ 21 * fuel`). -/
theorem memoryCost_kickLoopProg_le (p : KickTreeParams) (base pathBase : ℕ)
    (st₀ : KickStepState) (fuel : ℕ) (s : Memory.State) :
    memoryCost (kickLoopIterGenProg ((⟨mkKickRuntimeParams p, base, pathBase⟩, st₀), fuel)) s ≤
      21 * fuel := by
  unfold kickLoopIterGenProg; dsimp only
  induction fuel generalizing st₀ s with
  | zero => simp [iterate]
  | succ n ih =>
    change memoryCost (kickStepProg p base pathBase st₀ >>=
      iterate kickStepGenProg ⟨mkKickRuntimeParams p, base, pathBase⟩ n) s ≤ 21 * (n + 1)
    rw [memoryCost_bind']
    have h1 := memoryCost_kickStepProg_le p base pathBase st₀ s
    have h2 := ih ((Memory.spec 0).clientResult s (kickStepProg p base pathBase st₀))
      ((Memory.spec 0).clientState s (kickStepProg p base pathBase st₀))
    omega

/-- Pure array-update specification for `kickStepProg` when the candidate slot `slot` is vacant
(`occAt base p s.mem slot = 0`): places `(quot, val, elevated)` into `slot`, sets
`occAt ... slot = 1`, preserves `metaAt` and memory outside `[base + p.hSpace, base +
totalSpace p)`, and terminates (`active = 0`). -/
theorem kickStepProg_vacant_spec (p : KickTreeParams) (hw : 0 < p.w)
    {base pathBase : ℕ} {st : KickStepState} {s : Memory.State}
    (hact : 0 < st.active)
    (hslot : s.mem (pathBase + st.stepIdx) < p.nMax)
    (hq : st.quot < 2 ^ quotBits p)
    (hv : st.val < 2 ^ valBits p.V)
    (he : st.elevated < 2 ^ 1)
    (hvac : occAt base p s.mem (s.mem (pathBase + st.stepIdx)) = 0) :
    let slot := s.mem (pathBase + st.stepIdx)
    let s' := (Memory.spec 0).clientState s (kickStepProg p base pathBase st)
    (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
        ⟨st.stepIdx + 1, 0, 0, 0, 0⟩ ∧
      s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = Function.update (quotAt base p s.mem) slot st.quot ∧
      valAt base p s'.mem = Function.update (valAt base p s.mem) slot st.val ∧
      elevAt base p s'.mem = Function.update (elevAt base p s.mem) slot st.elevated ∧
      occAt base p s'.mem = Function.update (occAt base p s.mem) slot 1 ∧
      metaAt base p s'.mem = metaAt base p s.mem := by
  intro slot s'
  change slot < p.nMax at hslot
  change occAt base p s.mem slot = 0 at hvac
  have hocc_lt : slot < occLen p := slot_lt_occLen hslot
  have hocc_read : readPacked (base + offOcc p) 1 p.w s.mem slot = 0 := by
    simpa [occAt, hocc_lt] using hvac
  set m1 := writeQuotMem base p s.mem slot st.quot
  set m2 := writeValMem base p m1 slot st.val
  set m3 := writeElevMem base p m2 slot st.elevated
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
  have heE := writeElevMem_effects (base := base) p hw m2 hslot he
  have heO := writeOccMem_effects (base := base) p hw m3 hocc_lt (by decide : 1 < 2 ^ 1)
  rw [hst]
  refine ⟨hres, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (heO.2.2.2.2.2 a (not_in_occ_of_outside ha)).trans
      ((heE.2.2.2.2.2 a (not_in_elev_of_outside ha)).trans
        ((heV.2.2.2.2.2 a (not_in_val_of_outside ha)).trans
          (heQ.2.2.2.2.2 a (not_in_quot_of_outside ha))))
  · exact heO.1.trans (heE.1.trans (heV.1.trans heQ.1))
  · exact heO.2.1.trans (heE.2.1.trans (heV.2.1.trans (by rw [heQ.2.1])))
  · exact heO.2.2.2.1.trans (heE.2.2.2.1.trans (by rw [heV.2.2.2.1, heQ.2.2.2.1]))
  · exact heO.2.2.1.trans (by rw [heE.2.2.1, heV.2.2.1, heQ.2.2.1])
  · exact heO.2.2.2.2.1.trans (heE.2.2.2.2.1.trans (heV.2.2.2.2.1.trans heQ.2.2.2.2.1))

/-- Pure array-update specification for `kickStepProg` when the candidate slot `slot` is occupied
(`occAt base p s.mem slot ≠ 0`): atomically displaces `(oldQuot, oldVal, oldElev)`, writes
`(quot, val, elevated)` into `slot`, preserves `occAt`, `metaAt`, and memory outside
`[base + p.hSpace, base + totalSpace p)`, and advances to `stepIdx + 1` with `active = 1`. -/
theorem kickStepProg_displace_spec (p : KickTreeParams) (hw : 0 < p.w)
    {base pathBase : ℕ} {st : KickStepState} {s : Memory.State}
    (hact : 0 < st.active)
    (hslot : s.mem (pathBase + st.stepIdx) < p.nMax)
    (hq : st.quot < 2 ^ quotBits p)
    (hv : st.val < 2 ^ valBits p.V)
    (he : st.elevated < 2 ^ 1)
    (hocc_ne : occAt base p s.mem (s.mem (pathBase + st.stepIdx)) ≠ 0) :
    let slot := s.mem (pathBase + st.stepIdx)
    let s' := (Memory.spec 0).clientState s (kickStepProg p base pathBase st)
    (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
        ⟨st.stepIdx + 1, quotAt base p s.mem slot, valAt base p s.mem slot,
          elevAt base p s.mem slot, 1⟩ ∧
      s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = Function.update (quotAt base p s.mem) slot st.quot ∧
      valAt base p s'.mem = Function.update (valAt base p s.mem) slot st.val ∧
      elevAt base p s'.mem = Function.update (elevAt base p s.mem) slot st.elevated ∧
      occAt base p s'.mem = occAt base p s.mem ∧
      metaAt base p s'.mem = metaAt base p s.mem := by
  intro slot s'
  change slot < p.nMax at hslot
  change occAt base p s.mem slot ≠ 0 at hocc_ne
  have hocc_lt : slot < occLen p := slot_lt_occLen hslot
  have hocc_read : readPacked (base + offOcc p) 1 p.w s.mem slot ≠ 0 := by
    simpa [occAt, hocc_lt] using hocc_ne
  set m1 := writeQuotMem base p s.mem slot st.quot
  set m2 := writeValMem base p m1 slot st.val
  set m3 := writeElevMem base p m2 slot st.elevated
  have hr_mem : (Memory.spec 0).clientState s (Memory.read (pathBase + st.stepIdx)) = s := rfl
  have hr_res : (Memory.spec 0).clientResult s (Memory.read (pathBase + st.stepIdx)) = slot := rfl
  have hres : (Memory.spec 0).clientResult s (kickStepProg p base pathBase st) =
      ⟨st.stepIdx + 1, quotAt base p s.mem slot, valAt base p s.mem slot,
        elevAt base p s.mem slot, 1⟩ := by
    unfold kickStepProg kickStepGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    rw [ite_eq_left hact, StateTransitionSpec.clientResult_bind, hr_mem, hr_res,
      StateTransitionSpec.clientResult_bind, clientState_readPackedProg,
      clientResult_readPackedProg, ite_eq_right hocc_read]
    iterate 3 rw [StateTransitionSpec.clientResult_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    iterate 3 rw [StateTransitionSpec.clientResult_bind, clientState_writePackedProg]
    change KickStepState.mk _ _ _ _ _ = _
    simp [quotAt, valAt, elevAt, hslot]
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
  have heE := writeElevMem_effects (base := base) p hw m2 hslot he
  rw [hst]
  refine ⟨hres, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (heE.2.2.2.2.2 a (not_in_elev_of_outside ha)).trans
      ((heV.2.2.2.2.2 a (not_in_val_of_outside ha)).trans
        (heQ.2.2.2.2.2 a (not_in_quot_of_outside ha)))
  · exact heE.1.trans (heV.1.trans heQ.1)
  · exact heE.2.1.trans (heV.2.1.trans (by rw [heQ.2.1]))
  · exact heE.2.2.2.1.trans (by rw [heV.2.2.2.1, heQ.2.2.2.1])
  · exact heE.2.2.1.trans (heV.2.2.1.trans heQ.2.2.1)
  · exact heE.2.2.2.2.1.trans (heV.2.2.2.2.1.trans heQ.2.2.2.2.1)

/-! ### 6. Bit-Packed Hashed-Slot Vacating and Unindexed Tail-Cubby Compaction Subroutines -/

/-- Input record for `clearSlotGenProg` (vacating a deleted slot in a hashed kick-tree). -/
structure KickClearInput where
  /-- Runtime layout parameters. -/
  rp : KickRuntimeParams
  /-- Base word address of the kick-tree table. -/
  base : ℕ
  /-- Primary slot index `slot < rp.nMax` being vacated. -/
  slot : ℕ

/-- Tuple equivalence for `KickClearInput` used by `WordEncoding.ofEquiv`. -/
def KickClearInput.equiv :
    KickClearInput ≃ (KickRuntimeParams × ℕ) × ℕ where
  toFun d := ((d.rp, d.base), d.slot)
  invFun := fun ((rp, base), slot) => ⟨rp, base, slot⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickClearInput := .ofEquiv KickClearInput.equiv

/-- Every encoded word of `d : KickClearInput` fits in `w` bits when its fields do. -/
theorem fits_encode_kickClearInput {w : ℕ} {d : KickClearInput}
    (hrp : ∀ i, Fits w (WordEncoding.encode d.rp i))
    (hbase : Fits w d.base) (hslot : Fits w d.slot) :
    ∀ i, Fits w (WordEncoding.encode d i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickClearInput.equiv d) i)
  dsimp only [KickClearInput.equiv]
  exact fits_encode_prod (fits_encode_prod hrp (fits_encode_nat hbase)) (fits_encode_nat hslot)

/-- Parameter-free bit-packed slot-vacating subroutine: zeroes `Quotients[slot]`, `Values[slot]`,
`Elevated[slot]`, and `Occupancy[slot]` at `slot` without moving other hashed items out of their
assigned bins. For Section 5.2 full-cubby deletion, callers pair `clearSlotProg` on the hashed
cubby with the local formalization adaptation `popUnindexedSlotProg` on the unindexed tail cubby
followed by `kickLoopProg` re-insertion along the popped item's own hashed switching path. -/
def clearSlotGenProg (d : KickClearInput) : Memory.Prog Unit := do
  writePackedGenProg ((((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.slot), 0)
  writePackedGenProg ((((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.slot), 0)
  writePackedGenProg ((((d.base, d.rp.offElev), (1, d.rp.w)), d.slot), 0)
  writePackedGenProg ((((d.base, d.rp.offOcc), (1, d.rp.w)), d.slot), 0)

/-- Typed wrapper for `clearSlotGenProg`. -/
abbrev clearSlotProg (p : KickTreeParams) (base slot : ℕ) : Memory.Prog Unit :=
  clearSlotGenProg ⟨mkKickRuntimeParams p, base, slot⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `clearSlotGenProg`. -/
theorem realizes_clearSlotGen :
    Realizes .exact clearSlotGenProg
      (WordEncoding.encode (α := KickClearInput))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax)
      (fun _ _ => 0) := by
  unfold clearSlotGenProg
  realize [realizes_writePackedGen]
  all_goals first
    | exact readPacked_quot_safe h.1 h.2
    | exact readPacked_val_safe h.1 h.2
    | exact readPacked_elev_safe h.1 h.2
    | exact readPacked_occ_safe h.1 h.2
    | exact fits_one_of_env h.1

/-- Admissible memory history for `clearSlotProg` on a well-formed machine state with
`[base, base + totalSpace p)` below `s.frontier`. -/
theorem validHistory_clearSlotProg {w base slot : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) (hslot : slot < p.nMax) {s : Memory.State}
    (hwf : Memory.WellFormed w s) (ha : base + totalSpace p ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (clearSlotProg p base slot)) := by
  obtain ⟨rfl, hw, hq, hv, _, _⟩ := henv
  obtain ⟨hQ, hV, hE, hO⟩ := array_ends_le_frontier p ha
  unfold clearSlotProg clearSlotGenProg writePackedGenProg
  dsimp only [mkKickRuntimeParams]
  refine validHistory_writePackedProg_bind hw hq hslot hwf hQ fun s1 hwf1 hfr1 => ?_
  refine validHistory_writePackedProg_bind hw hv hslot hwf1 (hfr1 ▸ hV) fun s2 hwf2 hfr2 => ?_
  refine validHistory_writePackedProg_bind hw hw hslot hwf2 (hfr2 ▸ hfr1 ▸ hE)
    fun s3 hwf3 hfr3 => ?_
  exact validHistory_writePackedProg hw hw (slot_lt_occLen hslot) hwf3 (hfr3 ▸ hfr2 ▸ hfr1 ▸ hO)

/-- Exact memory charge of `clearSlotProg` (`4` bit-packed writes = `16`). -/
theorem memoryCost_clearSlotProg (p : KickTreeParams) (base slot : ℕ) (s : Memory.State) :
    memoryCost (clearSlotProg p base slot) s = 16 := by
  unfold clearSlotProg clearSlotGenProg writePackedGenProg
  dsimp only [mkKickRuntimeParams]
  iterate 3 rw [memoryCost_bind', memoryCost_writePackedProg]
  rw [memoryCost_writePackedProg]

/-- Exact pure array-update specification for `clearSlotProg`: clears all four per-slot bit-packed
fields at `slot` (`quotAt`, `valAt`, `elevAt`, and `occAt`, so `querySlotProg` returns `none` at
`slot` for every key) while preserving all other slots, `metaAt`, and memory outside `[base +
p.hSpace, base + totalSpace p)`. -/
theorem clearSlotProg_spec (p : KickTreeParams) (hw : 0 < p.w)
    {base slot : ℕ} (hslot : slot < p.nMax) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (clearSlotProg p base slot)
    s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem = Function.update (quotAt base p s.mem) slot 0 ∧
      valAt base p s'.mem = Function.update (valAt base p s.mem) slot 0 ∧
      elevAt base p s'.mem = Function.update (elevAt base p s.mem) slot 0 ∧
      occAt base p s'.mem = Function.update (occAt base p s.mem) slot 0 ∧
      metaAt base p s'.mem = metaAt base p s.mem := by
  intro s'
  have hsO : slot < occLen p := slot_lt_occLen hslot
  set m1 := writeQuotMem base p s.mem slot 0
  set m2 := writeValMem base p m1 slot 0
  set m3 := writeElevMem base p m2 slot 0
  set m4 := writeOccMem base p m3 slot 0
  have hst : s' = { mem := m4, frontier := s.frontier } := by
    change (Memory.spec 0).clientState s (clearSlotProg p base slot) = _
    unfold clearSlotProg clearSlotGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    iterate 3 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
    rw [clientState_writePackedProg]
    rfl
  have he1 := writeQuotMem_effects (base := base) p hw s.mem hslot (by positivity)
  have he2 := writeValMem_effects (base := base) p hw m1 hslot (by positivity)
  have he3 := writeElevMem_effects (base := base) p hw m2 hslot (by positivity)
  have he4 := writeOccMem_effects (base := base) p hw m3 hsO (by positivity)
  rw [hst]
  refine ⟨rfl, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (he4.2.2.2.2.2 a (not_in_occ_of_outside ha)).trans
      ((he3.2.2.2.2.2 a (not_in_elev_of_outside ha)).trans
        ((he2.2.2.2.2.2 a (not_in_val_of_outside ha)).trans
          (he1.2.2.2.2.2 a (not_in_quot_of_outside ha))))
  · rw [he4.1, he3.1, he2.1, he1.1]
  · rw [he4.2.1, he3.2.1, he2.2.1, he1.2.1]
  · rw [he4.2.2.2.1, he3.2.2.2.1, he2.2.2.2.1, he1.2.2.2.1]
  · rw [he4.2.2.1, he3.2.2.1, he2.2.2.1, he1.2.2.1]
  · rw [he4.2.2.2.2.1, he3.2.2.2.2.1, he2.2.2.2.2.1, he1.2.2.2.2.1]

/-- Input record for `popUnindexedSlotGenProg` (local formalization adaptation swap-removing an
entry from an unindexed `[0, len)` `TailCubby` slot array). -/
structure KickPopInput where
  /-- Runtime layout parameters of the unindexed tail-cubby array. -/
  rp : KickRuntimeParams
  /-- Base word address of the unindexed tail-cubby array. -/
  base : ℕ
  /-- Selected index `slot < rp.nMax` to pop. -/
  slot : ℕ
  /-- Last active index `lastSlot < rp.nMax` compacted into `slot`. -/
  lastSlot : ℕ

/-- Tuple equivalence for `KickPopInput` used by `WordEncoding.ofEquiv`. -/
def KickPopInput.equiv :
    KickPopInput ≃ ((KickRuntimeParams × ℕ) × ℕ) × ℕ where
  toFun d := (((d.rp, d.base), d.slot), d.lastSlot)
  invFun := fun (((rp, base), slot), lastSlot) => ⟨rp, base, slot, lastSlot⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding KickPopInput := .ofEquiv KickPopInput.equiv

/-- Every encoded word of `d : KickPopInput` fits in `w` bits when its fields do. -/
theorem fits_encode_kickPopInput {w : ℕ} {d : KickPopInput}
    (hrp : ∀ i, Fits w (WordEncoding.encode d.rp i))
    (hbase : Fits w d.base) (hslot : Fits w d.slot) (hlast : Fits w d.lastSlot) :
    ∀ i, Fits w (WordEncoding.encode d i) := by
  change ∀ i, Fits w (WordEncoding.encode (KickPopInput.equiv d) i)
  dsimp only [KickPopInput.equiv]
  exact fits_encode_prod (fits_encode_prod (fits_encode_prod hrp
    (fits_encode_nat hbase)) (fits_encode_nat hslot)) (fits_encode_nat hlast)

/-- Local formalization adaptation: parameter-free bit-packed pop-and-compact subroutine strictly
for an **unindexed** `[0, len)` slot array (`Facility.TailCubby`, where entries occupy `[0, len)`
sequentially without hash-bin or bucket-prefix placement invariants): reads
`((quot, val), elevated)` at `d.slot`, compacts `d.lastSlot`'s `(quot, val, elevated, occ)` into
`d.slot`, delegates clearing of `d.lastSlot` to `clearSlotGenProg` (handling both
`slot ≠ lastSlot` and `slot = lastSlot`), and returns the popped item's `((quot, val), elevated)`
for subsequent re-hashing and `kickLoopProg` re-insertion. -/
def popUnindexedSlotGenProg (d : KickPopInput) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let poppedQuot ← readPackedGenProg (((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.slot)
  let poppedVal ← readPackedGenProg (((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.slot)
  let poppedElev ← readPackedGenProg (((d.base, d.rp.offElev), (1, d.rp.w)), d.slot)
  let lastQuot ← readPackedGenProg (((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.lastSlot)
  let lastVal ← readPackedGenProg (((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.lastSlot)
  let lastElev ← readPackedGenProg (((d.base, d.rp.offElev), (1, d.rp.w)), d.lastSlot)
  let lastOcc ← readPackedGenProg (((d.base, d.rp.offOcc), (1, d.rp.w)), d.lastSlot)
  writePackedGenProg ((((d.base, d.rp.offQuot), (d.rp.quotBits, d.rp.w)), d.slot), lastQuot)
  writePackedGenProg ((((d.base, d.rp.offVal), (d.rp.valBits, d.rp.w)), d.slot), lastVal)
  writePackedGenProg ((((d.base, d.rp.offElev), (1, d.rp.w)), d.slot), lastElev)
  writePackedGenProg ((((d.base, d.rp.offOcc), (1, d.rp.w)), d.slot), lastOcc)
  clearSlotGenProg ⟨d.rp, d.base, d.lastSlot⟩
  pure ((poppedQuot, poppedVal), poppedElev)

/-- Typed wrapper for `popUnindexedSlotGenProg`. -/
abbrev popUnindexedSlotProg (p : KickTreeParams) (base slot lastSlot : ℕ) :
    Memory.Prog ((ℕ × ℕ) × ℕ) :=
  popUnindexedSlotGenProg ⟨mkKickRuntimeParams p, base, slot, lastSlot⟩

/-- Uniform `Realizes .exact` (`¬ReadsWidth`) certificate for `popUnindexedSlotGenProg`. -/
theorem realizes_popUnindexedSlotGen :
    Realizes .exact popUnindexedSlotGenProg
      (WordEncoding.encode (α := KickPopInput))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w d _ => KickEnvGen w d.rp d.base ∧ d.slot < d.rp.nMax ∧ d.lastSlot < d.rp.nMax)
      (fun _ _ => 0) := by
  unfold popUnindexedSlotGenProg
  realize [realizes_readPackedGen, realizes_writePackedGen, realizes_clearSlotGen]
  all_goals first
    | exact h.1
    | exact h.2.2
    | exact readPacked_quot_safe h.1 h.2.1
    | exact readPacked_val_safe h.1 h.2.1
    | exact readPacked_elev_safe h.1 h.2.1
    | exact readPacked_occ_safe h.1 h.2.1
    | exact readPacked_quot_safe h.1 h.2.2
    | exact readPacked_val_safe h.1 h.2.2
    | exact readPacked_elev_safe h.1 h.2.2
    | exact readPacked_occ_safe h.1 h.2.2
    | exact fits_one_of_env h.1

/-- Admissible memory history for `popUnindexedSlotProg` on a well-formed machine state with
`[base, base + totalSpace p)` below `s.frontier`. -/
theorem validHistory_popUnindexedSlotProg {w base slot lastSlot : ℕ} (p : KickTreeParams)
    (henv : KickEnv p w base) (hslot : slot < p.nMax) (hlast : lastSlot < p.nMax)
    {s : Memory.State} (hwf : Memory.WellFormed w s) (ha : base + totalSpace p ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (popUnindexedSlotProg p base slot lastSlot)) := by
  have henv' := henv
  obtain ⟨rfl, hw, hq, hv, _, _⟩ := henv
  obtain ⟨hQ, hV, hE, hO⟩ := array_ends_le_frontier p ha
  unfold popUnindexedSlotProg popUnindexedSlotGenProg readPackedGenProg writePackedGenProg
  dsimp only [mkKickRuntimeParams]
  refine validHistory_readPackedProg_bind hw hslot hQ fun _ => ?_
  refine validHistory_readPackedProg_bind hw hslot hV fun _ => ?_
  refine validHistory_readPackedProg_bind hw hslot hE fun _ => ?_
  refine validHistory_readPackedProg_bind hw hlast hQ fun _ => ?_
  refine validHistory_readPackedProg_bind hw hlast hV fun _ => ?_
  refine validHistory_readPackedProg_bind hw hlast hE fun _ => ?_
  refine validHistory_readPackedProg_bind hw (slot_lt_occLen hlast) hO fun _ => ?_
  refine validHistory_writePackedProg_bind hw hq hslot hwf hQ fun s1 hwf1 hfr1 => ?_
  refine validHistory_writePackedProg_bind hw hv hslot hwf1 (hfr1 ▸ hV) fun s2 hwf2 hfr2 => ?_
  refine validHistory_writePackedProg_bind hw hw hslot hwf2 (hfr2 ▸ hfr1 ▸ hE)
    fun s3 hwf3 hfr3 => ?_
  refine validHistory_writePackedProg_bind hw hw (slot_lt_occLen hslot) hwf3
    (hfr3 ▸ hfr2 ▸ hfr1 ▸ hO) fun s4 hwf4 hfr4 => ?_
  rw [validHistory_bind']
  exact ⟨validHistory_clearSlotProg p henv' hlast hwf4 (hfr4 ▸ hfr3 ▸ hfr2 ▸ hfr1 ▸ ha), trivial⟩

/-- Exact memory charge of `popUnindexedSlotProg` (`7` bit-packed reads + `8` bit-packed writes =
`46`). -/
theorem memoryCost_popUnindexedSlotProg (p : KickTreeParams) (base slot lastSlot : ℕ)
    (s : Memory.State) :
    memoryCost (popUnindexedSlotProg p base slot lastSlot) s = 46 := by
  have hc : ∀ s', memoryCost (clearSlotGenProg ⟨mkKickRuntimeParams p, base, lastSlot⟩) s' = 16 :=
    memoryCost_clearSlotProg p base lastSlot
  unfold popUnindexedSlotProg popUnindexedSlotGenProg readPackedGenProg writePackedGenProg
  iterate 7 rw [memoryCost_bind', memoryCost_readPackedProg, clientState_readPackedProg]
  iterate 4 rw [memoryCost_bind', memoryCost_writePackedProg]
  rw [memoryCost_bind', hc, memoryCost_pure]

/-- Exact pure array-update specification for `popUnindexedSlotProg` (valid for both
`slot ≠ lastSlot` and `slot = lastSlot`): returns `((quotAt ... slot, valAt ... slot),
elevAt ... slot)`, compacts `lastSlot`'s fields into `slot`, and clears all four per-slot fields at
`lastSlot` via `clearSlotProg_spec` while preserving `metaAt`. -/
theorem popUnindexedSlotProg_spec (p : KickTreeParams) (hw : 0 < p.w)
    {base slot lastSlot : ℕ} (hslot : slot < p.nMax) (hlast : lastSlot < p.nMax)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (popUnindexedSlotProg p base slot lastSlot)
    (Memory.spec 0).clientResult s (popUnindexedSlotProg p base slot lastSlot) =
        ((quotAt base p s.mem slot, valAt base p s.mem slot), elevAt base p s.mem slot) ∧
      s'.frontier = s.frontier ∧
      (∀ a, ¬(base + p.hSpace ≤ a ∧ a < base + totalSpace p) → s'.mem a = s.mem a) ∧
      quotAt base p s'.mem =
        Function.update
          (Function.update (quotAt base p s.mem) slot (quotAt base p s.mem lastSlot))
          lastSlot 0 ∧
      valAt base p s'.mem =
        Function.update
          (Function.update (valAt base p s.mem) slot (valAt base p s.mem lastSlot))
          lastSlot 0 ∧
      elevAt base p s'.mem =
        Function.update
          (Function.update (elevAt base p s.mem) slot (elevAt base p s.mem lastSlot))
          lastSlot 0 ∧
      occAt base p s'.mem =
        Function.update
          (Function.update (occAt base p s.mem) slot (occAt base p s.mem lastSlot))
          lastSlot 0 ∧
      metaAt base p s'.mem = metaAt base p s.mem := by
  intro s'
  have hsO : slot < occLen p := slot_lt_occLen hslot
  have hlO : lastSlot < occLen p := slot_lt_occLen hlast
  have hpsQ : readPacked (base + offQuot p) (quotBits p) p.w s.mem slot =
      quotAt base p s.mem slot := by simp [quotAt, hslot]
  have hpsV : readPacked (base + offVal p) (valBits p.V) p.w s.mem slot =
      valAt base p s.mem slot := by simp [valAt, hslot]
  have hpsE : readPacked (base + offElev p) 1 p.w s.mem slot =
      elevAt base p s.mem slot := by simp [elevAt, hslot]
  have hq_eq : readPacked (base + offQuot p) (quotBits p) p.w s.mem lastSlot =
      quotAt base p s.mem lastSlot := by simp [quotAt, hlast]
  have hv_eq : readPacked (base + offVal p) (valBits p.V) p.w s.mem lastSlot =
      valAt base p s.mem lastSlot := by simp [valAt, hlast]
  have he_eq : readPacked (base + offElev p) 1 p.w s.mem lastSlot =
      elevAt base p s.mem lastSlot := by simp [elevAt, hlast]
  have ho_eq : readPacked (base + offOcc p) 1 p.w s.mem lastSlot =
      occAt base p s.mem lastSlot := by simp [occAt, hlO]
  set m1 := writeQuotMem base p s.mem slot (quotAt base p s.mem lastSlot)
  set m2 := writeValMem base p m1 slot (valAt base p s.mem lastSlot)
  set m3 := writeElevMem base p m2 slot (elevAt base p s.mem lastSlot)
  set m4 := writeOccMem base p m3 slot (occAt base p s.mem lastSlot)
  set sMid : Memory.State := { mem := m4, frontier := s.frontier }
  have hres : (Memory.spec 0).clientResult s (popUnindexedSlotProg p base slot lastSlot) =
      ((quotAt base p s.mem slot, valAt base p s.mem slot), elevAt base p s.mem slot) := by
    unfold popUnindexedSlotProg popUnindexedSlotGenProg readPackedGenProg writePackedGenProg
    dsimp only [mkKickRuntimeParams]
    iterate 7 rw [StateTransitionSpec.clientResult_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    iterate 4 rw [StateTransitionSpec.clientResult_bind, clientState_writePackedProg]
    rw [StateTransitionSpec.clientResult_bind]
    change ((_, _), _) = _
    rw [hpsQ, hpsV, hpsE]
  have hst : s' = (Memory.spec 0).clientState sMid (clearSlotProg p base lastSlot) := by
    change (Memory.spec 0).clientState s (popUnindexedSlotProg p base slot lastSlot) = _
    unfold popUnindexedSlotProg popUnindexedSlotGenProg readPackedGenProg writePackedGenProg
    dsimp only
    iterate 7 rw [StateTransitionSpec.clientState_bind,
      clientState_readPackedProg, clientResult_readPackedProg]
    dsimp only [mkKickRuntimeParams]
    rw [hq_eq, hv_eq, he_eq, ho_eq]
    iterate 4 rw [StateTransitionSpec.clientState_bind, clientState_writePackedProg]
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have he1 := writeQuotMem_effects (base := base) p hw s.mem hslot (quotAt_lt base p s.mem lastSlot)
  have he2 := writeValMem_effects (base := base) p hw m1 hslot (valAt_lt base p s.mem lastSlot)
  have he3 := writeElevMem_effects (base := base) p hw m2 hslot (elevAt_lt base p s.mem lastSlot)
  have he4 := writeOccMem_effects (base := base) p hw m3 hsO (occAt_lt base p s.mem lastSlot)
  obtain ⟨hc_fr, hc_out, hc_q, hc_v, hc_e, hc_o, hc_m⟩ :=
    clearSlotProg_spec p hw (base := base) hlast sMid
  rw [hst]
  refine ⟨hres, hc_fr, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hc_out a ha).trans
      ((he4.2.2.2.2.2 a (not_in_occ_of_outside ha)).trans
        ((he3.2.2.2.2.2 a (not_in_elev_of_outside ha)).trans
          ((he2.2.2.2.2.2 a (not_in_val_of_outside ha)).trans
            (he1.2.2.2.2.2 a (not_in_quot_of_outside ha)))))
  · rw [hc_q]; dsimp only [sMid]; rw [he4.1, he3.1, he2.1, he1.1]
  · rw [hc_v]; dsimp only [sMid]; rw [he4.2.1, he3.2.1, he2.2.1, he1.2.1]
  · rw [hc_e]; dsimp only [sMid]; rw [he4.2.2.2.1, he3.2.2.2.1, he2.2.2.2.1, he1.2.2.2.1]
  · rw [hc_o]; dsimp only [sMid]; rw [he4.2.2.1, he3.2.2.1, he2.2.2.1, he1.2.2.1]
  · rw [hc_m]; dsimp only [sMid]; rw [he4.2.2.2.2.1, he3.2.2.2.2.1, he2.2.2.2.2.1, he1.2.2.2.2.1]

end Cslib.DataStructure.Dictionary.WordRAM.KickTree
