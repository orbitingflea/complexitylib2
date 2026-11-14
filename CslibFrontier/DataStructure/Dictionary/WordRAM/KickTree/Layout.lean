/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
public import CslibFrontier.Foundations.Data.Nat.IterLog
import CslibFrontier.DataStructure.BallsToSlots.KickTree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameterized Bit-Packed Word-RAM Memory Layout for `k`-Kick Tree Slot Tables

This module defines a parameterized bit-packed Word-RAM memory layout and pure array extraction and
update laws for fixed-capacity `k`-kick tree slot tables toward the dynamic dictionary of Bender,
Farach-Colton, J. Kuszmaul, W. Kuszmaul, and Liu ([BenderFarachColtonKuszmaulKuszmaulLiu2022],
`arXiv:2111.00602v2`, Sections 3.1 and 5.1–5.3):

1. `[base, base + p.hSpace)`: `p.hSpace` words parameterized for hash seeds, precomputed
   Four-Russians word lookup tables, and fixed-size directory headers (mirroring
   `SuccinctLayout`'s `h_space` convention rather than hardcoding seed or table sizes).
2. `Quotients` (`offQuot p`): `packedWords p.nMax (fullQuotBits p.U p.nMax) p.w` words storing
   `p.nMax` quotients of `fullQuotBits p.U p.nMax` bits.
3. `Values` (`offVal p`): `packedWords p.nMax (valBits p.V) p.w` words storing `p.nMax` values of
   `valBits p.V` bits.
4. `Occupancy` (`offOcc p`): `packedWords (4 * p.nMax) 1 p.w` words storing `4 * p.nMax` 1-bit
   flags (`0 .. p.nMax - 1` for primary slot occupancy independent of zero quotients, plus up to
   `3 * p.nMax` free-slot bitmap bits).
5. `SlotMeta` (`offMeta p`): `packedWords (p.cMeta * p.nMax) (metaBits p) p.w` words storing
   `p.cMeta * p.nMax` entries of `metaBits p = max (Nat.iterLog p.k p.nMax) 1` bits (parameterized
   by multiplicity `p.cMeta` to accommodate per-slot kick-depth tags and auxiliary router/cubby
   metadata sub-arrays).

## Source attribution

* [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 3.1 (printed pp. 8–10 / PDF pp. 9–11) and Theorem 2 (printed p. 11 / PDF p. 12):
    `k`-kick tree slot hierarchy, priority depths, and worst-case switching cost `k + 1`.
  - Section 5.1–5.3 (printed pp. 27–35 / PDF pp. 28–36): free-slot bitmaps, cubby/router metadata
    budgets `O(n_max log^(k) n_max)`, tail replacement, and quotiented payload bit accounting.
  - Explicit layout adaptation: header/table word count `p.hSpace` and metadata array multiplicity
    `p.cMeta` are kept as explicit parameters in `KickTreeParams`, yielding the exact deterministic
    word bound `totalSpace p ≤ kickTreeWords (p.cMeta + 6) (p.hSpace + 11) p.U p.V p.w p.k p.nMax`
    via `BitPackedArray` ceiling-division subadditivity.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickTreeParams`, `defaultKickLimit`,
  `mkKickTreeParams`, `kickTreeParamsWords`: configuration record and 8-word encoding.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.offQuot`, `quotWords`, `offVal`, `valWords`,
  `occLen`, `offOcc`, `occWords`, `metaBits`, `metaLen`, `offMeta`, `metaWords`, `totalSpace`:
  bit-packed block offsets, bit/entry counts, and total word footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.kickTreeWords`: succinct word-space bound.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.quotAt`, `valAt`, `occAt`, `metaAt`,
  `writeQuotMem`, `writeValMem`, `writeOccMem`, `writeMetaMem`: pure bit-packed array extraction
  and update functions.

## Main results

* `totalSpace_eq`, `quot_end_le_totalSpace`, `val_end_le_totalSpace`, `occ_end_le_totalSpace`,
  `meta_end_le_totalSpace`: block footprint decompositions and bounds.
* `totalSpace_le_kickTreeWords`: `totalSpace p` is bounded by
  `kickTreeWords (p.cMeta + 6) (p.hSpace + 11) p.U p.V p.w p.k p.nMax`.
* `kickTreeWords_le_succinctWords`: specialization at `k = 2` connects to `Dynamic.succinctWords`.
* `quotAt_lt`, `valAt_lt`, `occAt_lt`, `metaAt_lt`: bit-width bounds on extracted entries.
* `quotAt_zero_of_init`, `valAt_zero_of_init`, `occAt_zero_of_init`, `metaAt_zero_of_init`:
  extracted arrays are identically zero when `[base + p.hSpace, base + totalSpace p)` is zeroed.
* `arrays_congr_of_eq_on`: extracted arrays depend only on `[base + p.hSpace, base + totalSpace p)`.
* `writeQuotMem_effects`, `writeValMem_effects`, `writeOccMem_effects`, `writeMetaMem_effects`:
  exact `Function.update` and cross-array non-interference laws for bit-packed updates.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022],
  STOC 2022, pp. 1284–1297 (`arXiv:2111.00602v2`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.KickTree

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.KickTree
open Cslib.DataStructure.Dictionary.FeistelQuotient

/-! ### 1. Parameter record and memory offsets -/

/-- Parameterized Word-RAM layout configuration for a fixed-capacity `k`-kick tree slot table
([BenderFarachColtonKuszmaulKuszmaulLiu2022], Sections 3.1 and 5.1–5.3). -/
structure KickTreeParams where
  /-- Machine word width `w`. -/
  w : ℕ
  /-- Primary slot capacity `nMax`. -/
  nMax : ℕ
  /-- Key universe size `U`. -/
  U : ℕ
  /-- Value range size `V`. -/
  V : ℕ
  /-- Kick parameter `k`. -/
  k : ℕ
  /-- Worst-case kick step limit (`k + 1` per Section 3.1 / Theorem 2). -/
  kickLimit : ℕ
  /-- Reserved header word count `[base, base + hSpace)` for hash seeds, Four-Russians word
  lookup tables, and fixed-size headers. -/
  hSpace : ℕ
  /-- Multiplicity of `metaBits`-wide entries per slot in `SlotMeta` (`cMeta * nMax` entries). -/
  cMeta : ℕ
deriving Repr, DecidableEq

/-- Default kick step limit `k + 1` from Section 3.1 / Theorem 2 switching cost. -/
@[expose] def defaultKickLimit (k : ℕ) : ℕ := k + 1

/-- Canonical constructor for `KickTreeParams` setting `kickLimit := defaultKickLimit k`. -/
@[expose] def mkKickTreeParams (w nMax U V k hSpace cMeta : ℕ) : KickTreeParams where
  w := w
  nMax := nMax
  U := U
  V := V
  k := k
  kickLimit := defaultKickLimit k
  hSpace := hSpace
  cMeta := cMeta

/-- 8-word encoding embedding for `KickTreeParams`. -/
def kickTreeParamsWords : KickTreeParams ↪ (Fin 8 → ℕ) where
  toFun p := ![p.w, p.nMax, p.U, p.V, p.k, p.kickLimit, p.hSpace, p.cMeta]
  inj' := by
    intro p₁ p₂ h
    have h0 := congrFun h ⟨0, by decide⟩
    have h1 := congrFun h ⟨1, by decide⟩
    have h2 := congrFun h ⟨2, by decide⟩
    have h3 := congrFun h ⟨3, by decide⟩
    have h4 := congrFun h ⟨4, by decide⟩
    have h5 := congrFun h ⟨5, by decide⟩
    have h6 := congrFun h ⟨6, by decide⟩
    have h7 := congrFun h ⟨7, by decide⟩
    cases p₁; cases p₂; dsimp at h0 h1 h2 h3 h4 h5 h6 h7
    rw [h0, h1, h2, h3, h4, h5, h6, h7]

instance : WordEncoding KickTreeParams := ⟨8, kickTreeParamsWords⟩

/-- Word offset of the bit-packed `Quotients` array relative to `base`. -/
@[expose] def offQuot (p : KickTreeParams) : ℕ := p.hSpace

/-- Word size of the bit-packed `Quotients` array (`p.nMax` entries). -/
@[expose] def quotWords (p : KickTreeParams) : ℕ :=
  packedWords p.nMax (fullQuotBits p.U p.nMax) p.w

/-- Word offset of the bit-packed `Values` array relative to `base`. -/
@[expose] def offVal (p : KickTreeParams) : ℕ :=
  offQuot p + quotWords p

/-- Word size of the bit-packed `Values` array (`p.nMax` entries). -/
@[expose] def valWords (p : KickTreeParams) : ℕ :=
  packedWords p.nMax (valBits p.V) p.w

/-- Number of 1-bit entries in `Occupancy` (`4 * p.nMax`: primary slot occupancy in
`0 .. p.nMax - 1` plus up to `3 * p.nMax` free-slot bitmap bits). -/
@[expose] def occLen (p : KickTreeParams) : ℕ := 4 * p.nMax

/-- Word offset of the bit-packed `Occupancy` bitmap relative to `base`. -/
@[expose] def offOcc (p : KickTreeParams) : ℕ :=
  offVal p + valWords p

/-- Word size of the bit-packed `Occupancy` bitmap. -/
@[expose] def occWords (p : KickTreeParams) : ℕ :=
  packedWords (occLen p) 1 p.w

/-- Bit width `max (Nat.iterLog p.k p.nMax) 1` of each entry in `SlotMeta`. -/
@[expose] def metaBits (p : KickTreeParams) : ℕ :=
  max (Nat.iterLog p.k p.nMax) 1

/-- Number of entries `p.cMeta * p.nMax` in `SlotMeta`. -/
@[expose] def metaLen (p : KickTreeParams) : ℕ := p.cMeta * p.nMax

/-- Word offset of the bit-packed `SlotMeta` array relative to `base`. -/
@[expose] def offMeta (p : KickTreeParams) : ℕ :=
  offOcc p + occWords p

/-- Word size of the bit-packed `SlotMeta` array. -/
@[expose] def metaWords (p : KickTreeParams) : ℕ :=
  packedWords (metaLen p) (metaBits p) p.w

/-- Total word footprint `[base, base + totalSpace p)` of the layout. -/
@[expose] def totalSpace (p : KickTreeParams) : ℕ :=
  offMeta p + metaWords p

/-! ### 2. Space bound theorems -/

/-- Total space decomposition identity. -/
theorem totalSpace_eq (p : KickTreeParams) :
    totalSpace p = p.hSpace + quotWords p + valWords p + occWords p + metaWords p := by
  unfold totalSpace offMeta offOcc offVal offQuot
  omega

/-- The `Quotients` block ends at or before `totalSpace p`. -/
theorem quot_end_le_totalSpace (p : KickTreeParams) :
    offQuot p + quotWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offQuot; omega

/-- The `Values` block ends at or before `totalSpace p`. -/
theorem val_end_le_totalSpace (p : KickTreeParams) :
    offVal p + valWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offVal offQuot; omega

/-- The `Occupancy` block ends at or before `totalSpace p`. -/
theorem occ_end_le_totalSpace (p : KickTreeParams) :
    offOcc p + occWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offOcc offVal offQuot; omega

/-- The `SlotMeta` block ends at or before `totalSpace p`. -/
theorem meta_end_le_totalSpace (p : KickTreeParams) :
    offMeta p + metaWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offMeta offOcc offVal offQuot; omega

/-- Succinct word-space bound for the `k`-kick tree dynamic dictionary:
`⌈(OPT(U, V, n_max) + C * n_max * max (Nat.iterLog k n_max) 1) / w⌉ + C₀`. -/
@[expose] def kickTreeWords (C C₀ U V w k n_max : ℕ) : ℕ :=
  (Dynamic.optBits U V n_max + C * n_max * max (Nat.iterLog k n_max) 1 + w - 1) / w + C₀

/-- Specialization: for `k = 2`, `kickTreeWords` is bounded by `Dynamic.succinctWords`
via `BallsToSlots.max_iterLog_two_le_logLogFactor`. -/
theorem kickTreeWords_le_succinctWords (C C₀ U V w n_max : ℕ) :
    kickTreeWords C C₀ U V w 2 n_max ≤ Dynamic.succinctWords C C₀ U V w n_max := by
  unfold kickTreeWords Dynamic.succinctWords
  have hle := BallsToSlots.max_iterLog_two_le_logLogFactor n_max
  have hmul : C * n_max * max (Nat.iterLog 2 n_max) 1 ≤
      C * n_max * Dynamic.logLogFactor n_max :=
    Nat.mul_le_mul_left _ hle
  have hadd : Dynamic.optBits U V n_max + C * n_max * max (Nat.iterLog 2 n_max) 1 + w - 1 ≤
      Dynamic.optBits U V n_max + C * n_max * Dynamic.logLogFactor n_max + w - 1 := by
    omega
  exact Nat.add_le_add_right (Nat.div_le_div_right hadd) _

/-- Master deterministic word-space bound: `totalSpace p` is bounded by
`kickTreeWords (p.cMeta + 6) (p.hSpace + 11) p.U p.V p.w p.k p.nMax`. -/
theorem totalSpace_le_kickTreeWords (p : KickTreeParams) :
    totalSpace p ≤
      kickTreeWords (p.cMeta + 6) (p.hSpace + 11) p.U p.V p.w p.k p.nMax := by
  rw [totalSpace_eq]
  have h12 := packedWords_add_le p.nMax (fullQuotBits p.U p.nMax) p.nMax (valBits p.V) p.w
  have h123 := div_add_packedWords_le
    (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V) 5
    (occLen p) 1 p.w
  have h1234 := div_add_packedWords_le
    (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V + occLen p * 1) 8
    (metaLen p) (metaBits p) p.w
  have hopt := mul_fullQuotBits_add_valBits_le_optBits p.U p.V p.nMax
  set M := metaBits p
  have hM : 1 ≤ M := le_max_right _ _
  have hterm1 : p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V ≤
      Dynamic.optBits p.U p.V p.nMax + 2 * p.nMax := by
    rw [← Nat.mul_add]; exact hopt
  have h6M : 6 * p.nMax ≤ 6 * p.nMax * M := by
    simpa using Nat.mul_le_mul_left (6 * p.nMax) hM
  have hnum_le : p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V +
      occLen p * 1 + metaLen p * M ≤
      Dynamic.optBits p.U p.V p.nMax + (p.cMeta + 6) * p.nMax * M := by
    calc p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V +
          occLen p * 1 + metaLen p * M
      _ = (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V) +
          4 * p.nMax + p.cMeta * p.nMax * M := by
        unfold occLen metaLen; ring
      _ ≤ Dynamic.optBits p.U p.V p.nMax + 2 * p.nMax + 4 * p.nMax +
          p.cMeta * p.nMax * M := by linarith [hterm1]
      _ = Dynamic.optBits p.U p.V p.nMax + 6 * p.nMax + p.cMeta * p.nMax * M := by ring
      _ ≤ Dynamic.optBits p.U p.V p.nMax + 6 * p.nMax * M + p.cMeta * p.nMax * M := by
        linarith [h6M]
      _ = Dynamic.optBits p.U p.V p.nMax + (p.cMeta + 6) * p.nMax * M := by ring
  have hdiv : (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V +
      occLen p * 1 + metaLen p * M + p.w - 1) / p.w ≤
      (Dynamic.optBits p.U p.V p.nMax + (p.cMeta + 6) * p.nMax * M + p.w - 1) / p.w :=
    Nat.div_le_div_right (by omega)
  unfold kickTreeWords quotWords valWords occWords metaWords
  have hM_def : max (Nat.iterLog p.k p.nMax) 1 = M := rfl
  have hM_meta : metaBits p = M := rfl
  rw [hM_def, hM_meta] at *
  omega

/-! ### 3. Pure extraction and update functions -/

/-- Pure extraction function for `Quotients[idx]` (`0` for `idx ≥ p.nMax`). -/
@[expose] def quotAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.nMax then
    readPacked (base + offQuot p) (fullQuotBits p.U p.nMax) p.w mem idx
  else 0

/-- Pure extraction function for `Values[idx]` (`0` for `idx ≥ p.nMax`). -/
@[expose] def valAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.nMax then
    readPacked (base + offVal p) (valBits p.V) p.w mem idx
  else 0

/-- Pure extraction function for `Occupancy[idx]` (`0` for `idx ≥ occLen p`). -/
@[expose] def occAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < occLen p then
    readPacked (base + offOcc p) 1 p.w mem idx
  else 0

/-- Pure extraction function for `SlotMeta[idx]` (`0` for `idx ≥ metaLen p`). -/
@[expose] def metaAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < metaLen p then
    readPacked (base + offMeta p) (metaBits p) p.w mem idx
  else 0

/-- Pure bit-packed update of `Quotients[idx]` to `val`. -/
@[expose] def writeQuotMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offQuot p) (fullQuotBits p.U p.nMax) p.w mem idx val

/-- Pure bit-packed update of `Values[idx]` to `val`. -/
@[expose] def writeValMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offVal p) (valBits p.V) p.w mem idx val

/-- Pure bit-packed update of `Occupancy[idx]` to `val`. -/
@[expose] def writeOccMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offOcc p) 1 p.w mem idx val

/-- Pure bit-packed update of `SlotMeta[idx]` to `val`. -/
@[expose] def writeMetaMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offMeta p) (metaBits p) p.w mem idx val

/-! ### 4. Value range, zero-initialization, congruence, and update laws -/

/-- Value range invariant for `quotAt`: every entry is `< 2 ^ fullQuotBits p.U p.nMax`. -/
theorem quotAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt base p mem idx < 2 ^ fullQuotBits p.U p.nMax := by
  unfold quotAt; split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `valAt`: every entry is `< 2 ^ valBits p.V`. -/
theorem valAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    valAt base p mem idx < 2 ^ valBits p.V := by
  unfold valAt; split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `occAt`: every entry is `< 2 ^ 1`. -/
theorem occAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    occAt base p mem idx < 2 ^ 1 := by
  unfold occAt; split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `metaAt`: every entry is `< 2 ^ metaBits p`. -/
theorem metaAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    metaAt base p mem idx < 2 ^ metaBits p := by
  unfold metaAt; split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- On zeroed array memory `[base + p.hSpace, base + totalSpace p)`, `quotAt` is identically `0`. -/
theorem quotAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem a = 0) :
    quotAt base p mem = fun _ => 0 := by
  funext idx; unfold quotAt; split_ifs with hidx
  · have hlt1 : wordOffset (fullQuotBits p.U p.nMax) p.w idx + 1 < quotWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := quot_end_le_totalSpace p
    unfold offQuot at hbound ⊢
    exact readPacked_zero (hzero _ (by omega) (by omega)) (hzero _ (by omega) (by omega))
  · rfl

/-- On zeroed array memory `[base + p.hSpace, base + totalSpace p)`, `valAt` is identically `0`. -/
theorem valAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem a = 0) :
    valAt base p mem = fun _ => 0 := by
  funext idx; unfold valAt; split_ifs with hidx
  · have hlt1 : wordOffset (valBits p.V) p.w idx + 1 < valWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := val_end_le_totalSpace p
    have hoff : p.hSpace ≤ offVal p := by unfold offVal offQuot; omega
    exact readPacked_zero (hzero _ (by omega) (by omega)) (hzero _ (by omega) (by omega))
  · rfl

/-- On zeroed array memory `[base + p.hSpace, base + totalSpace p)`, `occAt` is identically `0`. -/
theorem occAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem a = 0) :
    occAt base p mem = fun _ => 0 := by
  funext idx; unfold occAt; split_ifs with hidx
  · have hlt1 : wordOffset 1 p.w idx + 1 < occWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := occ_end_le_totalSpace p
    have hoff : p.hSpace ≤ offOcc p := by unfold offOcc offVal offQuot; omega
    exact readPacked_zero (hzero _ (by omega) (by omega)) (hzero _ (by omega) (by omega))
  · rfl

/-- On zeroed array memory `[base + p.hSpace, base + totalSpace p)`, `metaAt` is identically `0`. -/
theorem metaAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem a = 0) :
    metaAt base p mem = fun _ => 0 := by
  funext idx; unfold metaAt; split_ifs with hidx
  · have hlt1 : wordOffset (metaBits p) p.w idx + 1 < metaWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := meta_end_le_totalSpace p
    have hoff : p.hSpace ≤ offMeta p := by unfold offMeta offOcc offVal offQuot; omega
    exact readPacked_zero (hzero _ (by omega) (by omega)) (hzero _ (by omega) (by omega))
  · rfl

/-- Memories agreeing on `[base + p.hSpace, base + totalSpace p)` yield identical extracted
arrays. -/
theorem arrays_congr_of_eq_on {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem₁ a = mem₂ a) :
    quotAt base p mem₁ = quotAt base p mem₂ ∧
      valAt base p mem₁ = valAt base p mem₂ ∧
      occAt base p mem₁ = occAt base p mem₂ ∧
      metaAt base p mem₁ = metaAt base p mem₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext idx; unfold quotAt; split_ifs with hidx
    · have hbound := quot_end_le_totalSpace p
      exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by unfold offQuot at ha1; omega)
          (by dsimp [quotWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold valAt; split_ifs with hidx
    · have hbound := val_end_le_totalSpace p
      have hoff : p.hSpace ≤ offVal p := by unfold offVal offQuot; omega
      exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [valWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold occAt; split_ifs with hidx
    · have hbound := occ_end_le_totalSpace p
      have hoff : p.hSpace ≤ offOcc p := by unfold offOcc offVal offQuot; omega
      exact readPacked_congr (N := occLen p) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [occWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold metaAt; split_ifs with hidx
    · have hbound := meta_end_le_totalSpace p
      have hoff : p.hSpace ≤ offMeta p := by unfold offMeta offOcc offVal offQuot; omega
      exact readPacked_congr (N := metaLen p) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [metaWords] at hbound; omega)) hidx
    · rfl

/-- Exact array update and cross-array frame law for `writeQuotMem`. -/
theorem writeQuotMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < p.nMax) (hval : val < 2 ^ fullQuotBits p.U p.nMax) :
    quotAt base p (writeQuotMem base p mem idx val) = Function.update (quotAt base p mem) idx val ∧
      valAt base p (writeQuotMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeQuotMem base p mem idx val) = occAt base p mem ∧
      metaAt base p (writeQuotMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offQuot p ≤ a ∧ a < base + offQuot p + quotWords p) →
        writeQuotMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offQuot p ≤ a ∧ a < base + offQuot p + quotWords p) →
      writeQuotMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨?_, ?_, ?_, ?_, hout⟩
  · funext i; by_cases hi : i = idx
    · subst hi; simp [quotAt, hidx, writeQuotMem, readPacked_writePacked_self _ _ _ _ _ hval]
    · unfold quotAt; rw [Function.update_of_ne hi]; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem hi val
      · rfl
  · funext i; unfold valAt; split_ifs with hlt
    · exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offVal at ha1; omega)) hlt
    · rfl
  · funext i; unfold occAt; split_ifs with hlt
    · exact readPacked_congr (N := occLen p) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offOcc offVal at ha1; omega)) hlt
    · rfl
  · funext i; unfold metaAt; split_ifs with hlt
    · exact readPacked_congr (N := metaLen p) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offMeta offOcc offVal at ha1; omega)) hlt
    · rfl

/-- Exact array update and cross-array frame law for `writeValMem`. -/
theorem writeValMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < p.nMax) (hval : val < 2 ^ valBits p.V) :
    quotAt base p (writeValMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeValMem base p mem idx val) = Function.update (valAt base p mem) idx val ∧
      occAt base p (writeValMem base p mem idx val) = occAt base p mem ∧
      metaAt base p (writeValMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offVal p ≤ a ∧ a < base + offVal p + valWords p) →
        writeValMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offVal p ≤ a ∧ a < base + offVal p + valWords p) →
      writeValMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨?_, ?_, ?_, ?_, hout⟩
  · funext i; unfold quotAt; split_ifs with hlt
    · exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offVal; dsimp [quotWords]; omega)) hlt
    · rfl
  · funext i; by_cases hi : i = idx
    · subst hi; simp [valAt, hidx, writeValMem, readPacked_writePacked_self _ _ _ _ _ hval]
    · unfold valAt; rw [Function.update_of_ne hi]; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem hi val
      · rfl
  · funext i; unfold occAt; split_ifs with hlt
    · exact readPacked_congr (N := occLen p) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offOcc at ha1; omega)) hlt
    · rfl
  · funext i; unfold metaAt; split_ifs with hlt
    · exact readPacked_congr (N := metaLen p) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offMeta offOcc at ha1; omega)) hlt
    · rfl

/-- Exact array update and cross-array frame law for `writeOccMem`. -/
theorem writeOccMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < occLen p) (hval : val < 2 ^ 1) :
    quotAt base p (writeOccMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeOccMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeOccMem base p mem idx val) = Function.update (occAt base p mem) idx val ∧
      metaAt base p (writeOccMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offOcc p ≤ a ∧ a < base + offOcc p + occWords p) →
        writeOccMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offOcc p ≤ a ∧ a < base + offOcc p + occWords p) →
      writeOccMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨?_, ?_, ?_, ?_, hout⟩
  · funext i; unfold quotAt; split_ifs with hlt
    · exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offOcc offVal; dsimp [quotWords]; omega)) hlt
    · rfl
  · funext i; unfold valAt; split_ifs with hlt
    · exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offOcc; dsimp [valWords]; omega)) hlt
    · rfl
  · funext i; by_cases hi : i = idx
    · subst hi; simp [occAt, hidx, writeOccMem, readPacked_writePacked_self _ _ _ _ _ hval]
    · unfold occAt; rw [Function.update_of_ne hi]; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem hi val
      · rfl
  · funext i; unfold metaAt; split_ifs with hlt
    · exact readPacked_congr (N := metaLen p) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offMeta at ha1; omega)) hlt
    · rfl

/-- Exact array update and cross-array frame law for `writeMetaMem`. -/
theorem writeMetaMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < metaLen p) (hval : val < 2 ^ metaBits p) :
    quotAt base p (writeMetaMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeMetaMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeMetaMem base p mem idx val) = occAt base p mem ∧
      metaAt base p (writeMetaMem base p mem idx val) =
        Function.update (metaAt base p mem) idx val ∧
      (∀ a, ¬(base + offMeta p ≤ a ∧ a < base + offMeta p + metaWords p) →
        writeMetaMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offMeta p ≤ a ∧ a < base + offMeta p + metaWords p) →
      writeMetaMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨?_, ?_, ?_, ?_, hout⟩
  · funext i; unfold quotAt; split_ifs with hlt
    · exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offMeta offOcc offVal; dsimp [quotWords]; omega)) hlt
    · rfl
  · funext i; unfold valAt; split_ifs with hlt
    · exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offMeta offOcc; dsimp [valWords]; omega)) hlt
    · rfl
  · funext i; unfold occAt; split_ifs with hlt
    · exact readPacked_congr (N := occLen p) hw (fun a ⟨ha1, ha2⟩ =>
        hout a (by unfold offMeta; dsimp [occWords]; omega)) hlt
    · rfl
  · funext i; by_cases hi : i = idx
    · subst hi; simp [metaAt, hidx, writeMetaMem, readPacked_writePacked_self _ _ _ _ _ hval]
    · unfold metaAt; rw [Function.update_of_ne hi]; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem hi val
      · rfl

end Cslib.DataStructure.Dictionary.WordRAM.KickTree
