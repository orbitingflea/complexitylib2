/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
public import CslibFrontier.Foundations.Data.Nat.IterLog
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
2. `Quotients` (`offQuot p`): `packedWords p.nMax (quotBits p) p.w` words storing
   `p.nMax` quotients of `quotBits p` bits (`fullQuotBits p.U p.nMax` when quotiented,
   or `keyBits p.U` under the local adaptation `p.quotiented = false` for unindexed `[0, len)`
   tail-cubby arrays).
3. `Values` (`offVal p`): `packedWords p.nMax (valBits p.V) p.w` words storing `p.nMax` values of
   `valBits p.V` bits.
4. `Occupancy` (`offOcc p`): `packedWords (4 * p.nMax) 1 p.w` words storing `4 * p.nMax` 1-bit
   flags (`0 .. p.nMax - 1` for primary slot occupancy independent of zero quotients, plus up to
   `3 * p.nMax` free-slot bitmap bits).
5. `Elevated` (`offElev p`, local formalization adaptation): `packedWords p.nMax 1 p.w` words
   storing `p.nMax` 1-bit per-slot flags (`0` = occupant has priority depth `0`, `1` = occupant has
   elevated priority depth `≥ 1`), tracking whether a primary slot holds a non-depth-0 item so
   elevated status is preserved during kicks without dense multi-bit per-slot depth tags.
6. `SlotMeta` (`offMeta p`): `packedWords (p.cMeta * p.nMax) (metaBits p) p.w` words storing
   `p.cMeta * p.nMax` entries of `metaBits p = max (Nat.iterLog (p.k + 1) p.nMax) 1` bits for
   sparse auxiliary bin/router/cubby metadata (including elevated kick depths; parameterized by
   multiplicity `p.cMeta`). Under the 0-indexed `k`-kick tree convention of Section 3.1 / Theorem 2
   (switching-cost budget `k + 1`), a `k`-kick tree incurs `O(n_max log^(k + 1) n_max)` metadata
   bits (corresponding to Section 5.3 / Theorem 21's quotiented `(k' - 1)`-kick tree with `O(k')`
   time and `OPT + O(n_max log^(k') n_max)` bits for `k' = k + 1`).

## Source attribution and formalization adaptations

* **Primary source** — [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 3.1 (printed pp. 8–12 / PDF pp. 9–13) and Theorem 2 (printed p. 12 / PDF p. 13):
    0-indexed `k`-kick tree slot hierarchy (`k ≥ 0`), priority depths, and worst-case switching
    cost `k + 1`.
  - Section 5.1–5.2 (printed pp. 27–32 / PDF pp. 28–33): free-slot bitmaps and sparse
    `O(n_max log^(k + 1) n_max)` bin/router/cubby metadata (`occAt`, `metaAt`).
  - Section 5.3 and Theorem 21 (printed pp. 33–35 / PDF pp. 34–36): quotiented payload bit
    accounting (`OPT(U, V, n_max) + O(n_max log^(k + 1) n_max)` bits; `quotAt`, `valAt`,
    `totalSpace_le_kickTreeWords`).
* **Local formalization adaptations**:
  - Dedicated 1-bit per-slot `Elevated` (`depth ≥ 1`) bitmap (`offElev`, `elevAt`, `p.nMax` bits)
    tracking elevated priority status directly per primary slot rather than only through §§5.1–5.2's
    sparse bin/router metadata.
  - Unindexed `[0, len)` tail-cubby slot mode (`p.quotiented = false`, allocating full `keyBits p.U`
    keys in `Quotients` for swap-compacted `Facility.TailCubby` arrays).
  - Header/table word count `p.hSpace` and metadata array multiplicity `p.cMeta` are kept as
    explicit parameters in `KickTreeParams`, yielding the exact deterministic word bound
    `totalSpace p ≤ kickTreeWords (p.cMeta + 7) (p.hSpace + 14) p.U p.V p.w p.k p.nMax` via
    `BitPackedArray` ceiling-division subadditivity.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickTreeParams`,
  `mkKickTreeParams`: layout configuration record and canonical constructor.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.quotBits`, `offQuot`, `quotWords`, `offVal`,
  `valWords`, `occLen`, `offOcc`, `occWords`, `offElev`, `elevWords`, `metaBits`, `metaLen`,
  `offMeta`, `metaWords`, `totalSpace`: bit-packed block offsets, bit/entry counts, and word counts.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.kickTreeWords`: succinct word-space bound.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.quotAt`, `valAt`, `occAt`, `elevAt`, `metaAt`,
  `writeQuotMem`, `writeValMem`, `writeOccMem`, `writeElevMem`, `writeMetaMem`: pure bit-packed
  array extraction and update functions.

## Main results

* `totalSpace_eq`, `quot_end_le_totalSpace`, `val_end_le_totalSpace`, `occ_end_le_totalSpace`,
  `elev_end_le_totalSpace`, `meta_end_le_totalSpace`: block footprint decompositions and bounds.
* `totalSpace_le_kickTreeWords`: `totalSpace p` is bounded by
  `kickTreeWords (p.cMeta + 7) (p.hSpace + 14) p.U p.V p.w p.k p.nMax`.
* `kickTreeWords_le_succinctWords`: specialization at `k = 1` (`1`-kick tree, `iterLog 2`) connects
  to `Dynamic.succinctWords`.
* `quotAt_lt`, `valAt_lt`, `occAt_lt`, `elevAt_lt`, `metaAt_lt`: bit-width bounds on extracted
  entries.
* `quotAt_zero_of_init`, `valAt_zero_of_init`, `occAt_zero_of_init`, `elevAt_zero_of_init`,
  `metaAt_zero_of_init`: extracted arrays are identically zero when
  `[base + p.hSpace, base + totalSpace p)` is zeroed.
* `arrays_congr_of_eq_on`: extracted arrays depend only on `[base + p.hSpace, base + totalSpace p)`.
* `writeQuotMem_effects`, `writeValMem_effects`, `writeOccMem_effects`, `writeElevMem_effects`,
  `writeMetaMem_effects`: exact `Function.update` and cross-array non-interference laws.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022],
  STOC 2022, pp. 1284–1297 (`arXiv:2111.00602v2`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.KickTree

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
  /-- 0-indexed kick parameter `k` (`k ≥ 0`, with switching cost `k + 1` and iterated-log overhead
  `Nat.iterLog (k + 1) nMax`). -/
  k : ℕ
  /-- Worst-case kick step limit (`k + 1` per Section 3.1 / Theorem 2). -/
  kickLimit : ℕ
  /-- Reserved header word count `[base, base + hSpace)` for hash seeds, Four-Russians word
  lookup tables, and fixed-size headers. -/
  hSpace : ℕ
  /-- Multiplicity of `metaBits`-wide entries per slot in `SlotMeta` (`cMeta * nMax` entries). -/
  cMeta : ℕ
  /-- Whether slots store quotiented keys (`fullQuotBits p.U p.nMax`) or full keys
  (`keyBits p.U`, a local adaptation for unindexed `[0, len)` tail-cubby arrays). -/
  quotiented : Bool := true
deriving Repr, DecidableEq

/-- Canonical constructor for `KickTreeParams` setting `kickLimit := k + 1` (Section 3.1 /
Theorem 2 switching cost). -/
@[expose] def mkKickTreeParams (w nMax U V k hSpace cMeta : ℕ) (quotiented : Bool := true) :
    KickTreeParams where
  w := w
  nMax := nMax
  U := U
  V := V
  k := k
  kickLimit := k + 1
  hSpace := hSpace
  cMeta := cMeta
  quotiented := quotiented

/-- Number of bits allocated per quotient entry: `fullQuotBits p.U p.nMax` when quotiented,
or full key size `keyBits p.U` under the local adaptation `p.quotiented = false` for unindexed
tail-cubby arrays. -/
@[expose] def quotBits (p : KickTreeParams) : ℕ :=
  if p.quotiented then fullQuotBits p.U p.nMax else keyBits p.U

/-- Word offset of the bit-packed `Quotients` array relative to `base`. -/
@[expose] def offQuot (p : KickTreeParams) : ℕ := p.hSpace

/-- Word size of the bit-packed `Quotients` array (`p.nMax` entries). -/
@[expose] def quotWords (p : KickTreeParams) : ℕ :=
  packedWords p.nMax (quotBits p) p.w

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

/-- Word offset of the 1-bit per-slot `Elevated` (`depth ≥ 1`) bitmap relative to `base`. -/
@[expose] def offElev (p : KickTreeParams) : ℕ :=
  offOcc p + occWords p

/-- Word size of the 1-bit per-slot `Elevated` bitmap (`p.nMax` entries). -/
@[expose] def elevWords (p : KickTreeParams) : ℕ :=
  packedWords p.nMax 1 p.w

/-- Bit width `max (Nat.iterLog (p.k + 1) p.nMax) 1` of each entry in `SlotMeta` (matching the
`O(n_max log^(k + 1) n_max)` bit overhead of a 0-indexed `k`-kick tree). -/
@[expose] def metaBits (p : KickTreeParams) : ℕ :=
  max (Nat.iterLog (p.k + 1) p.nMax) 1

/-- Number of entries `p.cMeta * p.nMax` in `SlotMeta`. -/
@[expose] def metaLen (p : KickTreeParams) : ℕ := p.cMeta * p.nMax

/-- Word offset of the bit-packed `SlotMeta` array relative to `base`. -/
@[expose] def offMeta (p : KickTreeParams) : ℕ :=
  offElev p + elevWords p

/-- Word size of the bit-packed `SlotMeta` array. -/
@[expose] def metaWords (p : KickTreeParams) : ℕ :=
  packedWords (metaLen p) (metaBits p) p.w

/-- Total word footprint `[base, base + totalSpace p)` of the layout. -/
@[expose] def totalSpace (p : KickTreeParams) : ℕ :=
  offMeta p + metaWords p

/-! ### 2. Space bound theorems -/

/-- Total space decomposition identity. -/
theorem totalSpace_eq (p : KickTreeParams) :
    totalSpace p =
      p.hSpace + quotWords p + valWords p + occWords p + elevWords p + metaWords p := by
  unfold totalSpace offMeta offElev offOcc offVal offQuot
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

/-- The `Elevated` block ends at or before `totalSpace p`. -/
theorem elev_end_le_totalSpace (p : KickTreeParams) :
    offElev p + elevWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offElev offOcc offVal offQuot; omega

/-- The `SlotMeta` block ends at or before `totalSpace p`. -/
theorem meta_end_le_totalSpace (p : KickTreeParams) :
    offMeta p + metaWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offMeta offElev offOcc offVal offQuot; omega

/-- Succinct word-space bound for the 0-indexed `k`-kick tree dynamic dictionary:
`⌈(OPT(U, V, n_max) + C * n_max * max (Nat.iterLog (k + 1) n_max) 1) / w⌉ + C₀`. -/
@[expose] def kickTreeWords (C C₀ U V w k n_max : ℕ) : ℕ :=
  (Dynamic.optBits U V n_max + C * n_max * max (Nat.iterLog (k + 1) n_max) 1 + w - 1) / w + C₀

/-- Specialization: for a `1`-kick tree (`k = 1`, `kickLimit = 2`, `iterLog 2`),
`kickTreeWords` is bounded by `Dynamic.succinctWords`. -/
theorem kickTreeWords_le_succinctWords (C C₀ U V w n_max : ℕ) :
    kickTreeWords C C₀ U V w 1 n_max ≤ Dynamic.succinctWords C C₀ U V w n_max := by
  unfold kickTreeWords Dynamic.succinctWords
  have hle : max (Nat.iterLog 2 n_max) 1 ≤ Dynamic.logLogFactor n_max :=
    Nat.max_iterLog_two_eq n_max ▸ Nat.iterLog_two_max_four_le_clog n_max
  have hmul : C * n_max * max (Nat.iterLog 2 n_max) 1 ≤
      C * n_max * Dynamic.logLogFactor n_max :=
    Nat.mul_le_mul_left _ hle
  have hadd : Dynamic.optBits U V n_max + C * n_max * max (Nat.iterLog 2 n_max) 1 + w - 1 ≤
      Dynamic.optBits U V n_max + C * n_max * Dynamic.logLogFactor n_max + w - 1 := by
    omega
  exact Nat.add_le_add_right (Nat.div_le_div_right hadd) _

/-- Master deterministic word-space bound: `totalSpace p` is bounded by
`kickTreeWords (p.cMeta + 7) (p.hSpace + 14) p.U p.V p.w p.k p.nMax` when quotiented. -/
theorem totalSpace_le_kickTreeWords (p : KickTreeParams) (hq : p.quotiented) :
    totalSpace p ≤
      kickTreeWords (p.cMeta + 7) (p.hSpace + 14) p.U p.V p.w p.k p.nMax := by
  have hq_eq : quotBits p = fullQuotBits p.U p.nMax := by
    unfold quotBits; split_ifs; rfl
  rw [totalSpace_eq]
  unfold quotWords; rw [hq_eq]
  have h12 := packedWords_add_le p.nMax (fullQuotBits p.U p.nMax) p.nMax (valBits p.V) p.w
  have h123 := div_add_packedWords_le
    (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V) 5
    (occLen p) 1 p.w
  have h1234 := div_add_packedWords_le
    (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V + occLen p * 1) 8
    p.nMax 1 p.w
  have h12345 := div_add_packedWords_le
    (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V + occLen p * 1 + p.nMax * 1) 11
    (metaLen p) (metaBits p) p.w
  have hopt := mul_fullQuotBits_add_valBits_le_optBits p.U p.V p.nMax
  set M := metaBits p
  have hM : 1 ≤ M := le_max_right _ _
  have hterm1 : p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V ≤
      Dynamic.optBits p.U p.V p.nMax + 2 * p.nMax := by
    rw [← Nat.mul_add]; exact hopt
  have h7M : 7 * p.nMax ≤ 7 * p.nMax * M := by
    simpa using Nat.mul_le_mul_left (7 * p.nMax) hM
  have hnum_le : p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V +
      occLen p * 1 + p.nMax * 1 + metaLen p * M ≤
      Dynamic.optBits p.U p.V p.nMax + (p.cMeta + 7) * p.nMax * M := by
    calc p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V +
          occLen p * 1 + p.nMax * 1 + metaLen p * M
      _ = (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V) +
          5 * p.nMax + p.cMeta * p.nMax * M := by
        unfold occLen metaLen; ring
      _ ≤ Dynamic.optBits p.U p.V p.nMax + 2 * p.nMax + 5 * p.nMax +
          p.cMeta * p.nMax * M := by linarith [hterm1]
      _ = Dynamic.optBits p.U p.V p.nMax + 7 * p.nMax + p.cMeta * p.nMax * M := by ring
      _ ≤ Dynamic.optBits p.U p.V p.nMax + 7 * p.nMax * M + p.cMeta * p.nMax * M := by
        linarith [h7M]
      _ = Dynamic.optBits p.U p.V p.nMax + (p.cMeta + 7) * p.nMax * M := by ring
  have hdiv : (p.nMax * fullQuotBits p.U p.nMax + p.nMax * valBits p.V +
      occLen p * 1 + p.nMax * 1 + metaLen p * M + p.w - 1) / p.w ≤
      (Dynamic.optBits p.U p.V p.nMax + (p.cMeta + 7) * p.nMax * M + p.w - 1) / p.w :=
    Nat.div_le_div_right (by omega)
  unfold kickTreeWords valWords occWords elevWords metaWords
  have hM_def : max (Nat.iterLog (p.k + 1) p.nMax) 1 = M := rfl
  have hM_meta : metaBits p = M := rfl
  rw [hM_def, hM_meta] at *
  omega

/-! ### 3. Pure extraction and update functions -/

/-- Pure extraction function for `Quotients[idx]` (`0` for `idx ≥ p.nMax`). -/
@[expose] def quotAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.nMax then
    readPacked (base + offQuot p) (quotBits p) p.w mem idx
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

/-- Pure extraction function for `Elevated[idx]` (`0` for `idx ≥ p.nMax`). -/
@[expose] def elevAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.nMax then
    readPacked (base + offElev p) 1 p.w mem idx
  else 0

/-- Pure extraction function for `SlotMeta[idx]` (`0` for `idx ≥ metaLen p`). -/
@[expose] def metaAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < metaLen p then
    readPacked (base + offMeta p) (metaBits p) p.w mem idx
  else 0

/-- Pure bit-packed update of `Quotients[idx]` to `val`. -/
@[expose] def writeQuotMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offQuot p) (quotBits p) p.w mem idx val

/-- Pure bit-packed update of `Values[idx]` to `val`. -/
@[expose] def writeValMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offVal p) (valBits p.V) p.w mem idx val

/-- Pure bit-packed update of `Occupancy[idx]` to `val`. -/
@[expose] def writeOccMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offOcc p) 1 p.w mem idx val

/-- Pure bit-packed update of `Elevated[idx]` to `val`. -/
@[expose] def writeElevMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offElev p) 1 p.w mem idx val

/-- Pure bit-packed update of `SlotMeta[idx]` to `val`. -/
@[expose] def writeMetaMem (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writePacked (base + offMeta p) (metaBits p) p.w mem idx val

/-! ### 4. Value range, zero-initialization, congruence, and update laws -/

/-- Value range invariant for `quotAt`: every entry is `< 2 ^ quotBits p`. -/
theorem quotAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt base p mem idx < 2 ^ quotBits p := by
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

/-- Value range invariant for `elevAt`: every entry is `< 2 ^ 1`. -/
theorem elevAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    elevAt base p mem idx < 2 ^ 1 := by
  unfold elevAt; split_ifs
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
  · have hlt1 : wordOffset (quotBits p) p.w idx + 1 < quotWords p :=
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

/-- On zeroed array memory `[base + p.hSpace, base + totalSpace p)`, `elevAt` is identically `0`. -/
theorem elevAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem a = 0) :
    elevAt base p mem = fun _ => 0 := by
  funext idx; unfold elevAt; split_ifs with hidx
  · have hlt1 : wordOffset 1 p.w idx + 1 < elevWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := elev_end_le_totalSpace p
    have hoff : p.hSpace ≤ offElev p := by unfold offElev offOcc offVal offQuot; omega
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
    have hoff : p.hSpace ≤ offMeta p := by unfold offMeta offElev offOcc offVal offQuot; omega
    exact readPacked_zero (hzero _ (by omega) (by omega)) (hzero _ (by omega) (by omega))
  · rfl

/-- Memories agreeing on `[base + p.hSpace, base + totalSpace p)` yield identical extracted
arrays. -/
theorem arrays_congr_of_eq_on {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a, base + p.hSpace ≤ a → a < base + totalSpace p → mem₁ a = mem₂ a) :
    quotAt base p mem₁ = quotAt base p mem₂ ∧
      valAt base p mem₁ = valAt base p mem₂ ∧
      occAt base p mem₁ = occAt base p mem₂ ∧
      elevAt base p mem₁ = elevAt base p mem₂ ∧
      metaAt base p mem₁ = metaAt base p mem₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · funext idx; unfold elevAt; split_ifs with hidx
    · have hbound := elev_end_le_totalSpace p
      have hoff : p.hSpace ≤ offElev p := by unfold offElev offOcc offVal offQuot; omega
      exact readPacked_congr (N := p.nMax) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [elevWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold metaAt; split_ifs with hidx
    · have hbound := meta_end_le_totalSpace p
      have hoff : p.hSpace ≤ offMeta p := by unfold offMeta offElev offOcc offVal offQuot; omega
      exact readPacked_congr (N := metaLen p) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [metaWords] at hbound; omega)) hidx
    · rfl

/-- Congruence for bounded logical arrays agreeing on their allocated word range. -/
private theorem readPacked_bounded_congr {base N k w : ℕ} (hw : 0 < w)
    {m m' : ℕ → ℕ} (heq : ∀ a, base ≤ a ∧ a < base + packedWords N k w → m' a = m a) :
    (fun j => if j < N then readPacked base k w m' j else 0) =
      (fun j => if j < N then readPacked base k w m j else 0) := by
  funext j; split_ifs with hj
  · exact readPacked_congr (N := N) hw (fun a ha => heq a ha) hj
  · rfl

/-- Exact array update and cross-array frame law for `writeQuotMem`. -/
theorem writeQuotMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < p.nMax) (hval : val < 2 ^ quotBits p) :
    quotAt base p (writeQuotMem base p mem idx val) = Function.update (quotAt base p mem) idx val ∧
      valAt base p (writeQuotMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeQuotMem base p mem idx val) = occAt base p mem ∧
      elevAt base p (writeQuotMem base p mem idx val) = elevAt base p mem ∧
      metaAt base p (writeQuotMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offQuot p ≤ a ∧ a < base + offQuot p + quotWords p) →
        writeQuotMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offQuot p ≤ a ∧ a < base + offQuot p + quotWords p) →
      writeQuotMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨readPacked_writePacked_bounded hw hidx hval mem,
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ => hout a (by unfold offVal at ha1; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ =>
      hout a (by unfold offOcc offVal at ha1; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ =>
      hout a (by unfold offElev offOcc offVal at ha1; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ =>
      hout a (by unfold offMeta offElev offOcc offVal at ha1; omega)),
    hout⟩

/-- Exact array update and cross-array frame law for `writeValMem`. -/
theorem writeValMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < p.nMax) (hval : val < 2 ^ valBits p.V) :
    quotAt base p (writeValMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeValMem base p mem idx val) = Function.update (valAt base p mem) idx val ∧
      occAt base p (writeValMem base p mem idx val) = occAt base p mem ∧
      elevAt base p (writeValMem base p mem idx val) = elevAt base p mem ∧
      metaAt base p (writeValMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offVal p ≤ a ∧ a < base + offVal p + valWords p) →
        writeValMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offVal p ≤ a ∧ a < base + offVal p + valWords p) →
      writeValMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offVal; dsimp [quotWords]; omega)),
    readPacked_writePacked_bounded hw hidx hval mem,
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ => hout a (by unfold offOcc at ha1; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ => hout a (by unfold offElev offOcc at ha1; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ =>
      hout a (by unfold offMeta offElev offOcc at ha1; omega)),
    hout⟩

/-- Exact array update and cross-array frame law for `writeOccMem`. -/
theorem writeOccMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < occLen p) (hval : val < 2 ^ 1) :
    quotAt base p (writeOccMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeOccMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeOccMem base p mem idx val) = Function.update (occAt base p mem) idx val ∧
      elevAt base p (writeOccMem base p mem idx val) = elevAt base p mem ∧
      metaAt base p (writeOccMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offOcc p ≤ a ∧ a < base + offOcc p + occWords p) →
        writeOccMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offOcc p ≤ a ∧ a < base + offOcc p + occWords p) →
      writeOccMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offOcc offVal; dsimp [quotWords]; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offOcc; dsimp [valWords]; omega)),
    readPacked_writePacked_bounded hw hidx hval mem,
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ => hout a (by unfold offElev at ha1; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ =>
      hout a (by unfold offMeta offElev at ha1; omega)),
    hout⟩

/-- Exact array update and cross-array frame law for `writeElevMem`. -/
theorem writeElevMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < p.nMax) (hval : val < 2 ^ 1) :
    quotAt base p (writeElevMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeElevMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeElevMem base p mem idx val) = occAt base p mem ∧
      elevAt base p (writeElevMem base p mem idx val) =
        Function.update (elevAt base p mem) idx val ∧
      metaAt base p (writeElevMem base p mem idx val) = metaAt base p mem ∧
      (∀ a, ¬(base + offElev p ≤ a ∧ a < base + offElev p + elevWords p) →
        writeElevMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offElev p ≤ a ∧ a < base + offElev p + elevWords p) →
      writeElevMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offElev offOcc offVal; dsimp [quotWords]; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offElev offOcc; dsimp [valWords]; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offElev; dsimp [occWords]; omega)),
    readPacked_writePacked_bounded hw hidx hval mem,
    readPacked_bounded_congr hw (fun a ⟨ha1, _⟩ => hout a (by unfold offMeta at ha1; omega)),
    hout⟩

/-- Exact array update and cross-array frame law for `writeMetaMem`. -/
theorem writeMetaMem_effects {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) (mem : ℕ → ℕ)
    {idx val : ℕ} (hidx : idx < metaLen p) (hval : val < 2 ^ metaBits p) :
    quotAt base p (writeMetaMem base p mem idx val) = quotAt base p mem ∧
      valAt base p (writeMetaMem base p mem idx val) = valAt base p mem ∧
      occAt base p (writeMetaMem base p mem idx val) = occAt base p mem ∧
      elevAt base p (writeMetaMem base p mem idx val) = elevAt base p mem ∧
      metaAt base p (writeMetaMem base p mem idx val) =
        Function.update (metaAt base p mem) idx val ∧
      (∀ a, ¬(base + offMeta p ≤ a ∧ a < base + offMeta p + metaWords p) →
        writeMetaMem base p mem idx val a = mem a) := by
  have hout : ∀ a, ¬(base + offMeta p ≤ a ∧ a < base + offMeta p + metaWords p) →
      writeMetaMem base p mem idx val a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val ha
  refine ⟨readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offMeta offElev offOcc offVal; dsimp [quotWords]; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offMeta offElev offOcc; dsimp [valWords]; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offMeta offElev; dsimp [occWords]; omega)),
    readPacked_bounded_congr hw (fun a ⟨ha1, ha2⟩ =>
      hout a (by unfold offMeta; dsimp [elevWords]; omega)),
    readPacked_writePacked_bounded hw hidx hval mem,
    hout⟩

end Cslib.DataStructure.Dictionary.WordRAM.KickTree
