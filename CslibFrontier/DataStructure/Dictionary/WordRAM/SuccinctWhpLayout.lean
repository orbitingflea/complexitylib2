/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctProg
public import CslibFrontier.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import CslibFrontier.DataStructure.WordRAM.Randomized.HighProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Memory Layout, Runtime Parameter Block, and Representation Invariants for `SuccinctWhp`

This module defines the concrete Word-RAM word layout within
`[base, base + whpSpace c U V w n_max)`,
the 68-word runtime parameter vector `WhpCoreParams` (paired with the two `HashParams` vectors into
the 100-word `WhpParams` input record), disjoint-segment frame lemmas for `BitPackedArray`, and the
concrete memory representation invariants (`SmallMemRep`, `CsrMemRep`, `BTreeSliceMemRep`,
`BufTrieMemRep`, `FastMemRep`, `SeedWhpMemRep`, and `WhpMemRep`) linking Word-RAM memory `x.mem` to
the pure state machine `WhpDictState` of `SuccinctWhpModel`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.WhpCoreParams`, `WhpParams`,
  `mkWhpCoreParams`, `mkWhpParams`: runtime parameter tuples for parameter-free `Realizes .exact`
  subroutines.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.SmallMemRep`, `CsrMemRep`,
  `BTreeSliceMemRep`, `BufTrieMemRep`, `FastMemRep`, `SeedWhpMemRep`, `WhpMemRep`:
  concrete Word-RAM memory representation predicates across `.small`, `.fast`, and `.fallback`
  modes.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.smallOffsets_eq`,
  `largeOffsets_eq`: exact segment accounting matching `smallSpaceWhp` and `largeSpaceWhp`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fits_mkWhpParams`: every word of
  `mkWhpParams` fits in `w` bits whenever `0 < w`, `n_max ≤ U`, `Fits w U`, `Fits w V`, and
  `Fits w (base + whpSpace c U V w n_max)`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.WhpMemRep.congr_footprint`: frame invariance
  of `WhpMemRep` under memory changes outside `[base, base + whpSpace c U V w n_max)`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct (readPackedProg writePackedProg
  readPackedGenProg writePackedGenProg realizes_readPackedGen realizes_writePackedGen
  validHistory_readPackedProg validHistory_writePackedProg memoryCost_bind_of_clientState_eq)
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Header slots and segment word offsets -/

/-- Header slot `0`: active regime tag (`0` = `.small`, `1` = `.fast`, `2` = `.fallback`). -/
@[expose] def hdrMode : ℕ := 0
/-- Header slot `1`: `fs.poolFreeTop`. -/
@[expose] def hdrPoolFreeTop : ℕ := 1
/-- Header slot `2`: `fs.curEp` (`0` or `1`). -/
@[expose] def hdrCurEp : ℕ := 2
/-- Header slot `3`: `fs.epochClock`. -/
@[expose] def hdrEpochClock : ℕ := 3
/-- Header slot `4`: `fs.rebStage` (`0 .. 5`). -/
@[expose] def hdrRebStage : ℕ := 4
/-- Header slot `5`: `fs.stageCursor`. -/
@[expose] def hdrStageCursor : ℕ := 5
/-- Header slot `6`: `fs.dirtyCount`. -/
@[expose] def hdrDirtyCount : ℕ := 6
/-- Header slot `7`: `fs.dirtyIdx`. -/
@[expose] def hdrDirtyIdx : ℕ := 7
/-- Header slot `8`: `fs.rebCandSalt`. -/
@[expose] def hdrRebCandSalt : ℕ := 8
/-- Header slot `9`: `fs.rebScanCursor`. -/
@[expose] def hdrRebScanCursor : ℕ := 9
/-- Header slot `10`: `fs.rebInsCount`. -/
@[expose] def hdrRebInsCount : ℕ := 10
/-- Header slot `11`: `fs.rebCollision`. -/
@[expose] def hdrRebCollision : ℕ := 11
/-- Header slot `12`: `(fs.buf 0).nodeAlloc`. -/
@[expose] def hdrBuf0NodeAlloc : ℕ := 12
/-- Header slot `13`: `(fs.buf 0).itemAlloc`. -/
@[expose] def hdrBuf0ItemAlloc : ℕ := 13
/-- Header slot `14`: `(fs.buf 1).nodeAlloc`. -/
@[expose] def hdrBuf1NodeAlloc : ℕ := 14
/-- Header slot `15`: `(fs.buf 1).itemAlloc`. -/
@[expose] def hdrBuf1ItemAlloc : ℕ := 15

/-- Small-regime occupancy array offset (`base + 32`). -/
@[expose] def offSmallPres : ℕ := hdrWordsWhp

/-- Small-regime packed keys array offset. -/
@[expose] def offSmallKeys (_U w n_max : ℕ) : ℕ :=
  offSmallPres + packedWords n_max 1 w

/-- Small-regime packed values array offset. -/
@[expose] def offSmallVals (U w n_max : ℕ) : ℕ :=
  offSmallKeys U w n_max + packedWords n_max (keyBits U) w

theorem smallOffsets_eq (U V w n_max : ℕ) :
    offSmallVals U w n_max + packedWords n_max (valBits V) w = smallSpaceWhp U V w n_max := by
  unfold offSmallVals offSmallKeys offSmallPres smallSpaceWhp
  omega

/-- Word count of `θ.1 : BktSeed c U n_max` (`BitPackedDoubleTabulation.space`). -/
@[expose] def bktHashWords (c w n_max : ℕ) : ℕ :=
  BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max)

/-- Word count of `θ.2 : FpSeed c U n_max` (`BitPackedDoubleTabulation.space`). -/
@[expose] def fpHashWords (c w n_max : ℕ) : ℕ :=
  BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)

/-- Large-regime bucket-hash block offset (`base + 32`). -/
@[expose] def offHashBkt : ℕ := hdrWordsWhp

/-- Large-regime fingerprint-hash block offset. -/
@[expose] def offHashFp (c w n_max : ℕ) : ℕ :=
  offHashBkt + bktHashWords c w n_max

/-- Large-regime Feistel quotients array offset (`n_max` entries of `quotBitsWhp U n_max` bits). -/
@[expose] def offQuotWhp (c w n_max : ℕ) : ℕ :=
  offHashFp c w n_max + fpHashWords c w n_max

/-- Large-regime values array offset (`n_max` entries of `valBits V` bits). -/
@[expose] def offValWhp (c U w n_max : ℕ) : ℕ :=
  offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w

/-- Start of the 13 auxiliary packed arrays in `largeAuxWordsWhp`. -/
@[expose] def offPermAct (c U V w n_max : ℕ) : ℕ :=
  offValWhp c U w n_max + packedWords n_max (valBits V) w

/-- 2-bit per-coordinate location tag array (`M * totalLocalCoordsWhp n_max` entries). -/
@[expose] def offLocState (c U V w n_max : ℕ) : ℕ :=
  offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w

/-- Per-bucket scalar metadata and slice `(alloc, root)` array (`16 * M` entries of
`globalPtrBits n_max` bits). -/
@[expose] def offBktMeta (c U V w n_max : ℕ) : ℕ :=
  offLocState c U V w n_max + packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w

/-- CSR bucket prefix-sum array `fbStart` (`M + 1` entries of `globalPtrBits n_max` bits). -/
@[expose] def offFbStart (c U V w n_max : ℕ) : ℕ :=
  offBktMeta c U V w n_max + packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w

/-- Backyard pointer directory `backPtr` (`M * capBackWhp n_max` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offBackPtr (c U V w n_max : ℕ) : ℕ :=
  offFbStart c U V w n_max + packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w

/-- Auxiliary backyard scratch array (`M * capBackWhp n_max` entries of `12 * ellWhp + 4` bits). -/
@[expose] def offBackAux (c U V w n_max : ℕ) : ℕ :=
  offBackPtr c U V w n_max +
    packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w

/-- Backyard free-slot stack `poolFreeStack` (`poolSizeWhp n_max` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offPoolFreeStack (c U V w n_max : ℕ) : ℕ :=
  offBackAux c U V w n_max +
    packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w

/-- Backyard reverse owner array `poolOwner` (`poolSizeWhp n_max` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offPoolOwner (c U V w n_max : ℕ) : ℕ :=
  offPoolFreeStack c U V w n_max + packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w

/-- SWAR B+-tree node metadata array (`totalBTreeNodesWhp n_max` entries of `nodeMetaBitsWhp n_max`
bits). -/
@[expose] def offBtMeta (c U V w n_max : ℕ) : ℕ :=
  offPoolOwner c U V w n_max + packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w

/-- SWAR B+-tree node keys-word array (`totalBTreeNodesWhp n_max` entries of `keysWordBitsWhp n_max`
bits). -/
@[expose] def offBtKeys (c U V w n_max : ℕ) : ℕ :=
  offBtMeta c U V w n_max + packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w

/-- SWAR B+-tree node vals-word array (`totalBTreeNodesWhp n_max` entries of `valsWordBitsWhp n_max`
bits). -/
@[expose] def offBtVals (c U V w n_max : ℕ) : ℕ :=
  offBtKeys c U V w n_max + packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w

/-- Epoch buffer `0` `trieChild` array (`trieChildEntriesWhp c n_max` entries of
`globalPtrBits n_max` bits). -/
@[expose] def offTrieChild0 (c U V w n_max : ℕ) : ℕ :=
  offBtVals c U V w n_max + packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w

/-- Epoch buffer `1` `trieChild` array. -/
@[expose] def offTrieChild1 (c U V w n_max : ℕ) : ℕ :=
  offTrieChild0 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `0` per-node metadata array (`6 * maxTrieNodesWhp c n_max` entries of
`globalPtrBits n_max` bits; `4 * u + 0..3` store `nodeParent`, `nodeChar`, `nodeLeafItem`,
`nodeActive`). -/
@[expose] def offTrieMeta0 (c U V w n_max : ℕ) : ℕ :=
  offTrieChild1 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `1` per-node metadata array. -/
@[expose] def offTrieMeta1 (c U V w n_max : ℕ) : ℕ :=
  offTrieMeta0 c U V w n_max +
    packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `0` item log (`0 .. 3 * qEpoch - 1`) + `dirtyBuckets`
(`3 * qEpoch .. 4 * qEpoch - 1`) array (`6 * qEpochWhp n_max + 6` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offTrieItems0 (c U V w n_max : ℕ) : ℕ :=
  offTrieMeta1 c U V w n_max +
    packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `1` item log array (`6 * qEpochWhp n_max + 6` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offTrieItems1 (c U V w n_max : ℕ) : ℕ :=
  offTrieItems0 c U V w n_max + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w

theorem largeOffsets_eq (c U V w n_max : ℕ) :
    offTrieItems1 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w =
      largeSpaceWhp c U V w n_max := by
  unfold offTrieItems1 offTrieItems0 offTrieMeta1 offTrieMeta0 offTrieChild1 offTrieChild0
    offBtVals offBtKeys offBtMeta offPoolOwner offPoolFreeStack offBackAux offBackPtr offFbStart
    offBktMeta offLocState offPermAct offValWhp offQuotWhp offHashFp offHashBkt
    bktHashWords fpHashWords largeSpaceWhp largeAuxWordsWhp
  ring

/-! ## Section 2: Threshold, bit-width, and word-fit inequalities -/

theorem keyBits_le_w {U w : ℕ} (hU : Fits w U) : keyBits U ≤ w :=
  Nat.clog_le_of_le_pow hU.le

theorem valBits_le_w {V w : ℕ} (hV : Fits w V) : valBits V ≤ w :=
  Nat.clog_le_of_le_pow hV.le

theorem w0Whp_le_w {U w : ℕ} (hw : 0 < w) (hU : Fits w U) : w0Whp U ≤ w :=
  max_le hw (keyBits_le_w hU)

theorem globalPtrBits_le_w {U w n_max : ℕ} (hnU : n_max ≤ U) (hU : Fits w U) :
    globalPtrBits n_max ≤ w := by
  unfold globalPtrBits
  exact Nat.clog_le_of_le_pow (by dsimp [Fits] at hU; omega)

theorem lt_two_pow_globalPtrBits_of_le {n_max x : ℕ} (hx : x ≤ n_max) :
    x < 2 ^ globalPtrBits n_max := by
  have hle : n_max + 1 ≤ 2 ^ globalPtrBits n_max := Nat.le_pow_clog Nat.one_lt_two (n_max + 1)
  omega

theorem log_n_max_lt_w {c U w n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (hnU : n_max ≤ U) (hU : Fits w U) :
    Nat.log 2 n_max < w := by
  have hn0 : 0 < n_max := (whpThreshold_pos c).trans_le hth
  have hpow : 2 ^ Nat.log 2 n_max ≤ n_max := Nat.pow_log_le_self 2 hn0.ne'
  have hlt : 2 ^ Nat.log 2 n_max < 2 ^ w := (hpow.trans hnU).trans_lt hU
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt

theorem log_le_scaleWhp {c n_max : ℕ} (_ : whpThreshold c ≤ n_max) :
    Nat.log 2 n_max ≤ scaleWhp n_max := by
  have h1 : Nat.log 2 n_max ≤ Nat.clog 2 (max n_max 4) :=
    (Nat.log_mono_right (le_max_left n_max 4)).trans (Nat.log_le_clog 2 _)
  exact h1.trans (Nat.le_pow_clog Nat.one_lt_two _)

theorem bMinWhp_le_scaleWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    bMinWhp c ≤ scaleWhp n_max :=
  (bMinWhp_le_log hth).trans (log_le_scaleWhp hth)

theorem two_mul_rIndepWhp_lt_qEpochWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    2 * rIndepWhp c n_max < qEpochWhp n_max := by
  have hce : cEff c + 4 ≤ scaleWhp n_max :=
    (cEff_add_four_le_bMinWhp c).trans (bMinWhp_le_scaleWhp hth)
  have hL_ge : 6553600 ≤ scaleWhp n_max := (le_bMinWhp c).trans (bMinWhp_le_scaleWhp hth)
  calc 2 * rIndepWhp c n_max
      = 2 * (cEff c + 4) * scaleWhp n_max := by unfold rIndepWhp; ring
    _ ≤ (scaleWhp n_max * scaleWhp n_max) * scaleWhp n_max :=
        Nat.mul_le_mul_right _ (by nlinarith)
    _ = (scaleWhp n_max) ^ 3 := by ring
    _ < (scaleWhp n_max) ^ 18 := Nat.pow_lt_pow_right (by omega) (by decide)

theorem nodeAlloc_bound_lt_maxTrieNodes {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    1 + cTabWhp c * (2 * rIndepWhp c n_max) < maxTrieNodesWhp c n_max := by
  have hlt := two_mul_rIndepWhp_lt_qEpochWhp hth
  unfold maxTrieNodesWhp
  nlinarith [le_cTabWhp c]

theorem globalPtrBits_pos_of_large {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    0 < globalPtrBits n_max := by
  have hn : 1 ≤ n_max := (whpThreshold_pos c).trans_le hth
  have hpow := Nat.le_pow_clog Nat.one_lt_two (n_max + 1)
  by_contra h0
  have hz : globalPtrBits n_max = 0 := by unfold globalPtrBits at *; omega
  unfold globalPtrBits at hz
  rw [hz, pow_zero] at hpow
  omega

theorem large_bounds_lt_n_max {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    1024 ≤ numBucketsWhp n_max ∧
    nSliceWhp n_max < n_max ∧
    totalLocalCoordsWhp n_max < n_max ∧
    8 * (scaleWhp n_max) ^ 12 < n_max ∧
    sMaxWhp c n_max < n_max ∧
    maxTrieNodesWhp c n_max < n_max ∧
    qEpochWhp n_max < n_max ∧
    2 ^ bCharWhp n_max < n_max := by
  have hlog := mul_ell_le_log hth
  have hell := one_le_ellWhp n_max
  have hL2 := two_le_scaleWhp n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h8t := eight_le_tMinWhp hth
  obtain ⟨_, _, _, _, htm_le, hq6_le⟩ := sublinear_table_bits_le hth
  have hg_pos := globalPtrBits_pos_of_large hth
  have hb_ge : 10 ≤ bWhp n_max := by unfold bWhp; omega
  have hM_ge : 1024 ≤ numBucketsWhp n_max := by
    calc 1024 = 2 ^ 10 := by decide
      _ ≤ 2 ^ bWhp n_max := Nat.pow_le_pow_right (by decide) hb_ge
  have h1024L12 : 1024 * (scaleWhp n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ hM_ge).trans hML12
  have hL12_pos : 1 ≤ (scaleWhp n_max) ^ 12 := Nat.one_le_pow 12 _ (by omega)
  have hnslice : nSliceWhp n_max < n_max := by
    have hd : 32 * (scaleWhp n_max) ^ 12 / (tMinWhp n_max - 1) ≤ 32 * (scaleWhp n_max) ^ 12 :=
      Nat.div_le_self _ _
    unfold nSliceWhp
    omega
  have htotLoc : totalLocalCoordsWhp n_max < n_max := by
    have hcf : capFrontWhp n_max ≤ n_max / 1024 :=
      (Nat.sub_le _ _).trans (Nat.div_le_div_left hM_ge (by decide))
    have hcb : capBackWhp n_max ≤ (scaleWhp n_max) ^ 12 := by
      unfold capBackWhp
      calc 2 * (scaleWhp n_max) ^ 11 ≤ scaleWhp n_max * (scaleWhp n_max) ^ 11 :=
            Nat.mul_le_mul_right _ hL2
        _ = (scaleWhp n_max) ^ 12 := by ring
    unfold totalLocalCoordsWhp
    omega
  have hpow3 := pow_three_mul_bCharWhp_le hth
  have hbc_ge : 320 ≤ bCharWhp n_max := by have := mul_ell_le_bCharWhp hth; omega
  have hpow_bc_lt : 2 ^ bCharWhp n_max < n_max := by
    calc 2 ^ bCharWhp n_max < 2 ^ (3 * bCharWhp n_max) :=
          Nat.pow_lt_pow_right (by decide) (by omega)
      _ ≤ n_max := hpow3
  have hsMax_lt : sMaxWhp c n_max < n_max :=
    (sMaxWhp_le_pow_bChar hth).trans_lt hpow_bc_lt
  have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
  have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
  have hmt_pos : 2 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
  exact ⟨hM_ge, hnslice, htotLoc, by omega, hsMax_lt, by omega, by omega, hpow_bc_lt⟩

theorem two_pow_quotBitsWhp_lt_U {c U n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (hnU : n_max ≤ U) :
    2 ^ quotBitsWhp U n_max < U := by
  have hlog := mul_ell_le_log hth
  have hell := one_le_ellWhp n_max
  have hU_ge : 4 ≤ U := by
    have hbc_ge : 320 ≤ bCharWhp n_max := by have := mul_ell_le_bCharWhp hth; omega
    have hp := pow_three_mul_bCharWhp_le hth
    have h4 : 4 ≤ 2 ^ (3 * bCharWhp n_max) :=
      (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  have hb_ge : 2 ≤ bWhp n_max := by unfold bWhp; omega
  have hsplit := quotBitsWhp_add_bWhp hnU
  have hpow_key : 2 ^ keyBits U ≤ 2 * U := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
  have h4 : 4 * 2 ^ quotBitsWhp U n_max ≤ 2 ^ keyBits U := by
    rw [← hsplit, Nat.pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos hb_ge)
  omega

/-- Convolution width `(4 * tMinWhp n_max) * keyLaneBitsWhp n_max` fits strictly inside
`Nat.log 2 n_max` whenever `whpThreshold c ≤ n_max`. -/
theorem swarConvBits_lt_log {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (4 * tMinWhp n_max) * keyLaneBitsWhp n_max < Nat.log 2 n_max := by
  have h := mul_ell_le_log hth
  have h1 := one_le_ellWhp n_max
  have h8 := eight_le_tMinWhp hth
  have ht : tMinWhp n_max = Nat.log 2 n_max / (160 * ellWhp n_max) := by
    unfold tMinWhp at h8 ⊢; omega
  have hmul : tMinWhp n_max * (160 * ellWhp n_max) ≤ Nat.log 2 n_max := by
    rw [ht]; exact Nat.div_mul_le_self _ _
  have hkl : keyLaneBitsWhp n_max ≤ 38 * ellWhp n_max := by
    unfold keyLaneBitsWhp fpBitsWhp; omega
  calc (4 * tMinWhp n_max) * keyLaneBitsWhp n_max
      ≤ (4 * tMinWhp n_max) * (38 * ellWhp n_max) := Nat.mul_le_mul_left _ hkl
    _ = 152 * (tMinWhp n_max * ellWhp n_max) := by ring
    _ < 160 * (tMinWhp n_max * ellWhp n_max) := by nlinarith
    _ = tMinWhp n_max * (160 * ellWhp n_max) := by ring
    _ ≤ Nat.log 2 n_max := hmul

/-! ## Section 3: Disjoint-segment `BitPackedArray` frame lemmas -/

/-- `writePacked` only modifies memory words in `[off, off + packedWords N k w)`. -/
theorem mem_writePacked_of_outside {off N k w idx val a : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hidx : idx < N)
    (ha : a < off ∨ off + packedWords N k w ≤ a) :
    writePacked off k w mem idx val a = mem a := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  unfold writePacked
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- `readPacked` on `[off_r, off_r + packedWords N_r k_r w)` is invariant under `writePacked` on a
disjoint segment `[off_w, off_w + packedWords N_w k_w w)`. -/
theorem readPacked_writePacked_disjoint {off_r N_r k_r off_w N_w k_w w idx_r idx_w val : ℕ}
    {mem : ℕ → ℕ} (hw : 0 < w) (hr : idx_r < N_r) (hw_idx : idx_w < N_w)
    (hdisj : off_r + packedWords N_r k_r w ≤ off_w ∨ off_w + packedWords N_w k_w w ≤ off_r) :
    readPacked off_r k_r w (writePacked off_w k_w w mem idx_w val) idx_r =
      readPacked off_r k_r w mem idx_r := by
  have hlt_r := wordOffset_add_one_lt_packedWords (k := k_r) hw hr
  unfold readPacked
  dsimp only
  rw [mem_writePacked_of_outside hw hw_idx (by omega),
    mem_writePacked_of_outside hw hw_idx (by omega)]

/-- Updating a single plain word at `addr < off_r` or `off_r + packedWords N_r k_r w ≤ addr`
leaves `readPacked off_r k_r w` unchanged on `0 .. N_r - 1`. -/
theorem readPacked_update_outside {off_r N_r k_r w addr val idx : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hidx : idx < N_r)
    (ha : addr < off_r ∨ off_r + packedWords N_r k_r w ≤ addr) :
    readPacked off_r k_r w (Function.update mem addr val) idx =
      readPacked off_r k_r w mem idx := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k_r) hw hidx
  unfold readPacked
  dsimp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- `readPacked` depends only on words in `[off, off + packedWords N k w)`. -/
theorem readPacked_congr_on {off N k w idx : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w) (hidx : idx < N)
    (heq : ∀ a, off ≤ a → a < off + packedWords N k w → mem₁ a = mem₂ a) :
    readPacked off k w mem₁ idx = readPacked off k w mem₂ idx := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  unfold readPacked
  dsimp only
  rw [heq _ (by omega) (by omega), heq _ (by omega) (by omega)]

private theorem readPacked_eq_of_mem_eq {base space off N k w idx val : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w)
    (hmem : ∀ a, base ≤ a → a < base + space → mem₂ a = mem₁ a)
    (h : readPacked (base + off) k w mem₁ idx = val)
    (hidx : idx < N)
    (hle : off + packedWords N k w ≤ space) :
    readPacked (base + off) k w mem₂ idx = val :=
  (readPacked_congr_on hw hidx fun a ha1 ha2 => hmem a (by omega) (by omega)).trans h

/-! ## Section 4: Concrete memory representation invariants (`WhpMemRep`) -/

/-- Memory representation of `SmallDictState` at `base` (`mem[base] = 0`). -/
@[expose] def SmallMemRep (base U V w n_max : ℕ) (sm : SmallDictState) (mem : ℕ → ℕ) : Prop :=
  mem (base + hdrMode) = 0 ∧
  (∀ i < n_max,
    readPacked (base + offSmallPres) 1 w mem i = sm.present i ∧
    readPacked (base + offSmallKeys U w n_max) (keyBits U) w mem i = sm.keys i ∧
    readPacked (base + offSmallVals U w n_max) (valBits V) w mem i = sm.vals i)

/-- Memory representation of `CsrState` at `base` (`mem[base] = 2`). -/
@[expose] def CsrMemRep (base c U V w n_max : ℕ) (csr : CsrState) (mem : ℕ → ℕ) : Prop :=
  mem (base + hdrMode) = 2 ∧
  (∀ b ≤ numBucketsWhp n_max,
    readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w mem b = csr.fbStart b) ∧
  (∀ i < n_max,
    readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w mem i = csr.qArr i ∧
    readPacked (base + offValWhp c U w n_max) (valBits V) w mem i = csr.vArr i)

/-- Memory representation of a single SWAR B+-tree slice `sIdx = 3 * b + role < 3 * M` on its
allocated prefix `0 .. sl.alloc - 1`. -/
@[expose] def BTreeSliceMemRep (base c U V w n_max sIdx : ℕ) (sl : BTreeSlice)
    (mem : ℕ → ℕ) : Prop :=
  let b := sIdx / 3
  let role := sIdx % 3
  let gBits := globalPtrBits n_max
  sl.alloc ≤ nSliceWhp n_max ∧
  readPacked (base + offBktMeta c U V w n_max) gBits w mem (16 * b + 10 + 2 * role) = sl.alloc ∧
  readPacked (base + offBktMeta c U V w n_max) gBits w mem (16 * b + 11 + 2 * role) = sl.root ∧
  ∀ u < sl.alloc,
    let idx := sIdx * nSliceWhp n_max + u
    readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem idx =
      (sl.nodes u).metaWord ∧
    readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem idx =
      (sl.nodes u).keysWord ∧
    readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w mem idx =
      (sl.nodes u).valsWord

/-- Memory representation of epoch buffer trie `ep ∈ {0, 1}`. -/
@[expose] def BufTrieMemRep (base c U V w n_max ep : ℕ) (tr : BufTrie) (mem : ℕ → ℕ) : Prop :=
  let offChild := if ep = 0 then offTrieChild0 c U V w n_max else offTrieChild1 c U V w n_max
  let offMeta := if ep = 0 then offTrieMeta0 c U V w n_max else offTrieMeta1 c U V w n_max
  let offItems := if ep = 0 then offTrieItems0 c U V w n_max else offTrieItems1 c U V w n_max
  let hdrNA := if ep = 0 then hdrBuf0NodeAlloc else hdrBuf1NodeAlloc
  let hdrIA := if ep = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc
  let gBits := globalPtrBits n_max
  let qEp := qEpochWhp n_max
  tr.nodeAlloc ≤ maxTrieNodesWhp c n_max ∧
  tr.itemAlloc ≤ qEp ∧
  mem (base + hdrNA) = tr.nodeAlloc ∧
  mem (base + hdrIA) = tr.itemAlloc ∧
  (∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
    readPacked (base + offChild) gBits w mem (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch) ∧
  (∀ u, 1 ≤ u → u < tr.nodeAlloc →
    readPacked (base + offMeta) gBits w mem (4 * u + 0) = tr.nodeParent u ∧
    readPacked (base + offMeta) gBits w mem (4 * u + 1) = tr.nodeChar u) ∧
  (∀ u < tr.nodeAlloc,
    readPacked (base + offMeta) gBits w mem (4 * u + 2) = tr.nodeLeafItem u ∧
    (tr.nodeLeafItem u ≠ 0 →
      readPacked (base + offMeta) gBits w mem (4 * u + 3) = tr.nodeActive u)) ∧
  (∀ id < tr.itemAlloc,
    readPacked (base + offItems) gBits w mem id = tr.itemLeaf id ∧
    readPacked (base + offItems) gBits w mem (qEp + id) = tr.itemBucket id ∧
    readPacked (base + offItems) gBits w mem (2 * qEp + id) = tr.itemLoc id)

/-- Memory representation of `FastState` at `base` (`mem[base] = 1`). -/
@[expose] def FastMemRep (base c U V w n_max : ℕ) (fs : FastState) (mem : ℕ → ℕ) : Prop :=
  let M := numBucketsWhp n_max
  let gBits := globalPtrBits n_max
  let qEp := qEpochWhp n_max
  fs.dirtyCount ≤ qEp ∧
  mem (base + hdrMode) = 1 ∧
  mem (base + hdrPoolFreeTop) = fs.poolFreeTop ∧
  mem (base + hdrCurEp) = fs.curEp ∧
  mem (base + hdrEpochClock) = fs.epochClock ∧
  mem (base + hdrRebStage) = fs.rebStage ∧
  mem (base + hdrStageCursor) = fs.stageCursor ∧
  mem (base + hdrDirtyCount) = fs.dirtyCount ∧
  mem (base + hdrDirtyIdx) = fs.dirtyIdx ∧
  mem (base + hdrRebCandSalt) = fs.rebCandSalt ∧
  mem (base + hdrRebScanCursor) = fs.rebScanCursor ∧
  mem (base + hdrRebInsCount) = fs.rebInsCount ∧
  mem (base + hdrRebCollision) = fs.rebCollision ∧
  (∀ i < n_max,
    readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w mem i = fs.quotArr i ∧
    readPacked (base + offValWhp c U w n_max) (valBits V) w mem i = fs.valArr i) ∧
  (∀ b < M, ∀ loc < totalLocalCoordsWhp n_max,
    readPacked (base + offLocState c U V w n_max) 2 w mem (b * totalLocalCoordsWhp n_max + loc) =
      fs.locState b loc) ∧
  (∀ b < M,
    let bm := offBktMeta c U V w n_max
    readPacked (base + bm) gBits w mem (16 * b + 0) = fs.bktCount b ∧
    readPacked (base + bm) gBits w mem (16 * b + 1) = fs.bktSalt b ∧
    readPacked (base + bm) gBits w mem (16 * b + 2) = fs.liveRole b ∧
    readPacked (base + bm) gBits w mem (16 * b + 3) = fs.liveInsCount b ∧
    readPacked (base + bm) gBits w mem (16 * b + 4) = fs.overmarsRole b ∧
    readPacked (base + bm) gBits w mem (16 * b + 5) = fs.overmarsActive b ∧
    readPacked (base + bm) gBits w mem (16 * b + 6) = fs.overmarsCursor b ∧
    readPacked (base + bm) gBits w mem (16 * b + 7) = fs.overmarsInsCount b ∧
    readPacked (base + bm) gBits w mem (16 * b + 8) = fs.rebDoneFlag b ∧
    readPacked (base + bm) gBits w mem (16 * b + 9) = fs.rebQueued b) ∧
  (∀ b < M, ∀ k < capBackWhp n_max,
    readPacked (base + offBackPtr c U V w n_max) gBits w mem (b * capBackWhp n_max + k) =
      fs.backPtr b k) ∧
  (∀ j < poolSizeWhp n_max,
    readPacked (base + offPoolFreeStack c U V w n_max) gBits w mem j = fs.poolFreeStack j ∧
    readPacked (base + offPoolOwner c U V w n_max) gBits w mem j = fs.poolOwner j) ∧
  (∀ sIdx < 3 * M, BTreeSliceMemRep base c U V w n_max sIdx (fs.slices sIdx) mem) ∧
  BufTrieMemRep base c U V w n_max 0 (fs.buf 0) mem ∧
  BufTrieMemRep base c U V w n_max 1 (fs.buf 1) mem ∧
  (∀ j < fs.dirtyCount,
    readPacked (base + offTrieItems0 c U V w n_max) gBits w mem (3 * qEp + j) = fs.dirtyBuckets j)

/-- Memory representation of the two static double-tabulation seeds `(θ.1, θ.2)` in the large
regime. -/
@[expose] def SeedWhpMemRep (base c U w n_max : ℕ) (θ : SeedWhp c U n_max)
    (mem : ℕ → ℕ) : Prop :=
  BitPackedDoubleTabulation.SeedRep (base + offHashBkt) w (w0Whp U)
    (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) θ.1 mem ∧
  BitPackedDoubleTabulation.SeedRep (base + offHashFp c w n_max) w (w0Whp U)
    (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) θ.2 mem

/-- Combined memory representation linking `θ` and `st : WhpDictState` to `mem` across all
capacities `n_max`. -/
@[expose] def WhpMemRep (base c U V w n_max : ℕ) (θ : SeedWhp c U n_max)
    (st : WhpDictState) (mem : ℕ → ℕ) : Prop :=
  match st with
  | .small sm => n_max < whpThreshold c ∧ SmallMemRep base U V w n_max sm mem
  | .fast fs =>
    whpThreshold c ≤ n_max ∧
    SeedWhpMemRep base c U w n_max θ mem ∧
    FastMemRep base c U V w n_max fs mem
  | .fallback csr =>
    whpThreshold c ≤ n_max ∧
    SeedWhpMemRep base c U w n_max θ mem ∧
    CsrMemRep base c U V w n_max csr mem

private theorem seedRep_congr {base w w₀ c_tab d b_char M_out : ℕ}
    {θ : BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w)
    (heq : ∀ a, base ≤ a → a < base + BitPackedDoubleTabulation.space w c_tab d b_char M_out →
      mem₁ a = mem₂ a)
    (hrep : BitPackedDoubleTabulation.SeedRep base w w₀ c_tab d b_char M_out θ mem₁) :
    BitPackedDoubleTabulation.SeedRep base w w₀ c_tab d b_char M_out θ mem₂ := by
  have hsp_pos := BitPackedDoubleTabulation.space_pos w c_tab d b_char M_out
  refine ⟨(heq base le_rfl (by omega)).symm.trans hrep.1, fun i j ch => ?_, fun j ch => ?_⟩
  · have hidx : (j.val * (c_tab + 1) + i.val) * 2 ^ b_char + ch.val <
        BitPackedDoubleTabulation.topEntries c_tab d b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d b_char i j ch
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords,
        BitPackedDoubleTabulation.topEntries] at h ⊢
      omega
    have hsp_eq : BitPackedDoubleTabulation.space w c_tab d b_char M_out =
        1 + packedWords (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w +
          BitPackedDoubleTabulation.botWords w d b_char M_out := rfl
    rw [readPacked_congr_on hw hidx (fun a ha1 ha2 => (heq a (by omega) (by omega)).symm)]
    exact hrep.2.1 i j ch
  · have hidx : j.val * 2 ^ b_char + ch.val < BitPackedDoubleTabulation.botEntries d b_char := by
      calc j.val * 2 ^ b_char + ch.val
          < j.val * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left ch.isLt _
        _ = (j.val + 1) * 2 ^ b_char := by ring
        _ ≤ d * 2 ^ b_char := Nat.mul_le_mul_right _ j.isLt
    have hsp_eq : BitPackedDoubleTabulation.space w c_tab d b_char M_out =
        BitPackedDoubleTabulation.offBot w c_tab d b_char +
          packedWords (BitPackedDoubleTabulation.botEntries d b_char) M_out w := rfl
    rw [readPacked_congr_on hw hidx (fun a ha1 ha2 => (heq a (by omega) (by omega)).symm)]
    exact hrep.2.2 j ch

/-- `SeedWhpMemRep` depends only on `[base + offHashBkt, base + offQuotWhp c w n_max)`. -/
theorem SeedWhpMemRep.congr_hash {base c U w n_max : ℕ} {θ : SeedWhp c U n_max}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w)
    (heq : ∀ a, base + offHashBkt ≤ a → a < base + offQuotWhp c w n_max → mem₁ a = mem₂ a)
    (hseed : SeedWhpMemRep base c U w n_max θ mem₁) :
    SeedWhpMemRep base c U w n_max θ mem₂ := by
  have hoff_eq : offQuotWhp c w n_max =
      offHashBkt + bktHashWords c w n_max + fpHashWords c w n_max := rfl
  have hfp_eq : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have hb_eq : bktHashWords c w n_max =
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) :=
    rfl
  have hfs_eq : fpHashWords c w n_max =
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
        (fpBitsWhp n_max) := rfl
  exact ⟨seedRep_congr hw (fun a ha1 ha2 => heq a ha1 (by omega)) hseed.1,
    seedRep_congr hw (fun a ha1 ha2 => heq a (by omega) (by omega)) hseed.2⟩

private theorem bufTrieMemRep_congr {base c U V w n_max ep : ℕ} {tr : BufTrie}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w) (hep : ep = 0 ∨ ep = 1)
    (hmem : ∀ a, base ≤ a → a < base + largeSpaceWhp c U V w n_max → mem₂ a = mem₁ a)
    (hrep : BufTrieMemRep base c U V w n_max ep tr mem₁) :
    BufTrieMemRep base c U V w n_max ep tr mem₂ := by
  have hend := largeOffsets_eq c U V w n_max
  have hhdr_le : 32 ≤ largeSpaceWhp c U V w n_max := by
    change hdrWordsWhp ≤ largeSpaceWhp c U V w n_max
    unfold largeSpaceWhp; omega
  have hc01 : offTrieChild1 c U V w n_max =
      offTrieChild0 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm0 : offTrieMeta0 c U V w n_max =
      offTrieChild1 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm1 : offTrieMeta1 c U V w n_max =
      offTrieMeta0 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max =
      offTrieMeta1 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi1 : offTrieItems1 c U V w n_max =
      offTrieItems0 c U V w n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  let rp := @readPacked_eq_of_mem_eq base (largeSpaceWhp c U V w n_max)
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hch, hpar, hleaf, hitems⟩ := hrep
  rcases hep with rfl | rfl
  · simp only [↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    have hna_pos : hdrBuf0NodeAlloc = 12 := rfl
    have hia_pos : hdrBuf0ItemAlloc = 13 := rfl
    refine ⟨hna, hia,
      (hmem _ (by omega) (by omega)).trans hhdr_na,
      (hmem _ (by omega) (by omega)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact rp hw hmem (hch u hu ch hch_lt) hidx (by omega)
    · exact ⟨rp hw hmem (hpar u hu1 hu).1 (show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega),
        rp hw hmem (hpar u hu1 hu).2 (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega)⟩
    · exact ⟨rp hw hmem (hleaf u hu).1 (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega),
        fun hnz => rp hw hmem ((hleaf u hu).2 hnz)
          (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega) (by omega)⟩
    · exact ⟨rp hw hmem (hitems id hid).1 (show id < 6 * qEpochWhp n_max + 6 by omega) (by omega),
        rp hw hmem (hitems id hid).2.1
          (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) (by omega),
        rp hw hmem (hitems id hid).2.2
          (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) (by omega)⟩
  · simp only [Nat.one_ne_zero, ↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    have hna_pos : hdrBuf1NodeAlloc = 14 := rfl
    have hia_pos : hdrBuf1ItemAlloc = 15 := rfl
    refine ⟨hna, hia,
      (hmem _ (by omega) (by omega)).trans hhdr_na,
      (hmem _ (by omega) (by omega)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact rp hw hmem (hch u hu ch hch_lt) hidx (by omega)
    · exact ⟨rp hw hmem (hpar u hu1 hu).1 (show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega),
        rp hw hmem (hpar u hu1 hu).2 (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega)⟩
    · exact ⟨rp hw hmem (hleaf u hu).1 (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega),
        fun hnz => rp hw hmem ((hleaf u hu).2 hnz)
          (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega) (by omega)⟩
    · exact ⟨rp hw hmem (hitems id hid).1 (show id < 6 * qEpochWhp n_max + 6 by omega) (by omega),
        rp hw hmem (hitems id hid).2.1
          (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) (by omega),
        rp hw hmem (hitems id hid).2.2
          (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) (by omega)⟩

/-- Pure footprint invariance of `WhpMemRep`: depends only on memory words in
`[base, base + whpSpace c U V w n_max)`. -/
theorem WhpMemRep.congr_footprint {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {st : WhpDictState} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w)
    (heq : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max)).footprint, mem₂ a = mem₁ a)
    (hrep : WhpMemRep base c U V w n_max θ st mem₁) :
    WhpMemRep base c U V w n_max θ st mem₂ := by
  have hmem : ∀ a, base ≤ a → a < base + whpSpace c U V w n_max → mem₂ a = mem₁ a :=
    fun a h1 h2 => heq a (by simp only [Block.mem_footprint, Block.Owns]; exact ⟨h1, h2⟩)
  -- Shared layout chain for large regime
  have hendL := largeOffsets_eq c U V w n_max
  have hl_hb : offHashBkt = 32 := rfl
  have hl_hf : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have hl_q : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
  have hl_v : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hl_pa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hl_ls : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
  have hl_bm : offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
  have hl_fb : offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
  have hl_bp : offBackPtr c U V w n_max =
      offFbStart c U V w n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w := rfl
  have hl_ba : offBackAux c U V w n_max =
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
  have hl_ps : offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w := rfl
  have hl_po : offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hl_btm : offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hl_btk : offBtKeys c U V w n_max =
      offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w := rfl
  have hl_btv : offBtVals c U V w n_max =
      offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w := rfl
  have hl_tc0 : offTrieChild0 c U V w n_max =
      offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w := rfl
  have hl_tc1 : offTrieChild1 c U V w n_max =
      offTrieChild0 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hl_tm0 : offTrieMeta0 c U V w n_max =
      offTrieChild1 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hl_tm1 : offTrieMeta1 c U V w n_max =
      offTrieMeta0 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hl_ti0 : offTrieItems0 c U V w n_max =
      offTrieMeta1 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hl_ti1 : offTrieItems1 c U V w n_max =
      offTrieItems0 c U V w n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  cases st with
  | small sm =>
    obtain ⟨hsm, hm0, hfields⟩ := hrep
    have hsp : whpSpace c U V w n_max = smallSpaceWhp U V w n_max := by
      unfold whpSpace; exact ite_eq_left hsm
    have hs0 : hdrMode = 0 := rfl
    have hs1 : offSmallPres = 32 := rfl
    have hs2 : offSmallKeys U w n_max = offSmallPres + packedWords n_max 1 w := rfl
    have hs3 : offSmallVals U w n_max = offSmallKeys U w n_max + packedWords n_max (keyBits U) w :=
      rfl
    have hend := smallOffsets_eq U V w n_max
    refine ⟨hsm, (hmem _ (by omega) (by omega)).trans hm0, fun i hi => ?_⟩
    obtain ⟨hp, hk, hv⟩ := hfields i hi
    exact ⟨(readPacked_congr_on hw hi fun a ha1 ha2 => hmem a (by omega) (by omega)).trans hp,
      (readPacked_congr_on hw hi fun a ha1 ha2 => hmem a (by omega) (by omega)).trans hk,
      (readPacked_congr_on hw hi fun a ha1 ha2 => hmem a (by omega) (by omega)).trans hv⟩
  | fallback csr =>
    obtain ⟨hth, hseed, hm0, hfb, hqv⟩ := hrep
    have hsp : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
      unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
    have hmemL : ∀ a, base ≤ a → a < base + largeSpaceWhp c U V w n_max → mem₂ a = mem₁ a :=
      fun a h1 h2 => hmem a h1 (hsp ▸ h2)
    let rp := @readPacked_eq_of_mem_eq base (largeSpaceWhp c U V w n_max)
    have hs0 : hdrMode = 0 := rfl
    refine ⟨hth,
      hseed.congr_hash hw (fun a ha1 ha2 => (hmemL a (by omega) (by omega)).symm),
      (hmemL _ (by omega) (by omega)).trans hm0,
      fun b hb => rp hw hmemL (hfb b hb) (show b < numBucketsWhp n_max + 1 by omega) (by omega),
      fun i hi => ⟨rp hw hmemL (hqv i hi).1 hi (by omega),
        rp hw hmemL (hqv i hi).2 hi (by omega)⟩⟩
  | fast fs =>
    obtain ⟨hth, hseed, hfast⟩ := hrep
    have hsp : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
      unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
    have hmemL : ∀ a, base ≤ a → a < base + largeSpaceWhp c U V w n_max → mem₂ a = mem₁ a :=
      fun a h1 h2 => hmem a h1 (hsp ▸ h2)
    have hhdr : ∀ h < 32, mem₂ (base + h) = mem₁ (base + h) :=
      fun h hh => hmemL (base + h) (by omega) (by omega)
    let rp := @readPacked_eq_of_mem_eq base (largeSpaceWhp c U V w n_max)
    dsimp only [FastMemRep] at hfast ⊢
    rcases hfast with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv, hloc, hbmeta, hbptr, hpool, hslices, hbuf0, hbuf1, hdirty⟩
    refine ⟨hth,
      hseed.congr_hash hw (fun a ha1 ha2 => (hmemL a (by omega) (by omega)).symm),
      hdc_le,
      (hhdr hdrMode (by decide)).trans hm0,
      (hhdr hdrPoolFreeTop (by decide)).trans hm1,
      (hhdr hdrCurEp (by decide)).trans hm2,
      (hhdr hdrEpochClock (by decide)).trans hm3,
      (hhdr hdrRebStage (by decide)).trans hm4,
      (hhdr hdrStageCursor (by decide)).trans hm5,
      (hhdr hdrDirtyCount (by decide)).trans hm6,
      (hhdr hdrDirtyIdx (by decide)).trans hm7,
      (hhdr hdrRebCandSalt (by decide)).trans hm8,
      (hhdr hdrRebScanCursor (by decide)).trans hm9,
      (hhdr hdrRebInsCount (by decide)).trans hm10,
      (hhdr hdrRebCollision (by decide)).trans hm11,
      fun i hi => ⟨rp hw hmemL (hqv i hi).1 hi (by omega),
        rp hw hmemL (hqv i hi).2 hi (by omega)⟩,
      fun b hb loc hloc_lt => ?_,
      fun b hb => ?_,
      fun b hb k hk => ?_,
      fun j hj => ⟨rp hw hmemL (hpool j hj).1 hj (by omega),
        rp hw hmemL (hpool j hj).2 hj (by omega)⟩,
      fun sIdx hsIdx => ?_,
      bufTrieMemRep_congr hw (Or.inl rfl) hmemL hbuf0,
      bufTrieMemRep_congr hw (Or.inr rfl) hmemL hbuf1,
      fun j hj => rp hw hmemL (hdirty j hj)
        (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega) (by omega)⟩
    · have hidx : b * totalLocalCoordsWhp n_max + loc <
          numBucketsWhp n_max * totalLocalCoordsWhp n_max := by
        calc b * totalLocalCoordsWhp n_max + loc
            < b * totalLocalCoordsWhp n_max + totalLocalCoordsWhp n_max :=
              Nat.add_lt_add_left hloc_lt _
          _ = (b + 1) * totalLocalCoordsWhp n_max := by ring
          _ ≤ numBucketsWhp n_max * totalLocalCoordsWhp n_max := Nat.mul_le_mul_right _ hb
      exact rp hw hmemL (hloc b hb loc hloc_lt) hidx (by omega)
    · have hm := hbmeta b hb
      exact ⟨rp hw hmemL hm.1 (show 16 * b + 0 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.1 (show 16 * b + 1 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.1 (show 16 * b + 2 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.1 (show 16 * b + 3 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.2.1 (show 16 * b + 4 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.2.2.1
          (show 16 * b + 5 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.1
          (show 16 * b + 6 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.2.1
          (show 16 * b + 7 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.2.2.1
          (show 16 * b + 8 < 16 * numBucketsWhp n_max by omega) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.2.2.2
          (show 16 * b + 9 < 16 * numBucketsWhp n_max by omega) (by omega)⟩
    · have hidx : b * capBackWhp n_max + k < numBucketsWhp n_max * capBackWhp n_max := by
        calc b * capBackWhp n_max + k < b * capBackWhp n_max + capBackWhp n_max :=
              Nat.add_lt_add_left hk _
          _ = (b + 1) * capBackWhp n_max := by ring
          _ ≤ numBucketsWhp n_max * capBackWhp n_max := Nat.mul_le_mul_right _ hb
      exact rp hw hmemL (hbptr b hb k hk) hidx (by omega)
    · obtain ⟨ha_le, halloc_r, hroot_r, hnodes_r⟩ := hslices sIdx hsIdx
      have hb_lt : sIdx / 3 < numBucketsWhp n_max := by omega
      have hrole_lt : sIdx % 3 < 3 := Nat.mod_lt _ (by decide)
      refine ⟨ha_le,
        rp hw hmemL halloc_r
          (show 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max by omega)
          (by omega),
        rp hw hmemL hroot_r
          (show 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max by omega)
          (by omega),
        fun u hu => ?_⟩
      have hu_ns : u < nSliceWhp n_max := hu.trans_le ha_le
      have hidx : sIdx * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
        unfold totalBTreeNodesWhp
        calc sIdx * nSliceWhp n_max + u < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
              Nat.add_lt_add_left hu_ns _
          _ = (sIdx + 1) * nSliceWhp n_max := by ring
          _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
      exact ⟨rp hw hmemL (hnodes_r u hu).1 hidx (by omega),
        rp hw hmemL (hnodes_r u hu).2.1 hidx (by omega),
        rp hw hmemL (hnodes_r u hu).2.2 hidx (by omega)⟩

/-! ## Section 5: Precomputed runtime parameter block `WhpParams` (`68 + 16 + 16 = 100` words) -/

/-- Core 68-word runtime parameter vector for `SuccinctWhp` `Memory.Prog` subroutines. -/
@[expose] def WhpCoreParams : Type := Fin 68 → ℕ

instance : WordEncoding WhpCoreParams := ⟨68, Function.Embedding.refl (Fin 68 → ℕ)⟩

/-- Combined 100-word runtime parameter bundle `(coreParams, (bktHashParams, fpHashParams))`. -/
abbrev WhpParams : Type :=
  WhpCoreParams × BitPackedDoubleTabulation.HashParams × BitPackedDoubleTabulation.HashParams

/-- Construct `WhpCoreParams` for `(c, U, V, w, n_max)`. When `n_max < whpThreshold c`, all
large-regime entries (`10 .. 67`) are `0` so every entry fits in `w` bits for all `w > 0`. -/
@[expose] def mkWhpCoreParams (c U V w n_max : ℕ) : WhpCoreParams := fun i =>
  if n_max < whpThreshold c then
    match i.val with
    | 0 => 1
    | 1 => w
    | 2 => n_max
    | 3 => U
    | 4 => V
    | 5 => keyBits U
    | 6 => valBits V
    | 7 => offSmallPres
    | 8 => offSmallKeys U w n_max
    | 9 => offSmallVals U w n_max
    | _ => 0
  else
    match i.val with
    | 0 => 0
    | 1 => w
    | 2 => n_max
    | 3 => U
    | 4 => V
    | 5 => keyBits U
    | 6 => valBits V
    | 7 => 0
    | 8 => 0
    | 9 => 0
    | 10 => bWhp n_max
    | 11 => numBucketsWhp n_max
    | 12 => numBucketsWhp n_max - 1
    | 13 => quotBitsWhp U n_max
    | 14 => fpBitsWhp n_max
    | 15 => 2 ^ fpBitsWhp n_max
    | 16 => bCharWhp n_max
    | 17 => 2 ^ bCharWhp n_max
    | 18 => 2 ^ bCharWhp n_max - 1
    | 19 => cTabWhp c
    | 20 => sMaxWhp c n_max
    | 21 => 2 * rIndepWhp c n_max
    | 22 => qEpochWhp n_max
    | 23 => deltaWhp n_max
    | 24 => capFrontWhp n_max
    | 25 => capBackWhp n_max
    | 26 => totalLocalCoordsWhp n_max
    | 27 => numBucketsWhp n_max * capFrontWhp n_max
    | 28 => poolSizeWhp n_max
    | 29 => 5 * (scaleWhp n_max) ^ 12
    | 30 => globalPtrBits n_max
    | 31 => 12 * ellWhp n_max + 4
    | 32 => trieChildEntriesWhp c n_max
    | 33 => maxTrieNodesWhp c n_max
    | 34 => hMaxBTree
    | 35 => tMinWhp n_max
    | 36 => 2 * tMinWhp n_max
    | 37 => 2 * tMinWhp n_max - 1
    | 38 => keyLaneBitsWhp n_max
    | 39 => 2 ^ keyLaneBitsWhp n_max - 1
    | 40 => swarOnes (keyLaneBitsWhp n_max) (2 * tMinWhp n_max)
    | 41 => valsWordBitsWhp n_max
    | 42 => keysWordBitsWhp n_max
    | 43 => valLaneBitsWhp n_max
    | 44 => 2 ^ valLaneBitsWhp n_max - 1
    | 45 => nodeMetaBitsWhp n_max
    | 46 => nSliceWhp n_max
    | 47 => offHashBkt
    | 48 => offHashFp c w n_max
    | 49 => offQuotWhp c w n_max
    | 50 => offValWhp c U w n_max
    | 51 => offPermAct c U V w n_max
    | 52 => offLocState c U V w n_max
    | 53 => offBktMeta c U V w n_max
    | 54 => offFbStart c U V w n_max
    | 55 => offBackPtr c U V w n_max
    | 56 => offPoolFreeStack c U V w n_max
    | 57 => offPoolOwner c U V w n_max
    | 58 => offBtMeta c U V w n_max
    | 59 => offBtKeys c U V w n_max
    | 60 => offBtVals c U V w n_max
    | 61 => offTrieChild0 c U V w n_max
    | 62 => offTrieChild1 c U V w n_max
    | 63 => offTrieMeta0 c U V w n_max
    | 64 => offTrieMeta1 c U V w n_max
    | 65 => offTrieItems0 c U V w n_max
    | 66 => offTrieItems1 c U V w n_max
    | _ => 0

/-- Construct the full 100-word `WhpParams` bundle for `(c, U, V, w, n_max)`. -/
@[expose] def mkWhpParams (c U V w n_max : ℕ) : WhpParams :=
  if n_max < whpThreshold c then
    (mkWhpCoreParams c U V w n_max, ((fun _ => 0), (fun _ => 0)))
  else
    (mkWhpCoreParams c U V w n_max,
     (BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max),
      BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)))

/-! ### Named projections on `WhpCoreParams` -/

@[expose] def wpIsSmall (cp : WhpCoreParams) : ℕ := cp ⟨0, by decide⟩
@[expose] def wpW (cp : WhpCoreParams) : ℕ := cp ⟨1, by decide⟩
@[expose] def wpNMax (cp : WhpCoreParams) : ℕ := cp ⟨2, by decide⟩
@[expose] def wpU (cp : WhpCoreParams) : ℕ := cp ⟨3, by decide⟩
@[expose] def wpV (cp : WhpCoreParams) : ℕ := cp ⟨4, by decide⟩
@[expose] def wpKeyBits (cp : WhpCoreParams) : ℕ := cp ⟨5, by decide⟩
@[expose] def wpValBits (cp : WhpCoreParams) : ℕ := cp ⟨6, by decide⟩
@[expose] def wpOffSmallPres (cp : WhpCoreParams) : ℕ := cp ⟨7, by decide⟩
@[expose] def wpOffSmallKeys (cp : WhpCoreParams) : ℕ := cp ⟨8, by decide⟩
@[expose] def wpOffSmallVals (cp : WhpCoreParams) : ℕ := cp ⟨9, by decide⟩
@[expose] def wpBWhp (cp : WhpCoreParams) : ℕ := cp ⟨10, by decide⟩
@[expose] def wpM (cp : WhpCoreParams) : ℕ := cp ⟨11, by decide⟩
@[expose] def wpMaskBkt (cp : WhpCoreParams) : ℕ := cp ⟨12, by decide⟩
@[expose] def wpQuotBits (cp : WhpCoreParams) : ℕ := cp ⟨13, by decide⟩
@[expose] def wpFpBits (cp : WhpCoreParams) : ℕ := cp ⟨14, by decide⟩
@[expose] def wpPowFp (cp : WhpCoreParams) : ℕ := cp ⟨15, by decide⟩
@[expose] def wpBChar (cp : WhpCoreParams) : ℕ := cp ⟨16, by decide⟩
@[expose] def wpPowBChar (cp : WhpCoreParams) : ℕ := cp ⟨17, by decide⟩
@[expose] def wpMaskBChar (cp : WhpCoreParams) : ℕ := cp ⟨18, by decide⟩
@[expose] def wpCTab (cp : WhpCoreParams) : ℕ := cp ⟨19, by decide⟩
@[expose] def wpSMax (cp : WhpCoreParams) : ℕ := cp ⟨20, by decide⟩
@[expose] def wpBufItemCap (cp : WhpCoreParams) : ℕ := cp ⟨21, by decide⟩
@[expose] def wpQEpoch (cp : WhpCoreParams) : ℕ := cp ⟨22, by decide⟩
@[expose] def wpDelta (cp : WhpCoreParams) : ℕ := cp ⟨23, by decide⟩
@[expose] def wpCapFront (cp : WhpCoreParams) : ℕ := cp ⟨24, by decide⟩
@[expose] def wpCapBack (cp : WhpCoreParams) : ℕ := cp ⟨25, by decide⟩
@[expose] def wpTotalLoc (cp : WhpCoreParams) : ℕ := cp ⟨26, by decide⟩
@[expose] def wpFrontTotal (cp : WhpCoreParams) : ℕ := cp ⟨27, by decide⟩
@[expose] def wpPoolSize (cp : WhpCoreParams) : ℕ := cp ⟨28, by decide⟩
@[expose] def wpOvermarsThresh (cp : WhpCoreParams) : ℕ := cp ⟨29, by decide⟩
@[expose] def wpGlobalPtrBits (cp : WhpCoreParams) : ℕ := cp ⟨30, by decide⟩
@[expose] def wpPermActBits (cp : WhpCoreParams) : ℕ := cp ⟨31, by decide⟩
@[expose] def wpTrieChildEntries (cp : WhpCoreParams) : ℕ := cp ⟨32, by decide⟩
@[expose] def wpMaxTrieNodes (cp : WhpCoreParams) : ℕ := cp ⟨33, by decide⟩
@[expose] def wpHMaxBTree (cp : WhpCoreParams) : ℕ := cp ⟨34, by decide⟩
@[expose] def wpTMin (cp : WhpCoreParams) : ℕ := cp ⟨35, by decide⟩
@[expose] def wpCapLanes (cp : WhpCoreParams) : ℕ := cp ⟨36, by decide⟩
@[expose] def wpFullKeys (cp : WhpCoreParams) : ℕ := cp ⟨37, by decide⟩
@[expose] def wpWKey (cp : WhpCoreParams) : ℕ := cp ⟨38, by decide⟩
@[expose] def wpMaskWKey (cp : WhpCoreParams) : ℕ := cp ⟨39, by decide⟩
@[expose] def wpSwarOnesCap (cp : WhpCoreParams) : ℕ := cp ⟨40, by decide⟩
@[expose] def wpValsWordBits (cp : WhpCoreParams) : ℕ := cp ⟨41, by decide⟩
@[expose] def wpKeysWordBits (cp : WhpCoreParams) : ℕ := cp ⟨42, by decide⟩
@[expose] def wpWVal (cp : WhpCoreParams) : ℕ := cp ⟨43, by decide⟩
@[expose] def wpMaskWVal (cp : WhpCoreParams) : ℕ := cp ⟨44, by decide⟩
@[expose] def wpNodeMetaBits (cp : WhpCoreParams) : ℕ := cp ⟨45, by decide⟩
@[expose] def wpNSlice (cp : WhpCoreParams) : ℕ := cp ⟨46, by decide⟩
@[expose] def wpOffHashBkt (cp : WhpCoreParams) : ℕ := cp ⟨47, by decide⟩
@[expose] def wpOffHashFp (cp : WhpCoreParams) : ℕ := cp ⟨48, by decide⟩
@[expose] def wpOffQuot (cp : WhpCoreParams) : ℕ := cp ⟨49, by decide⟩
@[expose] def wpOffVal (cp : WhpCoreParams) : ℕ := cp ⟨50, by decide⟩
@[expose] def wpOffPermAct (cp : WhpCoreParams) : ℕ := cp ⟨51, by decide⟩
@[expose] def wpOffLocState (cp : WhpCoreParams) : ℕ := cp ⟨52, by decide⟩
@[expose] def wpOffBktMeta (cp : WhpCoreParams) : ℕ := cp ⟨53, by decide⟩
@[expose] def wpOffFbStart (cp : WhpCoreParams) : ℕ := cp ⟨54, by decide⟩
@[expose] def wpOffBackPtr (cp : WhpCoreParams) : ℕ := cp ⟨55, by decide⟩
@[expose] def wpOffPoolFreeStack (cp : WhpCoreParams) : ℕ := cp ⟨56, by decide⟩
@[expose] def wpOffPoolOwner (cp : WhpCoreParams) : ℕ := cp ⟨57, by decide⟩
@[expose] def wpOffBtMeta (cp : WhpCoreParams) : ℕ := cp ⟨58, by decide⟩
@[expose] def wpOffBtKeys (cp : WhpCoreParams) : ℕ := cp ⟨59, by decide⟩
@[expose] def wpOffBtVals (cp : WhpCoreParams) : ℕ := cp ⟨60, by decide⟩
@[expose] def wpOffTrieChild0 (cp : WhpCoreParams) : ℕ := cp ⟨61, by decide⟩
@[expose] def wpOffTrieChild1 (cp : WhpCoreParams) : ℕ := cp ⟨62, by decide⟩
@[expose] def wpOffTrieMeta0 (cp : WhpCoreParams) : ℕ := cp ⟨63, by decide⟩
@[expose] def wpOffTrieMeta1 (cp : WhpCoreParams) : ℕ := cp ⟨64, by decide⟩
@[expose] def wpOffTrieItems0 (cp : WhpCoreParams) : ℕ := cp ⟨65, by decide⟩
@[expose] def wpOffTrieItems1 (cp : WhpCoreParams) : ℕ := cp ⟨66, by decide⟩

/-- Both `HashParams` vectors satisfy `BitPackedDoubleTabulation.HashEnv` in the large regime. -/
theorem hashEnvs_of_large {base c U V w n_max : ℕ}
    (hw : 0 < w) (hth : whpThreshold c ≤ n_max) (hnU : n_max ≤ U)
    (hU : Fits w U) (hfit : Fits w (base + whpSpace c U V w n_max)) :
    BitPackedDoubleTabulation.HashEnv w
      (BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max))
      (base + offHashBkt) ∧
    BitPackedDoubleTabulation.HashEnv w
      (BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))
      (base + offHashFp c w n_max) := by
  have hsp : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
    unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
  rw [hsp] at hfit
  have hlog_w := log_n_max_lt_w hth hnU hU
  have hlog_ge := mul_ell_le_log hth
  have hell := one_le_ellWhp n_max
  have hbc_lt : bCharWhp n_max < w := (Nat.div_le_self _ 4).trans_lt hlog_w
  have hb_le : bWhp n_max ≤ w := ((Nat.sub_le _ _).trans_lt hlog_w).le
  have hfp_le : fpBitsWhp n_max ≤ w := by
    have : fpBitsWhp n_max ≤ Nat.log 2 n_max := by unfold fpBitsWhp; omega
    exact (this.trans_lt hlog_w).le
  obtain ⟨htb1, _, _, _, _, _⟩ := sublinear_table_bits_le hth
  have hbc_pos : 0 < bCharWhp n_max := by have := mul_ell_le_bCharWhp hth; omega
  have htop_le :
      BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hbc_pos).trans htb1
  have hn_lt_w : n_max < 2 ^ w := hnU.trans_lt hU
  have htop_lt : BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) <
      2 ^ w := htop_le.trans_lt hn_lt_w
  have hbot_le : BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp n_max) ≤
      BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) := by
    dsimp only [BitPackedDoubleTabulation.botEntries, BitPackedDoubleTabulation.topEntries]
    have : dTabWhp c ≤ (cTabWhp c + 1) * dTabWhp c := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.mul_le_mul_right _ this
  have hbot_lt : BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp n_max) < 2 ^ w :=
    hbot_le.trans_lt htop_lt
  have hc1_lt : cTabWhp c + 1 < 2 ^ w := by
    have hd_pos : 0 < dTabWhp c * 2 ^ bCharWhp n_max :=
      Nat.mul_pos (dTabWhp_pos c) (Nat.two_pow_pos _)
    have : cTabWhp c + 1 ≤
        BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) := by
      dsimp only [BitPackedDoubleTabulation.topEntries]
      rw [mul_assoc]
      exact Nat.le_mul_of_pos_right _ hd_pos
    exact this.trans_lt htop_lt
  have hd_lt : dTabWhp c < 2 ^ w := by
    have : dTabWhp c ≤ BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp n_max) :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    exact this.trans_lt hbot_lt
  have hfit1 : Fits w ((base + offHashBkt) + bktHashWords c w n_max) := by
    refine hfit.of_le ?_
    unfold largeSpaceWhp offHashBkt bktHashWords
    omega
  have hfit2 : Fits w ((base + offHashFp c w n_max) + fpHashWords c w n_max) := by
    refine hfit.of_le ?_
    unfold largeSpaceWhp offHashFp offHashBkt bktHashWords fpHashWords
    omega
  exact ⟨⟨w0Whp U, rRedWhp c n_max, cTabWhp c, dTabWhp c, bCharWhp n_max, bWhp n_max,
      hw, w0Whp_pos U, w0Whp_le_w hw hU, hbc_lt, hb_le, htop_lt, hbot_lt, hc1_lt, hd_lt,
      hfit1, rfl⟩,
    ⟨w0Whp U, rRedWhp c n_max, cTabWhp c, dTabWhp c, bCharWhp n_max, fpBitsWhp n_max,
      hw, w0Whp_pos U, w0Whp_le_w hw hU, hbc_lt, hfp_le, htop_lt, hbot_lt, hc1_lt, hd_lt,
      hfit2, rfl⟩⟩

/-- Every word in the 100-word `WordEncoding.encode (mkWhpParams c U V w n_max)` vector fits in `w`
bits under standard dictionary parameter admissibility. -/
theorem fits_mkWhpParams {base c U V w n_max : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max)) :
    (∀ i : Fin 68, Fits w (mkWhpCoreParams c U V w n_max i)) ∧
    (∀ j : Fin 16, Fits w ((mkWhpParams c U V w n_max).2.1 j) ∧
      Fits w ((mkWhpParams c U V w n_max).2.2 j)) := by
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  have hn_lt : n_max < 2 ^ w := hnU.trans_lt hU
  have h0_fit : Fits w 0 := Nat.two_pow_pos w
  have h1_fit : Fits w 1 := Nat.one_lt_two_pow hw.ne'
  by_cases hsm : n_max < whpThreshold c
  · have hsp : whpSpace c U V w n_max = smallSpaceWhp U V w n_max := by
      unfold whpSpace; exact ite_eq_left hsm
    rw [hsp] at hfit
    have hs1 : offSmallPres = 32 := rfl
    have hs2 : offSmallKeys U w n_max = offSmallPres + packedWords n_max 1 w := rfl
    have hs3 : offSmallVals U w n_max = offSmallKeys U w n_max + packedWords n_max (keyBits U) w :=
      rfl
    have hend := smallOffsets_eq U V w n_max
    refine ⟨fun i => ?_, fun j => ?_⟩
    · dsimp only [mkWhpCoreParams]
      rw [ite_eq_left hsm]
      split
      · exact h1_fit
      · exact hw_lt
      · exact hn_lt
      · exact hU
      · exact hV
      · exact (keyBits_le_w hU).trans_lt hw_lt
      · exact (valBits_le_w hV).trans_lt hw_lt
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact h0_fit
    · dsimp only [mkWhpParams]
      rw [ite_eq_left hsm]
      exact ⟨h0_fit, h0_fit⟩
  · have hth : whpThreshold c ≤ n_max := Nat.le_of_not_lt hsm
    obtain ⟨henv1, henv2⟩ := hashEnvs_of_large hw hth hnU hU hfit
    have hsp : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
      unfold whpSpace; exact ite_eq_right hsm
    rw [hsp] at hfit
    have hend := largeOffsets_eq c U V w n_max
    have hlog_w := log_n_max_lt_w hth hnU hU
    have hlog_ge := mul_ell_le_log hth
    have hell := one_le_ellWhp n_max
    obtain ⟨hM_ge, hns_lt, htl_lt, h8L_lt, hsMax_lt, hmt_lt, hq_lt, hpbc_lt⟩ :=
      large_bounds_lt_n_max hth
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hkw_log := keysWordBitsWhp_lt_log hth
    have hvw_log := valsWordBitsWhp_lt_log hth
    have hM_le_n : numBucketsWhp n_max ≤ n_max := by
      have hL12 : 1 ≤ (scaleWhp n_max) ^ 12 := Nat.one_le_pow 12 _ (scaleWhp_pos n_max)
      exact (Nat.le_mul_of_pos_right _ hL12).trans (numBucketsWhp_mul_scale_pow12_le hth)
    have hl_hb : offHashBkt = 32 := rfl
    have hl_hf : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
    have hl_q : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
    have hl_v : offValWhp c U w n_max =
        offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
    have hl_pa : offPermAct c U V w n_max =
        offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
    have hl_ls : offLocState c U V w n_max =
        offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
    have hl_bm : offBktMeta c U V w n_max =
        offLocState c U V w n_max +
          packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
    have hl_fb : offFbStart c U V w n_max =
        offBktMeta c U V w n_max +
          packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
    have hl_bp : offBackPtr c U V w n_max =
        offFbStart c U V w n_max +
          packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w := rfl
    have hl_ba : offBackAux c U V w n_max =
        offBackPtr c U V w n_max +
          packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
    have hl_ps : offPoolFreeStack c U V w n_max =
        offBackAux c U V w n_max +
          packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w := rfl
    have hl_po : offPoolOwner c U V w n_max =
        offPoolFreeStack c U V w n_max +
          packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
    have hl_btm : offBtMeta c U V w n_max =
        offPoolOwner c U V w n_max +
          packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
    have hl_btk : offBtKeys c U V w n_max =
        offBtMeta c U V w n_max +
          packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w := rfl
    have hl_btv : offBtVals c U V w n_max =
        offBtKeys c U V w n_max +
          packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w := rfl
    have hl_tc0 : offTrieChild0 c U V w n_max =
        offBtVals c U V w n_max +
          packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w := rfl
    have hl_tc1 : offTrieChild1 c U V w n_max =
        offTrieChild0 c U V w n_max +
          packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
    have hl_tm0 : offTrieMeta0 c U V w n_max =
        offTrieChild1 c U V w n_max +
          packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
    have hl_tm1 : offTrieMeta1 c U V w n_max =
        offTrieMeta0 c U V w n_max +
          packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
    have hl_ti0 : offTrieItems0 c U V w n_max =
        offTrieMeta1 c U V w n_max +
          packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
    have hl_ti1 : offTrieItems1 c U V w n_max =
        offTrieItems0 c U V w n_max +
          packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
    refine ⟨fun i => ?_, fun j => ?_⟩
    · dsimp only [mkWhpCoreParams]
      rw [ite_eq_right hsm]
      split
      · exact h0_fit
      · exact hw_lt
      · exact hn_lt
      · exact hU
      · exact hV
      · exact (keyBits_le_w hU).trans_lt hw_lt
      · exact (valBits_le_w hV).trans_lt hw_lt
      · exact h0_fit
      · exact h0_fit
      · exact h0_fit
      · exact ((Nat.sub_le _ _).trans_lt hlog_w).trans hw_lt
      · exact hM_le_n.trans_lt hn_lt
      · exact (Nat.sub_le _ _).trans_lt (hM_le_n.trans_lt hn_lt)
      · exact ((Nat.sub_le _ _).trans (keyBits_le_w hU)).trans_lt hw_lt
      · exact (by unfold fpBitsWhp; omega : fpBitsWhp n_max < w).trans hw_lt
      · exact Nat.pow_lt_pow_right (by decide) (by unfold fpBitsWhp; omega : fpBitsWhp n_max < w)
      · exact ((Nat.div_le_self _ 4).trans_lt hlog_w).trans hw_lt
      · exact hpbc_lt.trans hn_lt
      · exact (Nat.sub_le _ _).trans_lt (hpbc_lt.trans hn_lt)
      · have hq_pos : 1 ≤ qEpochWhp n_max := Nat.one_le_pow 18 _ (scaleWhp_pos n_max)
        have : cTabWhp c < maxTrieNodesWhp c n_max := by
          calc cTabWhp c ≤ (cTabWhp c + 1) * 1 := by omega
            _ ≤ (cTabWhp c + 1) * qEpochWhp n_max := Nat.mul_le_mul_left _ hq_pos
            _ < maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
        exact (this.trans hmt_lt).trans hn_lt
      · exact hsMax_lt.trans hn_lt
      · exact (hrc_lt.trans hq_lt).trans hn_lt
      · exact hq_lt.trans hn_lt
      · exact (Nat.div_le_self _ _).trans_lt hn_lt
      · exact ((Nat.sub_le _ _).trans (Nat.div_le_self _ _)).trans_lt hn_lt
      · exact ((Nat.le_add_left _ _).trans_lt htl_lt).trans hn_lt
      · exact htl_lt.trans hn_lt
      · exact ((Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)).trans_lt hn_lt
      · exact (Nat.sub_le _ _).trans_lt hn_lt
      · exact (Nat.mul_le_mul_right _ (by decide : 5 ≤ 8)).trans_lt (h8L_lt.trans hn_lt)
      · exact (globalPtrBits_le_w hnU hU).trans_lt hw_lt
      · exact (by omega : 12 * ellWhp n_max + 4 < w).trans hw_lt
      · exact htc_n.trans_lt hn_lt
      · exact hmt_lt.trans hn_lt
      · rw [hMaxBTree_eq]
        exact (by omega : 42 < 1024).trans (hM_ge.trans_lt (hM_le_n.trans_lt hn_lt))
      · have : tMinWhp n_max < w := by
          have : tMinWhp n_max ≤ Nat.log 2 n_max := by
            unfold tMinWhp; exact max_le (by omega) (Nat.div_le_self _ _)
          omega
        exact this.trans hw_lt
      · have hkl_pos : 0 < keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp; positivity
        have h2t : 2 * tMinWhp n_max ≤ keysWordBitsWhp n_max :=
          Nat.le_mul_of_pos_right _ hkl_pos
        exact (h2t.trans_lt (by omega : keysWordBitsWhp n_max < w)).trans hw_lt
      · have hkl_pos : 0 < keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp; positivity
        have h2t : 2 * tMinWhp n_max - 1 ≤ keysWordBitsWhp n_max :=
          (Nat.sub_le _ _).trans (Nat.le_mul_of_pos_right _ hkl_pos)
        exact (h2t.trans_lt (by omega : keysWordBitsWhp n_max < w)).trans hw_lt
      · exact (by omega : keyLaneBitsWhp n_max < w).trans hw_lt
      · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans
          (Nat.pow_lt_pow_right (by decide) (by omega : keyLaneBitsWhp n_max < w))
      · exact (swarOnes_lt (keyLaneBitsWhp n_max) (2 * tMinWhp n_max)).trans
          (Nat.pow_lt_pow_right (by decide) (by
            have : 2 * tMinWhp n_max * keyLaneBitsWhp n_max = keysWordBitsWhp n_max := rfl
            omega))
      · exact (by omega : valsWordBitsWhp n_max < w).trans hw_lt
      · exact (by omega : keysWordBitsWhp n_max < w).trans hw_lt
      · exact (by omega : valLaneBitsWhp n_max < w).trans hw_lt
      · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans
          (Nat.pow_lt_pow_right (by decide) (by omega : valLaneBitsWhp n_max < w))
      · exact (by unfold nodeMetaBitsWhp; omega : nodeMetaBitsWhp n_max < w).trans hw_lt
      · exact hns_lt.trans hn_lt
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact hfit.of_le (by omega)
      · exact h0_fit
    · dsimp only [mkWhpParams]
      rw [ite_eq_right hsm]
      exact ⟨BitPackedDoubleTabulation.fits_mkHashParams henv1 j,
        BitPackedDoubleTabulation.fits_mkHashParams henv2 j⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
