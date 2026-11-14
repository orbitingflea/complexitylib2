/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.SuccinctBucket
public import CslibFrontier.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameters, Threshold Inequalities, and Succinct Space Accounting for the WHP Dictionary

This module defines the dimension, hashing, buffer, SWAR B+-tree, and memory-layout parameters for
the with-high-probability fixed-capacity succinct dynamic dictionary (`insert`, `delete`, `query`),
and proves the threshold and succinct word-space inequalities across all word widths `w` and all
`n_max ≤ U`.

## Parameter regimes and theoretical `O_c(1)` constants

For any fixed failure-probability exponent `c : ℕ` (normalized to `cEff c = max c 1 ≥ 1`):
* Below the `c`-only capacity threshold `whpThreshold c = 2 ^ bMinWhp c` (`bMinWhp c = Θ(c^6)`),
  the dictionary uses a deterministic bit-packed array of `n_max` entries (`Present`, `Keys`,
  `Values`). Every operation completes deterministically in `O_c(1)` instructions
  (`failureProb = 0`), and by `FeistelQuotient.pow_le_pow_mul_choose`,
  `n_max * keyBits U ≤ optBits + (bMinWhp c + 2) * n_max * logLogFactor n_max`.
* At or above `whpThreshold c ≤ n_max` (`bMinWhp c ≤ ⌊log₂ n_max⌋`), `Nat.mul_log_le_add_sq` gives
  `codeExpWhp c * logLogFactor n_max ≤ bCharWhp n_max = ⌊log₂ n_max⌋ / 4`, simultaneously
  discharging Thorup's double-tabulation threshold
  `2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c n_max) ≤
  2 ^ bCharWhp n_max`, the polylogarithmic scale separation `(slabScale n_max) ^ 24 ≤ n_max`, and
  the SWAR B+-tree branching bound `8 ≤ tMinWhp n_max`. Note that `whpThreshold c`,
  `whpTimeBound c`, `whpInitFactor c`, and `whpSpaceFactor c` are explicit theoretical `O_c(1)`
  constants (large due to `bMinWhp c = Θ(c^6)`).

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.cEff`, `cTabWhp`, `qTabWhp`, `dTabWhp`, `codeExpWhp`,
  `bMinWhp`, `whpThreshold`: `c`-only exponent, tabulation, and capacity-threshold parameters.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.bWhp`, `numBucketsWhp`, `quotBitsWhp`, `fpBitsWhp`,
  `bCharWhp`, `rRedWhp`, `sMaxWhp`, `kIndepWhp`, `qEpochWhp`: bucket, quotient, fingerprint, salt,
  and epoch parameters for `whpThreshold c ≤ n_max`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.deltaWhp`, `capFrontWhp`, `capBackWhp`, `capMaxWhp`,
  `poolSizeWhp`, `tMinWhp`, `nSliceWhp`: front-yard/backyard conservation and SWAR B+-tree slice
  parameters.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.whpSpace`, `whpSpaceFactor`, `whpSpaceConst`:
  total `w`-bit word footprint and `c`-only succinct space constants.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.codeExpWhp_mul_ell_le_bCharWhp`:
  `codeExpWhp c * logLogFactor n_max ≤ bCharWhp n_max` whenever `whpThreshold c ≤ n_max`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.two_mul_doubleTabCodeBound_le_pow_bCharWhp`:
  Thorup's `k`-uniqueness threshold holds for all `whpThreshold c ≤ n_max`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.sum_sub_capFront_le_poolSize`:
  3-case front-yard/backyard conservation bound across all `0 ≤ n ≤ n_max`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.whpSpace_le_succinctWords`:
  `whpSpace c U V w n_max ≤ Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max`
  for every `w` and every `n_max ≤ U`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open Finset
open scoped BigOperators

/-! ## Section 1: `c`-only exponent, tabulation, and capacity-threshold parameters -/

/-- Normalized failure exponent `max c 1 ≥ 1`. -/
@[expose] def cEff (c : ℕ) : ℕ :=
  max c 1

theorem one_le_cEff (c : ℕ) : 1 ≤ cEff c :=
  le_max_right c 1

theorem le_cEff (c : ℕ) : c ≤ cEff c :=
  le_max_left c 1

/-- Number of base-`2 ^ bCharWhp` key characters `8 * (cEff c + 5)` (`≥ 48`), serving as both the
Stage-1 reduced-key character count and the constant height of the `G`/`S` buffer tries. -/
def cTabWhp (c : ℕ) : ℕ :=
  8 * (cEff c + 5)

theorem cTabWhp_eq (c : ℕ) : cTabWhp c = 8 * (cEff c + 5) := by rfl

theorem le_cTabWhp (c : ℕ) : 48 ≤ cTabWhp c := by
  unfold cTabWhp
  have := one_le_cEff c
  omega

/-- Double-tabulation expansion parameter `q = 4 * (cEff c + 6) + 2` (`≥ 30`). -/
def qTabWhp (c : ℕ) : ℕ :=
  4 * (cEff c + 6) + 2

theorem qTabWhp_eq (c : ℕ) : qTabWhp c = 4 * (cEff c + 6) + 2 := by rfl

theorem le_qTabWhp (c : ℕ) : 30 ≤ qTabWhp c := by
  unfold qTabWhp
  have := one_le_cEff c
  omega

/-- Double-tabulation intermediate tuple length `d = 2 * qTabWhp c * (cTabWhp c + 1)`. -/
def dTabWhp (c : ℕ) : ℕ :=
  2 * qTabWhp c * (cTabWhp c + 1)

theorem dTabWhp_eq (c : ℕ) : dTabWhp c = 2 * qTabWhp c * (cTabWhp c + 1) := by rfl

theorem dTabWhp_pos (c : ℕ) : 0 < dTabWhp c := by
  unfold dTabWhp
  have := le_qTabWhp c
  positivity

/-- Combined logarithmic exponent multiplier `320 + 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c` (`Θ(c^3)`)
chosen so `codeExpWhp c * logLogFactor n_max ≤ bCharWhp n_max` discharges both Thorup's code bound
and all polylogarithmic scale inequalities. -/
def codeExpWhp (c : ℕ) : ℕ :=
  320 + 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c

theorem le_codeExpWhp (c : ℕ) : 320 ≤ codeExpWhp c := by
  unfold codeExpWhp
  omega

/-- Minimum `⌊log₂ n_max⌋` threshold `64 * (codeExpWhp c) ^ 2 + 16 * codeExpWhp c` (`Θ(c^6)`). -/
def bMinWhp (c : ℕ) : ℕ :=
  64 * (codeExpWhp c) ^ 2 + 16 * codeExpWhp c

theorem le_bMinWhp (c : ℕ) : 6553600 ≤ bMinWhp c := by
  unfold bMinWhp
  have := le_codeExpWhp c
  nlinarith

theorem cEff_add_four_le_bMinWhp (c : ℕ) : cEff c + 4 ≤ bMinWhp c := by
  have hcTab : 2 * (cEff c + 4) ≤ cTabWhp c + 1 := by unfold cTabWhp; omega
  have hq := le_qTabWhp c
  have hcd : cTabWhp c + 1 ≤ codeExpWhp c := by unfold codeExpWhp; nlinarith
  unfold bMinWhp
  nlinarith

/-- Capacity threshold `2 ^ bMinWhp c` separating the deterministic bit-packed regime
(`n_max < whpThreshold c`) from the succinct two-stage double-tabulation regime
(`whpThreshold c ≤ n_max`). -/
def whpThreshold (c : ℕ) : ℕ :=
  2 ^ bMinWhp c

theorem whpThreshold_pos (c : ℕ) : 0 < whpThreshold c := by
  unfold whpThreshold
  positivity

/-! ## Section 2: Bucket, quotient, fingerprint, salt, B+-tree, and buffer parameters -/

/-- Shorthand for `Dynamic.logLogFactor n_max ≥ 1`. -/
@[expose] def ellWhp (n_max : ℕ) : ℕ :=
  Dynamic.logLogFactor n_max

/-- Polylogarithmic scale `L = 2 ^ ellWhp n_max = slabScale n_max ≥ 2`. -/
@[expose] def scaleWhp (n_max : ℕ) : ℕ :=
  slabScale n_max

/-- Tabulation character width `⌊log₂ n_max⌋ / 4`. -/
@[expose] def bCharWhp (n_max : ℕ) : ℕ :=
  Nat.log 2 n_max / 4

/-- Stage-1 universe-reduced key bit-width `cTabWhp c * bCharWhp n_max`. -/
@[expose] def rRedWhp (c n_max : ℕ) : ℕ :=
  cTabWhp c * bCharWhp n_max

/-- Feistel bucket index bit-width `⌊log₂ n_max⌋ - 12 * ellWhp n_max`. -/
@[expose] def bWhp (n_max : ℕ) : ℕ :=
  Nat.log 2 n_max - 12 * ellWhp n_max

/-- Number of Feistel buckets `M = 2 ^ bWhp n_max`. -/
@[expose] def numBucketsWhp (n_max : ℕ) : ℕ :=
  2 ^ bWhp n_max

/-- Stored quotient bit-width `keyBits U - bWhp n_max`. -/
@[expose] def quotBitsWhp (U n_max : ℕ) : ℕ :=
  keyBits U - bWhp n_max

/-- Salted fingerprint bit-width `36 * ellWhp n_max` (`2 ^ fpBitsWhp = L ^ 36`). -/
@[expose] def fpBitsWhp (n_max : ℕ) : ℕ :=
  36 * ellWhp n_max

/-- Per-bucket salt search bound `(cEff c + 4) * scaleWhp n_max`. -/
@[expose] def sMaxWhp (c n_max : ℕ) : ℕ :=
  (cEff c + 4) * scaleWhp n_max

/-- Half-independence parameter `rIndepWhp c n_max = (cEff c + 4) * scaleWhp n_max`. -/
@[expose] def rIndepWhp (c n_max : ℕ) : ℕ :=
  (cEff c + 4) * scaleWhp n_max

/-- Required `k`-wise independence degree `2 * rIndepWhp c n_max`. -/
@[expose] def kIndepWhp (c n_max : ℕ) : ℕ :=
  2 * rIndepWhp c n_max

/-- Deamortization epoch length `Q = (scaleWhp n_max) ^ 18`. -/
@[expose] def qEpochWhp (n_max : ℕ) : ℕ :=
  (scaleWhp n_max) ^ 18

/-- Per-bucket load concentration margin
`δ = n_max / (numBucketsWhp n_max * (8 * scaleWhp n_max))`. -/
@[expose] def deltaWhp (n_max : ℕ) : ℕ :=
  n_max / (numBucketsWhp n_max * (8 * scaleWhp n_max))

/-- Dedicated front-yard slot capacity per bucket `⌊n_max / M⌋ - 4 * deltaWhp n_max`. -/
@[expose] def capFrontWhp (n_max : ℕ) : ℕ :=
  n_max / numBucketsWhp n_max - 4 * deltaWhp n_max

/-- Per-bucket backyard pointer directory capacity `2 * (scaleWhp n_max) ^ 11`. -/
@[expose] def capBackWhp (n_max : ℕ) : ℕ :=
  2 * (scaleWhp n_max) ^ 11

/-- Total local coordinates per bucket `capFrontWhp n_max + capBackWhp n_max`. -/
@[expose] def totalLocalCoordsWhp (n_max : ℕ) : ℕ :=
  capFrontWhp n_max + capBackWhp n_max

/-- Maximum good-event bucket occupancy `4 * (scaleWhp n_max) ^ 12`. -/
@[expose] def capMaxWhp (n_max : ℕ) : ℕ :=
  4 * (scaleWhp n_max) ^ 12

/-- Global shared backyard pool capacity `n_max - numBucketsWhp n_max * capFrontWhp n_max`. -/
@[expose] def poolSizeWhp (n_max : ℕ) : ℕ :=
  n_max - numBucketsWhp n_max * capFrontWhp n_max

/-- Minimum degree `t ≥ 2` of internal SWAR B+-tree nodes:
`max 2 (⌊log₂ n_max⌋ / (160 * ellWhp n_max))`. -/
@[expose] def tMinWhp (n_max : ℕ) : ℕ :=
  max 2 (Nat.log 2 n_max / (160 * ellWhp n_max))

/-- SWAR key lane bit-width `fpBitsWhp n_max + 2 = 36 * ellWhp n_max + 2`. -/
@[expose] def keyLaneBitsWhp (n_max : ℕ) : ℕ :=
  fpBitsWhp n_max + 2

/-- SWAR child/local-coord lane bit-width `12 * ellWhp n_max + 8`. -/
@[expose] def valLaneBitsWhp (n_max : ℕ) : ℕ :=
  12 * ellWhp n_max + 8

/-- Packed SWAR keys-word bit-width `2 * tMinWhp n_max * keyLaneBitsWhp n_max`. -/
@[expose] def keysWordBitsWhp (n_max : ℕ) : ℕ :=
  2 * tMinWhp n_max * keyLaneBitsWhp n_max

/-- Packed SWAR values/children-word bit-width `2 * tMinWhp n_max * valLaneBitsWhp n_max`. -/
@[expose] def valsWordBitsWhp (n_max : ℕ) : ℕ :=
  2 * tMinWhp n_max * valLaneBitsWhp n_max

/-- Packed SWAR B+-tree node metadata bit-width `ellWhp n_max + 4` (`isLeaf` + `keyCount`). -/
@[expose] def nodeMetaBitsWhp (n_max : ℕ) : ℕ :=
  ellWhp n_max + 4

/-- Nodes per SWAR B+-tree slice `32 * (scaleWhp n_max) ^ 12 / (tMinWhp n_max - 1) + 64`. -/
@[expose] def nSliceWhp (n_max : ℕ) : ℕ :=
  32 * (scaleWhp n_max) ^ 12 / (tMinWhp n_max - 1) + 64

/-- Total SWAR B+-tree nodes across all `3 * M` slices (`3` independent roles per bucket). -/
@[expose] def totalBTreeNodesWhp (n_max : ℕ) : ℕ :=
  3 * numBucketsWhp n_max * nSliceWhp n_max

/-- Maximum `BufTrie` nodes per buffer (`(cTabWhp c + 1) * qEpochWhp n_max + 2`). -/
@[expose] def maxTrieNodesWhp (c n_max : ℕ) : ℕ :=
  (cTabWhp c + 1) * qEpochWhp n_max + 2

/-- Total child-pointer entries `(maxTrieNodesWhp c n_max) * 2 ^ bCharWhp n_max` per `BufTrie`. -/
@[expose] def trieChildEntriesWhp (c n_max : ℕ) : ℕ :=
  maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max
/-! ## Section 3: Threshold inequalities for `whpThreshold c ≤ n_max` -/

theorem one_le_ellWhp (n : ℕ) : 1 ≤ ellWhp n :=
  Dynamic.one_le_logLogFactor n

theorem two_le_scaleWhp (n : ℕ) : 2 ≤ scaleWhp n :=
  two_le_slabScale n

theorem scaleWhp_pos (n : ℕ) : 0 < scaleWhp n :=
  slabScale_pos n

theorem bMinWhp_le_log {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    bMinWhp c ≤ Nat.log 2 n_max := by
  unfold whpThreshold at hth
  exact Nat.le_log_of_pow_le Nat.one_lt_two hth

/-- Whenever `4 ≤ n` and `2 ≤ Nat.log 2 n`, `ellWhp n ≤ Nat.log 2 (Nat.log 2 n) + 2`. -/
theorem ellWhp_le_log_log_add_two {n : ℕ} (hn4 : 4 ≤ n) (hlog2 : 2 ≤ Nat.log 2 n) :
    ellWhp n ≤ Nat.log 2 (Nat.log 2 n) + 2 := by
  unfold ellWhp Dynamic.logLogFactor
  rw [max_eq_left hn4]
  have hlt1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hcl1 : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hlt1.le
  have hlt2 : Nat.log 2 n < 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two (Nat.log 2 n)
  refine (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr ?_
  rw [Nat.pow_succ]
  omega

/-- **Core threshold separation**: for all `whpThreshold c ≤ n_max`,
`codeExpWhp c * ellWhp n_max ≤ bCharWhp n_max`. -/
theorem codeExpWhp_mul_ell_le_bCharWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    codeExpWhp c * ellWhp n_max ≤ bCharWhp n_max := by
  have hm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  have hn4 : 4 ≤ n_max := by
    have h4 : 2 ^ 2 ≤ whpThreshold c := by
      unfold whpThreshold
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (by decide : 4 ≤ 2 ^ 2).trans (h4.trans hth)
  set m := Nat.log 2 n_max
  have hell := ellWhp_le_log_log_add_two hn4 (by omega : 2 ≤ m)
  set A := codeExpWhp c
  have hmul_sq := Nat.mul_log_le_add_sq Nat.one_lt_two (8 * A) m
  have h1 : 8 * A * ellWhp n_max ≤ 8 * A * (Nat.log 2 m + 2) :=
    Nat.mul_le_mul_left _ hell
  have h2 : 8 * A * (Nat.log 2 m + 2) = 8 * A * Nat.log 2 m + 16 * A := by ring
  have hbm_def : bMinWhp c = 64 * A ^ 2 + 16 * A := rfl
  have hsq : (8 * A) * (8 * A) = 64 * A ^ 2 := by ring
  rw [hsq] at hmul_sq
  have h8 : 8 * (A * ellWhp n_max) ≤ 2 * m := by linarith
  unfold bCharWhp
  change A * ellWhp n_max ≤ m / 4
  omega

/-- For `whpThreshold c ≤ n_max`, `320 * ellWhp n_max ≤ bCharWhp n_max`. -/
theorem mul_ell_le_bCharWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    320 * ellWhp n_max ≤ bCharWhp n_max :=
  (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)

/-- For `whpThreshold c ≤ n_max`, `1280 * ellWhp n_max ≤ Nat.log 2 n_max`. -/
theorem mul_ell_le_log {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    1280 * ellWhp n_max ≤ Nat.log 2 n_max := by
  have h := mul_ell_le_bCharWhp hth
  unfold bCharWhp at h
  omega

theorem bWhp_pos {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    0 < bWhp n_max := by
  have h := mul_ell_le_log hth
  have h1 := one_le_ellWhp n_max
  unfold bWhp
  omega

theorem bWhp_le_keyBits {U n_max : ℕ} (hnU : n_max ≤ U) :
    bWhp n_max ≤ keyBits U := by
  unfold bWhp keyBits
  have h1 : Nat.log 2 n_max - 12 * ellWhp n_max ≤ Nat.log 2 n_max := Nat.sub_le _ _
  have h2 : Nat.log 2 n_max ≤ Nat.log 2 U := Nat.log_mono_right hnU
  have h3 : Nat.log 2 U ≤ Nat.clog 2 U := Nat.log_le_clog 2 U
  omega

theorem quotBitsWhp_add_bWhp {U n_max : ℕ} (hnU : n_max ≤ U) :
    quotBitsWhp U n_max + bWhp n_max = keyBits U :=
  Nat.sub_add_cancel (bWhp_le_keyBits hnU)

/-- When `whpThreshold c ≤ n_max`, `numBucketsWhp n_max * (scaleWhp n_max) ^ 12 ≤ n_max`. -/
theorem numBucketsWhp_mul_scale_pow12_le {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    numBucketsWhp n_max * (scaleWhp n_max) ^ 12 ≤ n_max := by
  have h := mul_ell_le_log hth
  have hn0 : n_max ≠ 0 := by
    have := whpThreshold_pos c
    omega
  have hadd : bWhp n_max + 12 * ellWhp n_max = Nat.log 2 n_max := by
    unfold bWhp
    omega
  calc numBucketsWhp n_max * (scaleWhp n_max) ^ 12
      = 2 ^ bWhp n_max * (2 ^ ellWhp n_max) ^ 12 := rfl
    _ = 2 ^ (bWhp n_max + 12 * ellWhp n_max) := by
        rw [← Nat.pow_mul, Nat.mul_comm (ellWhp n_max) 12, ← Nat.pow_add]
    _ = 2 ^ Nat.log 2 n_max := by rw [hadd]
    _ ≤ n_max := Nat.pow_log_le_self 2 hn0

/-- For every `n_max`, `n_max ≤ 2 * numBucketsWhp n_max * (scaleWhp n_max) ^ 12`. -/
theorem le_two_mul_numBucketsWhp_mul_scale_pow12 (n_max : ℕ) :
    n_max ≤ 2 * numBucketsWhp n_max * (scaleWhp n_max) ^ 12 := by
  rcases Nat.eq_zero_or_pos n_max with rfl | hn
  · exact Nat.zero_le _
  · have hlt : n_max < 2 ^ (Nat.log 2 n_max + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n_max
    have hle : Nat.log 2 n_max + 1 ≤ bWhp n_max + 12 * ellWhp n_max + 1 := by
      unfold bWhp
      omega
    have hpow := hlt.le.trans (Nat.pow_le_pow_right (by decide) hle)
    have heq : 2 ^ (bWhp n_max + 12 * ellWhp n_max + 1) =
        2 * numBucketsWhp n_max * (scaleWhp n_max) ^ 12 := by
      unfold numBucketsWhp scaleWhp slabScale ellWhp
      rw [← Nat.pow_mul, Nat.mul_comm _ 12, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      ring
    omega

/-- When `whpThreshold c ≤ n_max`, `(scaleWhp n_max) ^ 24 ≤ 2 ^ bCharWhp n_max`. -/
theorem scaleWhp_pow24_le_pow_bChar {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (scaleWhp n_max) ^ 24 ≤ 2 ^ bCharWhp n_max := by
  have h := mul_ell_le_bCharWhp hth
  calc (scaleWhp n_max) ^ 24 = (2 ^ ellWhp n_max) ^ 24 := rfl
    _ = 2 ^ (24 * ellWhp n_max) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ bCharWhp n_max := Nat.pow_le_pow_right (by decide) (by omega)

/-- When `whpThreshold c ≤ n_max`, `(scaleWhp n_max) ^ 96 ≤ n_max`. -/
theorem scaleWhp_pow96_le_n_max {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (scaleWhp n_max) ^ 96 ≤ n_max := by
  have h := mul_ell_le_log hth
  have hn0 : n_max ≠ 0 := by have := whpThreshold_pos c; omega
  calc (scaleWhp n_max) ^ 96 = 2 ^ (96 * ellWhp n_max) := by
        unfold scaleWhp slabScale ellWhp
        rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ Nat.log 2 n_max := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ n_max := Nat.pow_log_le_self 2 hn0

/-- When `whpThreshold c ≤ n_max`, `8 ≤ tMinWhp n_max`. -/
theorem eight_le_tMinWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    8 ≤ tMinWhp n_max := by
  have h := mul_ell_le_log hth
  have h1 := one_le_ellWhp n_max
  have hdiv : 8 ≤ Nat.log 2 n_max / (160 * ellWhp n_max) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    omega
  unfold tMinWhp
  exact hdiv.trans (le_max_right 2 _)

/-- When `whpThreshold c ≤ n_max`,
`keysWordBitsWhp n_max + keyLaneBitsWhp n_max < Nat.log 2 n_max`. -/
theorem keysWordBitsWhp_lt_log {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    keysWordBitsWhp n_max + keyLaneBitsWhp n_max < Nat.log 2 n_max := by
  have h := mul_ell_le_log hth
  have h1 := one_le_ellWhp n_max
  have ht : tMinWhp n_max = Nat.log 2 n_max / (160 * ellWhp n_max) := by
    have h8 := eight_le_tMinWhp hth
    unfold tMinWhp at h8 ⊢
    omega
  have hmul : tMinWhp n_max * (160 * ellWhp n_max) ≤ Nat.log 2 n_max := by
    rw [ht]
    exact Nat.div_mul_le_self _ _
  have hkl : keyLaneBitsWhp n_max ≤ 38 * ellWhp n_max := by
    unfold keyLaneBitsWhp fpBitsWhp
    omega
  have h2t : (2 * tMinWhp n_max + 1) * keyLaneBitsWhp n_max <
      tMinWhp n_max * (160 * ellWhp n_max) := by
    have h8 := eight_le_tMinWhp hth
    calc (2 * tMinWhp n_max + 1) * keyLaneBitsWhp n_max
        ≤ (2 * tMinWhp n_max + 1) * (38 * ellWhp n_max) := Nat.mul_le_mul_left _ hkl
      _ < tMinWhp n_max * (160 * ellWhp n_max) := by nlinarith
  unfold keysWordBitsWhp
  linarith

/-- When `whpThreshold c ≤ n_max`,
`valsWordBitsWhp n_max + valLaneBitsWhp n_max < Nat.log 2 n_max`. -/
theorem valsWordBitsWhp_lt_log {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    valsWordBitsWhp n_max + valLaneBitsWhp n_max < Nat.log 2 n_max := by
  have h := keysWordBitsWhp_lt_log hth
  have h1 := one_le_ellWhp n_max
  have hle : valLaneBitsWhp n_max ≤ keyLaneBitsWhp n_max := by
    unfold valLaneBitsWhp keyLaneBitsWhp fpBitsWhp
    omega
  unfold valsWordBitsWhp
  unfold keysWordBitsWhp at h
  nlinarith

/-- When `whpThreshold c ≤ n_max`, `sMaxWhp c n_max ≤ 2 ^ bCharWhp n_max`. -/
theorem sMaxWhp_le_pow_bChar {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    sMaxWhp c n_max ≤ 2 ^ bCharWhp n_max := by
  have h := codeExpWhp_mul_ell_le_bCharWhp hth
  have h1 := one_le_ellWhp n_max
  have hlt : cEff c + 4 < 2 ^ (cTabWhp c) := by
    have hpow := @Nat.lt_two_pow_self (cTabWhp c)
    unfold cTabWhp at hpow ⊢
    omega
  have hexp : cTabWhp c + ellWhp n_max ≤ bCharWhp n_max := by
    have hce : cTabWhp c + 1 ≤ codeExpWhp c := by
      have hq := le_qTabWhp c
      have hc := le_cTabWhp c
      have h1a : cTabWhp c + 1 ≤ (cTabWhp c + 1) ^ 2 := by nlinarith
      have h2a : (cTabWhp c + 1) ^ 2 ≤ (cTabWhp c + 1) ^ 2 * qTabWhp c :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h3a : (cTabWhp c + 1) ^ 2 * qTabWhp c ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
        rw [mul_assoc 16]
        exact Nat.le_mul_of_pos_left _ (by decide)
      unfold codeExpWhp
      omega
    calc cTabWhp c + ellWhp n_max
        ≤ cTabWhp c * ellWhp n_max + ellWhp n_max :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right _ h1) _
      _ = (cTabWhp c + 1) * ellWhp n_max := by ring
      _ ≤ codeExpWhp c * ellWhp n_max := Nat.mul_le_mul_right _ hce
      _ ≤ bCharWhp n_max := h
  calc sMaxWhp c n_max = (cEff c + 4) * 2 ^ ellWhp n_max := rfl
    _ ≤ 2 ^ cTabWhp c * 2 ^ ellWhp n_max := Nat.mul_le_mul_right _ hlt.le
    _ = 2 ^ (cTabWhp c + ellWhp n_max) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ bCharWhp n_max := Nat.pow_le_pow_right (by decide) hexp

/-- **Thorup's `k`-uniqueness threshold inequality** for `(cTabWhp c + 1, dTabWhp c, qTabWhp c)`:
whenever `whpThreshold c ≤ n_max`,
`2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c n_max) ≤
2 ^ bCharWhp n_max`. -/
theorem two_mul_doubleTabCodeBound_le_pow_bCharWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c n_max) ≤
      2 ^ bCharWhp n_max := by
  have hmain := codeExpWhp_mul_ell_le_bCharWhp hth
  have hell := one_le_ellWhp n_max
  set c' := cTabWhp c + 1
  set q := qTabWhp c
  set d := dTabWhp c
  set ell := ellWhp n_max
  have hc' : 49 ≤ c' := by have := le_cTabWhp c; omega
  have hq : 30 ≤ q := le_qTabWhp c
  have h2c' : 2 * c' ≤ 2 ^ (2 * c') := by
    have := @Nat.lt_two_pow_self (2 * c')
    omega
  have hck : c' * kIndepWhp c n_max ≤ 2 ^ (2 * c' + ell) := by
    have h1 : c' * (2 * (cEff c + 4)) ≤ 2 ^ (2 * c') := by
      have hlt1 : c' ≤ 2 ^ c' := (@Nat.lt_two_pow_self c').le
      have hlt2 : 2 * (cEff c + 4) ≤ 2 ^ c' := by
        have hlt := (@Nat.lt_two_pow_self c').le
        have hle : 2 * (cEff c + 4) ≤ c' := by
          dsimp only [c', cTabWhp]
          omega
        exact hle.trans hlt
      calc c' * (2 * (cEff c + 4)) ≤ 2 ^ c' * 2 ^ c' := Nat.mul_le_mul hlt1 hlt2
        _ = 2 ^ (2 * c') := by rw [← Nat.pow_add, two_mul]
    have hrew : c' * kIndepWhp c n_max = (c' * (2 * (cEff c + 4))) * 2 ^ ell := by
      unfold kIndepWhp rIndepWhp scaleWhp slabScale
      dsimp only [ell, ellWhp]
      ring
    calc c' * kIndepWhp c n_max = (c' * (2 * (cEff c + 4))) * 2 ^ ell := hrew
      _ ≤ 2 ^ (2 * c') * 2 ^ ell := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (2 * c' + ell) := (Nat.pow_add 2 _ _).symm
  have hd_le : d ≤ 2 ^ (3 * c') := by
    have hqc' : q ≤ c' := by
      dsimp only [q, c', qTabWhp, cTabWhp]
      have := one_le_cEff c
      omega
    have hlt1 : 2 * q ≤ 2 ^ (2 * c') := by
      have := (@Nat.lt_two_pow_self (2 * c')).le
      omega
    have hlt2 : c' ≤ 2 ^ c' := (@Nat.lt_two_pow_self c').le
    calc d = (2 * q) * c' := rfl
      _ ≤ 2 ^ (2 * c') * 2 ^ c' := Nat.mul_le_mul hlt1 hlt2
      _ = 2 ^ (3 * c') := by rw [← Nat.pow_add]; ring_nf
  have hterm : (c' * kIndepWhp c n_max) ^ (2 * c') * d ≤ 2 ^ (6 * c' ^ 2 * ell + 3 * c' * ell) := by
    have he1 : 2 * c' * (2 * c' + ell) ≤ 6 * c' ^ 2 * ell := by
      have hc2_pos : 0 ≤ c' ^ 2 := Nat.zero_le _
      have heq1 : 2 * c' * (2 * c' + ell) = 4 * c' ^ 2 + 2 * c' * ell := by ring
      have hle1 : 4 * c' ^ 2 ≤ 4 * c' ^ 2 * ell := Nat.le_mul_of_pos_right _ hell
      have hle2 : 2 * c' * ell ≤ 2 * c' ^ 2 * ell :=
        Nat.mul_le_mul_right ell (by nlinarith)
      linarith
    have he2 : 3 * c' ≤ 3 * c' * ell := Nat.le_mul_of_pos_right _ hell
    calc (c' * kIndepWhp c n_max) ^ (2 * c') * d
        ≤ (2 ^ (2 * c' + ell)) ^ (2 * c') * 2 ^ (3 * c') :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hck (2 * c')) hd_le
      _ = 2 ^ (2 * c' * (2 * c' + ell) + 3 * c') := by
          rw [← Nat.pow_mul, Nat.mul_comm (2 * c' + ell) (2 * c'), ← Nat.pow_add]
      _ ≤ 2 ^ (6 * c' ^ 2 * ell + 3 * c' * ell) := Nat.pow_le_pow_right (by decide) (by omega)
  have hexp_le : 2 * c' + q * (6 * c' ^ 2 * ell + 3 * c' * ell) ≤ codeExpWhp c * ell := by
    have h2 : 2 * c' ≤ c' ^ 2 * q * ell := by
      have ha : 2 * c' ≤ c' ^ 2 := by nlinarith
      have hb : c' ^ 2 ≤ c' ^ 2 * q := Nat.le_mul_of_pos_right _ (by omega)
      exact (ha.trans hb).trans (Nat.le_mul_of_pos_right _ hell)
    have h3 : 3 * c' * q * ell ≤ 3 * c' ^ 2 * q * ell := by
      have ha : 3 * c' ≤ 3 * c' ^ 2 := by nlinarith
      exact Nat.mul_le_mul_right ell (Nat.mul_le_mul_right q ha)
    have hdist : q * (6 * c' ^ 2 * ell + 3 * c' * ell) =
        6 * (c' ^ 2 * q * ell) + 3 * c' * q * ell := by ring
    have hrhs : codeExpWhp c * ell = 320 * ell + 16 * (c' ^ 2 * q * ell) := by
      unfold codeExpWhp
      dsimp only [c', q]
      ring
    rw [hdist, hrhs]
    have h3' : 3 * c' ^ 2 * q * ell = 3 * (c' ^ 2 * q * ell) := by ring
    omega
  calc 2 * doubleTabCodeBound c' d q (kIndepWhp c n_max)
      = (2 * c') * ((c' * kIndepWhp c n_max) ^ (2 * c') * d) ^ q := by
        unfold doubleTabCodeBound; ring
    _ ≤ 2 ^ (2 * c') * (2 ^ (6 * c' ^ 2 * ell + 3 * c' * ell)) ^ q :=
        Nat.mul_le_mul h2c' (Nat.pow_le_pow_left hterm q)
    _ = 2 ^ (2 * c' + q * (6 * c' ^ 2 * ell + 3 * c' * ell)) := by
        rw [← Nat.pow_mul, Nat.mul_comm _ q, ← Nat.pow_add]
    _ ≤ 2 ^ (codeExpWhp c * ell) := Nat.pow_le_pow_right (by decide) hexp_le
    _ ≤ 2 ^ bCharWhp n_max := Nat.pow_le_pow_right (by decide) hmain

theorem two_mul_doubleTabCodeBound_le_pow_q_sub_one {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c n_max) ≤
      2 ^ ((qTabWhp c - 1) * bCharWhp n_max) := by
  refine (two_mul_doubleTabCodeBound_le_pow_bCharWhp hth).trans
    (Nat.pow_le_pow_right (by decide) ?_)
  have hq := le_qTabWhp c
  exact Nat.le_mul_of_pos_left _ (by omega)

/-! ## Section 4: Three-case Front-Yard / Backyard conservation bound -/

/-- **Three-case Front-Yard / Backyard conservation theorem**:
Suppose `M = numBucketsWhp n_max` buckets hold counts `X : Fin M → ℕ` summing to `n ≤ n_max`, and
every bucket satisfies both `M * X b ≤ n + M * deltaWhp n_max` and
`n ≤ M * X b + M * deltaWhp n_max` (`|X b - n / M| ≤ deltaWhp n_max`). Then:
1. Every bucket uses fewer than `capBackWhp n_max` backyard slots (`X b - capFrontWhp n_max <
   capBackWhp n_max`),
2. Every bucket has total load at most `capMaxWhp n_max`, and
3. Total backyard usage across all `M` buckets satisfies
   `∑ b, (X b - capFrontWhp n_max) ≤ poolSizeWhp n_max`. -/
theorem sum_sub_capFront_le_poolSize {c n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (X : Fin (numBucketsWhp n_max) → ℕ)
    (hsum : ∑ b, X b ≤ n_max)
    (hupper : ∀ b,
      numBucketsWhp n_max * X b ≤ (∑ b', X b') + numBucketsWhp n_max * deltaWhp n_max)
    (hlower : ∀ b,
      (∑ b', X b') ≤ numBucketsWhp n_max * X b + numBucketsWhp n_max * deltaWhp n_max) :
    (∀ b, X b - capFrontWhp n_max < capBackWhp n_max) ∧
    (∀ b, X b ≤ capMaxWhp n_max) ∧
    (∑ b, (X b - capFrontWhp n_max) ≤ poolSizeWhp n_max) := by
  have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
  have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
  have hle_2M := le_two_mul_numBucketsWhp_mul_scale_pow12 n_max
  have hL2 := two_le_scaleWhp n_max
  have hδ_le : deltaWhp n_max ≤ (scaleWhp n_max) ^ 11 / 4 := by
    have hmul : deltaWhp n_max * (numBucketsWhp n_max * (8 * scaleWhp n_max)) ≤
        2 * numBucketsWhp n_max * (scaleWhp n_max) ^ 12 :=
      (Nat.div_mul_le_self n_max _).trans hle_2M
    have hpow : (scaleWhp n_max) ^ 12 = scaleWhp n_max * (scaleWhp n_max) ^ 11 := by ring
    rw [hpow] at hmul
    have hpos : 0 < numBucketsWhp n_max * scaleWhp n_max :=
      Nat.mul_pos hM_pos (scaleWhp_pos n_max)
    have h8 : 8 * deltaWhp n_max * (numBucketsWhp n_max * scaleWhp n_max) ≤
        2 * (scaleWhp n_max) ^ 11 * (numBucketsWhp n_max * scaleWhp n_max) := by linarith
    have h8' := Nat.le_of_mul_le_mul_right h8 hpos
    omega
  have h4δ_le_q : 4 * deltaWhp n_max ≤ n_max / numBucketsWhp n_max := by
    have hdiv_ge : (scaleWhp n_max) ^ 12 ≤ n_max / numBucketsWhp n_max :=
      (Nat.le_div_iff_mul_le hM_pos).mpr (by linarith)
    have hL11 : 4 * ((scaleWhp n_max) ^ 11 / 4) ≤ (scaleWhp n_max) ^ 12 := by
      have h1 : (scaleWhp n_max) ^ 11 / 4 * 4 ≤ (scaleWhp n_max) ^ 11 := Nat.div_mul_le_self _ 4
      have hpow : (scaleWhp n_max) ^ 12 = (scaleWhp n_max) ^ 11 * scaleWhp n_max := by ring
      rw [hpow]
      nlinarith
    omega
  have hcf_mul_le : numBucketsWhp n_max * capFrontWhp n_max +
      4 * numBucketsWhp n_max * deltaWhp n_max ≤ n_max := by
    have hdiv : numBucketsWhp n_max * (n_max / numBucketsWhp n_max) ≤ n_max :=
      Nat.mul_div_le n_max _
    have hle_m : numBucketsWhp n_max * (4 * deltaWhp n_max) ≤
        numBucketsWhp n_max * (n_max / numBucketsWhp n_max) :=
      Nat.mul_le_mul_left _ h4δ_le_q
    have heq_m : numBucketsWhp n_max * (4 * deltaWhp n_max) =
        4 * numBucketsWhp n_max * deltaWhp n_max := by ring
    unfold capFrontWhp
    rw [Nat.mul_sub]
    omega
  have hpool_ge : 4 * numBucketsWhp n_max * deltaWhp n_max ≤ poolSizeWhp n_max := by
    unfold poolSizeWhp
    omega
  have hq_lt : n_max < numBucketsWhp n_max * (n_max / numBucketsWhp n_max + 1) := by
    have := Nat.div_add_mod n_max (numBucketsWhp n_max)
    have := Nat.mod_lt n_max hM_pos
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hub := hupper b
    have hxb : numBucketsWhp n_max * X b <
        numBucketsWhp n_max * (n_max / numBucketsWhp n_max + 1 + deltaWhp n_max) := by
      calc numBucketsWhp n_max * X b ≤ (∑ b', X b') + numBucketsWhp n_max * deltaWhp n_max := hub
        _ ≤ n_max + numBucketsWhp n_max * deltaWhp n_max := by omega
        _ < numBucketsWhp n_max * (n_max / numBucketsWhp n_max + 1) +
              numBucketsWhp n_max * deltaWhp n_max := by omega
        _ = numBucketsWhp n_max * (n_max / numBucketsWhp n_max + 1 + deltaWhp n_max) := by ring
    have hxb' : X b < n_max / numBucketsWhp n_max + 1 + deltaWhp n_max :=
      (Nat.mul_lt_mul_left hM_pos).mp hxb
    have hL11_pos : 4 ≤ (scaleWhp n_max) ^ 11 := by
      calc 4 ≤ 2 ^ 11 := by decide
        _ ≤ (scaleWhp n_max) ^ 11 := Nat.pow_le_pow_left hL2 11
    unfold capFrontWhp capBackWhp
    omega
  · intro b
    have hub := hupper b
    have hδ_pow : deltaWhp n_max ≤ (scaleWhp n_max) ^ 12 := by
      have hpow : (scaleWhp n_max) ^ 12 = (scaleWhp n_max) ^ 11 * scaleWhp n_max := by ring
      nlinarith
    have hxb : numBucketsWhp n_max * X b ≤ numBucketsWhp n_max * capMaxWhp n_max := by
      calc numBucketsWhp n_max * X b
          ≤ n_max + numBucketsWhp n_max * deltaWhp n_max := by omega
        _ ≤ 2 * numBucketsWhp n_max * (scaleWhp n_max) ^ 12 +
              numBucketsWhp n_max * (scaleWhp n_max) ^ 12 :=
            Nat.add_le_add hle_2M (Nat.mul_le_mul_left _ hδ_pow)
        _ ≤ numBucketsWhp n_max * capMaxWhp n_max := by unfold capMaxWhp; linarith
    exact Nat.le_of_mul_le_mul_left hxb hM_pos
  · by_cases hcase : (∑ b', X b') ≤
        numBucketsWhp n_max * capFrontWhp n_max + numBucketsWhp n_max * deltaWhp n_max
    · have hper : ∀ b, X b - capFrontWhp n_max ≤ 2 * deltaWhp n_max := fun b => by
        have hub := hupper b
        have h1 : numBucketsWhp n_max * X b ≤
            numBucketsWhp n_max * (capFrontWhp n_max + 2 * deltaWhp n_max) := by linarith
        have h2 : X b ≤ capFrontWhp n_max + 2 * deltaWhp n_max :=
          Nat.le_of_mul_le_mul_left h1 hM_pos
        omega
      calc ∑ b, (X b - capFrontWhp n_max)
          ≤ ∑ _b : Fin (numBucketsWhp n_max), 2 * deltaWhp n_max := sum_le_sum fun b _ => hper b
        _ = numBucketsWhp n_max * (2 * deltaWhp n_max) := by
            rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ poolSizeWhp n_max := by linarith
    · have hge_cf : ∀ b, capFrontWhp n_max ≤ X b := fun b => by
        have hlb := hlower b
        have h1 : numBucketsWhp n_max * capFrontWhp n_max ≤ numBucketsWhp n_max * X b := by omega
        exact Nat.le_of_mul_le_mul_left h1 hM_pos
      have hsum_add : ∑ b, (X b - capFrontWhp n_max) +
          numBucketsWhp n_max * capFrontWhp n_max = ∑ b', X b' := by
        have h1 : ∑ b : Fin (numBucketsWhp n_max),
            (X b - capFrontWhp n_max + capFrontWhp n_max) = ∑ b', X b' :=
          sum_congr rfl fun b _ => Nat.sub_add_cancel (hge_cf b)
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
        exact h1
      unfold poolSizeWhp
      omega
/-! ## Section 5: Memory layout and master succinct space theorem (`whpSpace_le_succinctWords`) -/

/-- Number of plain header words at `base + 0 .. base + 31`. -/
@[expose] def hdrWordsWhp : ℕ := 32

/-- Word footprint in the small-`n_max` deterministic regime (`n_max < whpThreshold c`):
32 header words plus bit-packed `Present` (`1` bit), `Keys` (`keyBits U` bits), and `Values`
(`valBits V` bits). -/
@[expose] def smallSpaceWhp (U V w n_max : ℕ) : ℕ :=
  hdrWordsWhp +
    packedWords n_max 1 w +
    packedWords n_max (keyBits U) w +
    packedWords n_max (valBits V) w

/-- Combined word footprint of the auxiliary metadata, SWAR B+-tree, and `G`/`S` `BufTrie` arrays in
the large-`n_max` regime (`whpThreshold c ≤ n_max`). -/
@[expose] def largeAuxWordsWhp (c w n_max : ℕ) : ℕ :=
  packedWords n_max (12 * ellWhp n_max + 4) w +
  packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w +
  packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w +
  packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w +
  packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w +
  packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w +
  2 * packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w +
  packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w +
  packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w +
  packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w +
  2 * packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w +
  2 * packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w +
  2 * packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w

/-- Word footprint in the large-`n_max` regime (`whpThreshold c ≤ n_max`). -/
@[expose] def largeSpaceWhp (c U V w n_max : ℕ) : ℕ :=
  hdrWordsWhp +
  BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) +
  BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) +
  packedWords n_max (quotBitsWhp U n_max) w +
  packedWords n_max (valBits V) w +
  largeAuxWordsWhp c w n_max

/-- Total `w`-bit word footprint of the WHP succinct dictionary across all `n_max`. -/
@[expose] def whpSpace (c U V w n_max : ℕ) : ℕ :=
  if n_max < whpThreshold c then
    smallSpaceWhp U V w n_max
  else
    largeSpaceWhp c U V w n_max

/-- `c`-only redundancy multiplier on `n_max * logLogFactor n_max` (`Θ(c^6)` due to `bMinWhp c`). -/
@[expose] def whpSpaceFactor (c : ℕ) : ℕ :=
  bMinWhp c + 120000

/-- Universal additive `w`-bit word slack (`160` words, independent of `c, U, V, w, n_max`). -/
@[expose] def whpSpaceConst : ℕ := 160

/-- Worst-case Word-RAM execution instruction bound for each dynamic dictionary operation
(`query`, `insert`, `delete`) on the fast path (`O_c(1)` independent of `n_max, U, V, w`). -/
@[expose] def whpTimeBound (c : ℕ) : ℕ :=
  4 * whpThreshold c + 500000 * (cEff c + 1)

/-- Linear initialization instruction factor (`O_c(1)` independent of `n_max, U, V, w`). -/
@[expose] def whpInitFactor (c : ℕ) : ℕ :=
  4 * whpThreshold c + 100000

/-- Universal bit accounting for `n_max` quotients of `quotBitsWhp U n_max` bits and `n_max` values
of `valBits V` bits across all `n_max ≤ U`. -/
theorem quotient_val_whp_bits_le_optBits {U V n_max : ℕ} (hnU : n_max ≤ U) :
    n_max * quotBitsWhp U n_max + n_max * valBits V ≤
      Dynamic.optBits U V n_max + 14 * n_max * ellWhp n_max := by
  rcases Nat.eq_zero_or_pos n_max with rfl | hn
  · simp
  · have hU : 1 ≤ U := hn.trans_le hnU
    have hpow_key : 2 ^ keyBits U ≤ 2 * U := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
    have hpow_n : n_max ≤ 2 ^ (bWhp n_max + 12 * ellWhp n_max + 1) := by
      have hlt : n_max < 2 ^ (Nat.log 2 n_max + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n_max
      exact hlt.le.trans (Nat.pow_le_pow_right (by decide) (by unfold bWhp; omega))
    have hchoose : U.choose n_max ≤ 2 ^ Nat.clog 2 (U.choose n_max) :=
      Nat.le_pow_clog (by decide) (U.choose n_max)
    have hmain :
        2 ^ (n_max * keyBits U) ≤
          2 ^ (n_max + n_max * (bWhp n_max + 12 * ellWhp n_max + 1) +
            Nat.clog 2 (U.choose n_max)) := by
      calc 2 ^ (n_max * keyBits U)
          = (2 ^ keyBits U) ^ n_max := by rw [Nat.mul_comm, Nat.pow_mul]
        _ ≤ (2 * U) ^ n_max := Nat.pow_le_pow_left hpow_key n_max
        _ = 2 ^ n_max * U ^ n_max := Nat.mul_pow 2 U n_max
        _ ≤ 2 ^ n_max * (n_max ^ n_max * U.choose n_max) :=
            Nat.mul_le_mul_left _ (pow_le_pow_mul_choose hnU)
        _ ≤ 2 ^ n_max * ((2 ^ (bWhp n_max + 12 * ellWhp n_max + 1)) ^ n_max *
              2 ^ Nat.clog 2 (U.choose n_max)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hpow_n n_max) hchoose)
        _ = 2 ^ (n_max + n_max * (bWhp n_max + 12 * ellWhp n_max + 1) +
              Nat.clog 2 (U.choose n_max)) := by
            rw [← Nat.pow_mul, Nat.mul_comm (bWhp n_max + 12 * ellWhp n_max + 1) n_max,
              ← Nat.pow_add, ← Nat.pow_add, ← Nat.add_assoc]
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hmain
    have hsplit : keyBits U = quotBitsWhp U n_max + bWhp n_max :=
      (quotBitsWhp_add_bWhp hnU).symm
    have hll : 1 ≤ ellWhp n_max := one_le_ellWhp n_max
    rw [hsplit, Nat.mul_add] at hexp
    unfold Dynamic.optBits valBits
    nlinarith

/-- Small-`n_max` bit accounting (`n_max < whpThreshold c` and `n_max ≤ U`). -/
theorem small_bits_le_optBits {c U V n_max : ℕ} (hsmall : n_max < whpThreshold c)
    (hnU : n_max ≤ U) :
    n_max * 1 + n_max * keyBits U + n_max * valBits V ≤
      Dynamic.optBits U V n_max + (bMinWhp c + 2) * n_max * ellWhp n_max := by
  rcases Nat.eq_zero_or_pos n_max with rfl | hn
  · simp
  · have hpow_key : 2 ^ keyBits U ≤ 2 * U := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
    have hpow_n : n_max ≤ 2 ^ bMinWhp c := by
      unfold whpThreshold at hsmall
      exact hsmall.le
    have hchoose : U.choose n_max ≤ 2 ^ Nat.clog 2 (U.choose n_max) :=
      Nat.le_pow_clog (by decide) (U.choose n_max)
    have hmain :
        2 ^ (n_max * keyBits U) ≤
          2 ^ (n_max + n_max * bMinWhp c + Nat.clog 2 (U.choose n_max)) := by
      calc 2 ^ (n_max * keyBits U)
          = (2 ^ keyBits U) ^ n_max := by rw [Nat.mul_comm, Nat.pow_mul]
        _ ≤ (2 * U) ^ n_max := Nat.pow_le_pow_left hpow_key n_max
        _ = 2 ^ n_max * U ^ n_max := Nat.mul_pow 2 U n_max
        _ ≤ 2 ^ n_max * (n_max ^ n_max * U.choose n_max) :=
            Nat.mul_le_mul_left _ (pow_le_pow_mul_choose hnU)
        _ ≤ 2 ^ n_max * ((2 ^ bMinWhp c) ^ n_max * 2 ^ Nat.clog 2 (U.choose n_max)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hpow_n n_max) hchoose)
        _ = 2 ^ (n_max + n_max * bMinWhp c + Nat.clog 2 (U.choose n_max)) := by
            rw [← Nat.pow_mul, Nat.mul_comm (bMinWhp c) n_max, ← Nat.pow_add, ← Nat.pow_add,
              ← Nat.add_assoc]
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hmain
    have hll : 1 ≤ ellWhp n_max := one_le_ellWhp n_max
    have hmul1 : (bMinWhp c + 2) * n_max ≤ (bMinWhp c + 2) * n_max * ellWhp n_max :=
      Nat.le_mul_of_pos_right _ hll
    have hdist : (bMinWhp c + 2) * n_max = n_max * bMinWhp c + 2 * n_max := by ring
    unfold Dynamic.optBits valBits
    omega

/-- Upper bound on `globalPtrBits n_max` when `whpThreshold c ≤ n_max`:
`globalPtrBits n_max ≤ 2 * scaleWhp n_max`. -/
theorem globalPtrBits_le_two_mul_scaleWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    globalPtrBits n_max ≤ 2 * scaleWhp n_max := by
  have hb : 0 < bucketBits n_max := by
    have h := mul_ell_le_log hth
    have h1 := one_le_ellWhp n_max
    unfold bucketBits ellWhp at *
    omega
  exact globalPtrBits_le_two_mul_slabScale hb

/-- Upper bound on `poolSizeWhp n_max` when `whpThreshold c ≤ n_max`:
`poolSizeWhp n_max ≤ n_max / scaleWhp n_max`. -/
theorem poolSizeWhp_le_div_scale {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    poolSizeWhp n_max ≤ n_max / scaleWhp n_max := by
  have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
  have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
  have hL2 := two_le_scaleWhp n_max
  have h4δ_le : 4 * numBucketsWhp n_max * deltaWhp n_max ≤ n_max / (2 * scaleWhp n_max) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc 4 * numBucketsWhp n_max * deltaWhp n_max * (2 * scaleWhp n_max)
        = deltaWhp n_max * (numBucketsWhp n_max * (8 * scaleWhp n_max)) := by ring
      _ ≤ n_max := Nat.div_mul_le_self _ _
  have hmod_lt : n_max - numBucketsWhp n_max * (n_max / numBucketsWhp n_max) <
      numBucketsWhp n_max := by
    have h1 := Nat.div_add_mod n_max (numBucketsWhp n_max)
    have h2 := Nat.mod_lt n_max hM_pos
    omega
  have hM_le : numBucketsWhp n_max ≤ n_max / (2 * scaleWhp n_max) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have hpow : 2 * scaleWhp n_max ≤ (scaleWhp n_max) ^ 12 := by
      have hp : (scaleWhp n_max) ^ 12 = (scaleWhp n_max) ^ 11 * scaleWhp n_max := by ring
      have h11 : 2 ≤ (scaleWhp n_max) ^ 11 := by
        calc 2 ≤ 2 ^ 11 := by decide
          _ ≤ (scaleWhp n_max) ^ 11 := Nat.pow_le_pow_left hL2 11
      nlinarith
    exact (Nat.mul_le_mul_left _ hpow).trans hM_L12
  have h2div : 2 * (n_max / (2 * scaleWhp n_max)) ≤ n_max / scaleWhp n_max := by
    rw [Nat.le_div_iff_mul_le (scaleWhp_pos n_max)]
    have := Nat.div_mul_le_self n_max (2 * scaleWhp n_max)
    linarith
  have h4δ_div : 4 * deltaWhp n_max ≤ n_max / numBucketsWhp n_max := by
    have hle := Nat.div_mul_le_self n_max (numBucketsWhp n_max * (8 * scaleWhp n_max))
    rw [Nat.le_div_iff_mul_le hM_pos]
    have h1 : 4 * deltaWhp n_max * numBucketsWhp n_max ≤
        deltaWhp n_max * (numBucketsWhp n_max * (8 * scaleWhp n_max)) := by
      have heq : 4 * deltaWhp n_max * numBucketsWhp n_max * (2 * scaleWhp n_max) =
          deltaWhp n_max * (numBucketsWhp n_max * (8 * scaleWhp n_max)) := by ring
      rw [← heq]
      exact Nat.le_mul_of_pos_right _ (by omega)
    exact h1.trans hle
  have hpool_eq : poolSizeWhp n_max =
      (n_max - numBucketsWhp n_max * (n_max / numBucketsWhp n_max)) +
        4 * numBucketsWhp n_max * deltaWhp n_max := by
    unfold poolSizeWhp capFrontWhp
    rw [Nat.mul_sub]
    have hle1 : numBucketsWhp n_max * (4 * deltaWhp n_max) ≤
        numBucketsWhp n_max * (n_max / numBucketsWhp n_max) :=
      Nat.mul_le_mul_left _ h4δ_div
    have hle2 : numBucketsWhp n_max * (n_max / numBucketsWhp n_max) ≤ n_max :=
      Nat.mul_div_le n_max _
    have hm : numBucketsWhp n_max * (4 * deltaWhp n_max) =
        4 * numBucketsWhp n_max * deltaWhp n_max := by ring
    omega
  omega
/-- Ceiling-division subadditivity for two word-bounded blocks. -/
theorem ceil_div_add_le (A c₁ B c₂ w : ℕ) :
    ((A + w - 1) / w + c₁) + ((B + w - 1) / w + c₂) ≤
      (A + B + w - 1) / w + (c₁ + c₂ + 1) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have h1 := Nat.div_add_mod (A + w - 1) w
    have h2 := Nat.div_add_mod (B + w - 1) w
    have h3 := Nat.div_add_mod (A + B + w - 1) w
    have hm3 : (A + B + w - 1) % w < w := Nat.mod_lt _ hw
    have hlt : w * ((A + w - 1) / w + (B + w - 1) / w) <
        w * ((A + B + w - 1) / w + 2) := by
      rw [Nat.left_distrib, Nat.left_distrib, Nat.mul_two]
      omega
    have hlt' := (Nat.mul_lt_mul_left hw).mp hlt
    omega

/-- When `whpThreshold c ≤ n_max`, `2 ^ (3 * bCharWhp n_max) ≤ n_max`. -/
theorem pow_three_mul_bCharWhp_le {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    2 ^ (3 * bCharWhp n_max) ≤ n_max := by
  have hn0 : n_max ≠ 0 := by have := whpThreshold_pos c; omega
  have hle : 3 * bCharWhp n_max ≤ Nat.log 2 n_max := by
    unfold bCharWhp
    omega
  exact (Nat.pow_le_pow_right (by decide) hle).trans (Nat.pow_log_le_self 2 hn0)

private theorem add_six_le_two_pow : ∀ {k : ℕ}, 4 ≤ k → k + 6 ≤ 2 ^ k
  | 4, _ => by decide
  | k + 5, _ => by
    have ih := add_six_le_two_pow (k := k + 4) (by omega)
    rw [Nat.pow_succ]
    omega

/-- When `whpThreshold c ≤ n_max`, all `2 ^ bCharWhp n_max`-scaled hash and `BufTrie` bit counts
are individually bounded by `n_max`. -/
theorem sublinear_table_bits_le {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    let bc := bCharWhp n_max
    BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) bc * bc ≤ n_max ∧
    BitPackedDoubleTabulation.botEntries (dTabWhp c) bc * bWhp n_max ≤ n_max ∧
    BitPackedDoubleTabulation.botEntries (dTabWhp c) bc * fpBitsWhp n_max ≤ n_max ∧
    trieChildEntriesWhp c n_max * globalPtrBits n_max ≤ n_max ∧
    (6 * maxTrieNodesWhp c n_max) * globalPtrBits n_max ≤ n_max ∧
    (6 * qEpochWhp n_max + 6) * globalPtrBits n_max ≤ n_max := by
  intro bc
  have hmain := codeExpWhp_mul_ell_le_bCharWhp hth
  have hell := one_le_ellWhp n_max
  have hpow3 := pow_three_mul_bCharWhp_le hth
  have hbc_ge : 320 ≤ bc := by
    have := mul_ell_le_bCharWhp hth
    omega
  have hc1_d_lt : (cTabWhp c + 1) * dTabWhp c ≤ 2 ^ bc := by
    have hexp : 4 * (cTabWhp c + 1) ≤ bc := by
      have hq := le_qTabWhp c
      have hc := le_cTabWhp c
      have h1a : 4 * (cTabWhp c + 1) ≤ (cTabWhp c + 1) ^ 2 := by nlinarith
      have h2a : (cTabWhp c + 1) ^ 2 ≤ (cTabWhp c + 1) ^ 2 * qTabWhp c :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h3a : (cTabWhp c + 1) ^ 2 * qTabWhp c ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
        rw [mul_assoc 16]
        exact Nat.le_mul_of_pos_left _ (by decide)
      have hce : 4 * (cTabWhp c + 1) ≤ codeExpWhp c := by
        unfold codeExpWhp
        omega
      exact (hce.trans (Nat.le_mul_of_pos_right _ hell)).trans hmain
    have hlt1 : cTabWhp c + 1 ≤ 2 ^ (cTabWhp c + 1) := (@Nat.lt_two_pow_self _).le
    have hlt2 : dTabWhp c ≤ 2 ^ (3 * (cTabWhp c + 1)) := by
      have hqc : qTabWhp c ≤ cTabWhp c + 1 := by
        unfold qTabWhp cTabWhp
        have := one_le_cEff c
        omega
      have ha : 2 * qTabWhp c ≤ 2 ^ (2 * (cTabWhp c + 1)) := by
        have := (@Nat.lt_two_pow_self (2 * (cTabWhp c + 1))).le
        omega
      calc dTabWhp c = (2 * qTabWhp c) * (cTabWhp c + 1) := rfl
        _ ≤ 2 ^ (2 * (cTabWhp c + 1)) * 2 ^ (cTabWhp c + 1) := Nat.mul_le_mul ha hlt1
        _ = 2 ^ (3 * (cTabWhp c + 1)) := by rw [← Nat.pow_add]; ring_nf
    calc (cTabWhp c + 1) * dTabWhp c
        ≤ 2 ^ (cTabWhp c + 1) * 2 ^ (3 * (cTabWhp c + 1)) := Nat.mul_le_mul hlt1 hlt2
      _ = 2 ^ (4 * (cTabWhp c + 1)) := by rw [← Nat.pow_add]; ring_nf
      _ ≤ 2 ^ bc := Nat.pow_le_pow_right (by decide) hexp
  have hd_lt : dTabWhp c ≤ 2 ^ bc :=
    (Nat.le_mul_of_pos_left _ (by omega)).trans hc1_d_lt
  have hlog_lt_pow : Nat.log 2 n_max ≤ 2 ^ bc := by
    have hlt : 4 * (bc + 1) ≤ 2 ^ bc := by
      have h1 : bc + 4 ≤ 2 ^ (bc - 2) := by
        have h6 := add_six_le_two_pow (k := bc - 2) (by omega)
        omega
      calc 4 * (bc + 1) ≤ 4 * (bc + 4) := by omega
        _ ≤ 4 * 2 ^ (bc - 2) := Nat.mul_le_mul_left 4 h1
        _ = 2 ^ 2 * 2 ^ (bc - 2) := rfl
        _ = 2 ^ bc := by rw [← Nat.pow_add]; congr 1; omega
    have hdiv : Nat.log 2 n_max ≤ 4 * (bc + 1) := by
      have hdef : bc = Nat.log 2 n_max / 4 := rfl
      omega
    exact hdiv.trans hlt
  have hbc_lt_pow : bc ≤ 2 ^ bc := (@Nat.lt_two_pow_self bc).le
  have hbWhp_lt_pow : bWhp n_max ≤ 2 ^ bc := (Nat.sub_le _ _).trans hlog_lt_pow
  have hfp_lt_pow : fpBitsWhp n_max ≤ 2 ^ bc := by
    have : fpBitsWhp n_max ≤ Nat.log 2 n_max := by
      have := mul_ell_le_log hth
      unfold fpBitsWhp
      omega
    exact this.trans hlog_lt_pow
  have hptr_lt_pow : globalPtrBits n_max ≤ 2 ^ bc := by
    have hptr := globalPtrBits_le_two_mul_scaleWhp hth
    have hsc : 2 * scaleWhp n_max ≤ (scaleWhp n_max) ^ 24 := by
      have h2 := two_le_scaleWhp n_max
      calc 2 * scaleWhp n_max ≤ scaleWhp n_max * scaleWhp n_max := Nat.mul_le_mul_right _ h2
        _ = (scaleWhp n_max) ^ 2 := by ring
        _ ≤ (scaleWhp n_max) ^ 24 := Nat.pow_le_pow_right (by omega) (by decide)
    exact (hptr.trans hsc).trans (scaleWhp_pow24_le_pow_bChar hth)
  have hpow3_eq : 2 ^ bc * 2 ^ bc * 2 ^ bc = 2 ^ (3 * bc) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    ring
  have hmaxTrie_lt : 6 * maxTrieNodesWhp c n_max ≤ 2 ^ bc := by
    have hexp : cTabWhp c + 18 * ellWhp n_max + 8 ≤ bc := by
      have hq := le_qTabWhp c
      have hc := le_cTabWhp c
      have h1a : cTabWhp c + 1 ≤ (cTabWhp c + 1) ^ 2 := by nlinarith
      have h2a : (cTabWhp c + 1) ^ 2 ≤ (cTabWhp c + 1) ^ 2 * qTabWhp c :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h3a : (cTabWhp c + 1) ^ 2 * qTabWhp c ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
        rw [mul_assoc 16]
        exact Nat.le_mul_of_pos_left _ (by decide)
      have hce : cTabWhp c + 26 ≤ codeExpWhp c := by
        unfold codeExpWhp
        omega
      calc cTabWhp c + 18 * ellWhp n_max + 8
          ≤ cTabWhp c * ellWhp n_max + 18 * ellWhp n_max + 8 * ellWhp n_max := by
            have := Nat.le_mul_of_pos_right (cTabWhp c) hell
            omega
        _ = (cTabWhp c + 26) * ellWhp n_max := by ring
        _ ≤ codeExpWhp c * ellWhp n_max := Nat.mul_le_mul_right _ hce
        _ ≤ bc := hmain
    have hc_pow : 12 * (cTabWhp c + 1) ≤ 2 ^ (cTabWhp c + 6) := by
      have h1 : cTabWhp c + 1 ≤ 2 ^ (cTabWhp c + 1) := (@Nat.lt_two_pow_self _).le
      calc 12 * (cTabWhp c + 1) ≤ 2 ^ 5 * 2 ^ (cTabWhp c + 1) :=
            Nat.mul_le_mul (by decide) h1
        _ = 2 ^ (cTabWhp c + 6) := by rw [← Nat.pow_add]; ring_nf
    have hq_eq : qEpochWhp n_max = 2 ^ (18 * ellWhp n_max) := by
      unfold qEpochWhp scaleWhp slabScale ellWhp
      rw [← Nat.pow_mul, Nat.mul_comm]
    have hq_pos : 1 ≤ qEpochWhp n_max := by rw [hq_eq]; exact Nat.one_le_two_pow
    calc 6 * maxTrieNodesWhp c n_max
        = 6 * (cTabWhp c + 1) * qEpochWhp n_max + 12 := by unfold maxTrieNodesWhp; ring
      _ ≤ 12 * (cTabWhp c + 1) * qEpochWhp n_max := by
          have := le_cTabWhp c
          nlinarith
      _ ≤ 2 ^ (cTabWhp c + 6) * 2 ^ (18 * ellWhp n_max) := by
          rw [hq_eq]; exact Nat.mul_le_mul_right _ hc_pow
      _ = 2 ^ (cTabWhp c + 6 + 18 * ellWhp n_max) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ bc := Nat.pow_le_pow_right (by decide) (by omega)
  have hmax1 : maxTrieNodesWhp c n_max ≤ 2 ^ bc := by omega
  have hq6_lt : 6 * qEpochWhp n_max + 6 ≤ 2 ^ bc := by
    have : 6 * qEpochWhp n_max + 6 ≤ 6 * maxTrieNodesWhp c n_max := by
      unfold maxTrieNodesWhp
      have := le_cTabWhp c
      nlinarith
    exact this.trans hmaxTrie_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc ((cTabWhp c + 1) * dTabWhp c * 2 ^ bc) * bc
        ≤ (2 ^ bc * 2 ^ bc) * 2 ^ bc :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hc1_d_lt) hbc_lt_pow
      _ = 2 ^ (3 * bc) := hpow3_eq
      _ ≤ n_max := hpow3
  · calc (dTabWhp c * 2 ^ bc) * bWhp n_max
        ≤ (2 ^ bc * 2 ^ bc) * 2 ^ bc :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hd_lt) hbWhp_lt_pow
      _ = 2 ^ (3 * bc) := hpow3_eq
      _ ≤ n_max := hpow3
  · calc (dTabWhp c * 2 ^ bc) * fpBitsWhp n_max
        ≤ (2 ^ bc * 2 ^ bc) * 2 ^ bc :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hd_lt) hfp_lt_pow
      _ = 2 ^ (3 * bc) := hpow3_eq
      _ ≤ n_max := hpow3
  · calc (maxTrieNodesWhp c n_max * 2 ^ bc) * globalPtrBits n_max
        ≤ (2 ^ bc * 2 ^ bc) * 2 ^ bc :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hmax1) hptr_lt_pow
      _ = 2 ^ (3 * bc) := hpow3_eq
      _ ≤ n_max := hpow3
  · calc (6 * maxTrieNodesWhp c n_max) * globalPtrBits n_max
        ≤ 2 ^ bc * 2 ^ bc := Nat.mul_le_mul hmaxTrie_lt hptr_lt_pow
      _ ≤ 2 ^ bc * 2 ^ bc * 2 ^ bc := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos bc)
      _ = 2 ^ (3 * bc) := hpow3_eq
      _ ≤ n_max := hpow3
  · calc (6 * qEpochWhp n_max + 6) * globalPtrBits n_max
        ≤ 2 ^ bc * 2 ^ bc := Nat.mul_le_mul hq6_lt hptr_lt_pow
      _ ≤ 2 ^ bc * 2 ^ bc * 2 ^ bc := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos bc)
      _ = 2 ^ (3 * bc) := hpow3_eq
      _ ≤ n_max := hpow3

/-- **Master succinct word-space bound** valid across all `c, U, V, w, n_max` with `n_max ≤ U`:
`whpSpace c U V w n_max ≤ Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max`. -/
theorem whpSpace_le_succinctWords {c U V w n_max : ℕ} (hnU : n_max ≤ U) :
    whpSpace c U V w n_max ≤
      Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max := by
  unfold whpSpace
  split_ifs with hsmall
  · unfold smallSpaceWhp hdrWordsWhp
    have h12 := packedWords_add_le n_max 1 n_max (keyBits U) w
    have h123 := div_add_packedWords_le (n_max * 1 + n_max * keyBits U) 5 n_max (valBits V) w
    have hbits := small_bits_le_optBits (V := V) hsmall hnU
    have hfac : bMinWhp c + 2 ≤ whpSpaceFactor c := by unfold whpSpaceFactor; omega
    have hnum : n_max * 1 + n_max * keyBits U + n_max * valBits V ≤
        Dynamic.optBits U V n_max + whpSpaceFactor c * n_max * Dynamic.logLogFactor n_max := by
      calc n_max * 1 + n_max * keyBits U + n_max * valBits V
          ≤ Dynamic.optBits U V n_max + (bMinWhp c + 2) * n_max * ellWhp n_max := hbits
        _ ≤ Dynamic.optBits U V n_max +
              whpSpaceFactor c * n_max * Dynamic.logLogFactor n_max := by
            unfold ellWhp
            gcongr
    have hdiv : (n_max * 1 + n_max * keyBits U + n_max * valBits V + w - 1) / w ≤
        (Dynamic.optBits U V n_max + whpSpaceFactor c * n_max * Dynamic.logLogFactor n_max +
          w - 1) / w :=
      Nat.div_le_div_right (by omega)
    unfold Dynamic.succinctWords whpSpaceConst
    omega
  · have hth : whpThreshold c ≤ n_max := Nat.le_of_not_lt hsmall
    obtain ⟨htb1, htb2, htb3, htc, htm, htl⟩ := sublinear_table_bits_le hth
    have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
    have hptr := globalPtrBits_le_two_mul_scaleWhp hth
    have hpool := poolSizeWhp_le_div_scale hth
    have hell := one_le_ellWhp n_max
    have hL2 := two_le_scaleWhp n_max
    have h8t := eight_le_tMinWhp hth
    set ell := ellWhp n_max
    set L := scaleWhp n_max
    set M := numBucketsWhp n_max
    have hM_pos : 0 < M := by unfold M numBucketsWhp; positivity
    have hb_front : n_max * (12 * ell + 4) ≤ 16 * (n_max * ell) := by
      have : n_max * 4 ≤ 4 * (n_max * ell) := by
        have := Nat.le_mul_of_pos_right n_max hell
        omega
      linarith
    have hb_lstate : (M * totalLocalCoordsWhp n_max) * 2 ≤ 4 * (n_max * ell) := by
      have hcf : M * capFrontWhp n_max ≤ n_max :=
        (Nat.mul_le_mul_left M (Nat.sub_le _ _)).trans (Nat.mul_div_le n_max M)
      have hcb : M * capBackWhp n_max ≤ n_max := by
        calc M * (2 * L ^ 11) ≤ M * (L * L ^ 11) :=
              Nat.mul_le_mul_left M (Nat.mul_le_mul_right _ hL2)
          _ = M * L ^ 12 := by ring
          _ ≤ n_max := hM_L12
      have hne : n_max ≤ n_max * ell := Nat.le_mul_of_pos_right _ hell
      calc (M * (capFrontWhp n_max + capBackWhp n_max)) * 2
          = 2 * (M * capFrontWhp n_max + M * capBackWhp n_max) := by ring
        _ ≤ 4 * n_max := by omega
        _ ≤ 4 * (n_max * ell) := Nat.mul_le_mul_left 4 hne
    have hML_le : M * L ≤ n_max := by
      have hL11 : 1 ≤ L ^ 11 := Nat.one_le_pow 11 L (by omega)
      calc M * L ≤ M * L * L ^ 11 := Nat.le_mul_of_pos_right _ hL11
        _ = M * L ^ 12 := by ring
        _ ≤ n_max := hM_L12
    have hne : n_max ≤ n_max * ell := Nat.le_mul_of_pos_right _ hell
    have hb_bmeta : (16 * M) * globalPtrBits n_max ≤ 32 * (n_max * ell) := by
      calc (16 * M) * globalPtrBits n_max ≤ (16 * M) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 32 * (M * L) := by ring
        _ ≤ 32 * n_max := Nat.mul_le_mul_left 32 hML_le
        _ ≤ 32 * (n_max * ell) := Nat.mul_le_mul_left 32 hne
    have hb_m1start : (M + 1) * globalPtrBits n_max ≤ 4 * (n_max * ell) := by
      have hM1 : M + 1 ≤ 2 * M := by omega
      calc (M + 1) * globalPtrBits n_max ≤ (2 * M) * (2 * L) := Nat.mul_le_mul hM1 hptr
        _ = 4 * (M * L) := by ring
        _ ≤ 4 * n_max := Nat.mul_le_mul_left 4 hML_le
        _ ≤ 4 * (n_max * ell) := Nat.mul_le_mul_left 4 hne
    have hb_bptr : (M * capBackWhp n_max) * globalPtrBits n_max ≤ 4 * (n_max * ell) := by
      calc (M * (2 * L ^ 11)) * globalPtrBits n_max
          ≤ (M * (2 * L ^ 11)) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 4 * (M * L ^ 12) := by ring
        _ ≤ 4 * n_max := Nat.mul_le_mul_left 4 hM_L12
        _ ≤ 4 * (n_max * ell) := Nat.mul_le_mul_left 4 hne
    have hb_bfree : (M * capBackWhp n_max) * (12 * ell + 4) ≤ 32 * (n_max * ell) := by
      have hML11 : M * L ^ 11 ≤ n_max := by
        calc M * L ^ 11 ≤ M * L ^ 11 * L := Nat.le_mul_of_pos_right _ (by omega)
          _ = M * L ^ 12 := by ring
          _ ≤ n_max := hM_L12
      calc (M * (2 * L ^ 11)) * (12 * ell + 4)
          ≤ (2 * n_max) * (16 * ell) := Nat.mul_le_mul (by linarith) (by omega)
        _ = 32 * (n_max * ell) := by ring
    have hb_pool : poolSizeWhp n_max * globalPtrBits n_max ≤ 2 * (n_max * ell) := by
      calc poolSizeWhp n_max * globalPtrBits n_max
          ≤ (n_max / L) * (2 * L) := Nat.mul_le_mul hpool hptr
        _ = 2 * (n_max / L * L) := by ring
        _ ≤ 2 * n_max := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self n_max L)
        _ ≤ 2 * (n_max * ell) := Nat.mul_le_mul_left 2 hne
    have ht_le_L12 : tMinWhp n_max ≤ L ^ 12 := by
      have ht_log : tMinWhp n_max ≤ Nat.log 2 n_max := by
        have h := mul_ell_le_log hth
        unfold tMinWhp
        exact max_le (by omega) (Nat.div_le_self _ _)
      have hn4 : 4 ≤ n_max := by
        have hm := bMinWhp_le_log hth
        have hbm := le_bMinWhp c
        have h4 : 2 ^ 2 ≤ whpThreshold c := by
          unfold whpThreshold
          exact Nat.pow_le_pow_right (by decide) (by omega)
        exact (by decide : 4 ≤ 2 ^ 2).trans (h4.trans hth)
      have hlog_pow : Nat.log 2 n_max ≤ L := by
        have h1 : Nat.log 2 n_max ≤ Nat.clog 2 (max n_max 4) :=
          (Nat.log_mono_right (le_max_left n_max 4)).trans (Nat.log_le_clog 2 _)
        exact h1.trans (Nat.le_pow_clog Nat.one_lt_two _)
      have hL_pow : L ≤ L ^ 12 := by
        calc L = L ^ 1 := (pow_one L).symm
          _ ≤ L ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
      exact (ht_log.trans hlog_pow).trans hL_pow
    have hnslice_mul : nSliceWhp n_max * tMinWhp n_max ≤ 128 * L ^ 12 := by
      have h1 : 32 * L ^ 12 / (tMinWhp n_max - 1) * (tMinWhp n_max - 1) ≤ 32 * L ^ 12 :=
        Nat.div_mul_le_self _ _
      have h2 : tMinWhp n_max ≤ 2 * (tMinWhp n_max - 1) := by omega
      have h3 : 32 * L ^ 12 / (tMinWhp n_max - 1) * tMinWhp n_max ≤ 64 * L ^ 12 := by
        calc 32 * L ^ 12 / (tMinWhp n_max - 1) * tMinWhp n_max
            ≤ 32 * L ^ 12 / (tMinWhp n_max - 1) * (2 * (tMinWhp n_max - 1)) :=
              Nat.mul_le_mul_left _ h2
          _ = 2 * (32 * L ^ 12 / (tMinWhp n_max - 1) * (tMinWhp n_max - 1)) := by ring
          _ ≤ 64 * L ^ 12 := by linarith
      unfold nSliceWhp
      rw [Nat.add_mul]
      linarith
    have htot_t : totalBTreeNodesWhp n_max * tMinWhp n_max ≤ 384 * n_max := by
      calc (3 * M * nSliceWhp n_max) * tMinWhp n_max
          = (3 * M) * (nSliceWhp n_max * tMinWhp n_max) := by ring
        _ ≤ (3 * M) * (128 * L ^ 12) := Nat.mul_le_mul_left (3 * M) hnslice_mul
        _ = 384 * (M * L ^ 12) := by ring
        _ ≤ 384 * n_max := Nat.mul_le_mul_left 384 hM_L12
    have hb_bt_meta : totalBTreeNodesWhp n_max * nodeMetaBitsWhp n_max ≤ 384 * (n_max * ell) := by
      have hm_le : nodeMetaBitsWhp n_max ≤ tMinWhp n_max * ell := by
        have h4 : 4 ≤ 4 * ell := Nat.le_mul_of_pos_right 4 hell
        have h5 : 5 * ell ≤ tMinWhp n_max * ell := Nat.mul_le_mul_right ell (by omega)
        unfold nodeMetaBitsWhp
        dsimp only [ell] at h4 h5 ⊢
        omega
      calc totalBTreeNodesWhp n_max * nodeMetaBitsWhp n_max
          ≤ totalBTreeNodesWhp n_max * (tMinWhp n_max * ell) := Nat.mul_le_mul_left _ hm_le
        _ = (totalBTreeNodesWhp n_max * tMinWhp n_max) * ell := by ring
        _ ≤ (384 * n_max) * ell := Nat.mul_le_mul_right ell htot_t
        _ = 384 * (n_max * ell) := by ring
    have hb_bt_keys :
        totalBTreeNodesWhp n_max * keysWordBitsWhp n_max ≤ 29184 * (n_max * ell) := by
      have hk_le : keysWordBitsWhp n_max ≤ 76 * (tMinWhp n_max * ell) := by
        have hk1 : keyLaneBitsWhp n_max ≤ 38 * ell := by
          unfold keyLaneBitsWhp fpBitsWhp
          dsimp only [ell] at hell ⊢
          omega
        calc 2 * tMinWhp n_max * keyLaneBitsWhp n_max
            ≤ 2 * tMinWhp n_max * (38 * ell) := Nat.mul_le_mul_left _ hk1
          _ = 76 * (tMinWhp n_max * ell) := by ring
      calc totalBTreeNodesWhp n_max * keysWordBitsWhp n_max
          ≤ totalBTreeNodesWhp n_max * (76 * (tMinWhp n_max * ell)) := Nat.mul_le_mul_left _ hk_le
        _ = 76 * (totalBTreeNodesWhp n_max * tMinWhp n_max) * ell := by ring
        _ ≤ 76 * (384 * n_max) * ell := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 76 htot_t)
        _ = 29184 * (n_max * ell) := by ring
    have hb_bt_vals :
        totalBTreeNodesWhp n_max * valsWordBitsWhp n_max ≤ 15360 * (n_max * ell) := by
      have hv_le : valsWordBitsWhp n_max ≤ 40 * (tMinWhp n_max * ell) := by
        have hv1 : valLaneBitsWhp n_max ≤ 20 * ell := by
          unfold valLaneBitsWhp
          dsimp only [ell] at hell ⊢
          omega
        calc 2 * tMinWhp n_max * valLaneBitsWhp n_max
            ≤ 2 * tMinWhp n_max * (20 * ell) := Nat.mul_le_mul_left _ hv1
          _ = 40 * (tMinWhp n_max * ell) := by ring
      calc totalBTreeNodesWhp n_max * valsWordBitsWhp n_max
          ≤ totalBTreeNodesWhp n_max * (40 * (tMinWhp n_max * ell)) := Nat.mul_le_mul_left _ hv_le
        _ = 40 * (totalBTreeNodesWhp n_max * tMinWhp n_max) * ell := by ring
        _ ≤ 40 * (384 * n_max) * ell := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 40 htot_t)
        _ = 15360 * (n_max * ell) := by ring
    have hsp_bkt := BitPackedDoubleTabulation.space_le w (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (bWhp n_max)
    have hsp_fp := BitPackedDoubleTabulation.space_le w (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (fpBitsWhp n_max)
    have hqv := quotient_val_whp_bits_le_optBits (V := V) hnU
    let a1 := n_max * (12 * ell + 4)
    let a2 := a1 + (M * totalLocalCoordsWhp n_max) * 2
    let a3 := a2 + (16 * M) * globalPtrBits n_max
    let a4 := a3 + (M + 1) * globalPtrBits n_max
    let a5 := a4 + (M * capBackWhp n_max) * globalPtrBits n_max
    let a6 := a5 + (M * capBackWhp n_max) * (12 * ell + 4)
    let a7 := a6 + (2 * poolSizeWhp n_max) * globalPtrBits n_max
    let a8 := a7 + totalBTreeNodesWhp n_max * nodeMetaBitsWhp n_max
    let a9 := a8 + totalBTreeNodesWhp n_max * keysWordBitsWhp n_max
    let a10 := a9 + totalBTreeNodesWhp n_max * valsWordBitsWhp n_max
    let a11 := a10 + (2 * trieChildEntriesWhp c n_max) * globalPtrBits n_max
    let a12 := a11 + (2 * (6 * maxTrieNodesWhp c n_max)) * globalPtrBits n_max
    let B_aux := a12 + (2 * (6 * qEpochWhp n_max + 6)) * globalPtrBits n_max
    have haux_words : largeAuxWordsWhp c w n_max ≤ (B_aux + w - 1) / w + 50 := by
      unfold largeAuxWordsWhp
      have p1 := packedWords_add_le n_max (12 * ell + 4) (M * totalLocalCoordsWhp n_max) 2 w
      have p2 := div_add_packedWords_le a2 5 (16 * M) (globalPtrBits n_max) w
      have p3 := div_add_packedWords_le a3 8 (M + 1) (globalPtrBits n_max) w
      have p4 := div_add_packedWords_le a4 11 (M * capBackWhp n_max) (globalPtrBits n_max) w
      have p5 := div_add_packedWords_le a5 14 (M * capBackWhp n_max) (12 * ell + 4) w
      have p6 := div_add_mul_packedWords_le 2 a6 17 (poolSizeWhp n_max) (globalPtrBits n_max) w
      have p7 := div_add_packedWords_le a7 23 (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w
      have p8 := div_add_packedWords_le a8 26 (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w
      have p9 := div_add_packedWords_le a9 29 (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w
      have p10 := div_add_mul_packedWords_le 2 a10 32 (trieChildEntriesWhp c n_max)
        (globalPtrBits n_max) w
      have p11 := div_add_mul_packedWords_le 2 a11 38 (6 * maxTrieNodesWhp c n_max)
        (globalPtrBits n_max) w
      have p12 := div_add_mul_packedWords_le 2 a12 44 (6 * qEpochWhp n_max + 6)
        (globalPtrBits n_max) w
      dsimp only [ell, M] at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
      change _ ≤ (B_aux + w - 1) / w + 50
      dsimp only [B_aux, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, ell, M] at *
      omega
    let B_bkt := BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) *
        bCharWhp n_max +
      BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp n_max) * bWhp n_max
    let B_fp := BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) *
        bCharWhp n_max +
      BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp n_max) * fpBitsWhp n_max
    let B_qv := n_max * quotBitsWhp U n_max + n_max * valBits V
    have hqv_words := packedWords_add_le n_max (quotBitsWhp U n_max) n_max (valBits V) w
    have hhash_words := ceil_div_add_le B_bkt 6 B_fp 6 w
    have hcomb1 := ceil_div_add_le (B_bkt + B_fp) 13 B_qv 5 w
    have hcomb2 := ceil_div_add_le (B_bkt + B_fp + B_qv) 19 B_aux 50 w
    have hmul_assoc : ∀ k, (2 * k) * globalPtrBits n_max = 2 * (k * globalPtrBits n_max) :=
      fun _ => by ring
    have htot_bits : B_bkt + B_fp + B_qv + B_aux ≤
        Dynamic.optBits U V n_max + whpSpaceFactor c * n_max * Dynamic.logLogFactor n_max := by
      have hfac : 60000 ≤ whpSpaceFactor c := by unfold whpSpaceFactor; omega
      have h60k : B_bkt + B_fp + B_qv + B_aux ≤
          Dynamic.optBits U V n_max + 60000 * (n_max * ell) := by
        dsimp only [B_bkt, B_fp, B_qv, B_aux, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1]
        rw [hmul_assoc (poolSizeWhp n_max), hmul_assoc (trieChildEntriesWhp c n_max),
          hmul_assoc (6 * maxTrieNodesWhp c n_max), hmul_assoc (6 * qEpochWhp n_max + 6)]
        have hqv' : n_max * quotBitsWhp U n_max + n_max * valBits V ≤
            Dynamic.optBits U V n_max + 14 * (n_max * ell) := by
          simpa [ell, mul_assoc] using hqv
        linarith
      calc B_bkt + B_fp + B_qv + B_aux
          ≤ Dynamic.optBits U V n_max + 60000 * (n_max * ell) := h60k
        _ = Dynamic.optBits U V n_max + 60000 * n_max * Dynamic.logLogFactor n_max := by
            dsimp only [ell, ellWhp]; ring
        _ ≤ Dynamic.optBits U V n_max + whpSpaceFactor c * n_max * Dynamic.logLogFactor n_max := by
            gcongr
    have hdiv : (B_bkt + B_fp + B_qv + B_aux + w - 1) / w ≤
        (Dynamic.optBits U V n_max + whpSpaceFactor c * n_max * Dynamic.logLogFactor n_max +
          w - 1) / w :=
      Nat.div_le_div_right (by omega)
    dsimp only [B_bkt, B_fp, B_qv] at hhash_words hcomb1 hcomb2 hdiv
    unfold largeSpaceWhp hdrWordsWhp Dynamic.succinctWords whpSpaceConst
    omega

/-- Branching cube bound for SWAR B+-tree height: when `whpThreshold c ≤ n_max`,
`scaleWhp n_max ≤ (tMinWhp n_max) ^ 3`. -/
theorem scaleWhp_le_tMinWhp_cubed {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    scaleWhp n_max ≤ (tMinWhp n_max) ^ 3 := by
  have hm := bMinWhp_le_log hth
  have hbm := le_bMinWhp c
  have h1280 := mul_ell_le_log hth
  have hell := one_le_ellWhp n_max
  set m := Nat.log 2 n_max
  set ell := ellWhp n_max
  have hn4 : 4 ≤ n_max := by
    have h4 : 2 ^ 2 ≤ whpThreshold c := by
      unfold whpThreshold
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (by decide : 4 ≤ 2 ^ 2).trans (h4.trans hth)
  by_cases hell26 : ell ≤ 26
  · have ht_ge : 1575 ≤ tMinWhp n_max := by
      have hdiv : 1575 ≤ m / (160 * ell) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        dsimp only [ell, m] at hell26 hm ⊢
        omega
      unfold tMinWhp
      exact hdiv.trans (le_max_right 2 _)
    calc scaleWhp n_max = 2 ^ ell := rfl
      _ ≤ 2 ^ 26 := Nat.pow_le_pow_right (by decide) hell26
      _ ≤ 1575 ^ 3 := by decide
      _ ≤ (tMinWhp n_max) ^ 3 := Nat.pow_le_pow_left ht_ge 3
  · have hell27 : 27 ≤ ell := by omega
    have hell_eq : ell = Nat.clog 2 (Nat.clog 2 n_max) := by
      dsimp only [ell, ellWhp, Dynamic.logLogFactor]
      rw [max_eq_left hn4]
    have hgt_clog : 1 < Nat.clog 2 n_max := by
      by_contra hle
      have hc : Nat.clog 2 (Nat.clog 2 n_max) ≤ 1 := by
        have hc0 : Nat.clog 2 0 = 0 := by decide
        have hc1 : Nat.clog 2 1 = 0 := by decide
        interval_cases Nat.clog 2 n_max <;> simp_all
      omega
    have hL_lt : 2 ^ (ell - 1) < Nat.clog 2 n_max := by
      rw [hell_eq]
      exact Nat.pow_pred_clog_lt_self Nat.one_lt_two hgt_clog
    have hclog_le : Nat.clog 2 n_max ≤ m + 1 :=
      (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
        (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
    have hm_ge : 2 ^ (ell - 1) ≤ m := by omega
    set d := ell - 27
    have hd_eq : ell = d + 27 := by omega
    set k := d / 3 + 10
    set r := d - d / 3
    have hdiv3 := Nat.div_add_mod d 3
    have hmod3 := Nat.mod_lt d (by decide : 0 < 3)
    have hd_le_2r : d ≤ 2 * r := by omega
    have hlin_pow : ∀ x : ℕ, 160 * (2 * x + 27) ≤ 2 ^ (x + 16) := by
      intro x
      induction x with
      | zero => decide
      | succ x ih =>
        have h16 : 65536 ≤ 2 ^ (x + 16) := by
          calc 65536 = 2 ^ 16 := by decide
            _ ≤ 2 ^ (x + 16) := Nat.pow_le_pow_right (by decide) (by omega)
        have hsucc : 2 ^ (x + 1 + 16) = 2 * 2 ^ (x + 16) := by
          rw [show x + 1 + 16 = (x + 16) + 1 by omega, Nat.pow_succ']
        omega
    have hden_le : 160 * ell ≤ 2 ^ (r + 16) := by
      calc 160 * ell = 160 * (d + 27) := by rw [hd_eq]
        _ ≤ 160 * (2 * r + 27) := Nat.mul_le_mul_left 160 (by omega)
        _ ≤ 2 ^ (r + 16) := hlin_pow r
    have ht_pow : 2 ^ k ≤ tMinWhp n_max := by
      have hdiv : 2 ^ k ≤ m / (160 * ell) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        calc 2 ^ k * (160 * ell)
            ≤ 2 ^ k * 2 ^ (r + 16) := Nat.mul_le_mul_left _ hden_le
          _ = 2 ^ (ell - 1) := by rw [← Nat.pow_add]; congr 1; omega
          _ ≤ m := hm_ge
      unfold tMinWhp
      exact hdiv.trans (le_max_right 2 _)
    calc scaleWhp n_max = 2 ^ ell := rfl
      _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (2 ^ k) ^ 3 := by rw [Nat.mul_comm, Nat.pow_mul]
      _ ≤ (tMinWhp n_max) ^ 3 := Nat.pow_le_pow_left ht_pow 3

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
