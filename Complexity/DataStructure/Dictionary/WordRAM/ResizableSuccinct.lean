/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Resizable
public import Complexity.DataStructure.Dictionary.WordRAM.Succinct

/-!
# Word-Granular Resizable Succinct Dynamic Dictionary on the Word-RAM

This module builds the word-granular resizable succinct dynamic dictionary primitives on top of
the word-granular resizable Word-RAM model (`Cslib.WordRAM.Resizable`) and the fixed-capacity
succinct dictionary (`Cslib.DataStructure.Dictionary.WordRAM.Succinct`).

## Design choices and architecture

1. **Single linear word-resizable memory `[0, L)` (`RData`)**:
   The dictionary and all caller structures reside in a single linear word-addressed memory
   `[0, x.frontier)` on `RData (rSuccinct U V w N)`. Growing the active memory prefix executes the
   machine instruction `RCode.grow` against the **demonic** growth specification (`DemonicGrow`),
   followed by `zeroFill` (`growZeroCode_exec`) to deterministically zero the newly allocated words.
   Shrinking the active memory prefix executes `RCode.shrink` (`RDemonicExec.shrink`), returning
   released words to the unallocated suffix `[x.frontier, ∞)` so subsequent allocations reuse the
   exact same addresses.
2. **Stepwise `n_t`-tight space bounds (`activeEpochWords`)**:
   Within an epoch of capacity parameter `N`, the hash and bucket metadata (`metaWords U w N`)
   depend on `N`, while the active quotient and value item slots (`itemWords U V w N n_t`) scale
   with the current key count `n_t`. Whenever `n_t ≤ N ≤ 4 * n_t`, `quotientBits U N ≤
   quotientBits U n_t + 6` and `Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n_t`, so the
   total active word footprint `activeEpochWords U V w N n_t` at **every step `t`** is at most
   `Dynamic.succinctWords 1227 213 U V w n_t` words (and at `N ≤ 2 * n_t`, at most
   `Dynamic.succinctWords 312 213 U V w n_t` words). Converting words to bits
   (`succinctWords_mul_w_le_bits`) exhibits the exact additive space term `(C₀ + 1) * w = 214 * w`
   bits forced by word-granular rounding of the dictionary's sub-tables.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.metaWords`,
  `itemWords`, `activeEpochWords`: word-level metadata, live-item, and total active footprints in
  epoch `N` at live size `n`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.allocWordsCode`,
  `allocSuccinctCode`, `deallocWordsCode`, `deallocSuccinctCode`, `growTailWordsCode`,
  `shrinkTailWordsCode`: concrete `RCode` programs for demonic-safe allocation, deallocation, and
  within-epoch item-region resizing on `RData`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ResizableRep`: representation invariant
  on `RData (rSuccinct U V w N)` in `[0, base + Succinct.space U V w N)`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.succinctWords_mul_w_le_bits`,
  `activeEpochWords_le_succinctWords_of_le_two_mul`,
  `activeEpochWords_le_succinctWords_of_le_four_mul`: stepwise `n_t`-tight space bounds in words
  and bits with explicit `214 * w` word-rounding term.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.allocSuccinctCode_exec`,
  `deallocSuccinctCode_exec`, `init_resizable_succinct`, `step_resizable_succinct`,
  `seq_expected_amortized_modifies`: concrete resizable Word-RAM execution theorems under demonic
  `DemonicGrow` and `.shrink`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Logarithmic, Quotient-Bit, and Stepwise `n_t`-Tight Space Bounds -/

/-- Doubling the argument of `Nat.clog 2` increases it by at most `1`. -/
theorem clog_two_mul_le (x : ℕ) : Nat.clog 2 (2 * x) ≤ Nat.clog 2 x + 1 := by
  rw [Nat.clog_le_iff_le_pow one_lt_two, pow_succ']
  exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog one_lt_two x)

/-- `Dynamic.logLogFactor (2 * n)` exceeds `Dynamic.logLogFactor n` by at most `1`. -/
theorem logLogFactor_two_mul_le_add_one (n : ℕ) :
    Dynamic.logLogFactor (2 * n) ≤ Dynamic.logLogFactor n + 1 := by
  unfold Dynamic.logLogFactor
  have hm : max (2 * n) 4 ≤ 2 * max n 4 := by omega
  have hc1 : Nat.clog 2 (max (2 * n) 4) ≤ 2 * Nat.clog 2 (max n 4) := by
    have hle1 : Nat.clog 2 (max (2 * n) 4) ≤ Nat.clog 2 (2 * max n 4) :=
      Nat.clog_mono_right 2 hm
    have hle2 := clog_two_mul_le (max n 4)
    have hpos : 1 ≤ Nat.clog 2 (max n 4) := by
      have : Nat.clog 2 4 = 2 := by decide
      have h4 : Nat.clog 2 4 ≤ Nat.clog 2 (max n 4) :=
        Nat.clog_mono_right 2 (le_max_right n 4)
      omega
    omega
  exact (Nat.clog_mono_right 2 hc1).trans (clog_two_mul_le _)

/-- `Dynamic.logLogFactor (2 * n) ≤ 2 * Dynamic.logLogFactor n`. -/
theorem logLogFactor_two_mul_le (n : ℕ) :
    Dynamic.logLogFactor (2 * n) ≤ 2 * Dynamic.logLogFactor n := by
  have h1 := logLogFactor_two_mul_le_add_one n
  have h2 := Dynamic.one_le_logLogFactor n
  omega

/-- `Dynamic.logLogFactor (4 * n)` exceeds `Dynamic.logLogFactor n` by at most `2`. -/
theorem logLogFactor_four_mul_le_add_two (n : ℕ) :
    Dynamic.logLogFactor (4 * n) ≤ Dynamic.logLogFactor n + 2 := by
  have h1 : 4 * n = 2 * (2 * n) := by ring
  rw [h1]
  have ha := logLogFactor_two_mul_le_add_one (2 * n)
  have hb := logLogFactor_two_mul_le_add_one n
  omega

/-- `Dynamic.logLogFactor (4 * n) ≤ 4 * Dynamic.logLogFactor n`. -/
theorem logLogFactor_four_mul_le (n : ℕ) :
    Dynamic.logLogFactor (4 * n) ≤ 4 * Dynamic.logLogFactor n := by
  have h1 := logLogFactor_four_mul_le_add_two n
  have h2 := Dynamic.one_le_logLogFactor n
  omega

/-- Whenever `n ≤ N ≤ 2 * n`, the epoch quotient width `quotientBits U N` exceeds the exact
quotient width `quotientBits U n` by at most `3` bits. -/
theorem quotientBits_le_add_three_of_le_two_mul {n N : ℕ} (U : ℕ)
    (hnN : n ≤ N) (hN2 : N ≤ 2 * n) :
    quotientBits U N ≤ quotientBits U n + 3 := by
  have hlog : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN
  have hll : Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 1 :=
    (Dynamic.logLogFactor_mono hN2).trans (logLogFactor_two_mul_le_add_one n)
  unfold quotientBits bucketBits
  omega

/-- Whenever `n ≤ N ≤ 4 * n`, the epoch quotient width `quotientBits U N` exceeds the exact
quotient width `quotientBits U n` by at most `6` bits. -/
theorem quotientBits_le_add_six_of_le_four_mul {n N : ℕ} (U : ℕ)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    quotientBits U N ≤ quotientBits U n + 6 := by
  have hlog : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN
  have hll : Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 2 :=
    (Dynamic.logLogFactor_mono hN4).trans (logLogFactor_four_mul_le_add_two n)
  unfold quotientBits bucketBits
  omega

/-- Metadata word footprint in an epoch of capacity parameter `N`: the quotient hash family
(`hashSpace U w N`), `GlobalMeta`, and the 9 `LocalMeta` sub-arrays. -/
@[expose]
def metaWords (U w N : ℕ) : ℕ :=
  hashSpace U w N +
    packedWords (globalMetaLen N) (globalPtrBits N) w +
    9 * packedWords (totalMicroBuckets N) (effBucketPosBits N) w

/-- Live item word footprint in an epoch of capacity parameter `N` when `n` keys are currently
present: `n` packed quotients of `quotientBits U N` bits and `n` packed values of `valBits V`
bits. -/
@[expose]
def itemWords (U V w N n : ℕ) : ℕ :=
  packedWords n (quotientBits U N) w + packedWords n (valBits V) w

/-- Total active word footprint in epoch `N` at current live key count `n`. -/
@[expose]
def activeEpochWords (U V w N n : ℕ) : ℕ :=
  metaWords U w N + itemWords U V w N n

/-- At `N = n`, `activeEpochWords U V w n n` coincides identically with `Succinct.space U V w n`. -/
theorem activeEpochWords_eq_space (U V w n : ℕ) :
    activeEpochWords U V w n n = Succinct.space U V w n := by
  unfold activeEpochWords metaWords itemWords Succinct.space totalSpace offGM offLM offVal offQuot
    lmSubWords
  ring

/-- Monotonicity of `itemWords` in the live item count `n`. -/
theorem itemWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    itemWords U V w N n₁ ≤ itemWords U V w N n₂ := by
  unfold itemWords packedWords
  have h1 : (n₁ * quotientBits U N + w - 1) / w ≤ (n₂ * quotientBits U N + w - 1) / w :=
    Nat.div_le_div_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) w) 1)
  have h2 : (n₁ * valBits V + w - 1) / w ≤ (n₂ * valBits V + w - 1) / w :=
    Nat.div_le_div_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) w) 1)
  omega

/-- Whenever `n ≤ N`, `activeEpochWords U V w N n ≤ Succinct.space U V w N`. -/
theorem activeEpochWords_le_space {U V w N n : ℕ} (hnN : n ≤ N) :
    activeEpochWords U V w N n ≤ Succinct.space U V w N := by
  rw [← activeEpochWords_eq_space U V w N]
  exact Nat.add_le_add_left (itemWords_mono hnN) (metaWords U w N)

/-- Adding `1` live item increases `itemWords` by at most `2` words when `U, V ≤ 2 ^ w`. -/
theorem itemWords_succ_sub_le_two {U V w N n : ℕ} (hw : 0 < w)
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) :
    itemWords U V w N (n + 1) - itemWords U V w N n ≤ 2 := by
  have hq_le : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hv_le : valBits V ≤ w := Nat.clog_le_of_le_pow hV
  have h1 : packedWords (n + 1) (quotientBits U N) w ≤
      packedWords n (quotientBits U N) w + 1 := by
    unfold packedWords
    have hdiv : ((n + 1) * quotientBits U N + w - 1) / w ≤
        (n * quotientBits U N + w - 1) / w + 1 := by
      rw [Nat.add_mul, Nat.one_mul]
      calc (n * quotientBits U N + quotientBits U N + w - 1) / w
          ≤ (n * quotientBits U N + w - 1 + w) / w :=
            Nat.div_le_div_right (by omega)
        _ = (n * quotientBits U N + w - 1) / w + 1 :=
            Nat.add_div_right _ hw
    omega
  have h2 : packedWords (n + 1) (valBits V) w ≤ packedWords n (valBits V) w + 1 := by
    unfold packedWords
    have hdiv : ((n + 1) * valBits V + w - 1) / w ≤ (n * valBits V + w - 1) / w + 1 := by
      rw [Nat.add_mul, Nat.one_mul]
      calc (n * valBits V + valBits V + w - 1) / w
          ≤ (n * valBits V + w - 1 + w) / w :=
            Nat.div_le_div_right (by omega)
        _ = (n * valBits V + w - 1) / w + 1 :=
            Nat.add_div_right _ hw
    omega
  unfold itemWords
  omega

/-- Combined ceiling-division bound on `activeEpochWords U V w N n`. -/
private theorem activeEpochWords_le_div_add {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    activeEpochWords U V w N n ≤
      (n * quotientBits U N + n * valBits V + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * N) * 1 + w - 1) / w + 213 := by
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]
    ring
  have hh := hashSpace_le hw hNU hU
  have h12 := packedWords_add_le n (quotientBits U N) n (valBits V) w
  have h123 := div_add_mul_packedWords_le 9
    (n * quotientBits U N + n * valBits V) 5
    (totalMicroBuckets N) (effBucketPosBits N) w
  rw [hlm_eq] at h123
  have h1234 := div_add_packedWords_le
    (n * quotientBits U N + n * valBits V + localMetaLen N * effBucketPosBits N) 32
    (globalMetaLen N) (globalPtrBits N) w
  have h12345 := div_add_packedWords_le
    (n * quotientBits U N + n * valBits V + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N) 35
    (2 * N) 1 w
  unfold activeEpochWords metaWords itemWords
  omega

/-- **Stepwise `n_t`-tight space bound for `n ≤ N ≤ 2 * n`:**
Throughout any doubling/halving epoch with `n ≤ N ≤ 2 * n` and `N ≤ U`, the active word footprint
`activeEpochWords U V w N n` is at most `Dynamic.succinctWords 312 213 U V w n`. -/
theorem activeEpochWords_le_succinctWords_of_le_two_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN2 : N ≤ 2 * n) :
    activeEpochWords U V w N n ≤ Dynamic.succinctWords 312 213 U V w n := by
  have hbase := activeEpochWords_le_div_add (V := V) (n := n) hw hNU hU
  have hq3 := quotientBits_le_add_three_of_le_two_mul U hnN hN2
  have hqv_opt := quotient_val_bits_le_optBits (V := V) hnU
  rw [Nat.left_distrib] at hqv_opt
  have hll_n := Dynamic.one_le_logLogFactor n
  have hll_N : Dynamic.logLogFactor N ≤ 2 * Dynamic.logLogFactor n :=
    (Dynamic.logLogFactor_mono hN2).trans (logLogFactor_two_mul_le n)
  have hlm := localMetaLen_mul_effBucketPosBits_le N
  have hgm := globalMetaLen_mul_globalPtrBits_le N
  have hitem_bits :
      n * quotientBits U N + n * valBits V ≤
        Dynamic.optBits U V n + 8 * n * Dynamic.logLogFactor n := by
    have hmul : n * quotientBits U N ≤ n * quotientBits U n + 3 * n := by
      calc n * quotientBits U N ≤ n * (quotientBits U n + 3) := Nat.mul_le_mul_left n hq3
        _ = n * quotientBits U n + 3 * n := by ring
    have h3n : 3 * n ≤ 3 * n * Dynamic.logLogFactor n := by
      calc 3 * n = 3 * n * 1 := by ring
        _ ≤ 3 * n * Dynamic.logLogFactor n := by gcongr
    have h8 : 5 * n * Dynamic.logLogFactor n + 3 * n * Dynamic.logLogFactor n =
        8 * n * Dynamic.logLogFactor n := by ring
    omega
  have hmeta_bits :
      localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N + (2 * N) * 1 ≤
        304 * n * Dynamic.logLogFactor n := by
    have hll_N1 := Dynamic.one_le_logLogFactor N
    have h2N : (2 * N) * 1 ≤ 2 * N * Dynamic.logLogFactor N := by
      calc (2 * N) * 1 = 2 * N * 1 := by ring
        _ ≤ 2 * N * Dynamic.logLogFactor N := by gcongr
    have h76N :
        localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N + (2 * N) * 1 ≤
          76 * N * Dynamic.logLogFactor N := by
      have : 76 * N * Dynamic.logLogFactor N =
          54 * N * Dynamic.logLogFactor N + 20 * N * Dynamic.logLogFactor N +
            2 * N * Dynamic.logLogFactor N := by ring
      omega
    have hN_ll : N * Dynamic.logLogFactor N ≤ 4 * (n * Dynamic.logLogFactor n) := by
      calc N * Dynamic.logLogFactor N
          ≤ (2 * n) * (2 * Dynamic.logLogFactor n) := Nat.mul_le_mul hN2 hll_N
        _ = 4 * (n * Dynamic.logLogFactor n) := by ring
    nlinarith
  have hnum :
      n * quotientBits U N + n * valBits V + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * N) * 1 + w - 1 ≤
      Dynamic.optBits U V n + 312 * n * Dynamic.logLogFactor n + w - 1 := by
    have : 312 * n * Dynamic.logLogFactor n =
        8 * n * Dynamic.logLogFactor n + 304 * n * Dynamic.logLogFactor n := by ring
    omega
  have hdiv := Nat.div_le_div_right (c := w) hnum
  unfold Dynamic.succinctWords
  omega

/-- **Stepwise `n_t`-tight space bound for `n ≤ N ≤ 4 * n` (`EpochValid n N`):**
Throughout any epoch satisfying `n ≤ N ≤ 4 * n` and `N ≤ U`, the active word footprint
`activeEpochWords U V w N n` is at most `Dynamic.succinctWords 1227 213 U V w n`. -/
theorem activeEpochWords_le_succinctWords_of_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    activeEpochWords U V w N n ≤ Dynamic.succinctWords 1227 213 U V w n := by
  have hbase := activeEpochWords_le_div_add (V := V) (n := n) hw hNU hU
  have hq6 := quotientBits_le_add_six_of_le_four_mul U hnN hN4
  have hqv_opt := quotient_val_bits_le_optBits (V := V) hnU
  rw [Nat.left_distrib] at hqv_opt
  have hll_n := Dynamic.one_le_logLogFactor n
  have hll_N : Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n :=
    (Dynamic.logLogFactor_mono hN4).trans (logLogFactor_four_mul_le n)
  have hlm := localMetaLen_mul_effBucketPosBits_le N
  have hgm := globalMetaLen_mul_globalPtrBits_le N
  have hitem_bits :
      n * quotientBits U N + n * valBits V ≤
        Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by
    have hmul : n * quotientBits U N ≤ n * quotientBits U n + 6 * n := by
      calc n * quotientBits U N ≤ n * (quotientBits U n + 6) := Nat.mul_le_mul_left n hq6
        _ = n * quotientBits U n + 6 * n := by ring
    have h6n : 6 * n ≤ 6 * n * Dynamic.logLogFactor n := by
      calc 6 * n = 6 * n * 1 := by ring
        _ ≤ 6 * n * Dynamic.logLogFactor n := by gcongr
    have h11 : 5 * n * Dynamic.logLogFactor n + 6 * n * Dynamic.logLogFactor n =
        11 * n * Dynamic.logLogFactor n := by ring
    omega
  have hmeta_bits :
      localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N + (2 * N) * 1 ≤
        1216 * n * Dynamic.logLogFactor n := by
    have hll_N1 := Dynamic.one_le_logLogFactor N
    have h2N : (2 * N) * 1 ≤ 2 * N * Dynamic.logLogFactor N := by
      calc (2 * N) * 1 = 2 * N * 1 := by ring
        _ ≤ 2 * N * Dynamic.logLogFactor N := by gcongr
    have h76N :
        localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N + (2 * N) * 1 ≤
          76 * N * Dynamic.logLogFactor N := by
      have : 76 * N * Dynamic.logLogFactor N =
          54 * N * Dynamic.logLogFactor N + 20 * N * Dynamic.logLogFactor N +
            2 * N * Dynamic.logLogFactor N := by ring
      omega
    have hN_ll : N * Dynamic.logLogFactor N ≤ 16 * (n * Dynamic.logLogFactor n) := by
      calc N * Dynamic.logLogFactor N
          ≤ (4 * n) * (4 * Dynamic.logLogFactor n) := Nat.mul_le_mul hN4 hll_N
        _ = 16 * (n * Dynamic.logLogFactor n) := by ring
    nlinarith
  have hnum :
      n * quotientBits U N + n * valBits V + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * N) * 1 + w - 1 ≤
      Dynamic.optBits U V n + 1227 * n * Dynamic.logLogFactor n + w - 1 := by
    have : 1227 * n * Dynamic.logLogFactor n =
        11 * n * Dynamic.logLogFactor n + 1216 * n * Dynamic.logLogFactor n := by ring
    omega
  have hdiv := Nat.div_le_div_right (c := w) hnum
  unfold Dynamic.succinctWords
  omega

/-- **Bit-level succinct space bound with explicit word-rounding additive term:**
Any word footprint bounded by `Dynamic.succinctWords C C₀ U V w n` occupies at most
`Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + (C₀ + 1) * w` bits, where `(C₀ + 1) * w`
is the additive bit overhead forced by word-granular allocation (`C₀ = 213` words, so `214 * w`
bits). -/
theorem succinctWords_mul_w_le_bits (C C₀ U V w n : ℕ) :
    w * Dynamic.succinctWords C C₀ U V w n ≤
      Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + (C₀ + 1) * w := by
  unfold Dynamic.succinctWords
  rw [Nat.left_distrib]
  have hdiv := Nat.mul_div_le (Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + w - 1) w
  have hsub : Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + w - 1 ≤
      Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + w := by omega
  have hring : (C₀ + 1) * w = w + w * C₀ := by ring
  omega

/-! ## Section 2: Demonic-Grow Allocation, Deallocation, and Resizing on `RData` -/

/-- The 6 registers `[hqReg, baseReg, curReg, frontierReg, zeroReg, oneReg]` (`[248, 0, 241, 240,
242, 243]`) used by `allocWordsCode` are pairwise distinct. -/
theorem nodup_allocRegs (U V w N : ℕ) :
    [hqReg U V w N, baseReg U V w N, curReg U V w N,
      frontierReg U V w N, zeroReg U V w N, oneReg U V w N].Nodup := by
  change (List.map (sReg U V w N) [248, 0, 241, 240, 242, 243]).Nodup
  exact (List.nodup_map_iff (sReg_injective U V w N)).mpr (by decide)

/-- The 6 registers `[hqReg, resTagReg, curReg, frontierReg, zeroReg, oneReg]` (`[248, 252, 241,
240, 242, 243]`) used by `growTailWordsCode` are pairwise distinct and disjoint from `baseReg`
(`0`). -/
theorem nodup_growTailRegs (U V w N : ℕ) :
    [hqReg U V w N, resTagReg U V w N, curReg U V w N,
      frontierReg U V w N, zeroReg U V w N, oneReg U V w N].Nodup := by
  change (List.map (sReg U V w N) [248, 252, 241, 240, 242, 243]).Nodup
  exact (List.nodup_map_iff (sReg_injective U V w N)).mpr (by decide)

/-- Allocate and zero `k` words at `x.frontier` on `RData (rSuccinct U V w N)` under **demonic**
`DemonicGrow`, storing the old `x.frontier` in `baseReg` (`0`) and the new `x.frontier + k` in
`frontierReg` (`240`). -/
@[expose]
noncomputable def allocWordsCode (U V w N k : ℕ) : RCode .standard (rSuccinct U V w N) :=
  .seq (.op (.const (hqReg U V w N) k))
    (growZeroCode (hqReg U V w N) (baseReg U V w N) (curReg U V w N)
      (frontierReg U V w N) (zeroReg U V w N) (oneReg U V w N))

/-- **Demonic-safe block allocation (`allocWordsCode_exec`):**
Starting from `x : RData (rSuccinct U V w N)` with `x.Bounded w` and `x.frontier = base`,
`allocWordsCode U V w N k` executes in `4 * k + 8` instructions under **demonic** `DemonicGrow`,
zeroes every demonically initialized word in `[base, base + k)`, sets `baseReg = base` and
`frontierReg = base + k`, and produces `x₁` with `x₁.frontier = base + k`, `x₁.Bounded w`, and
`∀ a ∈ (Block.mk base k).footprint, x₁.mem a = 0`. -/
theorem allocWordsCode_exec {U V w N base k : ℕ} {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (hfr : x.frontier = base)
    (h1 : Fits w 1) (hfit : Fits w (base + k)) :
    ∃ x₁ : RData (rSuccinct U V w N),
      RDemonicExec w (allocWordsCode U V w N k) x (4 * k + 8) (· = x₁) ∧
      x₁.Bounded w ∧
      x₁.frontier = base + k ∧
      x₁.regs (baseReg U V w N) = base ∧
      x₁.regs (frontierReg U V w N) = base + k ∧
      x₁.mem = x.mem ∧
      ∀ a ∈ (Block.mk base k).footprint, x₁.mem a = 0 := by
  have hk_fits : Fits w k := hfit.of_le (Nat.le_add_left k base)
  set x₀ := x.set (hqReg U V w N) k
  have hx₀_bdd : x₀.Bounded w := hx.set hk_fits
  have e₀ : RDemonicExec (B := .standard) w (.op (.const (hqReg U V w N) k)) x 1 (· = x₀) :=
    RDemonicExec.const hk_fits
  have hx₀_cnt : x₀.regs (hqReg U V w N) = k := by simp [x₀]
  have hx₀_fr : x₀.frontier = base := hfr
  have e_gz := growZeroCode_exec (w := w)
    (count := hqReg U V w N) (result := baseReg U V w N) (cur := curReg U V w N)
    (stop := frontierReg U V w N) (zero := zeroReg U V w N) (one := oneReg U V w N)
    hx₀_bdd (nodup_allocRegs U V w N) h1
    (by rw [hx₀_cnt, hx₀_fr, Nat.add_comm]; exact hfit)
  dsimp only at e_gz
  rw [hx₀_cnt, hx₀_fr] at e_gz
  let regs₁ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      x₀.regs (zeroReg U V w N) 0) (oneReg U V w N) 1) (baseReg U V w N) base)
      (frontierReg U V w N) (base + k)) (curReg U V w N) (base + k)
  let x₁ : RData (rSuccinct U V w N) := ⟨regs₁, x₀.mem, base + k⟩
  have he_all : RDemonicExec w (allocWordsCode U V w N k) x (4 * k + 8) (· = x₁) :=
    (e₀.seq_eq e_gz).mono (by omega) fun _ h => h
  have hbase_fits : Fits w base := hfit.of_le (Nat.le_add_right base k)
  have hx₁_bdd : x₁.Bounded w := by
    have h0 := hx₀_bdd.set (i := zeroReg U V w N) (fits_zero w)
    have h1' := h0.set (i := oneReg U V w N) h1
    have h2 := h1'.set (i := baseReg U V w N) hbase_fits
    have h3 := h2.set (i := frontierReg U V w N) hfit
    have h4 := h3.set (i := curReg U V w N) hfit
    refine ⟨h4.1, hfit, fun a ha => ?_⟩
    dsimp only [x₁] at ha
    exact hx.zero_above (by omega)
  refine ⟨x₁, he_all, hx₁_bdd, rfl, ?_, ?_, rfl, fun a ha => ?_⟩
  · dsimp only [x₁, regs₁, baseReg, frontierReg, curReg]
    simp only [Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte]
  · dsimp only [x₁, regs₁, frontierReg, curReg]
    simp only [Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte]
  · simp only [Block.mem_footprint, Block.Owns] at ha
    exact hx.zero_above (by omega)

/-- Allocate and zero `[base, base + Succinct.space U V w N)` on `RData (rSuccinct U V w N)` under
**demonic** `DemonicGrow`. -/
@[expose]
noncomputable def allocSuccinctCode (U V w N : ℕ) : RCode .standard (rSuccinct U V w N) :=
  allocWordsCode U V w N (Succinct.space U V w N)

/-- **Demonic-safe dictionary allocation (`allocSuccinctCode_exec`):**
Allocates and zeroes `[base, base + Succinct.space U V w N)` in `4 * Succinct.space U V w N + 8`
instructions on `RData` under **demonic** `DemonicGrow`. -/
theorem allocSuccinctCode_exec {U V w N base : ℕ} {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (hfr : x.frontier = base)
    (hfit : Fits w (base + Succinct.space U V w N)) :
    ∃ x₁ : RData (rSuccinct U V w N),
      RDemonicExec w (allocSuccinctCode U V w N) x (4 * Succinct.space U V w N + 8) (· = x₁) ∧
      x₁.Bounded w ∧
      x₁.frontier = base + Succinct.space U V w N ∧
      x₁.regs (baseReg U V w N) = base ∧
      x₁.regs (frontierReg U V w N) = base + Succinct.space U V w N ∧
      x₁.mem = x.mem ∧
      ∀ a ∈ (Block.mk base (Succinct.space U V w N)).footprint, x₁.mem a = 0 := by
  have hw2 : 2 ≤ w := two_le_w_of_fits_space hfit
  have h1 : Fits w 1 :=
    lt_of_lt_of_le (by decide : 1 < 2 ^ 2) (Nat.pow_le_pow_right two_pos hw2)
  exact allocWordsCode_exec hx hfr h1 hfit

/-- Deallocate `k` words at the top of `[0, base + k)` via `RCode.shrink` and restore
`frontierReg := baseReg` (`base`). -/
@[expose]
noncomputable def deallocWordsCode (U V w N k : ℕ) : RCode .standard (rSuccinct U V w N) :=
  .seq (.op (.const (curReg U V w N) k))
  (.seq (.shrink (curReg U V w N))
        (.op (.copy (frontierReg U V w N) (baseReg U V w N))))

/-- **Deallocation via `.shrink` (`deallocWordsCode_exec`):**
Starting from `x : RData (rSuccinct U V w N)` with `x.Bounded w`, `x.frontier = base + k`, and
`x.regs (baseReg U V w N) = base`, `deallocWordsCode U V w N k` executes in `3` instructions,
shrinking `y.frontier` back to `base`, clearing `[base, base + k)` to `0`, preserving all caller
memory `< base`, and restoring `y.Bounded w`. -/
theorem deallocWordsCode_exec {U V w N base k : ℕ} {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (hfr : x.frontier = base + k)
    (hbase : x.regs (baseReg U V w N) = base) (hfit_k : Fits w k) :
    ∃ y : RData (rSuccinct U V w N),
      RDemonicExec w (deallocWordsCode U V w N k) x 3 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base ∧
      y.regs (baseReg U V w N) = base ∧
      y.regs (frontierReg U V w N) = base ∧
      y.mem = clear x.mem base k ∧
      ∀ a < base, y.mem a = x.mem a := by
  set x₁ := x.set (curReg U V w N) k
  have hx₁_bdd : x₁.Bounded w := hx.set hfit_k
  have e₁ : RDemonicExec (B := .standard) w (.op (.const (curReg U V w N) k)) x 1 (· = x₁) :=
    RDemonicExec.const hfit_k
  have hx₁_cur : x₁.regs (curReg U V w N) = k := by simp [x₁]
  have hx₁_fr : x₁.frontier = base + k := hfr
  have hsub : x.frontier - k = base := by omega
  let x₂ : RData (rSuccinct U V w N) := ⟨x₁.regs, clear x.mem base k, base⟩
  have e₂ : RDemonicExec (B := .standard) w (.shrink (curReg U V w N)) x₁ 1 (· = x₂) := by
    refine RDemonicExec.shrink (by rw [hx₁_cur, hx₁_fr]; omega) ?_
    ext a
    · rfl
    · simp [x₂, x₁, hx₁_cur, hsub]
    · simp [x₂, x₁, hx₁_cur, hsub]
  have hx₂_bdd : x₂.Bounded w := by
    have hs := hx₁_bdd.shrink (k := k) (by rw [hx₁_fr]; omega)
    simpa [x₂, x₁, hsub] using hs
  have hx₂_base : x₂.regs (baseReg U V w N) = base := by
    dsimp only [x₂, x₁, baseReg, curReg]
    simp only [RData.set_regs, Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte, hbase]
  set y := x₂.set (frontierReg U V w N) (x₂.regs (baseReg U V w N))
  have e₃ : RDemonicExec (B := .standard) w
      (.op (.copy (frontierReg U V w N) (baseReg U V w N))) x₂ 1 (· = y) :=
    RDemonicExec.copy
  have hy_bdd : y.Bounded w :=
    hx₂_bdd.set (by rw [hx₂_base]; exact hx₂_bdd.frontier_fits)
  refine ⟨y, (e₁.seq_eq (e₂.seq_eq e₃)).mono le_rfl (fun _ h => h),
    hy_bdd, rfl, ?_, ?_, rfl, fun a ha => ?_⟩
  · dsimp only [y, baseReg, frontierReg]
    simp only [RData.set_regs, Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte, hx₂_base]
  · dsimp only [y]
    simp [hx₂_base]
  · exact clear_of_not_owns (by simp only [Block.Owns]; omega)

/-- Deallocate the entire succinct dictionary footprint `Succinct.space U V w N` via `.shrink`. -/
@[expose]
noncomputable def deallocSuccinctCode (U V w N : ℕ) : RCode .standard (rSuccinct U V w N) :=
  deallocWordsCode U V w N (Succinct.space U V w N)

/-- **Dictionary deallocation (`deallocSuccinctCode_exec`):**
Deallocates `[base, base + Succinct.space U V w N)` in `3` instructions via `.shrink`, returning
`frontier` to `base` so the released words can be reused immediately. -/
theorem deallocSuccinctCode_exec {U V w N base : ℕ} {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (hfr : x.frontier = base + Succinct.space U V w N)
    (hbase : x.regs (baseReg U V w N) = base) :
    ∃ y : RData (rSuccinct U V w N),
      RDemonicExec w (deallocSuccinctCode U V w N) x 3 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base ∧
      y.regs (baseReg U V w N) = base ∧
      y.regs (frontierReg U V w N) = base ∧
      y.mem = clear x.mem base (Succinct.space U V w N) ∧
      ∀ a < base, y.mem a = x.mem a := by
  have hfit_sp : Fits w (Succinct.space U V w N) := by
    have hfr_fits := hx.frontier_fits
    rw [hfr] at hfr_fits
    exact hfr_fits.of_le (Nat.le_add_left _ _)
  exact deallocWordsCode_exec hx hfr hbase hfit_sp

/-- Grow the active item region at `x.frontier` by `Δ` words under **demonic** `DemonicGrow` and
zero the newly grown words `[x.frontier, x.frontier + Δ)` while preserving `baseReg`. -/
@[expose]
noncomputable def growTailWordsCode (U V w N Δ : ℕ) : RCode .standard (rSuccinct U V w N) :=
  .seq (.op (.const (hqReg U V w N) Δ))
    (growZeroCode (hqReg U V w N) (resTagReg U V w N) (curReg U V w N)
      (frontierReg U V w N) (zeroReg U V w N) (oneReg U V w N))

/-- **Demonic-safe item-tail growth (`growTailWordsCode_exec`):**
Extends `x.frontier` by `Δ` zeroed words in `4 * Δ + 8` instructions under **demonic**
`DemonicGrow`, preserving `x.mem` and `x.regs (baseReg U V w N)`. -/
theorem growTailWordsCode_exec {U V w N Δ : ℕ} {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (h1 : Fits w 1) (hfit : Fits w (x.frontier + Δ)) :
    ∃ y : RData (rSuccinct U V w N),
      RDemonicExec w (growTailWordsCode U V w N Δ) x (4 * Δ + 8) (· = y) ∧
      y.Bounded w ∧
      y.frontier = x.frontier + Δ ∧
      y.regs (baseReg U V w N) = x.regs (baseReg U V w N) ∧
      y.regs (frontierReg U V w N) = x.frontier + Δ ∧
      y.mem = x.mem := by
  have hΔ_fits : Fits w Δ := hfit.of_le (Nat.le_add_left Δ x.frontier)
  set x₀ := x.set (hqReg U V w N) Δ
  have hx₀_bdd : x₀.Bounded w := hx.set hΔ_fits
  have e₀ : RDemonicExec (B := .standard) w (.op (.const (hqReg U V w N) Δ)) x 1 (· = x₀) :=
    RDemonicExec.const hΔ_fits
  have hx₀_cnt : x₀.regs (hqReg U V w N) = Δ := by simp [x₀]
  have e_gz := growZeroCode_exec (w := w)
    (count := hqReg U V w N) (result := resTagReg U V w N) (cur := curReg U V w N)
    (stop := frontierReg U V w N) (zero := zeroReg U V w N) (one := oneReg U V w N)
    hx₀_bdd (nodup_growTailRegs U V w N) h1
    (by rw [hx₀_cnt, Nat.add_comm]; exact hfit)
  dsimp only at e_gz
  rw [hx₀_cnt] at e_gz
  let regs₁ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      x₀.regs (zeroReg U V w N) 0) (oneReg U V w N) 1) (resTagReg U V w N) x.frontier)
      (frontierReg U V w N) (x.frontier + Δ)) (curReg U V w N) (x.frontier + Δ)
  let y : RData (rSuccinct U V w N) := ⟨regs₁, x₀.mem, x.frontier + Δ⟩
  have hy_bdd : y.Bounded w := by
    have h0 := hx₀_bdd.set (i := zeroReg U V w N) (fits_zero w)
    have h1' := h0.set (i := oneReg U V w N) h1
    have h2 := h1'.set (i := resTagReg U V w N) hx.frontier_fits
    have h3 := h2.set (i := frontierReg U V w N) hfit
    have h4 := h3.set (i := curReg U V w N) hfit
    refine ⟨h4.1, hfit, fun a ha => ?_⟩
    dsimp only [y] at ha
    exact hx.zero_above (by omega)
  refine ⟨y, (e₀.seq_eq e_gz).mono (by omega) (fun _ h => h),
    hy_bdd, rfl, ?_, ?_, rfl⟩
  · dsimp only [y, regs₁, x₀, baseReg, hqReg, zeroReg, oneReg, resTagReg, frontierReg, curReg]
    simp only [RData.set_regs, Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte]
  · dsimp only [y, regs₁, frontierReg, curReg]
    simp only [Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte]

/-- Shrink the active item region at `x.frontier` by `Δ` words via `RCode.shrink` while preserving
`baseReg`. -/
@[expose]
noncomputable def shrinkTailWordsCode (U V w N Δ : ℕ) : RCode .standard (rSuccinct U V w N) :=
  .seq (.op (.const (curReg U V w N) Δ))
       (.shrink (curReg U V w N))

/-- **Item-tail contraction via `.shrink` (`shrinkTailWordsCode_exec`):**
Contracts `x.frontier` by `Δ ≤ x.frontier` words in `2` instructions, clearing
`[x.frontier - Δ, x.frontier)` to `0` and preserving `baseReg` and all words `< x.frontier - Δ`. -/
theorem shrinkTailWordsCode_exec {U V w N Δ : ℕ} {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (hΔ : Δ ≤ x.frontier) :
    ∃ y : RData (rSuccinct U V w N),
      RDemonicExec w (shrinkTailWordsCode U V w N Δ) x 2 (· = y) ∧
      y.Bounded w ∧
      y.frontier = x.frontier - Δ ∧
      y.regs (baseReg U V w N) = x.regs (baseReg U V w N) ∧
      y.mem = clear x.mem (x.frontier - Δ) Δ ∧
      ∀ a < x.frontier - Δ, y.mem a = x.mem a := by
  have hΔ_fits : Fits w Δ := hx.frontier_fits.of_le hΔ
  set x₁ := x.set (curReg U V w N) Δ
  have hx₁_bdd : x₁.Bounded w := hx.set hΔ_fits
  have e₁ : RDemonicExec (B := .standard) w (.op (.const (curReg U V w N) Δ)) x 1 (· = x₁) :=
    RDemonicExec.const hΔ_fits
  have hx₁_cur : x₁.regs (curReg U V w N) = Δ := by simp [x₁]
  let y : RData (rSuccinct U V w N) := ⟨x₁.regs, clear x.mem (x.frontier - Δ) Δ, x.frontier - Δ⟩
  have e₂ : RDemonicExec (B := .standard) w (.shrink (curReg U V w N)) x₁ 1 (· = y) := by
    refine RDemonicExec.shrink (by rw [hx₁_cur]; exact hΔ) ?_
    ext a <;> simp [y, x₁, hx₁_cur]
  have hy_bdd : y.Bounded w := by
    simpa [y, x₁] using hx₁_bdd.shrink hΔ
  refine ⟨y, (e₁.seq_eq e₂).mono le_rfl (fun _ h => h), hy_bdd, rfl, ?_, rfl, fun a ha => ?_⟩
  · dsimp only [y, x₁, baseReg, curReg]
    simp only [RData.set_regs, Function.update_apply, sReg_inj, Fin.reduceEq, ↓reduceIte]
  · exact clear_of_not_owns (by simp only [Block.Owns]; omega)

/-! ## Section 3: Resizable Succinct Representation on `RData` and Single-Epoch Lifecycle -/

/-- Representation invariant for the succinct dynamic dictionary at base address `base` on the
word-granular resizable Word-RAM state `x : RData (rSuccinct U V w N)`:
1. `x.Bounded w`: all registers and memory words fit in `w` bits, `x.frontier < 2 ^ w`, and all
   unallocated words `a ≥ x.frontier` are `0`;
2. `x.frontier = base + Succinct.space U V w N`: the active linear memory is `[0, base + space)`;
3. `Succinct.Rep U V w N base θ s_abs x.toData`: `x.toData` represents abstract dictionary state
   `s_abs : Dynamic.State U` under quotient hash seed `θ : QuotHashSeed U N`. -/
@[expose]
def ResizableRep (U V w N base : ℕ) (θ : QuotHashSeed U N)
    (s_abs : Dynamic.State U) (x : RData (rSuccinct U V w N)) : Prop :=
  x.Bounded w ∧
  x.frontier = base + Succinct.space U V w N ∧
  Succinct.Rep U V w N base θ s_abs x.toData

/-- Lift a `Data (rSuccinct U V w N)` satisfying `Succinct.Rep` and `Modifies` over a bounded
`RData` with `frontier = base + Succinct.space U V w N` back to a bounded `RData`. -/
theorem rData_bounded_of_rep_modifies {U V w N base : ℕ} {θ : QuotHashSeed U N}
    {s_abs : Dynamic.State U} {x : RData (rSuccinct U V w N)} {y : Data (rSuccinct U V w N)}
    (hx : x.Bounded w) (hfr : x.frontier = base + Succinct.space U V w N)
    (hrep : Succinct.Rep U V w N base θ s_abs y)
    (hmod : Modifies (Block.mk base (Succinct.space U V w N)).footprint x.mem y.mem) :
    (⟨y.regs, y.mem, base + Succinct.space U V w N⟩ : RData (rSuccinct U V w N)).Bounded w := by
  refine ⟨hrep.1, hfr ▸ hx.frontier_fits, fun a ha => ?_⟩
  dsimp only at ha ⊢
  have hnot : a ∉ (Block.mk base (Succinct.space U V w N)).footprint := by
    simp only [Block.mem_footprint, Block.Owns]
    omega
  rw [hmod a hnot]
  exact hx.zero_above (by omega)

/-- Multi-step `ExecStepsOfFn` preserves `Modifies (Block.mk base C.space).footprint` from an
initial memory `mem₀`. -/
theorem execStepsOfFn_modifies {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec}
    {w base : ℕ} {params : Fin k_init → ℕ} {s₀ : D.State}
    {C : Randomized.StateTransitionImpl P D w base params s₀}
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {s : D.State} {ops : List D.Op} {ν₀ ν_final : PMF (C.Seed × Data r_ds)}
    {T_ops : ℝ≥0∞} {mem₀ : ℕ → ℕ}
    (hex : C.ExecStepsOfFn s ops ν₀ ν_final T_ops)
    (h₀ : ∀ p ∈ ν₀.support, Modifies (Block.mk base C.space).footprint mem₀ p.2.mem) :
    ∀ q ∈ ν_final.support, Modifies (Block.mk base C.space).footprint mem₀ q.2.mem := by
  induction hex with
  | nil _ _ => exact h₀
  | @cons _ _ _ ν _ μ_step _ _ hstep _ ih =>
    refine ih fun q hq => ?_
    rw [PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq_step⟩ := hq
    exact fun a ha => (((hstep p hp).2 q hq_step).2.2 a ha).trans (h₀ p hp a ha)

/-- Multi-step `ExecStepsOfFn` preserves any memory value `p.2.mem a = v` at an address
`a ∉ (Block.mk base C.space).footprint`. -/
theorem execStepsOfFn_outside {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec}
    {w base : ℕ} {params : Fin k_init → ℕ} {s₀ : D.State}
    {C : Randomized.StateTransitionImpl P D w base params s₀}
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {s : D.State} {ops : List D.Op} {ν₀ ν_final : PMF (C.Seed × Data r_ds)}
    {T_ops : ℝ≥0∞} {a v : ℕ}
    (ha : a ∉ (Block.mk base C.space).footprint)
    (hex : C.ExecStepsOfFn s ops ν₀ ν_final T_ops)
    (h₀ : ∀ p ∈ ν₀.support, p.2.mem a = v) :
    ∀ q ∈ ν_final.support, q.2.mem a = v := by
  induction hex with
  | nil _ _ => exact h₀
  | @cons _ _ _ ν _ μ_step _ _ hstep _ ih =>
    refine ih fun q hq => ?_
    rw [PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq_step⟩ := hq
    exact (((hstep p hp).2 q hq_step).2.2 a ha).trans (h₀ p hp)

/-- **Demonic-grow initialization on `RData` (`init_resizable_succinct`):**
Starting from `x : RData (rSuccinct U V w N)` with `x.Bounded w` and `x.frontier = base`:
1. `allocSuccinctCode U V w N` executes in `4 * Succinct.space U V w N + 8` instructions under
   **demonic** `DemonicGrow` (`RDemonicExec`), extending `frontier` to
   `base + Succinct.space U V w N` and zeroing the demonically initialized words;
2. `(subroutineCode U V w N).initSetup` executes on `x₁.toData` in at most `initSteps U N`
   instructions (`ExecCodeDist`), producing a coupled distribution `ν₀` over
   `QuotHashSeed U N × RData (rSuccinct U V w N)` where every `(θ, y) ∈ ν₀.support` satisfies
   `ResizableRep U V w N base θ (Dynamic.empty U) y`, `potential = 0`, and preserves all caller
   memory outside `[base, base + Succinct.space U V w N)`. -/
theorem init_resizable_succinct {U V w N base : ℕ}
    (hw : 0 < w) (hnU : N ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + Succinct.space U V w N))
    {x : RData (rSuccinct U V w N)} (hx : x.Bounded w) (hfr : x.frontier = base) :
    ∃ (x₁ : RData (rSuccinct U V w N))
      (ν₀ : PMF (QuotHashSeed U N × RData (rSuccinct U V w N))),
      RDemonicExec w (allocSuccinctCode U V w N) x (4 * Succinct.space U V w N + 8) (· = x₁) ∧
      ExecCodeDist w (subroutineCode U V w N).initSetup x₁.toData
        ((ν₀.map Prod.snd).map RData.toData) (initSteps U N : ℝ≥0∞) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ (PMF.uniformOfFintype (QuotHashSeed U N)) θ) ∧
      ∀ p ∈ ν₀.support,
        ResizableRep U V w N base p.1 (Dynamic.empty U) p.2 ∧
        potential U V w N base p.1 p.2.toData = 0 ∧
        Modifies (Block.mk base (Succinct.space U V w N)).footprint x.mem p.2.mem := by
  have hwf : DictParamsWf U V w N := ⟨hw, hnU, hU, le_of_lt hV⟩
  obtain ⟨x₁, he_alloc, hx₁_bdd, hx₁_fr, hx₁_base, hx₁_fr_reg, hx₁_mem, hx₁_zero⟩ :=
    allocSuccinctCode_exec hx hfr hfit
  obtain ⟨ν_raw, he_setup, hseed_raw, hsupp_raw⟩ :=
    setup_exec_succinct hwf hfit hx₁_bdd.1 hx₁_base hx₁_fr_reg hx₁_zero
  let liftR (p : QuotHashSeed U N × Data (rSuccinct U V w N)) :
      QuotHashSeed U N × RData (rSuccinct U V w N) :=
    (p.1, ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N⟩)
  let ν₀ := ν_raw.map liftR
  refine ⟨x₁, ν₀, he_alloc, ?_, ?_, ?_⟩
  · refine he_setup.congr_dist ?_ ?_
    · dsimp only [ν₀, liftR]
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    · unfold initSteps
      norm_cast
      omega
  · intro θ
    have hs := hseed_raw θ
    rw [one_mul] at hs
    dsimp only [ν₀, liftR]
    rw [PMF.map_comp]
    exact hs
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hq_fr, hq_rep, hq_pot, hq_mod⟩ := hsupp_raw q hq
    have hy_bdd := rData_bounded_of_rep_modifies hx₁_bdd hx₁_fr hq_rep hq_mod
    dsimp only [liftR]
    change Modifies (Block.mk base (Succinct.space U V w N)).footprint x₁.mem q.2.mem at hq_mod
    rw [hx₁_mem] at hq_mod
    exact ⟨⟨hy_bdd, rfl, hq_rep⟩, Nat.eq_zero_of_le_zero hq_pot, hq_mod⟩

/-- **Per-operation execution on `RData` (`step_resizable_succinct`):**
Given `ResizableRep U V w N base θ s_abs x` and any valid `o : Dynamic.Op U` with
`argMatch U V w N o x.regs`, `opCode U V w N` executes on `x.toData` in `steps` instructions,
producing `y : RData (rSuccinct U V w N)` with `ResizableRep U V w N base θ s' y`, exact decoded
output, memory framing outside `[base, base + Succinct.space U V w N)`, and the amortized step
bound. -/
theorem step_resizable_succinct {U V w N base : ℕ}
    (hw : 0 < w) (hnU : N ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + Succinct.space U V w N))
    (θ : QuotHashSeed U N) (s_abs : Dynamic.State U) (o : Dynamic.Op U)
    (hval : (Dynamic.spec U V N).valid s_abs o)
    {x : RData (rSuccinct U V w N)}
    (hrep : ResizableRep U V w N base θ s_abs x)
    (harg : argMatch U V w N o x.regs) :
    ∃ (y : RData (rSuccinct U V w N)) (steps : ℕ),
      ExecWithin w (opCode U V w N) x.toData y.toData steps ∧
      decode U V w N o y.regs = some ((Dynamic.spec U V N).stepFn s_abs o).2 ∧
      ResizableRep U V w N base θ ((Dynamic.spec U V N).stepFn s_abs o).1 y ∧
      Modifies (Block.mk base (Succinct.space U V w N)).footprint x.mem y.mem ∧
      steps + potential U V w N base θ y.toData ≤
        potential U V w N base θ x.toData + (273 * opFactor U V w N + 284689) +
          (8 * opFactor U V w N) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
              (Dynamic.dom s_abs) (opKey o) := by
  have hwf : DictParamsWf U V w N := ⟨hw, hnU, hU, le_of_lt hV⟩
  obtain ⟨y_data, steps, hex, hdec, hy_rep, hmod, hpot⟩ :=
    exec_opCode hwf hfit θ s_abs o hval hrep.2.2 harg
  let y : RData (rSuccinct U V w N) := ⟨y_data.regs, y_data.mem, base + Succinct.space U V w N⟩
  have hy_bdd := rData_bounded_of_rep_modifies hrep.1 hrep.2.1 hy_rep hmod
  exact ⟨y, steps, hex, hdec, ⟨hy_bdd, rfl, hy_rep⟩, hmod, hpot⟩

/-- Multi-operation expected-amortized execution of `Succinct.impl` with explicit memory framing
`Modifies (Block.mk base (Succinct.space U V w n_max)).footprint x.mem p.2.mem`:
any valid operation sequence `ops` preserves `Succinct.Rep`, modifies only
`[base, base + Succinct.space U V w n_max)`, and bounds total expected cost. -/
theorem seq_expected_amortized_modifies {U V w n_max base : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + Succinct.space U V w n_max))
    {x : Data (rSuccinct U V w n_max)} (ops : List (Dynamic.Op U))
    (hx : x.Bounded w) (hfr : x.regs (frontierReg U V w n_max) = base)
    (hz : ∀ a ∈ (Block.mk base (Succinct.space U V w n_max)).footprint, x.mem a = 0)
    (hv : (Dynamic.spec U V n_max).ValidHistory (Dynamic.empty U) ops) :
    let C := Succinct.impl hw hnU hU hV hfit
    ∃ (ν₀ ν_final : PMF (C.Seed × Data (rSuccinct U V w n_max))) (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U V w n_max).initFresh x (ν₀.map Prod.snd) C.initTime ∧
      C.ExecStepsOfFn (Dynamic.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ) ∧
      (∀ p ∈ ν_final.support,
        Succinct.Rep U V w n_max base p.1
          ((Dynamic.spec U V n_max).run (Dynamic.empty U) ops).1 p.2 ∧
        Modifies (Block.mk base (Succinct.space U V w n_max)).footprint x.mem p.2.mem) ∧
      C.initTime + T_ops +
        (∑' q, ν_final q * (potential U V w n_max base q.1 q.2 : ℝ≥0∞)) ≤
        C.initTime + (ops.length * chargeVal U V w n_max : ℕ) := by
  intro C
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ := C.initFresh_exec hx hfr (fun j => Fin.elim0 j) hz
  obtain ⟨ν_final, T_ops, hex_steps, hseed_final, hrep_final, hamort⟩ :=
    C.steps_expected_amortized_ofFn ops ν₀ hv hseed₀ fun p hp => (hsupp₀ p hp).2.1
  have hmod_final := execStepsOfFn_modifies hex_steps fun p hp => (hsupp₀ p hp).2.2.2
  have hpot₀ : (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) = 0 := by
    refine tsum_eq_zero_iff.mpr fun p => ?_
    by_cases hp : p ∈ ν₀.support
    · have hp0 : C.potential p.1 p.2 ≤ 0 := (hsupp₀ p hp).2.2.1
      rw [Nat.eq_zero_of_le_zero hp0, Nat.cast_zero, mul_zero]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul]
  have hcost_gen : ∀ (l : List (Dynamic.Op U)) (s₀ : Dynamic.State U),
      (Dynamic.spec U V n_max).totalCost C.charge s₀ l =
        l.length * chargeVal U V w n_max := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons o os ih =>
      intro s₀
      rw [StateTransitionSpec.totalCost_cons, ih]
      change chargeVal U V w n_max + os.length * chargeVal U V w n_max =
        (o :: os).length * chargeVal U V w n_max
      simp only [List.length_cons]
      ring
  have hcost_eq := hcost_gen ops (Dynamic.empty U)
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final,
    fun p hp => ⟨hrep_final p hp, hmod_final p hp⟩, ?_⟩
  rw [hpot₀, add_zero, hcost_eq] at hamort
  calc C.initTime + T_ops + ∑' q, ν_final q * (potential U V w n_max base q.1 q.2 : ℝ≥0∞)
      = C.initTime + (T_ops + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) := by ac_rfl
    _ ≤ C.initTime + (ops.length * chargeVal U V w n_max : ℕ) := add_le_add le_rfl hamort

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
