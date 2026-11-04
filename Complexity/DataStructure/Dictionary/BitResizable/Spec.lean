/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Bit-Resizable Dynamic Dictionary Specification and Pointwise Bit-Space Accounting

This module defines the unbounded-capacity dynamic dictionary specification
(`Cslib.DataStructure.Dictionary.BitResizable.spec`) over key universe `Fin U` and value bound `V`,
together with the epoch capacity parameters and pointwise bit-level space accounting for a
bit-resizable succinct dictionary on the `w`-bit `BitRAM`.

## Architectural overview

In a bit-resizable succinct dictionary, the dictionary starts in `Dynamic.empty U` with `n_0 = 0`
keys and only a 4-word (`4 * w`-bit) header allocated in `[0, 4 * w)`. Whenever
`n_t = (dom s_t).card ≥ 1` keys are present, the dictionary maintains an epoch capacity parameter
`N` satisfying `n_t ≤ N ≤ 4 * n_t` and `N ≤ U`:

1. **Epoch metadata prefix (`[0, epochMetaBits U w N)`):** stores the 4-word header, the
   two-stage universe-reduced 3-wise independent hash family (`Succinct.hashSpace U w N`),
   the 9 micro-bucket local metadata sub-arrays (`9 * Succinct.lmSubWords N w`), the global
   slab/tail directory (`GlobalMeta`), and the two tail-compaction permutation arrays (`TailDense`
   and `DenseTail`, each of length `maxTailItems N` with `(globalPtrBits N)`-bit entries).
   Because `N ≤ 4 * n_t`, the entire epoch metadata prefix occupies
   `O(N log₂ log₂(max N 4)) + O(w) = O(n_t log₂ log₂(max n_t 4)) + O(w)` bits.
2. **Dense bit-resizable item suffix (`[epochMetaBits U w N, dictBitSize U V w N n_t)`):**
   stores **only the `n_t` active `(quotient, value)` items**, each of width
   `itemBits U V N = quotientBits U N + valBits V` bits.
   * Each insertion of a new key grows the bit-resizable memory by `itemBits U V N` bits
     (via two single-step `BitMemory.grow` calls of widths `quotientBits U N ≤ w` and
     `valBits V ≤ w`) and immediately overwrites the newly grown bits.
   * Each deletion of a present key compacts the vacated dense item slot with the last active
     dense slot `n_t - 1` and shrinks the bit-resizable memory by `itemBits U V N` bits,
     immediately releasing those `itemBits U V N` bits back to the unallocated suffix
     `[s_t.bitSize, ∞)` for reuse by other data structures.
   * Because `n_t ≤ N ≤ 4 * n_t`, `bucketBits n_t ≤ bucketBits N + 3`, so each stored quotient
     uses at most `quotientBits U n_t + 3` bits, and the `n_t` active items occupy at most
     `Dynamic.optBits U V n_t + 8 * n_t * Dynamic.logLogFactor n_t` bits.

Combining the metadata prefix and dense item suffix yields the pointwise bit bound at **every**
step `t` (including `n_t = 0`):
`dictBitSize U V w N n_t ≤`
`Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.valid`, `spec`: unbounded-capacity dynamic
  dictionary admissibility predicate and `StateTransitionSpec` (`insert`, `delete`, `query` from
  `Dynamic.empty U`).
* `Cslib.DataStructure.Dictionary.BitResizable.itemBits`, `epochMetaWords`, `epochMetaBits`,
  `dictBitSize`, `EpochInv`: per-item bit width, epoch metadata footprint, total bit footprint
  at current size `n_t`, and epoch capacity invariant `n_t ≤ N ≤ 4 * n_t`.

## Main results

* `valid_iff_dynamic_valid`, `validHistory_iff_dynamic_validHistory`, `run_eq_dynamic_run`:
  equivalence between the unbounded-capacity specification `spec U V` and `Dynamic.spec U V U`.
* `logLogFactor_le_succ_of_le_four_mul`, `bucketBits_le_add_three_of_between`,
  `quotientBits_le_add_three_of_between`: scale-invariance of `logLogFactor`, `bucketBits`, and
  `quotientBits` across an epoch `n_t ≤ N ≤ 4 * n_t`.
* `mul_itemBits_le_optBits`: `n_t` dense `(quotient, value)` items under epoch parameter `N`
  occupy at most `Dynamic.optBits U V n_t + 8 * n_t * Dynamic.logLogFactor n_t` bits.
* `epochMetaBits_le`: the epoch metadata prefix occupies at most
  `84 * N * Dynamic.logLogFactor N + 218 * w` bits.
* `dictBitSize_le_optBits`: at every step `t` (`n_t = (Dynamic.dom s_t).card`),
  `dictBitSize U V w N n_t ≤`
  `Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM

/-! ## Section 1: Unbounded-capacity dynamic dictionary specification -/

/-- Admissibility precondition for an unbounded-capacity dynamic dictionary over `Fin U` with
values bounded by `V`: `query` and `delete` are always admissible, and `insert u v` requires only
`v < V` (with no capacity restriction on `(Dynamic.dom s).card`). -/
abbrev valid {U : ℕ} (V : ℕ) (_s : Dynamic.State U) : Dynamic.Op U → Prop
  | .query _ => True
  | .insert _ v => v < V
  | .delete _ => True

/-- Unbounded-capacity dynamic dictionary specification over key universe `Fin U` and value bound
`V`, supporting `insert`, `delete`, and `query` starting from `Dynamic.empty U`. -/
abbrev spec (U V : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := Dynamic.State U) (Op := Dynamic.Op U)
    (Result := Dynamic.Op.Result) Dynamic.step (valid V)

/-- Unbounded-capacity admissibility `valid V s o` is equivalent to bounded-capacity admissibility
`(Dynamic.spec U V U).valid s o` with capacity `n_max = U`, since a dictionary over `Fin U` can hold
at most `U` distinct keys. -/
theorem valid_iff_dynamic_valid {U V : ℕ} (s : Dynamic.State U) (o : Dynamic.Op U) :
    (spec U V).valid s o ↔ (Dynamic.spec U V U).valid s o := by
  cases o with
  | query u => rfl
  | insert u v => exact (Dynamic.valid_insert_iff_of_le le_rfl s u v).symm
  | delete u => rfl

/-- `(spec U V).run` coincides with `(Dynamic.spec U V U).run` on every initial state and operation
sequence. -/
@[simp]
theorem run_eq_dynamic_run {U V : ℕ} (s : Dynamic.State U) (os : List (Dynamic.Op U)) :
    (spec U V).run s os = (Dynamic.spec U V U).run s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [StateTransitionSpec.run]
    have hstep : (spec U V).stepFn s o = (Dynamic.spec U V U).stepFn s o := rfl
    rw [hstep, ih]

/-- An operation sequence `os` is a valid history under `spec U V` if and only if it is a valid
history under `Dynamic.spec U V U`. -/
theorem validHistory_iff_dynamic_validHistory {U V : ℕ} (s : Dynamic.State U)
    (os : List (Dynamic.Op U)) :
    (spec U V).ValidHistory s os ↔ (Dynamic.spec U V U).ValidHistory s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [StateTransitionSpec.ValidHistory]
    have hv := valid_iff_dynamic_valid (V := V) s o
    have hstep : (spec U V).stepFn s o = (Dynamic.spec U V U).stepFn s o := rfl
    rw [hstep]
    exact and_congr hv (ih _)

/-- Every reachable state from `Dynamic.empty U` has at most `U` active keys. -/
theorem card_dom_run_empty_le_univ {U V : ℕ} (os : List (Dynamic.Op U)) :
    (Dynamic.dom ((spec U V).run (Dynamic.empty U) os).1).card ≤ U :=
  Dynamic.card_dom_le_univ _

/-- Every admissible operation sequence from `Dynamic.empty U` under `spec U V` preserves
`Dynamic.ValuesBounded V`. -/
theorem valuesBounded_run_empty {U V : ℕ} {os : List (Dynamic.Op U)}
    (hvh : (spec U V).ValidHistory (Dynamic.empty U) os) :
    Dynamic.ValuesBounded V ((spec U V).run (Dynamic.empty U) os).1 := by
  rw [run_eq_dynamic_run]
  exact Dynamic.valuesBounded_run_empty ((validHistory_iff_dynamic_validHistory _ _).mp hvh)

/-! ## Section 2: Epoch capacity parameters and bit-level layout sizes -/

/-- Bit width `quotientBits U N + valBits V` of a single dense `(quotient, value)` item under epoch
capacity parameter `N`. -/
@[expose]
def itemBits (U V N : ℕ) : ℕ :=
  quotientBits U N + valBits V

/-- Word footprint of the epoch metadata prefix under epoch capacity parameter `N`:
* when `N = 0` (the empty-dictionary epoch `n_t = 0`), only the 4-word header `[0, 4)` is
  allocated;
* when `N > 0`, the prefix stores the 4-word header, the two-stage quotient hash family
  `Succinct.hashSpace U w N`, the 9 `LocalMeta` sub-arrays `9 * Succinct.lmSubWords N w`,
  `GlobalMeta`, and the two tail-compaction bijection arrays `TailDense` and `DenseTail` (each of
  length `maxTailItems N` with `globalPtrBits N`-bit entries). -/
@[expose]
def epochMetaWords (U w N : ℕ) : ℕ :=
  if N = 0 then 4
  else
    4 + Succinct.hashSpace U w N +
      9 * Succinct.lmSubWords N w +
      packedWords (globalMetaLen N) (globalPtrBits N) w +
      2 * packedWords (maxTailItems N) (globalPtrBits N) w

/-- Bit footprint `epochMetaWords U w N * w` of the word-aligned epoch metadata prefix. -/
@[expose]
def epochMetaBits (U w N : ℕ) : ℕ :=
  epochMetaWords U w N * w

/-- Exact bit footprint `epochMetaBits U w N + n_t * itemBits U V N` of the bit-resizable
succinct dictionary when `n_t` keys are present in an epoch with capacity parameter `N`. -/
@[expose]
def dictBitSize (U V w N n_t : ℕ) : ℕ :=
  epochMetaBits U w N + n_t * itemBits U V N

/-- Epoch capacity invariant relating the current active key count `n_t = (Dynamic.dom s_t).card`
to the epoch capacity parameter `N`: either `n_t = 0 ∧ N = 0`, or `1 ≤ n_t ≤ N ≤ 4 * n_t` and
`N ≤ U`. -/
@[expose]
def EpochInv (U N n_t : ℕ) : Prop :=
  (n_t = 0 ∧ N = 0) ∨ (1 ≤ n_t ∧ n_t ≤ N ∧ N ≤ 4 * n_t ∧ N ≤ U)

/-- In the empty state (`n_t = 0`, `N = 0`), `EpochInv U 0 0` holds. -/
theorem epochInv_zero (U : ℕ) : EpochInv U 0 0 :=
  Or.inl ⟨rfl, rfl⟩

/-- When `U ≤ 2 ^ w` and `V ≤ 2 ^ w`, a single item's quotient part fits in one `w`-bit word
(`quotientBits U N ≤ w`) and its value part fits in one `w`-bit word (`valBits V ≤ w`), so
`itemBits U V N ≤ 2 * w`. -/
theorem itemBits_le_two_mul_w {U V w N : ℕ} (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) :
    itemBits U V N ≤ 2 * w := by
  unfold itemBits
  have hq := quotientBits_le_of_le_pow (n := N) hU
  have hv := valBits_le_of_le_pow hV
  omega

/-! ## Section 3: Scale-invariance across an epoch `n_t ≤ N ≤ 4 * n_t` -/

/-- Whenever `N ≤ 4 * n`, `Nat.clog 2 (max N 4) ≤ Nat.clog 2 (max n 4) + 2`. -/
theorem clog_max_four_le_add_two {n N : ℕ} (hN : N ≤ 4 * n) :
    Nat.clog 2 (max N 4) ≤ Nat.clog 2 (max n 4) + 2 := by
  refine Nat.clog_le_of_le_pow ?_
  have hm : max N 4 ≤ 4 * max n 4 := by omega
  have hc : max n 4 ≤ 2 ^ Nat.clog 2 (max n 4) := Nat.le_pow_clog (by decide) (max n 4)
  calc max N 4
      ≤ 4 * max n 4 := hm
    _ ≤ 4 * 2 ^ Nat.clog 2 (max n 4) := Nat.mul_le_mul_left 4 hc
    _ = 2 ^ (Nat.clog 2 (max n 4) + 2) := by
        rw [Nat.pow_add]
        ring

/-- For every `n : ℕ`, `2 ≤ Nat.clog 2 (max n 4)`. -/
theorem two_le_clog_max_four (n : ℕ) : 2 ≤ Nat.clog 2 (max n 4) := by
  calc 2 = Nat.clog 2 4 := by decide
    _ ≤ Nat.clog 2 (max n 4) := Nat.clog_mono_right 2 (le_max_right n 4)

/-- Whenever `N ≤ 4 * n`, `Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 1`. -/
theorem logLogFactor_le_succ_of_le_four_mul {n N : ℕ} (hN : N ≤ 4 * n) :
    Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 1 := by
  unfold Dynamic.logLogFactor
  refine Nat.clog_le_of_le_pow ?_
  have h1 := clog_max_four_le_add_two hN
  have h2 := two_le_clog_max_four n
  have h3 : Nat.clog 2 (max n 4) ≤ 2 ^ Nat.clog 2 (Nat.clog 2 (max n 4)) :=
    Nat.le_pow_clog (by decide) _
  calc Nat.clog 2 (max N 4)
      ≤ Nat.clog 2 (max n 4) + 2 := h1
    _ ≤ 2 * Nat.clog 2 (max n 4) := by omega
    _ ≤ 2 * 2 ^ Nat.clog 2 (Nat.clog 2 (max n 4)) := Nat.mul_le_mul_left 2 h3
    _ = 2 ^ (Nat.clog 2 (Nat.clog 2 (max n 4)) + 1) := by
        rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm]

/-- Whenever `N ≤ 4 * n`, `Dynamic.logLogFactor N ≤ 2 * Dynamic.logLogFactor n`. -/
theorem logLogFactor_le_two_mul_of_le_four_mul {n N : ℕ} (hN : N ≤ 4 * n) :
    Dynamic.logLogFactor N ≤ 2 * Dynamic.logLogFactor n := by
  have h1 := logLogFactor_le_succ_of_le_four_mul hN
  have h2 := Dynamic.one_le_logLogFactor n
  omega

/-- Whenever `1 ≤ n ≤ N ≤ 4 * n`, `bucketBits n ≤ bucketBits N + 3`. -/
theorem bucketBits_le_add_three_of_between {n N : ℕ} (hnN : n ≤ N) (hN : N ≤ 4 * n) :
    bucketBits n ≤ bucketBits N + 3 := by
  unfold bucketBits
  have hlog : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN
  have hll : Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 1 :=
    logLogFactor_le_succ_of_le_four_mul hN
  omega

/-- Whenever `n ≤ N ≤ 4 * n`, `quotientBits U N ≤ quotientBits U n + 3`. -/
theorem quotientBits_le_add_three_of_between {U n N : ℕ} (hnN : n ≤ N) (hN : N ≤ 4 * n) :
    quotientBits U N ≤ quotientBits U n + 3 := by
  unfold quotientBits
  have hb := bucketBits_le_add_three_of_between hnN hN
  omega

/-- **Dense item bit-budget theorem (`mul_itemBits_le_optBits`):**
whenever `n ≤ U` and `n ≤ N ≤ 4 * n`, storing `n` dense `(quotient, value)` items of width
`itemBits U V N = quotientBits U N + valBits V` uses at most
`Dynamic.optBits U V n + 8 * n * Dynamic.logLogFactor n` bits. -/
theorem mul_itemBits_le_optBits {U V n N : ℕ} (hnU : n ≤ U) (hnN : n ≤ N) (hN : N ≤ 4 * n) :
    n * itemBits U V N ≤ Dynamic.optBits U V n + 8 * n * Dynamic.logLogFactor n := by
  have hqv := quotient_val_bits_le_optBits (V := V) hnU
  have hq := quotientBits_le_add_three_of_between (U := U) hnN hN
  have hll := Dynamic.one_le_logLogFactor n
  have hitem : itemBits U V N ≤ (quotientBits U n + valBits V) + 3 := by
    unfold itemBits
    omega
  have hmul : n * itemBits U V N ≤ n * (quotientBits U n + valBits V) + 3 * n := by
    calc n * itemBits U V N
        ≤ n * ((quotientBits U n + valBits V) + 3) := Nat.mul_le_mul_left n hitem
      _ = n * (quotientBits U n + valBits V) + 3 * n := by ring
  have h3n : 3 * n ≤ 3 * n * Dynamic.logLogFactor n := by
    calc 3 * n = (3 * n) * 1 := by ring
      _ ≤ (3 * n) * Dynamic.logLogFactor n := Nat.mul_le_mul_left (3 * n) hll
  have h8 : 5 * n * Dynamic.logLogFactor n + 3 * n * Dynamic.logLogFactor n =
      8 * n * Dynamic.logLogFactor n := by ring
  omega

/-! ## Section 4: Epoch metadata bit bound and pointwise succinct bit bound -/

/-- Every `packedWords m k w` block of `w`-bit words occupies at most `m * k + 3 * w` bits. -/
theorem packedWords_mul_le (m k w : ℕ) :
    packedWords m k w * w ≤ m * k + 3 * w := by
  unfold packedWords
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have hdiv : (m * k + w - 1) / w * w ≤ m * k + w - 1 := Nat.div_mul_le_self _ w
    rw [Nat.add_mul]
    omega

/-- The 9 `LocalMeta` sub-arrays of length `totalMicroBuckets N` and width `effBucketPosBits N`
occupy at most `54 * N * Dynamic.logLogFactor N + 27 * w` bits. -/
theorem lmSubWords_bits_le (N w : ℕ) :
    9 * Succinct.lmSubWords N w * w ≤ 54 * N * Dynamic.logLogFactor N + 27 * w := by
  unfold Succinct.lmSubWords
  have hpw := packedWords_mul_le (totalMicroBuckets N) (effBucketPosBits N) w
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]
    ring
  have hlm := localMetaLen_mul_effBucketPosBits_le N
  calc 9 * packedWords (totalMicroBuckets N) (effBucketPosBits N) w * w
      = 9 * (packedWords (totalMicroBuckets N) (effBucketPosBits N) w * w) := by ring
    _ ≤ 9 * (totalMicroBuckets N * effBucketPosBits N + 3 * w) := Nat.mul_le_mul_left 9 hpw
    _ = (9 * totalMicroBuckets N) * effBucketPosBits N + 27 * w := by ring
    _ = localMetaLen N * effBucketPosBits N + 27 * w := by rw [hlm_eq]
    _ ≤ 54 * N * Dynamic.logLogFactor N + 27 * w := by omega

/-- `GlobalMeta` occupies at most `20 * N * Dynamic.logLogFactor N + 3 * w` bits. -/
theorem globalMeta_bits_le (N w : ℕ) :
    packedWords (globalMetaLen N) (globalPtrBits N) w * w ≤
      20 * N * Dynamic.logLogFactor N + 3 * w := by
  have hpw := packedWords_mul_le (globalMetaLen N) (globalPtrBits N) w
  have hgm := globalMetaLen_mul_globalPtrBits_le N
  omega

/-- The two tail-compaction arrays (`TailDense` and `DenseTail`) occupy at most `8 * N + 6 * w`
bits. -/
theorem tailDense_bits_le (N w : ℕ) :
    2 * packedWords (maxTailItems N) (globalPtrBits N) w * w ≤ 8 * N + 6 * w := by
  have hpw := packedWords_mul_le (maxTailItems N) (globalPtrBits N) w
  have htd := maxTailItems_mul_globalPtrBits_le N
  calc 2 * packedWords (maxTailItems N) (globalPtrBits N) w * w
      = 2 * (packedWords (maxTailItems N) (globalPtrBits N) w * w) := by ring
    _ ≤ 2 * (maxTailItems N * globalPtrBits N + 3 * w) := Nat.mul_le_mul_left 2 hpw
    _ ≤ 2 * (4 * N + 3 * w) := by omega
    _ = 8 * N + 6 * w := by ring

/-- The quotient hash family (`Succinct.hashSpace U w N`) occupies at most `2 * N + 178 * w` bits
whenever `0 < w`, `N ≤ U`, and `U ≤ 2 ^ w`. -/
theorem hashSpace_bits_le {U w N : ℕ} (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    Succinct.hashSpace U w N * w ≤ 2 * N + 178 * w := by
  have hh := Succinct.hashSpace_le hw hNU hU
  have hpw := packedWords_mul_le (2 * N) 1 w
  calc Succinct.hashSpace U w N * w
      ≤ (175 + packedWords (2 * N) 1 w) * w := Nat.mul_le_mul_right w hh
    _ = 175 * w + packedWords (2 * N) 1 w * w := by ring
    _ ≤ 175 * w + (2 * N * 1 + 3 * w) := by omega
    _ = 2 * N + 178 * w := by ring

/-- **Epoch metadata bit-budget theorem (`epochMetaBits_le`):**
for every `0 < w`, `N ≤ U`, and `U ≤ 2 ^ w`, the epoch metadata prefix occupies at most
`84 * N * Dynamic.logLogFactor N + 218 * w` bits. -/
theorem epochMetaBits_le {U w N : ℕ} (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    epochMetaBits U w N ≤ 84 * N * Dynamic.logLogFactor N + 218 * w := by
  unfold epochMetaBits epochMetaWords
  split_ifs with hN0
  · subst hN0
    omega
  · have hh := hashSpace_bits_le hw hNU hU
    have hlm := lmSubWords_bits_le N w
    have hgm := globalMeta_bits_le N w
    have htd := tailDense_bits_le N w
    have hll := Dynamic.one_le_logLogFactor N
    have h10N : 10 * N ≤ 10 * N * Dynamic.logLogFactor N := by
      calc 10 * N = (10 * N) * 1 := by ring
        _ ≤ (10 * N) * Dynamic.logLogFactor N := Nat.mul_le_mul_left (10 * N) hll
    have h84 :
        54 * N * Dynamic.logLogFactor N + 20 * N * Dynamic.logLogFactor N +
          10 * N * Dynamic.logLogFactor N =
        84 * N * Dynamic.logLogFactor N := by ring
    have hexpand :
        (4 + Succinct.hashSpace U w N + 9 * Succinct.lmSubWords N w +
          packedWords (globalMetaLen N) (globalPtrBits N) w +
          2 * packedWords (maxTailItems N) (globalPtrBits N) w) * w =
        4 * w + Succinct.hashSpace U w N * w +
          (9 * Succinct.lmSubWords N w * w) +
          packedWords (globalMetaLen N) (globalPtrBits N) w * w +
          (2 * packedWords (maxTailItems N) (globalPtrBits N) w * w) := by ring
    rw [hexpand]
    omega

/-- **Pointwise succinct bit-space theorem (`dictBitSize_le_optBits`):**
at every step `t` with current key count `n_t` and epoch capacity parameter `N` satisfying
`EpochInv U N n_t` (`n_t = 0 ∧ N = 0`, or `1 ≤ n_t ≤ N ≤ 4 * n_t` and `N ≤ U`), the total
bit-resizable memory footprint `dictBitSize U V w N n_t` is at most
`Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w` bits. -/
theorem dictBitSize_le_optBits {U V w N n_t : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hepoch : EpochInv U N n_t) :
    dictBitSize U V w N n_t ≤
      Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w := by
  unfold dictBitSize
  rcases hepoch with ⟨rfl, rfl⟩ | ⟨_hn1, hnN, hN4, hNU⟩
  · unfold epochMetaBits epochMetaWords
    simp only [ ↓reduceIte, Nat.zero_mul, Nat.add_zero]
    omega
  · have hnU : n_t ≤ U := hnN.trans hNU
    have hmeta := epochMetaBits_le hw hNU hU
    have hitems := mul_itemBits_le_optBits (V := V) hnU hnN hN4
    have hll : Dynamic.logLogFactor N ≤ 2 * Dynamic.logLogFactor n_t :=
      logLogFactor_le_two_mul_of_le_four_mul hN4
    have hN_ll : 84 * N * Dynamic.logLogFactor N ≤ 672 * n_t * Dynamic.logLogFactor n_t := by
      calc 84 * N * Dynamic.logLogFactor N
          ≤ 84 * (4 * n_t) * (2 * Dynamic.logLogFactor n_t) := by
            have h1 : 84 * N ≤ 84 * (4 * n_t) := Nat.mul_le_mul_left 84 hN4
            exact Nat.mul_le_mul h1 hll
        _ = 672 * n_t * Dynamic.logLogFactor n_t := by ring
    have h680 :
        672 * n_t * Dynamic.logLogFactor n_t + 8 * n_t * Dynamic.logLogFactor n_t =
        680 * n_t * Dynamic.logLogFactor n_t := by ring
    omega

end Cslib.DataStructure.Dictionary.BitResizable
