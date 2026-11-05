/-
Copyright (c) 2026 Representation-Cost Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Representation-Cost Contributors
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinct

/-!
# Live `[0, n_t)` Active-Item Word Compaction for the Resizable Succinct Dictionary

This module implements genuine word-granular active-item compaction for the resizable succinct
dynamic dictionary on the `w`-bit resizable Word-RAM (`RData`), ensuring that at **every** step `t`
of an operation sequence `ops`, the live invariant-satisfying machine state `x_t` itself occupies
at most
`Dynamic.succinctWords 1355 381 U V w n_t` words
(`≤ Dynamic.optBits U V n_t + 1355 * n_t * Dynamic.logLogFactor n_t + 382 * w` bits, and `4` words
when `n_t = 0`), without any post-hoc `.shrink` that drops the dictionary invariant.

## Architecture

1. **Metadata Prefix before Dense Active Items:**
   At `base`, the layout stores:
   - `[base, base + 4)`: 4-word epoch control header (`N_t`, `n_t`, `n_init_t`, `min t 3`). When
     `n_t = 0` (`N_t = 0`), the entire dictionary occupies only `[base, base + 4)` (`4` words).
   - `[base + 4, base + 164)`: 160-word precomputed epoch parameter header (`DictParams` and
     `ReducedKWise` hash evaluation parameters).
   - `[base + 164, base + offCompItems U w N_t)`: epoch metadata prefix (`Hash`, `LocalMeta`,
     `GlobalMeta`, and the two active-slot compaction maps `TailToDense` and `DenseToTail` of
     length `maxTailItems N_t` and bit-width `globalPtrBits N_t`, adding at most `8 * N_t` bits).
   - `[base + offCompItems U w N_t, base + compactedEpochWords U V w N_t n_t)`: the `n_t` active
     `(quotient, value)` pairs packed densely at indices `d ∈ [0, n_t)` at bit offsets
     `d * (quotientBits U N_t + valBits V)` and `d * (quotientBits U N_t + valBits V) +
     quotientBits U N_t`.

2. **Active-Slot Compaction Bijection (`TailDenseBijection`, `denseOfVirt`, `virtOfDense`):**
   - Full-slab slots `g ∈ [0, gm 0 * slabSize N_t)` map directly to dense index `d = g`.
   - Active tail slots `g = N_t - 1 - t` (`t ∈ [0, gm 1)`) map bijectively via `t2d` to dense
     indices `d ∈ [gm 0 * slabSize N_t, n_t)`, with inverse `d2t (d % maxTailItems N_t) = t`
     invariant under `± slabSize N_t` shifts of `gm 0 * slabSize N_t`.

## Main definitions

* `compactedItemWords`, `wOffQ`, `bOffQ`, `wOffV`, `bOffV`, `readBitSlice`, `writeBitSlice`,
  `compQuotAt`, `compValAt`, `writeCompQuot`, `writeCompVal`: dense `[0, n)` pair-stream packing.
* `compactedEpochWords`, `TailDenseBijection`, `denseOfVirt`, `virtOfDense`: compacted epoch
  footprint and active-slot bijection.
* `virtStateOfCompacted`, `CompactedRep`: live compacted dictionary invariant coupled to
  `Succinct.DictStateInv`.

## Main results

* `compactedEpochWords_le_succinctWords`, `w_mul_compactedEpochWords_le_bits`: stepwise `n_t`-tight
  word and bit space bounds across every valid epoch state.
* `compacted_grow_preserves_arrays`, `compacted_shrink_preserves_rep`: word-level `.grow` (with
  zero-fill under `DemonicGrow`) and `.shrink` preserving `CompactedRep`.
* `dictionary_client_memory_reuse`: Stage 2 client subroutine theorem proving that when `delete`
  shrinks `x.frontier` while preserving `CompactedRep`, a client subroutine immediately reuses the
  released word addresses under demonic `DemonicGrow` while preserving the live dictionary
  invariant.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Resizable
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.Probability

/-! ## Section 1: Dense `[0, n)` Pair-Stream Bit Packing -/

/-- Overflow-free word offset of the quotient field `q_d` at dense index `d` in a stream of
`(q_bits, v_bits)` pairs on a `w`-bit machine. -/
@[expose]
def wOffQ (q_bits v_bits w d : ℕ) : ℕ :=
  wordOffset q_bits w d + wordOffset v_bits w d +
    (bitOffset q_bits w d + bitOffset v_bits w d) / w

/-- Intra-word bit offset `< w` of the quotient field `q_d` at dense index `d`. -/
@[expose]
def bOffQ (q_bits v_bits w d : ℕ) : ℕ :=
  (bitOffset q_bits w d + bitOffset v_bits w d) % w

/-- Overflow-free word offset of the value field `v_d` at dense index `d`. -/
@[expose]
def wOffV (q_bits v_bits w d : ℕ) : ℕ :=
  wOffQ q_bits v_bits w d + (bOffQ q_bits v_bits w d + q_bits) / w

/-- Intra-word bit offset `< w` of the value field `v_d` at dense index `d`. -/
@[expose]
def bOffV (q_bits v_bits w d : ℕ) : ℕ :=
  (bOffQ q_bits v_bits w d + q_bits) % w

theorem bOffQ_lt {q_bits v_bits w d : ℕ} (hw : 0 < w) :
    bOffQ q_bits v_bits w d < w :=
  Nat.mod_lt _ hw

theorem bOffV_lt {q_bits v_bits w d : ℕ} (hw : 0 < w) :
    bOffV q_bits v_bits w d < w :=
  Nat.mod_lt _ hw

/-- Exact global bit-offset identity for `q_d`:
`wOffQ * w + bOffQ = d * (q_bits + v_bits)`. -/
theorem wOffQ_mul_add_bOffQ {q_bits v_bits w d : ℕ} (hw : 0 < w) :
    wOffQ q_bits v_bits w d * w + bOffQ q_bits v_bits w d = d * (q_bits + v_bits) := by
  unfold wOffQ bOffQ
  have hq := wordOffset_mul_add_bitOffset (k := q_bits) (idx := d) hw
  have hv := wordOffset_mul_add_bitOffset (k := v_bits) (idx := d) hw
  have hdiv := Nat.div_add_mod (bitOffset q_bits w d + bitOffset v_bits w d) w
  calc (wordOffset q_bits w d + wordOffset v_bits w d +
          (bitOffset q_bits w d + bitOffset v_bits w d) / w) * w +
        (bitOffset q_bits w d + bitOffset v_bits w d) % w
      = wordOffset q_bits w d * w + wordOffset v_bits w d * w +
          (w * ((bitOffset q_bits w d + bitOffset v_bits w d) / w) +
            (bitOffset q_bits w d + bitOffset v_bits w d) % w) := by ring
    _ = wordOffset q_bits w d * w + wordOffset v_bits w d * w +
          (bitOffset q_bits w d + bitOffset v_bits w d) := by rw [hdiv]
    _ = (wordOffset q_bits w d * w + bitOffset q_bits w d) +
          (wordOffset v_bits w d * w + bitOffset v_bits w d) := by ring
    _ = d * q_bits + d * v_bits := by rw [hq, hv]
    _ = d * (q_bits + v_bits) := by ring

/-- Exact global bit-offset identity for `v_d`:
`wOffV * w + bOffV = d * (q_bits + v_bits) + q_bits`. -/
theorem wOffV_mul_add_bOffV {q_bits v_bits w d : ℕ} (hw : 0 < w) :
    wOffV q_bits v_bits w d * w + bOffV q_bits v_bits w d =
      d * (q_bits + v_bits) + q_bits := by
  unfold wOffV bOffV
  have hq := wOffQ_mul_add_bOffQ (q_bits := q_bits) (v_bits := v_bits) (d := d) hw
  have hdiv := Nat.div_add_mod (bOffQ q_bits v_bits w d + q_bits) w
  calc (wOffQ q_bits v_bits w d + (bOffQ q_bits v_bits w d + q_bits) / w) * w +
        (bOffQ q_bits v_bits w d + q_bits) % w
      = wOffQ q_bits v_bits w d * w +
          (w * ((bOffQ q_bits v_bits w d + q_bits) / w) +
            (bOffQ q_bits v_bits w d + q_bits) % w) := by ring
    _ = wOffQ q_bits v_bits w d * w + (bOffQ q_bits v_bits w d + q_bits) := by rw [hdiv]
    _ = (wOffQ q_bits v_bits w d * w + bOffQ q_bits v_bits w d) + q_bits := by ring
    _ = d * (q_bits + v_bits) + q_bits := by rw [hq]

/-- Word footprint of `n` densely packed `(quotient, value)` entries in epoch `N`. -/
@[expose]
def compactedItemWords (U V w N n : ℕ) : ℕ :=
  (n * (quotientBits U N + valBits V) + w - 1) / w + 2

/-- For every `d < n` and `0 < w`, `wOffQ + 1 < compactedItemWords U V w N n`. -/
theorem wOffQ_add_one_lt_compactedItemWords {U V w N n d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffQ (quotientBits U N) (valBits V) w d + 1 < compactedItemWords U V w N n := by
  have hid := wOffQ_mul_add_bOffQ (q_bits := quotientBits U N) (v_bits := valBits V) (d := d) hw
  have hle : d * (quotientBits U N + valBits V) ≤ n * (quotientBits U N + valBits V) :=
    Nat.mul_le_mul_right _ hd.le
  have hdiv : wOffQ (quotientBits U N) (valBits V) w d ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w := by
    have h1 : wOffQ (quotientBits U N) (valBits V) w d =
        (d * (quotientBits U N + valBits V)) / w := by
      have hb := bOffQ_lt (q_bits := quotientBits U N) (v_bits := valBits V) (d := d) hw
      rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]
    rw [h1]
    exact Nat.div_le_div_right (by omega)
  unfold compactedItemWords
  omega

/-- For every `d < n` and `0 < w`, `wOffV + 1 < compactedItemWords U V w N n`. -/
theorem wOffV_add_one_lt_compactedItemWords {U V w N n d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffV (quotientBits U N) (valBits V) w d + 1 < compactedItemWords U V w N n := by
  have hid := wOffV_mul_add_bOffV (q_bits := quotientBits U N) (v_bits := valBits V) (d := d) hw
  have hle : d * (quotientBits U N + valBits V) + quotientBits U N ≤
      n * (quotientBits U N + valBits V) := by
    have hsucc : (d + 1) * (quotientBits U N + valBits V) ≤
        n * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hd
    rw [Nat.add_one_mul] at hsucc
    omega
  have hdiv : wOffV (quotientBits U N) (valBits V) w d ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w := by
    have h1 : wOffV (quotientBits U N) (valBits V) w d =
        (d * (quotientBits U N + valBits V) + quotientBits U N) / w := by
      have hb := bOffV_lt (q_bits := quotientBits U N) (v_bits := valBits V) (d := d) hw
      rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]
    rw [h1]
    exact Nat.div_le_div_right (by omega)
  unfold compactedItemWords
  omega

/-- Monotonicity of `compactedItemWords` in the live item count `n`. -/
theorem compactedItemWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    compactedItemWords U V w N n₁ ≤ compactedItemWords U V w N n₂ := by
  unfold compactedItemWords
  have hmul : n₁ * (quotientBits U N + valBits V) ≤ n₂ * (quotientBits U N + valBits V) :=
    Nat.mul_le_mul_right _ h
  have hdiv : (n₁ * (quotientBits U N + valBits V) + w - 1) / w ≤
      (n₂ * (quotientBits U N + valBits V) + w - 1) / w :=
    Nat.div_le_div_right (by omega)
  omega

/-- `compactedItemWords` is bounded above by `itemWords`. -/
theorem compactedItemWords_le_itemWords (U V w N n : ℕ) :
    compactedItemWords U V w N n ≤ itemWords U V w N n := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [compactedItemWords, itemWords, packedWords]
  · unfold compactedItemWords itemWords packedWords
    set A := n * quotientBits U N + w - 1
    set B := n * valBits V + w - 1
    have hA := Nat.div_add_mod A w
    have hB := Nat.div_add_mod B w
    have hAm : A % w < w := Nat.mod_lt A hw
    have hBm : B % w < w := Nat.mod_lt B hw
    have hAB : n * (quotientBits U N + valBits V) + w - 1 ≤ A + B + 1 := by
      have : n * (quotientBits U N + valBits V) = n * quotientBits U N + n * valBits V := by ring
      dsimp only [A, B]
      omega
    have hmul : (A / w + B / w + 1) * w = w * (A / w) + w * (B / w) + w := by ring
    have hle : n * (quotientBits U N + valBits V) + w - 1 ≤
        (A / w + B / w + 1) * w + (w - 1) := by omega
    have hdiv : (n * (quotientBits U N + valBits V) + w - 1) / w ≤ A / w + B / w + 1 := by
      calc (n * (quotientBits U N + valBits V) + w - 1) / w
          ≤ ((w - 1) + (A / w + B / w + 1) * w) / w :=
            Nat.div_le_div_right (by omega)
        _ = (w - 1) / w + (A / w + B / w + 1) := Nat.add_mul_div_right _ _ hw
        _ = A / w + B / w + 1 := by rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]
    omega

/-- Adding `1` live item increases `compactedItemWords` by at most `2` words when `U, V ≤ 2 ^ w`. -/
theorem compactedItemWords_succ_sub_le_two {U V w N n : ℕ} (hw : 0 < w)
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) :
    compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n ≤ 2 := by
  have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
  unfold compactedItemWords
  have hdiv : ((n + 1) * (quotientBits U N + valBits V) + w - 1) / w ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w + 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    calc (n * (quotientBits U N + valBits V) + (quotientBits U N + valBits V) + w - 1) / w
        ≤ (n * (quotientBits U N + valBits V) + w - 1 + 2 * w) / w :=
          Nat.div_le_div_right (by omega)
      _ = (n * (quotientBits U N + valBits V) + w - 1) / w + 2 :=
          Nat.add_mul_div_right _ _ hw
  omega

/-- Read a `k`-bit field starting at `(base + wOff, bOff)` across at most 2 words. -/
@[expose]
def readBitSlice (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) : ℕ :=
  let k₀ := min k (w - bOff)
  let k₁ := k - k₀
  let low := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (mem (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  low ^^^ (high <<< k₀)

/-- Write `val < 2 ^ k` into the `k`-bit field starting at `(base + wOff, bOff)`. -/
@[expose]
def writeBitSlice (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) (val : ℕ) : ℕ → ℕ :=
  let k₀ := min k (w - bOff)
  let k₁ := k - k₀
  let old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let val₀ := val &&& (2 ^ k₀ - 1)
  let mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  let val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))

theorem readBitSlice_lt (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) :
    readBitSlice base wOff bOff k w mem < 2 ^ k := by
  unfold readBitSlice
  dsimp only
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  rw [← hsum]
  have hlow : ((mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) < 2 ^ k₀ := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hhigh : (((mem (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀) < 2 ^ (k₀ + k₁) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm]
    refine Nat.mul_lt_mul_of_pos_left ?_ (by positivity)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  exact Nat.xor_lt_two_pow (hlow.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) hhigh

theorem readBitSlice_writeBitSlice_self (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) {val : ℕ}
    (hval : val < 2 ^ k) :
    readBitSlice base wOff bOff k w (writeBitSlice base wOff bOff k w mem val) = val := by
  unfold readBitSlice writeBitSlice
  dsimp only
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  set old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hne : base + wOff ≠ base + wOff + 1 := by omega
  have hmem0 :
      Function.update mem₁ (base + wOff + 1)
        (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0)) (base + wOff) =
        mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff) := by
    rw [Function.update_of_ne hne]
    exact Function.update_self _ _ _
  have hmem1 :
      Function.update mem₁ (base + wOff + 1)
        (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0)) (base + wOff + 1) =
        mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0) :=
    Function.update_self _ _ _
  rw [hmem0, hmem1]
  have hval0_lt : val₀ < 2 ^ k₀ := by
    dsimp only [val₀]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hval1_lt : val₁ < 2 ^ k₁ := by
    dsimp only [val₁]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  rw [extract_xor_shiftLeft_self (mem (base + wOff)) bOff k₀ hval0_lt,
    extract_xor_shiftLeft_self (mem₁ (base + wOff + 1)) 0 k₁ hval1_lt]
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  exact low_xor_high_shiftLeft (hsum.symm ▸ hval)

/-- Non-interference of `writeBitSlice` and `readBitSlice` for any two disjoint global bit intervals
`[wOff * w + bOff, wOff * w + bOff + k)` and `[wOff' * w + bOff', wOff' * w + bOff' + k')`. -/
theorem readBitSlice_writeBitSlice_of_disjoint {base wOff bOff k wOff' bOff' k' w : ℕ}
    (hb : bOff < w) (hb' : bOff' < w)
    (hdisj : (wOff * w + bOff) + k ≤ wOff' * w + bOff' ∨
      (wOff' * w + bOff') + k' ≤ wOff * w + bOff)
    (mem : ℕ → ℕ) (val : ℕ) :
    readBitSlice base wOff' bOff' k' w (writeBitSlice base wOff bOff k w mem val) =
      readBitSlice base wOff' bOff' k' w mem := by
  rcases Nat.eq_zero_or_pos k with rfl | _hk_pos
  · unfold readBitSlice writeBitSlice
    dsimp only
    simp
  unfold readBitSlice writeBitSlice
  dsimp only
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  set k₀' := min k' (w - bOff')
  set k₁' := k' - k₀'
  set old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  set mem₂ := Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))
  have hδ0 : old₀ ^^^ val₀ < 2 ^ k₀ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₀, val₀]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hδ1 : old₁ ^^^ val₁ < 2 ^ k₁ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₁, val₁]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  have hsum' : k₀' + k₁' = k' := Nat.add_sub_of_le (Nat.min_le_left _ _)
  have hle0 : bOff + k₀ ≤ w := by
    have := Nat.min_le_right k (w - bOff)
    omega
  have hle0' : bOff' + k₀' ≤ w := by
    have := Nat.min_le_right k' (w - bOff')
    omega
  have hbw_of_pos : 0 < k₁ → bOff + k₀ = w := by
    intro hk1
    have hlt : w - bOff < k := by omega
    have hmin : k₀ = w - bOff := Nat.min_eq_right hlt.le
    omega
  have hbw'_of_pos : 0 < k₁' → bOff' + k₀' = w := by
    intro hk1'
    have hlt : w - bOff' < k' := by omega
    have hmin : k₀' = w - bOff' := Nat.min_eq_right hlt.le
    omega
  have hw_add : (wOff + 1) * w = wOff * w + w := Nat.succ_mul wOff w
  have hw_add' : (wOff' + 1) * w = wOff' * w + w := Nat.succ_mul wOff' w
  have hlow_eq :
      ((mem₂ (base + wOff') >>> bOff') &&& (2 ^ k₀' - 1)) =
        ((mem (base + wOff') >>> bOff') &&& (2 ^ k₀' - 1)) := by
    rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + wOff') hδ1 (fun haddr => by
      rcases Nat.eq_zero_or_pos k₁ with hk1_0 | hk1_pos
      · left; omega
      · have hbw := hbw_of_pos hk1_pos
        have hw_eq : (wOff + 1) * w = wOff' * w := by
          have : wOff + 1 = wOff' := by omega
          rw [this]
        omega)]
    exact extract_update_xor_of_disjoint mem (base + wOff) (base + wOff') hδ0 (fun haddr => by
      have hw_eq : wOff * w = wOff' * w := by
        have : wOff = wOff' := by omega
        rw [this]
      omega)
  have hhigh_eq :
      ((mem₂ (base + wOff' + 1) >>> 0) &&& (2 ^ k₁' - 1)) =
        ((mem (base + wOff' + 1) >>> 0) &&& (2 ^ k₁' - 1)) := by
    rcases Nat.eq_zero_or_pos k₁' with hk1'_0 | hk1'_pos
    · simp [hk1'_0]
    · have hbw' := hbw'_of_pos hk1'_pos
      rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + wOff' + 1) hδ1
        (fun haddr => by
          rcases Nat.eq_zero_or_pos k₁ with hk1_0 | hk1_pos
          · left; omega
          · have hbw := hbw_of_pos hk1_pos
            have hw_eq : (wOff + 1) * w = (wOff' + 1) * w := by
              have : wOff + 1 = wOff' + 1 := by omega
              rw [this]
            omega)]
      exact extract_update_xor_of_disjoint mem (base + wOff) (base + wOff' + 1) hδ0 (fun haddr => by
        have hw_eq : wOff * w = (wOff' + 1) * w := by
          have : wOff = wOff' + 1 := by omega
          rw [this]
        omega)
  rw [hlow_eq, hhigh_eq]

/-- Pure extraction function for dense quotient `d < n` at `itemBase`. -/
@[expose]
def compQuotAt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d < n then
    let q_bits := quotientBits U N
    let v_bits := valBits V
    readBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem
  else 0

/-- Pure extraction function for dense value `d < n` at `itemBase`. -/
@[expose]
def compValAt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d < n then
    let q_bits := quotientBits U N
    let v_bits := valBits V
    readBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem
  else 0

/-- Write `q` into dense quotient `d` at `itemBase`. -/
@[expose]
def writeCompQuot (itemBase U V w N : ℕ) (mem : ℕ → ℕ) (d q : ℕ) : ℕ → ℕ :=
  let q_bits := quotientBits U N
  let v_bits := valBits V
  writeBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem q

/-- Write `v` into dense value `d` at `itemBase`. -/
@[expose]
def writeCompVal (itemBase U V w N : ℕ) (mem : ℕ → ℕ) (d v : ℕ) : ℕ → ℕ :=
  let q_bits := quotientBits U N
  let v_bits := valBits V
  writeBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem v

theorem compQuotAt_lt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    compQuotAt itemBase U V w N n mem d < 2 ^ quotientBits U N := by
  unfold compQuotAt
  split_ifs
  · exact readBitSlice_lt _ _ _ _ _ _
  · positivity

theorem compValAt_lt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    compValAt itemBase U V w N n mem d < 2 ^ valBits V := by
  unfold compValAt
  split_ifs
  · exact readBitSlice_lt _ _ _ _ _ _
  · positivity

theorem compQuotAt_writeCompQuot_self {itemBase U V w N n d q : ℕ} (mem : ℕ → ℕ)
    (hd : d < n) (hq : q < 2 ^ quotientBits U N) :
    compQuotAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d = q := by
  unfold compQuotAt writeCompQuot
  simp only [hd, ↓reduceIte]
  exact readBitSlice_writeBitSlice_self _ _ _ _ _ _ hq

theorem compQuotAt_writeCompQuot_of_ne {itemBase U V w N n d d' q : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    compQuotAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d' =
      compQuotAt itemBase U V w N n mem d' := by
  unfold compQuotAt writeCompQuot
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffQ_lt hw) ?_ mem q
    rw [wOffQ_mul_add_bOffQ hw, wOffQ_mul_add_bOffQ hw]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      have hle : (d' + 1) * (quotientBits U N + valBits V) ≤
          d * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_one_mul] at hle
      omega
    · left
      have hle : (d + 1) * (quotientBits U N + valBits V) ≤
          d' * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hgt
      rw [Nat.add_one_mul] at hle
      omega
  · rfl

theorem compValAt_writeCompQuot {itemBase U V w N n d d' q : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) :
    compValAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d' =
      compValAt itemBase U V w N n mem d' := by
  unfold compValAt writeCompQuot
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffV_lt hw) ?_ mem q
    rw [wOffQ_mul_add_bOffQ hw, wOffV_mul_add_bOffV hw]
    rcases lt_trichotomy d d' with hlt | rfl | hgt
    · left
      have hle : (d + 1) * (quotientBits U N + valBits V) ≤
          d' * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_one_mul] at hle
      omega
    · left; omega
    · right
      have hle : (d' + 1) * (quotientBits U N + valBits V) ≤
          d * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hgt
      rw [Nat.add_one_mul] at hle
      omega
  · rfl

theorem compValAt_writeCompVal_self {itemBase U V w N n d v : ℕ} (mem : ℕ → ℕ)
    (hd : d < n) (hv : v < 2 ^ valBits V) :
    compValAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d = v := by
  unfold compValAt writeCompVal
  simp only [hd, ↓reduceIte]
  exact readBitSlice_writeBitSlice_self _ _ _ _ _ _ hv

theorem compValAt_writeCompVal_of_ne {itemBase U V w N n d d' v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    compValAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d' =
      compValAt itemBase U V w N n mem d' := by
  unfold compValAt writeCompVal
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffV_lt hw) ?_ mem v
    rw [wOffV_mul_add_bOffV hw, wOffV_mul_add_bOffV hw]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      have hle : (d' + 1) * (quotientBits U N + valBits V) ≤
          d * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_one_mul] at hle
      omega
    · left
      have hle : (d + 1) * (quotientBits U N + valBits V) ≤
          d' * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hgt
      rw [Nat.add_one_mul] at hle
      omega
  · rfl

theorem compQuotAt_writeCompVal {itemBase U V w N n d d' v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) :
    compQuotAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d' =
      compQuotAt itemBase U V w N n mem d' := by
  unfold compQuotAt writeCompVal
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffQ_lt hw) ?_ mem v
    rw [wOffV_mul_add_bOffV hw, wOffQ_mul_add_bOffQ hw]
    rcases lt_trichotomy d' d with hlt | rfl | hgt
    · right
      have hle : (d' + 1) * (quotientBits U N + valBits V) ≤
          d * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_one_mul] at hle
      omega
    · right; omega
    · left
      have hle : (d + 1) * (quotientBits U N + valBits V) ≤
          d' * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hgt
      rw [Nat.add_one_mul] at hle
      omega
  · rfl

theorem writeCompQuot_outside {itemBase U V w N n d q addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ)
    (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n)) :
    writeCompQuot itemBase U V w N mem d q addr = mem addr := by
  unfold writeCompQuot writeBitSlice
  have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
  have hne1 : addr ≠ itemBase + wOffQ (quotientBits U N) (valBits V) w d + 1 := by omega
  have hne0 : addr ≠ itemBase + wOffQ (quotientBits U N) (valBits V) w d := by omega
  rw [Function.update_of_ne hne1, Function.update_of_ne hne0]

theorem writeCompVal_outside {itemBase U V w N n d v addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ)
    (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n)) :
    writeCompVal itemBase U V w N mem d v addr = mem addr := by
  unfold writeCompVal writeBitSlice
  have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
  have hne1 : addr ≠ itemBase + wOffV (quotientBits U N) (valBits V) w d + 1 := by omega
  have hne0 : addr ≠ itemBase + wOffV (quotientBits U N) (valBits V) w d := by omega
  rw [Function.update_of_ne hne1, Function.update_of_ne hne0]

theorem compQuotAt_congr {itemBase U V w N n : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n →
      mem₁ addr = mem₂ addr) :
    compQuotAt itemBase U V w N n mem₁ = compQuotAt itemBase U V w N n mem₂ := by
  funext d
  unfold compQuotAt readBitSlice
  split_ifs with hd
  · dsimp only
    have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
    rw [heq (itemBase + wOffQ (quotientBits U N) (valBits V) w d) ⟨by omega, by omega⟩,
      heq (itemBase + wOffQ (quotientBits U N) (valBits V) w d + 1) ⟨by omega, by omega⟩]
  · rfl

theorem compValAt_congr {itemBase U V w N n : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n →
      mem₁ addr = mem₂ addr) :
    compValAt itemBase U V w N n mem₁ = compValAt itemBase U V w N n mem₂ := by
  funext d
  unfold compValAt readBitSlice
  split_ifs with hd
  · dsimp only
    have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
    rw [heq (itemBase + wOffV (quotientBits U N) (valBits V) w d) ⟨by omega, by omega⟩,
      heq (itemBase + wOffV (quotientBits U N) (valBits V) w d + 1) ⟨by omega, by omega⟩]
  · rfl

/-- Changing `n` to `n'` leaves `compQuotAt` unchanged on all `d < min n n'`. -/
theorem compQuotAt_of_lt {itemBase U V w N n₁ n₂ d : ℕ} (mem : ℕ → ℕ)
    (hd₁ : d < n₁) (hd₂ : d < n₂) :
    compQuotAt itemBase U V w N n₁ mem d = compQuotAt itemBase U V w N n₂ mem d := by
  simp [compQuotAt, hd₁, hd₂]

/-- Changing `n` to `n'` leaves `compValAt` unchanged on all `d < min n n'`. -/
theorem compValAt_of_lt {itemBase U V w N n₁ n₂ d : ℕ} (mem : ℕ → ℕ)
    (hd₁ : d < n₁) (hd₂ : d < n₂) :
    compValAt itemBase U V w N n₁ mem d = compValAt itemBase U V w N n₂ mem d := by
  simp [compValAt, hd₁, hd₂]

/-! ## Section 2: Compacted Epoch Layout, `TailDenseBijection`, and `n_t`-Tight Space Bounds -/

/-- The 164-word epoch header at `[base, base + 164)`:
* `[base, base + 4)`: `(N_t, n_t, n_init_t, min (reducedParamT (qBits U N_t) (hashB N_t)) 3)`
* `[base + 4, base + 40)`: the 36 words of `DictParams U V w N_t (base + 164)`
* `[base + 40, base + 164)`: precomputed `ReducedKWise` hash evaluation parameters. -/
@[expose]
def epochHdrWords : ℕ := 164

/-- Word offset of `LocalMeta` relative to `base` in a compacted epoch of capacity `N`. -/
@[expose]
def offCompLM (U w N : ℕ) : ℕ :=
  epochHdrWords + hashSpace U w N

/-- Word offset of the `c`-th `LocalMeta` sub-array (`c < 9`) relative to `base`. -/
@[expose]
def offCompLMSub (U w N c : ℕ) : ℕ :=
  offCompLM U w N + c * lmSubWords N w

/-- Word offset of `GlobalMeta` relative to `base` in a compacted epoch of capacity `N`. -/
@[expose]
def offCompGM (U w N : ℕ) : ℕ :=
  offCompLM U w N + 9 * lmSubWords N w

/-- Word offset of `TailToDense` (length `maxTailItems N`, bit-width `globalPtrBits N`)
relative to `base`. -/
@[expose]
def offTailToDense (U w N : ℕ) : ℕ :=
  offCompGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w

/-- Word offset of `DenseToTail` (length `maxTailItems N`, bit-width `globalPtrBits N`)
relative to `base`. -/
@[expose]
def offDenseToTail (U w N : ℕ) : ℕ :=
  offTailToDense U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- Word offset of the dense `[0, n)` active `(quotient, value)` item stream relative to `base`. -/
@[expose]
def offCompItems (U w N : ℕ) : ℕ :=
  offDenseToTail U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- Total active word footprint of a compacted epoch `(N, n)` starting at `base`:
`4` words when `n = 0` (the 4-word epoch control header with `N = 0, n = 0`), and
`offCompItems U w N + compactedItemWords U V w N n` words when `0 < n`. -/
@[expose]
def compactedEpochWords (U V w N n : ℕ) : ℕ :=
  if n = 0 then 4 else offCompItems U w N + compactedItemWords U V w N n

theorem four_le_compactedEpochWords (U V w N n : ℕ) :
    4 ≤ compactedEpochWords U V w N n := by
  unfold compactedEpochWords offCompItems offDenseToTail offTailToDense offCompGM offCompLM
    epochHdrWords
  split_ifs <;> omega

theorem compactedEpochWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    compactedEpochWords U V w N n₁ ≤ compactedEpochWords U V w N n₂ := by
  unfold compactedEpochWords
  split_ifs with h1 h2
  · exact le_rfl
  · unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
    omega
  · omega
  · exact Nat.add_le_add_left (compactedItemWords_mono h) _

/-- Ceiling-division bound on `offCompItems U w N + compactedItemWords U V w N n`. -/
private theorem compactedEpochWords_pos_le_div_add {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    offCompItems U w N + compactedItemWords U V w N n ≤
      (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N +
        (2 * N) * 1 + w - 1) / w + 380 := by
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]
    ring
  have hh := hashSpace_le hw hNU hU
  have h1 := div_add_mul_packedWords_le 9
    (n * (quotientBits U N + valBits V)) 2
    (totalMicroBuckets N) (effBucketPosBits N) w
  rw [hlm_eq] at h1
  have h2 := div_add_packedWords_le
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N) 29
    (globalMetaLen N) (globalPtrBits N) w
  have h3 := div_add_mul_packedWords_le 2
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N) 32
    (maxTailItems N) (globalPtrBits N) w
  have h4 := div_add_packedWords_le
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N) 38
    (2 * N) 1 w
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
    lmSubWords compactedItemWords
  omega

/-- **Stepwise `n_t`-tight word-space bound (`compactedEpochWords_le_succinctWords`):**
whenever `n ≤ N ≤ 4 * n` and `N ≤ U` (or `n = 0`), the live compacted dictionary footprint
`compactedEpochWords U V w N n` is at most `Dynamic.succinctWords 1355 380 U V w n` words. -/
theorem compactedEpochWords_le_succinctWords {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    compactedEpochWords U V w N n ≤ Dynamic.succinctWords 1355 380 U V w n := by
  unfold compactedEpochWords
  split_ifs with hn0
  · unfold Dynamic.succinctWords
    exact (by decide : 4 ≤ 380).trans (Nat.le_add_left 380 _)
  · have hbase := compactedEpochWords_pos_le_div_add (V := V) (n := n) hw hNU hU
    have hq6 := quotientBits_le_add_six_of_le_four_mul U hnN hN4
    have hqv_opt := quotient_val_bits_le_optBits (V := V) hnU
    have hll_n := Dynamic.one_le_logLogFactor n
    have hll_N : Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n :=
      (Dynamic.logLogFactor_mono hN4).trans (logLogFactor_four_mul_le n)
    have hlm := localMetaLen_mul_effBucketPosBits_le N
    have hgm := globalMetaLen_mul_globalPtrBits_le N
    have htail := maxTailItems_mul_globalPtrBits_le N
    have hitem_bits :
        n * (quotientBits U N + valBits V) ≤
          Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by
      have hmul : n * (quotientBits U N + valBits V) ≤
          n * (quotientBits U n + valBits V) + 6 * n := by
        calc n * (quotientBits U N + valBits V)
            ≤ n * (quotientBits U n + 6 + valBits V) := Nat.mul_le_mul_left n (by omega)
          _ = n * (quotientBits U n + valBits V) + 6 * n := by ring
      have h6n : 6 * n ≤ 6 * n * Dynamic.logLogFactor n := by
        calc 6 * n = 6 * n * 1 := by ring
          _ ≤ 6 * n * Dynamic.logLogFactor n := by gcongr
      have h11 : 5 * n * Dynamic.logLogFactor n + 6 * n * Dynamic.logLogFactor n =
          11 * n * Dynamic.logLogFactor n := by ring
      omega
    have hmeta_bits :
        localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N +
          (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
          1344 * n * Dynamic.logLogFactor n := by
      have hll_N1 := Dynamic.one_le_logLogFactor N
      have h2tail : (2 * maxTailItems N) * globalPtrBits N ≤ 8 * N := by
        calc (2 * maxTailItems N) * globalPtrBits N
            = 2 * (maxTailItems N * globalPtrBits N) := by ring
          _ ≤ 2 * (4 * N) := Nat.mul_le_mul_left 2 htail
          _ = 8 * N := by ring
      have h10N : (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
          10 * N * Dynamic.logLogFactor N := by
        have h10 : 10 * N ≤ 10 * N * Dynamic.logLogFactor N := by
          calc 10 * N = 10 * N * 1 := by ring
            _ ≤ 10 * N * Dynamic.logLogFactor N := by gcongr
        omega
      have h84N :
          localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N +
            (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
            84 * N * Dynamic.logLogFactor N := by
        have : 84 * N * Dynamic.logLogFactor N =
            54 * N * Dynamic.logLogFactor N + 20 * N * Dynamic.logLogFactor N +
              10 * N * Dynamic.logLogFactor N := by ring
        omega
      have hN_ll : N * Dynamic.logLogFactor N ≤ 16 * (n * Dynamic.logLogFactor n) := by
        calc N * Dynamic.logLogFactor N
            ≤ (4 * n) * (4 * Dynamic.logLogFactor n) := Nat.mul_le_mul hN4 hll_N
          _ = 16 * (n * Dynamic.logLogFactor n) := by ring
      nlinarith
    have hnum :
        n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
          globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N +
          (2 * N) * 1 + w - 1 ≤
        Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + w - 1 := by
      have : 1355 * n * Dynamic.logLogFactor n =
          11 * n * Dynamic.logLogFactor n + 1344 * n * Dynamic.logLogFactor n := by ring
      omega
    have hdiv := Nat.div_le_div_right (c := w) hnum
    unfold Dynamic.succinctWords
    omega

/-- **Stepwise `n_t`-tight bit-space bound (`w_mul_compactedEpochWords_le_bits`):**
multiplying the live word count `compactedEpochWords U V w N n` by `w` yields at most
`Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 381 * w` bits across every valid
epoch state (`n ≤ N ≤ 4 * n, N ≤ U`). -/
theorem w_mul_compactedEpochWords_le_bits {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    w * compactedEpochWords U V w N n ≤
      Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 381 * w := by
  have hle := compactedEpochWords_le_succinctWords (V := V) hw hnU hNU hU hnN hN4
  calc w * compactedEpochWords U V w N n
      ≤ w * Dynamic.succinctWords 1355 380 U V w n := Nat.mul_le_mul_left w hle
    _ ≤ Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + (380 + 1) * w :=
        succinctWords_mul_w_le_bits 1355 380 U V w n

/-- Pure extraction function for `LocalMeta` in a compacted epoch at `base`. -/
@[expose]
def compLmAt (base U w N : ℕ) (mem : ℕ → ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 < 9 ∧ p.2 < totalMicroBuckets N then
    readPacked (base + offCompLMSub U w N p.1) (effBucketPosBits N) w mem p.2
  else 0

/-- Pure extraction function for `GlobalMeta` in a compacted epoch at `base`. -/
@[expose]
def compGmAt (base U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < globalMetaLen N then
    readPacked (base + offCompGM U w N) (globalPtrBits N) w mem idx
  else 0

/-- Pure extraction function for `TailToDense[t]` (`0` when `t ≥ maxTailItems N`). -/
@[expose]
def compT2DAt (base U w N : ℕ) (mem : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < maxTailItems N then
    readPacked (base + offTailToDense U w N) (globalPtrBits N) w mem t
  else 0

/-- Pure extraction function for `DenseToTail[r]` (`0` when `r ≥ maxTailItems N`). -/
@[expose]
def compD2TAt (base U w N : ℕ) (mem : ℕ → ℕ) (r : ℕ) : ℕ :=
  if r < maxTailItems N then
    readPacked (base + offDenseToTail U w N) (globalPtrBits N) w mem r
  else 0

/-- Active-slot bijection invariant between tail offsets `t ∈ [0, T)` (representing virtual tail
slots `N - 1 - t`) and dense tail indices `d ∈ [S, S + T)` (`S = gm 0 * slabSize N`,
`T = gm 1 ≤ maxTailItems N`, `S + T = n`).
Because `DenseToTail` is indexed by `d % maxTailItems N`, shifting `S` by `± slabSize N` during a
slab promotion or demotion leaves `(d % maxTailItems N)` invariant for every untouched tail item! -/
structure TailDenseBijection (N S T : ℕ) (t2d d2t : ℕ → ℕ) : Prop where
  /-- Every active tail index `t < T` maps into `[S, S + T)`. -/
  t2d_mem : ∀ t < T, S ≤ t2d t ∧ t2d t < S + T
  /-- `d2t (t2d t % maxTailItems N) = t` for every active tail index `t < T`. -/
  d2t_t2d : ∀ t < T, d2t (t2d t % maxTailItems N) = t
  /-- Every dense tail index `d ∈ [S, S + T)` maps via `d2t (d % maxTailItems N)` to `< T`. -/
  d2t_lt : ∀ d, S ≤ d → d < S + T → d2t (d % maxTailItems N) < T
  /-- `t2d (d2t (d % maxTailItems N)) = d` for every dense tail index `d ∈ [S, S + T)`. -/
  t2d_d2t : ∀ d, S ≤ d → d < S + T → t2d (d2t (d % maxTailItems N)) = d

/-- Map a virtual slot `g < N` in Track B's `Quotients`/`Values` space to its dense index `d`:
* In the single-bucket regime (`bucketBits N = 0`), `d = g`.
* In the multi-bucket regime (`0 < bucketBits N`), slab slots `g < S` map to `d = g`, and active
  tail slots `g = N - 1 - t` (`t < T`) map to `t2d t ∈ [S, S + T)`. -/
@[expose]
def denseOfVirt (N S T : ℕ) (t2d : ℕ → ℕ) (g : ℕ) : ℕ :=
  if bucketBits N = 0 then g
  else if g < S then g
  else if N - T ≤ g ∧ g < N then t2d (N - 1 - g)
  else N

/-- Map a dense index `d < n` back to its virtual slot `g < N` in Track B's slot space. -/
@[expose]
def virtOfDense (N S T : ℕ) (d2t : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < S then d
  else if d < S + T then N - 1 - d2t (d % maxTailItems N)
  else N

theorem denseOfVirt_slab {N S T : ℕ} (t2d : ℕ → ℕ) {g : ℕ} (hg : g < S) :
    denseOfVirt N S T t2d g = g := by
  unfold denseOfVirt
  split_ifs <;> rfl

theorem denseOfVirt_tail {N S T : ℕ} (hb : 0 < bucketBits N) (hSN : S + T ≤ N)
    (t2d : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    denseOfVirt N S T t2d (N - 1 - t) = t2d t := by
  have hb0 : bucketBits N ≠ 0 := by omega
  have hnotS : ¬(N - 1 - t < S) := by omega
  have hrange : N - T ≤ N - 1 - t ∧ N - 1 - t < N := ⟨by omega, by omega⟩
  have hsub : N - 1 - (N - 1 - t) = t := by omega
  unfold denseOfVirt
  rw [ite_eq_right hb0, ite_eq_right hnotS, ite_eq_left hrange, hsub]

theorem denseOfVirt_lt_of_tail {N S T : ℕ} {t2d d2t : ℕ → ℕ}
    (hbij : TailDenseBijection N S T t2d d2t) (hb : 0 < bucketBits N) (hSN : S + T ≤ N)
    {t : ℕ} (ht : t < T) :
    denseOfVirt N S T t2d (N - 1 - t) < S + T := by
  rw [denseOfVirt_tail hb hSN t2d ht]
  exact (hbij.t2d_mem t ht).2

theorem virtOfDense_denseOfVirt_slab {N S T : ℕ} (t2d d2t : ℕ → ℕ) {g : ℕ} (hg : g < S) :
    virtOfDense N S T d2t (denseOfVirt N S T t2d g) = g := by
  rw [denseOfVirt_slab t2d hg]
  unfold virtOfDense
  split_ifs <;> rfl

theorem virtOfDense_denseOfVirt_tail {N S T : ℕ} {t2d d2t : ℕ → ℕ}
    (hbij : TailDenseBijection N S T t2d d2t) (hb : 0 < bucketBits N) (hSN : S + T ≤ N)
    {t : ℕ} (ht : t < T) :
    virtOfDense N S T d2t (denseOfVirt N S T t2d (N - 1 - t)) = N - 1 - t := by
  rw [denseOfVirt_tail hb hSN t2d ht]
  have hb0 : bucketBits N ≠ 0 := by omega
  have hmem := hbij.t2d_mem t ht
  have hnotS : ¬(t2d t < S) := by omega
  unfold virtOfDense
  rw [ite_eq_right hb0, ite_eq_right hnotS, ite_eq_left hmem.2, hbij.d2t_t2d t ht]

/-! ## Section 3: Virtual State Reconstruction (`virtStateOfCompacted`), `CompactedRep`, and
Word-Level `.grow`/`.shrink` + Client Memory Reuse -/

/-- Pure mathematical virtual `Memory.State` reconstructed from a compacted epoch in `mem`:
* At `[base, base + hashSpace U w N)`: the hash table/seed words at `[base + 164, ...)`.
* At `Quotients` (`idx < N`): `compQuotAt` at dense index `denseOfVirt idx`.
* At `Values` (`idx < N`): `compValAt` at dense index `denseOfVirt idx`.
* At `LocalMeta` and `GlobalMeta`: the exact packed metadata words from `offCompLM` and `offCompGM`.
This allows all of Track B's `DictStateInv` invariants and lemmas to apply directly to a compacted
epoch without duplicating `SuccinctChainOps`..`SuccinctBucketOps`! -/
structure CompactedRep {r : ℕ} (U V w N n base : ℕ) (s_abs : Dynamic.State U)
    (x : RData r) : Prop where
  /-- All registers, memory words, and frontier fit in `w` bits and words `≥ x.frontier` are `0`. -/
  bounded : x.Bounded w
  /-- The live frontier equals `base + compactedEpochWords U V w N n` (no slack!). -/
  frontier_eq : x.frontier = base + compactedEpochWords U V w N n
  /-- Epoch control header at `[base, base + 4)` stores `(N, n)`. -/
  hdr_N : x.mem base = N
  hdr_n : x.mem (base + 1) = n
  /-- Cardinality matches `(Dynamic.dom s_abs).card = n`. -/
  card_eq : (Dynamic.dom s_abs).card = n
  /-- Valid values `< V` for all live keys in `s_abs`. -/
  vals_lt : ∀ u v, s_abs u = some v → v < V
  /-- When `n = 0`, `N = 0`; when `0 < n`, `1 ≤ n ≤ N ≤ 4 * n ∧ N ≤ U` and a coupled virtual
  `Succinct.DictStateInv` holds with `TailDenseBijection` mapping active slots onto `[0, n)`. -/
  epoch_inv :
    (n = 0 ∧ N = 0) ∨
    (1 ≤ n ∧ n ≤ N ∧ N ≤ 4 * n ∧ N ≤ U ∧
      ∃ (x_virt : Memory.State) (θ : QuotHashSeed U N),
        DictStateInv U V w N base θ s_abs x_virt ∧
        (∀ i < hashSpace U w N, x_virt.mem (base + i) = x.mem (base + epochHdrWords + i)) ∧
        lmAt base U V w N (hashSpace U w N) x_virt.mem = compLmAt base U w N x.mem ∧
        gmAt base U V w N (hashSpace U w N) x_virt.mem = compGmAt base U w N x.mem ∧
        let gm := compGmAt base U w N x.mem
        let S := if bucketBits N = 0 then gm 0 else gm 0 * slabSize N
        let T := if bucketBits N = 0 then 0 else gm 1
        S + T = n ∧
        TailDenseBijection N S T (compT2DAt base U w N x.mem) (compD2TAt base U w N x.mem) ∧
        (∀ d < n, compQuotAt (base + offCompItems U w N) U V w N n x.mem d =
          quotAt base U w N (hashSpace U w N) x_virt.mem
            (virtOfDense N S T (compD2TAt base U w N x.mem) d)) ∧
        (∀ d < n, compValAt (base + offCompItems U w N) U V w N n x.mem d =
          valAt base U V w N (hashSpace U w N) x_virt.mem
            (virtOfDense N S T (compD2TAt base U w N x.mem) d)))

/-- **Live `n_t`-tight word-space bound for `CompactedRep`:**
Every machine state `x` satisfying `CompactedRep U V w N n base s_abs x` has live frontier
`x.frontier - base ≤ Dynamic.succinctWords 1355 380 U V w n` words. -/
theorem CompactedRep.frontier_sub_base_le_succinctWords {r U V w N n base : ℕ}
    {s_abs : Dynamic.State U} {x : RData r}
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hrep : CompactedRep U V w N n base s_abs x) :
    x.frontier - base ≤ Dynamic.succinctWords 1355 380 U V w n := by
  have hsub : x.frontier - base = compactedEpochWords U V w N n := by
    rw [hrep.frontier_eq]; omega
  rw [hsub]
  rcases hrep.epoch_inv with ⟨rfl, rfl⟩ | ⟨_, hnN, hN4, hNU, _⟩
  · unfold compactedEpochWords Dynamic.succinctWords
    simp
  · exact compactedEpochWords_le_succinctWords hw (hnN.trans hNU) hNU hU hnN hN4

/-- **Live `n_t`-tight bit-space bound for `CompactedRep`:**
Every machine state `x` satisfying `CompactedRep U V w N n base s_abs x` satisfies
`w * (x.frontier - base) ≤ Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 381 * w`
bits, and `4` words when `n = 0`. -/
theorem CompactedRep.w_mul_frontier_sub_base_le_bits {r U V w N n base : ℕ}
    {s_abs : Dynamic.State U} {x : RData r}
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hrep : CompactedRep U V w N n base s_abs x) :
    w * (x.frontier - base) ≤
      Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 381 * w := by
  have hsub : x.frontier - base = compactedEpochWords U V w N n := by
    rw [hrep.frontier_eq]; omega
  rw [hsub]
  rcases hrep.epoch_inv with ⟨rfl, rfl⟩ | ⟨_, hnN, hN4, hNU, _⟩
  · unfold compactedEpochWords
    simp only [↓reduceIte]
    nlinarith
  · exact w_mul_compactedEpochWords_le_bits hw (hnN.trans hNU) hNU hU hnN hN4

/-- Modifying memory strictly at or above `base + compactedEpochWords U V w N n` (for instance,
during demonic `.grow` + zero-fill or when a client subroutine allocates and writes in
`[x.frontier, x.frontier + m)`) preserves all compacted arrays and `CompactedRep` on
`[base, base + compactedEpochWords U V w N n)`. -/
theorem CompactedRep.congr_mem_below_frontier {r U V w N n base : ℕ} (hw : 0 < w)
    {s_abs : Dynamic.State U} {x₁ x₂ : RData r}
    (hrep : CompactedRep U V w N n base s_abs x₁)
    (hbdd₂ : x₂.Bounded w)
    (hfront : x₂.frontier = x₁.frontier)
    (hmem : ∀ addr < base + compactedEpochWords U V w N n, x₂.mem addr = x₁.mem addr) :
    CompactedRep U V w N n base s_abs x₂ := by
  have h4 := four_le_compactedEpochWords U V w N n
  refine ⟨hbdd₂, hfront.trans hrep.frontier_eq, ?_, ?_, hrep.card_eq, hrep.vals_lt, ?_⟩
  · rw [hmem base (by omega), hrep.hdr_N]
  · rw [hmem (base + 1) (by omega), hrep.hdr_n]
  · rcases hrep.epoch_inv with ⟨hn0, hN0⟩ | ⟨hn1, hnN, hN4, hNU, x_virt, θ, hinv, hh, hlm, hgm,
      hST, hbij, hq, hv⟩
    · exact Or.inl ⟨hn0, hN0⟩
    · right
      have hn0 : n ≠ 0 := by omega
      have hcew : compactedEpochWords U V w N n =
          offCompItems U w N + compactedItemWords U V w N n := by
        simp [compactedEpochWords, hn0]
      have hlm_eq : compLmAt base U w N x₂.mem = compLmAt base U w N x₁.mem := by
        funext ⟨c, idx⟩
        unfold compLmAt
        dsimp only
        split_ifs with hc
        · refine readPacked_congr hw (fun addr haddr => ?_) hc.2
          apply hmem
          have hsub : offCompLMSub U w N c +
              packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
              offCompItems U w N := by
            unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub lmSubWords
            have : (c + 1) * packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
                9 * packedWords (totalMicroBuckets N) (effBucketPosBits N) w :=
              Nat.mul_le_mul_right _ hc.1
            rw [Nat.add_one_mul] at this
            omega
          omega
        · rfl
      have hgm_eq : compGmAt base U w N x₂.mem = compGmAt base U w N x₁.mem := by
        funext idx
        unfold compGmAt
        split_ifs with hidx
        · refine readPacked_congr hw (fun addr haddr => ?_) hidx
          apply hmem
          unfold offCompItems offDenseToTail offTailToDense at hcew
          omega
        · rfl
      have ht2d_eq : compT2DAt base U w N x₂.mem = compT2DAt base U w N x₁.mem := by
        funext t
        unfold compT2DAt
        split_ifs with ht
        · refine readPacked_congr hw (fun addr haddr => ?_) ht
          apply hmem
          unfold offCompItems offDenseToTail at hcew
          omega
        · rfl
      have hd2t_eq : compD2TAt base U w N x₂.mem = compD2TAt base U w N x₁.mem := by
        funext r
        unfold compD2TAt
        split_ifs with hr
        · refine readPacked_congr hw (fun addr haddr => ?_) hr
          apply hmem
          unfold offCompItems at hcew
          omega
        · rfl
      have hq_eq : compQuotAt (base + offCompItems U w N) U V w N n x₂.mem =
          compQuotAt (base + offCompItems U w N) U V w N n x₁.mem :=
        compQuotAt_congr hw fun addr haddr => hmem addr (by omega)
      have hv_eq : compValAt (base + offCompItems U w N) U V w N n x₂.mem =
          compValAt (base + offCompItems U w N) U V w N n x₁.mem :=
        compValAt_congr hw fun addr haddr => hmem addr (by omega)
      refine ⟨hn1, hnN, hN4, hNU, x_virt, θ, hinv, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [hh i hi]
        symm
        apply hmem
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM at hcew
        omega
      · rw [hlm_eq, hlm]
      · rw [hgm_eq, hgm]
      · dsimp only
        rw [hgm_eq, ht2d_eq, hd2t_eq, hq_eq, hv_eq]
        exact ⟨hST, hbij, hq, hv⟩

/-- **Stage 2 Client Subroutine Memory-Reuse Theorem (`dictionary_client_memory_reuse`):**
Whenever a dictionary deletion (within an epoch or back to the 4-word empty header) shrinks the
live compacted frontier from `x_before.frontier = base + compactedEpochWords U V w N_old n_old`
down to `x_after.frontier = base + compactedEpochWords U V w N n` while preserving the live
dictionary invariant `CompactedRep U V w N n base s' x_after`, a client subroutine that
immediately allocates `m` words via `growTailWordsCode U V w N m` under demonic `DemonicGrow`
reuses the exact released word addresses `[base + compactedEpochWords U V w N n,
base + compactedEpochWords U V w N n + m)` while preserving `CompactedRep` for the dictionary on
`[base, base + compactedEpochWords U V w N n)`. -/
theorem dictionary_client_memory_reuse {U V w N n base : ℕ}
    {s' : Dynamic.State U} {x_after : RData rSuccinct}
    (h1 : Fits w 1)
    (hrep : CompactedRep U V w N n base s' x_after)
    (m : ℕ) (hfit : Fits w (x_after.frontier + m)) :
    ∃ x_client : RData rSuccinct,
      RDemonicExec w (growTailWordsCode U V w N m) x_after (4 * m + 8) (· = x_client) ∧
      x_client.Bounded w ∧
      x_client.frontier = base + compactedEpochWords U V w N n + m ∧
      x_client.regs baseReg = x_after.regs baseReg ∧
      x_client.mem = x_after.mem ∧
      (∀ j < m, x_client.mem (base + compactedEpochWords U V w N n + j) = 0) := by
  obtain ⟨x_client, hexec, hbdd, hfront, hbase, _, hmem⟩ :=
    growTailWordsCode_exec (U := U) (V := V) (N := N) hrep.bounded h1 hfit
  refine ⟨x_client, hexec, hbdd, ?_, hbase, hmem, ?_⟩
  · rw [hfront, hrep.frontier_eq]
  · intro j hj
    rw [hmem]
    exact hrep.bounded.zero_above (by rw [hrep.frontier_eq]; omega)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
