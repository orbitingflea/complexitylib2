/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.EpochStep
import all Complexity.DataStructure.Dictionary.BitResizable.Companion
import all Complexity.DataStructure.Dictionary.BitResizable.EpochStep

/-!
# Bit-Resizable Dynamic Dictionary Transitions and Amortized Analysis

This module assembles the query, in-epoch update, and epoch-rebuild steps from
`Complexity.DataStructure.Dictionary.BitResizable.EpochStep` into the complete state-transition
and expected amortized complexity theorems for the bit-resizable succinct dictionary on the
`w`-bit `BitRAM` (`Cslib.WordRAM.BitRAM`).

## Potential function and amortized analysis

We combine two potential components into `totalPotential`:
1. **In-epoch bucket/window potential (`1008 * c.potential U V w N`):**
   absorbs the cost of overflow slab compactions (`pushBackSlotProg` / `popLastSlotProg`) and
   single-tape bit-packed array synchronization (`inEpochSyncCode`) during in-epoch `insert` and
   `delete` steps.
2. **Epoch capacity potential (`2660 * epochPotential U N n_t`):**
   where `epochPotential U N m = (if N < U then 2 * m - N else 0) + (N - 2 * m)`.
   * Immediately after any epoch rebuild to `N' = targetCap U m'` (`0` if `m' = 0`, else
     `min U (2 * m')`), `epochPotential U N' m' = 0`.
   * During each in-epoch step (`|m' - m| ≤ 1`), `epochPotential` increases by at most `2`,
     contributing at most `2660 * 2 = 5320` to the amortized potential change.
   * When an update violates `EpochInv U N m'`, `epochPotential U N m` is large enough to pay for
     the entire single-tape epoch rebuild (`rebuild_step`: `O(N + N' + m + m')` instructions) plus
     the initial bucket potential `1008 * c'.potential U V w N' ≤ 1008 * m'` of the new epoch.

Consequently, every operation (`query`, `insert`, `delete`) from any valid dictionary state has:
* deterministic amortized cost bounded by
  `stepOverhead U N θ s_abs op = 7849 + 37 * epochProbeExcess U N θ s_abs (opKey op)`,
* expected amortized cost over the epoch seed distribution `θ ← epochSeedPMF U N` at most
  `7849 + 37 * 5 = 8034` machine instructions (`O(1)` expected amortized time), and
* pointwise bit-space at every step `t` equal to `dictBitSize U V w N_t n_t`, which is at most
  `Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w` bits in the current
  active key count `n_t = (Dynamic.dom s_t).card`, with all bits above `x_t.bitSize` immediately
  released to `[x_t.bitSize, ∞)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.targetCap`: target epoch capacity `0` (if `m = 0`)
  or `min U (2 * m)` (if `m > 0`).
* `Cslib.DataStructure.Dictionary.BitResizable.epochPotential`: epoch capacity potential
  `(if N < U then 2 * m - N else 0) + (N - 2 * m)`.
* `Cslib.DataStructure.Dictionary.BitResizable.totalPotential`: combined potential
  `1008 * c.potential U V w N + 2660 * epochPotential U N (Dynamic.dom s_abs).card`.
* `Cslib.DataStructure.Dictionary.BitResizable.DictInv`: full machine-state and companion invariant
  on `BitRAM.Data 12`.
* `Cslib.DataStructure.Dictionary.BitResizable.opKey`, `stepOverhead`: target key and per-step
  amortized instruction bound `7849 + 37 * epochProbeExcess U N θ s_abs (opKey op)`.
* `Cslib.DataStructure.Dictionary.BitResizable.ExecTrace`: inductive execution trace of concrete
  `BitRAM.Code .standard 12` programs under `BitRAM.DemonicExecWithin` across an arbitrary sequence
  of dictionary operations.

## Main results

* `epochMetaWords_le_linear`: `epochMetaWords U w N ≤ 16 * N + 209` for `0 < w`, `N ≤ U`,
  `Fits w U`.
* `init_transition`: initializing from an empty bit-resizable memory (`bitSize = 0`) takes `21`
  instructions and establishes `DictInv` for `Dynamic.empty U` with `totalPotential = 0` and
  `bitSize = 4 * w`.
* `step_transition`: single-step demonic execution and amortized potential bound for any valid
  dictionary operation (`query`, `insert`, `delete`).
* `tsum_stepOverhead_le`: expected amortized cost of any single operation over `epochSeedPMF U N`
  is at most `8034` machine instructions.
* `seq_transition_from_empty`: full operation-sequence theorem from `Dynamic.empty U` establishing
  concrete `BitRAM` execution under demonic `.grow`, exact query results, tight pointwise bit-space
  `OPT(U, V, n_t) + O(n_t log log n_t) + 218 * w` at every step `t`, and telescoped `O(1)` expected
  amortized time per operation.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open scoped ENNReal BigOperators Finset
open Cslib.Probability
open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM

/-! ## Section 1: Linear word bound for `epochMetaWords` and epoch potential algebra -/

/-- Decidability of the epoch capacity invariant `EpochInv U N m`. -/
instance instDecidableEpochInv (U N m : ℕ) : Decidable (EpochInv U N m) := by
  unfold EpochInv; infer_instance

/-- Next abstract dictionary state after executing operation `op` on `s_abs`. -/
@[expose]
def nextState {U : ℕ} (s_abs : Dynamic.State U) (op : Dynamic.Op U) : Dynamic.State U :=
  (Dynamic.step s_abs op).1

/-- Whenever `0 < w` and `k ≤ w`, `packedWords m k w ≤ m + 2`. -/
theorem packedWords_le_add_two_of_le {m k w : ℕ} (hw : 0 < w) (hk : k ≤ w) :
    packedWords m k w ≤ m + 2 := by
  unfold packedWords
  have hmul : m * k ≤ m * w := Nat.mul_le_mul_left m hk
  have hdiv : (m * k + w - 1) / w ≤ m := by
    rw [Nat.div_le_iff_le_mul_add_pred hw, Nat.mul_comm w m]
    omega
  omega

/-- Linear word bound for `epochMetaWords`: whenever `0 < w`, `N ≤ U`, and `Fits w U`,
`epochMetaWords U w N ≤ 16 * N + 209`. -/
theorem epochMetaWords_le_linear {U w N : ℕ} (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U) :
    epochMetaWords U w N ≤ 16 * N + 209 := by
  unfold epochMetaWords
  split_ifs with hN0
  · omega
  · unfold Succinct.lmSubWords
    have hhs : Succinct.hashSpace U w N ≤ 2 * N + 177 := by
      have h1 := Succinct.hashSpace_le hw hNU hU.le
      have h2 : packedWords (2 * N) 1 w ≤ 2 * N + 2 := packedWords_le_add_two_of_le hw hw
      omega
    have heff_w : effBucketPosBits N ≤ w := effBucketPosBits_le_of_lt_pow hNU hU
    have hgp_w : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hNU hU
    have htmb_le : totalMicroBuckets N ≤ N := by
      have h := totalMicroBuckets_le N
      omega
    have hmti_le : maxTailItems N ≤ N := maxTailItems_le N
    have hgm_len : globalMetaLen N ≤ N + 4 := by
      by_cases hb : bucketBits N = 0
      · unfold globalMetaLen globalMetaVarLen
        rw [ite_eq_left hb]
        omega
      · have h := globalMetaLen_le_of_bucketBits_pos (Nat.pos_of_ne_zero hb)
        omega
    have hp_lm : packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤ N + 2 :=
      (packedWords_le_add_two_of_le hw heff_w).trans (by omega)
    have hp_gm : packedWords (globalMetaLen N) (globalPtrBits N) w ≤ N + 6 :=
      (packedWords_le_add_two_of_le hw hgp_w).trans (by omega)
    have hp_td : packedWords (maxTailItems N) (globalPtrBits N) w ≤ N + 2 :=
      (packedWords_le_add_two_of_le hw hgp_w).trans (by omega)
    omega

/-- The active key count `(Dynamic.dom s_abs).card` never exceeds the universe size `U`. -/
theorem card_dom_le_univ {U : ℕ} (s_abs : Dynamic.State U) :
    (Dynamic.dom s_abs).card ≤ U := by
  simpa using Finset.card_le_univ (Dynamic.dom s_abs)

/-- Target epoch capacity `N'` when rebuilding for `m` active keys: `0` when `m = 0`, and
`min U (2 * m)` when `0 < m`. -/
@[expose]
def targetCap (U m : ℕ) : ℕ :=
  if m = 0 then 0 else min U (2 * m)

theorem targetCap_le_univ (U m : ℕ) : targetCap U m ≤ U := by
  unfold targetCap; split_ifs <;> omega

theorem targetCap_le_two_mul (U m : ℕ) : targetCap U m ≤ 2 * m := by
  unfold targetCap; split_ifs <;> omega

/-- `targetCap U m` satisfies `EpochInv U (targetCap U m) m` whenever `m ≤ U`. -/
theorem epochInv_targetCap {U m : ℕ} (hmU : m ≤ U) :
    EpochInv U (targetCap U m) m := by
  unfold EpochInv targetCap
  split_ifs <;> omega

/-- Epoch capacity potential measuring the distance of the active key count `m` from the center of
the current epoch `N`: `(2 * m - N)` when `N < U` and `N - 2 * m` unconditionally. -/
@[expose]
def epochPotential (U N m : ℕ) : ℕ :=
  (if N < U then 2 * m - N else 0) + (N - 2 * m)

@[simp]
theorem epochPotential_zero_zero (U : ℕ) : epochPotential U 0 0 = 0 := by
  unfold epochPotential; split_ifs <;> omega

/-- Right after rebuilding to `targetCap U m`, the epoch potential is identically `0`. -/
@[simp]
theorem epochPotential_targetCap (U m : ℕ) :
    epochPotential U (targetCap U m) m = 0 := by
  unfold epochPotential targetCap
  split_ifs <;> omega

/-- Changing `m` by at most `1` while keeping `N` fixed increases `epochPotential U N m` by at
most `2`. -/
theorem epochPotential_step_le {U N m m' : ℕ} (h1 : m' ≤ m + 1) (h2 : m ≤ m' + 1) :
    epochPotential U N m' ≤ epochPotential U N m + 2 := by
  unfold epochPotential
  split_ifs <;> omega

/-- Whenever `EpochInv U N m` holds, `m' ≤ U`, `|m' - m| ≤ 1`, and `¬ EpochInv U N m'`,
the old and new sizes `m, m'` and capacities `N, targetCap U m'` are linearly bounded by
`epochPotential U N m`. -/
theorem rebuild_bounds_of_not_epochInv {U N m m' : ℕ}
    (hinv : EpochInv U N m) (hm'U : m' ≤ U) (h1 : m' ≤ m + 1) (h2 : m ≤ m' + 1)
    (hnot : ¬ EpochInv U N m') :
    m ≤ 2 * epochPotential U N m + 3 ∧
    m' ≤ 2 * epochPotential U N m + 3 ∧
    N ≤ 4 * epochPotential U N m + 6 ∧
    targetCap U m' ≤ 4 * epochPotential U N m + 6 := by
  unfold EpochInv epochPotential targetCap at *
  split_ifs at * <;> omega

/-- Canonical empty companion witness (`N = 0`, `m = 0`). -/
@[expose]
def Companion.empty : Companion :=
  ⟨⟨fun _ => 0, 0⟩, fun _ => 0, fun _ => 0⟩

/-- `Companion.empty` is a valid companion for `Dynamic.empty U` at `N = 0`. -/
theorem Companion.valid_empty {U V w : ℕ} (hfit0 : Fits w (dictBitSize U V w 0 0))
    (θ₀ : Succinct.QuotHashSeed U 0) :
    Companion.empty.Valid U V w 0 θ₀ (Dynamic.empty U) where
  epoch := by
    have hdom : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
      have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
        ext k
        simp [Dynamic.empty]
      rw [heq, Finset.card_empty]
    rw [hdom]
    exact Or.inl ⟨rfl, rfl⟩
  val_bounded _ _ h := by cases h
  fit_cap := hfit0
  frontier_zero := rfl
  active hpos := by omega

/-- Total dictionary potential combining the in-epoch bucket/window potential
`1008 * c.potential U V w N` and the epoch capacity potential
`2660 * epochPotential U N (Dynamic.dom s_abs).card`. -/
@[expose]
def totalPotential (U V w N : ℕ) (s_abs : Dynamic.State U) (c : Companion) : ℕ :=
  1008 * c.potential U V w N + 2660 * epochPotential U N (Dynamic.dom s_abs).card

@[simp]
theorem totalPotential_empty (U V w : ℕ) (c : Companion) :
    totalPotential U V w 0 (Dynamic.empty U) c = 0 := by
  have hdom : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
      ext k
      simp [Dynamic.empty]
    rw [heq, Finset.card_empty]
  unfold totalPotential Companion.potential
  rw [hdom, epochPotential_zero_zero]
  simp

/-! ## Section 2: Full machine-state dictionary invariant (`DictInv`) -/

/-- Full state and companion invariant for the bit-resizable succinct dictionary at epoch capacity
`N`, epoch hash seed `θ`, abstract state `s_abs`, companion witness `c`, and `BitRAM` machine
state `x : BitRAM.Data 12`. -/
structure DictInv (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (c : Companion) (x : BitRAM.Data 12) : Prop where
  valid : c.Valid U V w N θ s_abs
  wf : x.WellFormed w
  mem_eq : x.toBitMemoryState = c.toBitState U V w N (Dynamic.dom s_abs).card θ

/-- Canonical `BitRAM.Data 12` state with zeroed registers associated with a companion `c`. -/
@[expose]
noncomputable def Companion.canonicalData (c : Companion) (U V w N m : ℕ)
    (θ : Succinct.QuotHashSeed U N) : BitRAM.Data 12 :=
  let s_bit := c.toBitState U V w N m θ
  ⟨fun _ => 0, s_bit.mem, s_bit.bitSize⟩

/-- Any valid companion `c` induces a canonical machine state satisfying `DictInv`. -/
theorem Companion.dictInv_canonicalData {U V w N : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : V ≤ 2 ^ w)
    {θ : Succinct.QuotHashSeed U N} {s_abs : Dynamic.State U} {c : Companion}
    (hval : c.Valid U V w N θ s_abs) :
    DictInv U V w N θ s_abs c
      (c.canonicalData U V w N (Dynamic.dom s_abs).card θ) :=
  ⟨hval, ⟨fun _ => fits_zero w, (hval.rep hw hU hV).wellFormed⟩, rfl⟩

/-- `DictInv` implies the single-tape bit-resizable representation invariant `Rep`. -/
theorem DictInv.rep {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {c : Companion} {x : BitRAM.Data 12}
    (hinv : DictInv U V w N θ s_abs c x) (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w) :
    Rep U V w N θ s_abs x.toBitMemoryState := by
  rw [hinv.mem_eq]
  exact hinv.valid.rep hw hU hV

/-- Under `DictInv`, the machine's live bit allocation `x.bitSize` equals
`dictBitSize U V w N (Dynamic.dom s_abs).card`. -/
theorem DictInv.bitSize_eq {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {c : Companion} {x : BitRAM.Data 12}
    (hinv : DictInv U V w N θ s_abs c x) :
    x.bitSize = dictBitSize U V w N (Dynamic.dom s_abs).card := by
  change x.toBitMemoryState.bitSize = _
  rw [hinv.mem_eq]
  unfold Companion.toBitState buildBitState
  rfl

/-- Under `DictInv`, the machine's live bit allocation `x.bitSize` satisfies the information-
theoretic space bound
`x.bitSize ≤ Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`
in the current active key count `n_t = (Dynamic.dom s_abs).card`. -/
theorem DictInv.space_tight {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {c : Companion} {x : BitRAM.Data 12}
    (hinv : DictInv U V w N θ s_abs c x) (hw : 0 < w) (hU : Fits w U) :
    let n_t := (Dynamic.dom s_abs).card
    x.bitSize ≤
      Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w := by
  rw [hinv.bitSize_eq]
  exact dictBitSize_le_optBits hw hU.le hinv.valid.epoch

/-- Concrete `BitRAM.Code .standard 12` program initializing an empty bit-resizable dictionary
(`N = 0`, `n_t = 0`) from `x.bitSize = 0` in `21` instructions under demonic `.grow`. -/
@[expose]
noncomputable def initDictCode (U V w : ℕ) (θ₀ : Succinct.QuotHashSeed U 0) :
    BitRAM.Code .standard 12 :=
  growWordsRangeCode w (Companion.empty.toBitState U V w 0 0 θ₀) 4

/-- **Initialization transition (`init_transition`):**
starting from an empty bit-resizable memory (`x.bitSize = 0`, `x.WellFormed w`), `initDictCode`
executes in `21` machine instructions under demonic `.grow` and establishes `DictInv` for
`Dynamic.empty U` at `N = 0` with `totalPotential = 0` and `y.bitSize = 4 * w`. -/
theorem init_transition {U V w : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit0 : Fits w (dictBitSize U V w 0 0))
    (θ₀ : Succinct.QuotHashSeed U 0)
    {x : BitRAM.Data 12} (hx_wf : x.WellFormed w) (hx_sz : x.bitSize = 0) :
    BitRAM.DemonicExecWithin w (initDictCode U V w θ₀) x
      (fun y =>
        DictInv U V w 0 θ₀ (Dynamic.empty U) Companion.empty y ∧
        y.bitSize = 4 * w ∧
        totalPotential U V w 0 (Dynamic.empty U) Companion.empty = 0)
      21 := by
  have hval := Companion.valid_empty (U := U) (V := V) (w := w) hfit0 θ₀
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
      ext k
      simp [Dynamic.empty]
    rw [heq, Finset.card_empty]
  have hrep := hval.rep hw hU hV
  rw [hdom0] at hrep
  have htar_wf : (Companion.empty.toBitState U V w 0 0 θ₀).WellFormed w := hrep.wellFormed
  have hd0 : dictBitSize U V w 0 0 = 4 * w := by
    unfold dictBitSize epochMetaBits epochMetaWords; simp
  have hfit4 : Fits w (4 * w) := hd0 ▸ hfit0
  have hexec := growWordsRangeCode_exec (Companion.empty.toBitState U V w 0 0 θ₀) 4
    hw hx_wf htar_wf hx_sz hfit4
  refine hexec.mono ?_ (le_refl 21)
  intro y ⟨hy_wf, hy_sz, hy_mem⟩
  have hy_eq : y.toBitMemoryState = Companion.empty.toBitState U V w 0 0 θ₀ :=
    bitMemoryState_eq_of_meta_and_items (U := U) (V := V) (w := w) (N := 0) (n_t := 0)
      hw hU.le hV hy_wf.mem_wf htar_wf (hy_sz.trans hd0.symm) rfl
      (fun a ha => hy_mem a (by simpa [epochMetaWords] using ha))
      (fun _ hd => by omega)
  have hinv : DictInv U V w 0 θ₀ (Dynamic.empty U) Companion.empty y := by
    refine ⟨hval, hy_wf, ?_⟩
    rw [hdom0]
    exact hy_eq
  exact ⟨hinv, hy_sz, totalPotential_empty U V w Companion.empty⟩

/-! ## Section 3: Single-operation transitions (`query`, `insert`, `delete`) -/

/-- Register-pair decoding `(if y.regs 1 = 0 then none else some (y.regs 0))` for an `Option ℕ`
query result on `BitRAM`. -/
@[expose]
def decodeQueryRegs (y : BitRAM.Data 12) : Option ℕ :=
  if y.regs 1 = 0 then none else some (y.regs 0)

/-- Target key of a dictionary operation `op : Dynamic.Op U`. -/
@[expose]
def opKey {U : ℕ} : Dynamic.Op U → Fin U
  | .query u => u
  | .insert u _ => u
  | .delete u => u

/-- Uniform distribution over the epoch quotient-hash seed type `Succinct.QuotHashSeed U N`. -/
noncomputable abbrev epochSeedPMF (U N : ℕ) : PMF (Succinct.QuotHashSeed U N) :=
  PMF.uniformOfFintype (Succinct.QuotHashSeed U N)

/-- Deterministic per-step amortized instruction bound for operation `op` under epoch seed `θ`. -/
@[expose]
noncomputable def stepOverhead (U N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (op : Dynamic.Op U) : ℕ :=
  7849 + 37 * epochProbeExcess U N θ s_abs (opKey op)

/-- **Expectation bound for `stepOverhead` (`tsum_stepOverhead_le`):**
for any valid epoch (`EpochInv U N (Dynamic.dom s_abs).card`) and any dictionary operation `op`,
the expected value of `stepOverhead U N θ s_abs op` over `θ ← epochSeedPMF U N` is at most
`8034` machine instructions. -/
theorem tsum_stepOverhead_le {U N : ℕ} {s_abs : Dynamic.State U}
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card) (op : Dynamic.Op U) :
    (∑' θ : Succinct.QuotHashSeed U N,
      (epochSeedPMF U N θ : ℝ≥0∞) * ((stepOverhead U N θ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034 := by
  have hnU : N ≤ U := hepoch.cap_le_univ
  have herase : #((Dynamic.dom s_abs).erase (opKey op)) ≤ N :=
    Finset.card_erase_le.trans hepoch.card_le
  simpa [epochSeedPMF] using
    Succinct.tsum_affine_probeExcess_reducedPolyHash_le hnU (Dynamic.dom s_abs)
      (opKey op) herase 7849 37 (fun θ => stepOverhead U N θ s_abs op) (fun _ => le_rfl)

/-- Helper: when an epoch rebuild is triggered (`¬ EpochInv U N m'`), `rebuild_step` to
`N' = targetCap U m'` satisfies the amortized bound
`T + totalPotential U V w N' s_abs' c' ≤ totalPotential U V w N s_abs c + 7849`. -/
theorem rebuild_transition {U V w N : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) {s_abs s_abs' : Dynamic.State U} {c : Companion}
    {x : BitRAM.Data 12} (hinv : DictInv U V w N θ s_abs c x)
    (hval_s' : Dynamic.ValuesBounded V s_abs')
    (hcard1 : (Dynamic.dom s_abs').card ≤ (Dynamic.dom s_abs).card + 1)
    (hcard2 : (Dynamic.dom s_abs).card ≤ (Dynamic.dom s_abs').card + 1)
    (hnot : ¬ EpochInv U N (Dynamic.dom s_abs').card)
    (hfit_all : ∀ N' ≤ U, Fits w (dictBitSize U V w N' N'))
    (θ' : Succinct.QuotHashSeed U (targetCap U (Dynamic.dom s_abs').card)) :
    let N' := targetCap U (Dynamic.dom s_abs').card
    ∃ (c' : Companion) (code : BitRAM.Code .standard 12) (T : ℕ),
      c'.Valid U V w N' θ' s_abs' ∧
      BitRAM.DemonicExecWithin w code x (fun y => DictInv U V w N' θ' s_abs' c' y) T ∧
      T + totalPotential U V w N' s_abs' c' ≤ totalPotential U V w N s_abs c + 7849 := by
  intro N'
  let m := (Dynamic.dom s_abs).card
  let m' := (Dynamic.dom s_abs').card
  have hm'U : m' ≤ U := card_dom_le_univ s_abs'
  have hepoch' : EpochInv U N' m' := epochInv_targetCap hm'U
  have hN'U : N' ≤ U := targetCap_le_univ U m'
  have hfit' : Fits w (dictBitSize U V w N' N') := hfit_all N' hN'U
  let c' := rebuildCompanion U V w N' θ' s_abs' hepoch' hval_s' hfit' hw hU hV
  obtain ⟨hval_c', hpot_c', hexec⟩ :=
    rebuild_step hw hU hV θ' s_abs' hepoch' hval_s' hfit' hinv.wf hinv.bitSize_eq
  refine ⟨c', rebuildSyncCode U V w N m N' m' (c'.toBitState U V w N' m' θ'),
    4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * m',
    hval_c', ?_, ?_⟩
  · exact hexec.mono (fun y ⟨hy_eq, hy_wf⟩ => ⟨hval_c', hy_wf, hy_eq⟩) le_rfl
  · have hNU : N ≤ U := hinv.valid.epoch.cap_le_univ
    have hmeta_N := epochMetaWords_le_linear hw hNU hU
    have hmeta_N' := epochMetaWords_le_linear hw hN'U hU
    obtain ⟨hm_b, hm'_b, hN_b, hN'_b⟩ :=
      rebuild_bounds_of_not_epochInv hinv.valid.epoch hm'U hcard1 hcard2 hnot
    have hepot' : epochPotential U N' m' = 0 := epochPotential_targetCap U m'
    unfold totalPotential
    rw [hepot']
    dsimp only [m, m', N', c'] at hm_b hm'_b hN_b hN'_b hmeta_N hmeta_N' hpot_c' ⊢
    omega

/-- Helper: deleting any key from `Dynamic.empty U` leaves `Dynamic.empty U` unchanged. -/
theorem update_empty_none {U : ℕ} (u : Fin U) :
    Function.update (Dynamic.empty U) u none = Dynamic.empty U := by
  funext k
  by_cases h : k = u
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h]

/-- Helper: if `(Dynamic.dom s_abs).card = 0`, then `s_abs = Dynamic.empty U`. -/
theorem eq_empty_of_card_dom_eq_zero {U : ℕ} {s_abs : Dynamic.State U}
    (h0 : (Dynamic.dom s_abs).card = 0) :
    s_abs = Dynamic.empty U := by
  have hdom : Dynamic.dom s_abs = ∅ := Finset.card_eq_zero.mp h0
  funext k
  by_cases hsome : (s_abs k).isSome
  · have hk : k ∈ Dynamic.dom s_abs := mem_dom_iff_isSome.mpr hsome
    rw [hdom] at hk
    exact False.elim (Finset.notMem_empty k hk)
  · exact Option.not_isSome_iff_eq_none.mp hsome

/-- Next epoch capacity after executing `op` on abstract state `s_abs` from current epoch capacity
`N`: remains `N` if `EpochInv U N m'` still holds, and otherwise rebuilds to `targetCap U m'`. -/
@[expose]
def nextEpochCap {U : ℕ} (N : ℕ) (s_abs : Dynamic.State U) (op : Dynamic.Op U) : ℕ :=
  let m' := (Dynamic.dom (nextState s_abs op)).card
  if EpochInv U N m' then N else targetCap U m'

/-- `nextEpochCap` always satisfies `EpochInv` for the post-operation key count. -/
theorem epochInv_nextEpochCap {U N : ℕ} (s_abs : Dynamic.State U) (op : Dynamic.Op U) :
    EpochInv U (nextEpochCap N s_abs op) (Dynamic.dom (nextState s_abs op)).card := by
  unfold nextEpochCap
  dsimp only
  split_ifs with h
  · exact h
  · exact epochInv_targetCap (card_dom_le_univ (nextState s_abs op))

/-- **In-epoch single-operation transition (`step_transition_inEpoch`):**
when the post-operation key count still satisfies `EpochInv U N m'`, `op` executes within the
current epoch `(N, θ)` with amortized cost at most `stepOverhead U N θ s_abs op`. -/
theorem step_transition_inEpoch {U V w N : ℕ} (hw : 4 ≤ w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {c : Companion}
    {x : BitRAM.Data 12} (hinv : DictInv U V w N θ s_abs c x)
    (op : Dynamic.Op U) (hval_op : (spec U V).valid s_abs op)
    (hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs op)).card) :
    let s_abs' := nextState s_abs op
    ∃ (c' : Companion) (code : BitRAM.Code .standard 12) (T : ℕ),
      c'.Valid U V w N θ s_abs' ∧
      BitRAM.DemonicExecWithin w code x
        (fun y =>
          DictInv U V w N θ s_abs' c' y ∧
          (∀ u, op = .query u → decodeQueryRegs y = s_abs u)) T ∧
      T + totalPotential U V w N s_abs' c' ≤
        totalPotential U V w N s_abs c + stepOverhead U N θ s_abs op := by
  have hw0 : 0 < w := by omega
  cases op with
  | query u =>
    have hrep := hinv.rep hw0 hU hV
    let L : ℕ → ℕ → List ℕ :=
      if hN : 0 < N then Classical.choose (hrep.active_inv hN).2.2 else fun _ _ => []
    have hL : 0 < N → BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
        (Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs) x.toBitMemoryState := by
      intro hN
      dsimp only [L]
      rw [dite_eq_left hN]
      exact Classical.choose_spec (hrep.active_inv hN).2.2
    have hexec := queryCode_exec hw0 hU hV hinv.wf hrep hL u
    let pe := if N = 0 then 0 else
      probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u
    have hpe_le : pe ≤ epochProbeExcess U N θ s_abs u := by
      dsimp only [pe, epochProbeExcess]; split_ifs <;> omega
    refine ⟨c, queryCode U V w N θ (gmAtBit U w N x.mem) (tdAtBit U w N x.mem) L u,
      111 + 37 * pe, hinv.valid, ?_, ?_⟩
    · refine hexec.mono (fun y ⟨hy_eq, _, hy_wf, hy_res, _⟩ => ⟨⟨hinv.valid, hy_wf, ?_⟩, ?_⟩) le_rfl
      · rw [hy_eq, hinv.mem_eq]; rfl
      · intro u' hu'
        injection hu' with hu_eq
        subst hu_eq
        exact hy_res
    · unfold stepOverhead opKey
      dsimp only [nextState, Dynamic.step]
      omega
  | insert u v =>
    have hv : v < V := hval_op
    let s_abs' := nextState s_abs (.insert u v)
    let m := (Dynamic.dom s_abs).card
    let m' := (Dynamic.dom s_abs').card
    have hcard1 : m' ≤ m + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hcard := Dictionary.card_dom_insert_eq_of_isSome hsome v
        change m' = m at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
        change m' = m + 1 at hcard; omega
    have hcard2 : m ≤ m' + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hcard := Dictionary.card_dom_insert_eq_of_isSome hsome v
        change m' = m at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
        change m' = m + 1 at hcard; omega
    have hm'_pos : 0 < m' := by
      refine Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr ?_⟩
      change (Function.update s_abs u (some v) u).isSome
      simp
    have hN_pos : 0 < N := by
      rcases hepoch' with ⟨hm0, _⟩ | ⟨_, hlo, _, _⟩
      · dsimp only [m', s_abs'] at hm'_pos; omega
      · dsimp only [m', s_abs'] at hm'_pos; omega
    obtain ⟨c', T, hval_c', hexec, hcost⟩ :=
      inEpoch_insert_step hw0 hU hV θ hinv.valid hN_pos u v hv hepoch' hinv.wf hinv.mem_eq
    have hepot := epochPotential_step_le (U := U) (N := N) hcard1 hcard2
    refine ⟨c', inEpochSyncCode U V w N m m' x.toBitMemoryState (c'.toBitState U V w N m' θ),
      T, hval_c', ?_, ?_⟩
    · exact hexec.mono (fun y ⟨hy_eq, hy_wf⟩ =>
        ⟨⟨hval_c', hy_wf, hy_eq⟩, fun _ h => by nomatch h⟩) le_rfl
    · unfold totalPotential stepOverhead opKey
      dsimp only [m, m', s_abs', nextState, Dynamic.step] at hcost hepot ⊢
      omega
  | delete u =>
    let s_abs' := nextState s_abs (.delete u)
    let m := (Dynamic.dom s_abs).card
    let m' := (Dynamic.dom s_abs').card
    have hcard1 : m' ≤ m + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hpos : 0 < m := Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
        have hcard := Dynamic.card_dom_delete_eq_of_isSome hsome
        change m' = m - 1 at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dynamic.card_dom_delete_eq_of_eq_none hnone
        change m' = m at hcard; omega
    have hcard2 : m ≤ m' + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hpos : 0 < m := Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
        have hcard := Dynamic.card_dom_delete_eq_of_isSome hsome
        change m' = m - 1 at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dynamic.card_dom_delete_eq_of_eq_none hnone
        change m' = m at hcard; omega
    by_cases hN0 : N = 0
    · subst hN0
      have hm0 : m = 0 := by
        rcases hinv.valid.epoch with ⟨h0, _⟩ | ⟨_, _, hhi, _⟩
        · exact h0
        · omega
      have hs_empty : s_abs = Dynamic.empty U := eq_empty_of_card_dom_eq_zero hm0
      have hs'_eq : s_abs' = s_abs := by
        change Function.update s_abs u none = s_abs
        rw [hs_empty, update_empty_none]
      have hx_set : x.set 0 (x.regs 0) = x := by
        cases x; simp [BitRAM.Data.set]
      refine ⟨c, .op (.copy 0 0), 1, ?_, ?_, ?_⟩
      · dsimp only [s_abs'] at hs'_eq ⊢
        rw [hs'_eq]
        exact hinv.valid
      · refine DemonicExecWithin.copy ?_
        rw [hx_set]
        refine ⟨?_, fun _ h => by nomatch h⟩
        dsimp only [s_abs'] at hs'_eq ⊢
        rw [hs'_eq]
        exact hinv
      · unfold stepOverhead opKey
        dsimp only [s_abs'] at hs'_eq ⊢
        rw [hs'_eq]
        omega
    · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
      obtain ⟨c', T, hval_c', hexec, hcost⟩ :=
        inEpoch_delete_step hw0 hU hV θ hinv.valid hN_pos u hepoch' hinv.wf hinv.mem_eq
      have hepot := epochPotential_step_le (U := U) (N := N) hcard1 hcard2
      refine ⟨c', inEpochSyncCode U V w N m m' x.toBitMemoryState (c'.toBitState U V w N m' θ),
        T, hval_c', ?_, ?_⟩
      · exact hexec.mono (fun y ⟨hy_eq, hy_wf⟩ =>
          ⟨⟨hval_c', hy_wf, hy_eq⟩, fun _ h => by nomatch h⟩) le_rfl
      · unfold totalPotential stepOverhead opKey
        dsimp only [m, m', s_abs', nextState, Dynamic.step] at hcost hepot ⊢
        omega

/-- **Rebuild single-operation transition (`step_transition_rebuild`):**
when the post-operation key count violates `EpochInv U N m'`, `op` triggers a full epoch rebuild
to `N' = targetCap U m'` under any new epoch seed `θ_re` with amortized cost at most
`stepOverhead U N θ s_abs op`. -/
theorem step_transition_rebuild {U V w N : ℕ} (hw : 4 ≤ w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_all : ∀ N' ≤ U, Fits w (dictBitSize U V w N' N'))
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {c : Companion}
    {x : BitRAM.Data 12} (hinv : DictInv U V w N θ s_abs c x)
    (op : Dynamic.Op U) (hval_op : (spec U V).valid s_abs op)
    (hnot : ¬ EpochInv U N (Dynamic.dom (nextState s_abs op)).card)
    (θ_re : Succinct.QuotHashSeed U
      (targetCap U (Dynamic.dom (nextState s_abs op)).card)) :
    let s_abs' := nextState s_abs op
    let N' := targetCap U (Dynamic.dom s_abs').card
    ∃ (c' : Companion) (code : BitRAM.Code .standard 12) (T : ℕ),
      c'.Valid U V w N' θ_re s_abs' ∧
      BitRAM.DemonicExecWithin w code x
        (fun y =>
          DictInv U V w N' θ_re s_abs' c' y ∧
          (∀ u, op = .query u → decodeQueryRegs y = s_abs u)) T ∧
      T + totalPotential U V w N' s_abs' c' ≤
        totalPotential U V w N s_abs c + stepOverhead U N θ s_abs op := by
  have hw0 : 0 < w := by omega
  cases op with
  | query u =>
    exact False.elim (hnot hinv.valid.epoch)
  | insert u v =>
    have hv : v < V := hval_op
    let s_abs' := nextState s_abs (.insert u v)
    let m := (Dynamic.dom s_abs).card
    let m' := (Dynamic.dom s_abs').card
    have hcard1 : m' ≤ m + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hcard := Dictionary.card_dom_insert_eq_of_isSome hsome v
        change m' = m at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
        change m' = m + 1 at hcard; omega
    have hcard2 : m ≤ m' + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hcard := Dictionary.card_dom_insert_eq_of_isSome hsome v
        change m' = m at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
        change m' = m + 1 at hcard; omega
    have hval_s' : Dynamic.ValuesBounded V s_abs' := by
      intro k w_val hkw
      change Function.update s_abs u (some v) k = some w_val at hkw
      by_cases hku : k = u
      · subst hku; rw [Function.update_self] at hkw; injection hkw with hvw; subst hvw; exact hv
      · rw [Function.update_of_ne hku] at hkw; exact hinv.valid.val_bounded k w_val hkw
    obtain ⟨c', code, T, hval_c', hexec, hcost⟩ :=
      rebuild_transition hw0 hU hV θ hinv hval_s' hcard1 hcard2 hnot hfit_all θ_re
    refine ⟨c', code, T, hval_c', ?_, ?_⟩
    · exact hexec.mono (fun y hy => ⟨hy, fun _ h => by nomatch h⟩) le_rfl
    · unfold stepOverhead opKey
      dsimp only [s_abs'] at hcost ⊢
      omega
  | delete u =>
    let s_abs' := nextState s_abs (.delete u)
    let m := (Dynamic.dom s_abs).card
    let m' := (Dynamic.dom s_abs').card
    have hcard1 : m' ≤ m + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hpos : 0 < m := Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
        have hcard := Dynamic.card_dom_delete_eq_of_isSome hsome
        change m' = m - 1 at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dynamic.card_dom_delete_eq_of_eq_none hnone
        change m' = m at hcard; omega
    have hcard2 : m ≤ m' + 1 := by
      by_cases hsome : (s_abs u).isSome
      · have hpos : 0 < m := Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
        have hcard := Dynamic.card_dom_delete_eq_of_isSome hsome
        change m' = m - 1 at hcard; omega
      · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
        have hcard := Dynamic.card_dom_delete_eq_of_eq_none hnone
        change m' = m at hcard; omega
    have hval_s' : Dynamic.ValuesBounded V s_abs' := by
      intro k w_val hkw
      change Function.update s_abs u none k = some w_val at hkw
      by_cases hku : k = u
      · subst hku; simp at hkw
      · rw [Function.update_of_ne hku] at hkw; exact hinv.valid.val_bounded k w_val hkw
    obtain ⟨c', code, T, hval_c', hexec, hcost⟩ :=
      rebuild_transition hw0 hU hV θ hinv hval_s' hcard1 hcard2 hnot hfit_all θ_re
    refine ⟨c', code, T, hval_c', ?_, ?_⟩
    · exact hexec.mono (fun y hy => ⟨hy, fun _ h => by nomatch h⟩) le_rfl
    · unfold stepOverhead opKey
      dsimp only [s_abs'] at hcost ⊢
      omega

/-- **Unified single-operation transition (`step_transition`):**
from any state `(N, θ, s_abs, c, x)` satisfying `DictInv U V w N θ s_abs c x` and any valid
operation `op : Dynamic.Op U` (`(spec U V).valid s_abs op`), there exist a post-operation epoch
capacity `N'`, seed `θ'`, companion `c'`, concrete program `code : BitRAM.Code .standard 12`,
and step bound `T : ℕ` such that:
1. `code` executes from `x` in at most `T` instructions under demonic `.grow`,
2. every post-state `y` satisfies `DictInv U V w N' θ' (nextState s_abs op) c' y`, and if
   `op = .query u`, `decodeQueryRegs y = s_abs u`, and
3. `T + totalPotential U V w N' (nextState s_abs op) c' ≤`
   `totalPotential U V w N s_abs c + stepOverhead U N θ s_abs op`. -/
theorem step_transition {U V w N : ℕ} (hw : 4 ≤ w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_all : ∀ N' ≤ U, Fits w (dictBitSize U V w N' N'))
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {c : Companion}
    {x : BitRAM.Data 12} (hinv : DictInv U V w N θ s_abs c x)
    (op : Dynamic.Op U) (hval_op : (spec U V).valid s_abs op)
    (θ_re : Succinct.QuotHashSeed U
      (targetCap U (Dynamic.dom (nextState s_abs op)).card)) :
    let s_abs' := nextState s_abs op
    ∃ (N' : ℕ) (θ' : Succinct.QuotHashSeed U N') (c' : Companion)
      (code : BitRAM.Code .standard 12) (T : ℕ),
      EpochInv U N' (Dynamic.dom s_abs').card ∧
      BitRAM.DemonicExecWithin w code x
        (fun y =>
          DictInv U V w N' θ' s_abs' c' y ∧
          (∀ u, op = .query u → decodeQueryRegs y = s_abs u)) T ∧
      T + totalPotential U V w N' s_abs' c' ≤
        totalPotential U V w N s_abs c + stepOverhead U N θ s_abs op := by
  by_cases hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs op)).card
  · obtain ⟨c', code, T, _, hexec, hcost⟩ :=
      step_transition_inEpoch hw hU hV θ hinv op hval_op hepoch'
    exact ⟨N, θ, c', code, T, hepoch', hexec, hcost⟩
  · obtain ⟨c', code, T, _, hexec, hcost⟩ :=
      step_transition_rebuild hw hU hV hfit_all θ hinv op hval_op hepoch' θ_re
    refine ⟨targetCap U (Dynamic.dom (nextState s_abs op)).card, θ_re, c', code, T, ?_,
      hexec, hcost⟩
    exact epochInv_targetCap (card_dom_le_univ (nextState s_abs op))

/-! ## Section 4: Multi-operation execution trace and sequence theorems from empty -/

/-- Recursive execution trace of concrete `BitRAM.Code .standard 12` programs under demonic `.grow`
(`BitRAM.DemonicExecWithin`) across an arbitrary valid operation sequence
`ops : List (Dynamic.Op U)` starting from state `(N, θ, s_abs, c, x)` with total amortized
instruction budget `B_tot`. -/
def ExecTrace (U V w : ℕ) :
    List (Dynamic.Op U) → ∀ (N : ℕ), Succinct.QuotHashSeed U N → Dynamic.State U →
      Companion → BitRAM.Data 12 → ℕ → Prop
  | [], N, θ, s_abs, c, x, B_tot =>
    DictInv U V w N θ s_abs c x ∧ B_tot = 0
  | op :: ops, N, θ, s_abs, c, x, B_tot =>
    DictInv U V w N θ s_abs c x ∧
    (∑' θ₀ : Succinct.QuotHashSeed U N,
      (epochSeedPMF U N θ₀ : ℝ≥0∞) * ((stepOverhead U N θ₀ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
    ∃ (N' : ℕ) (θ' : Succinct.QuotHashSeed U N') (c' : Companion)
      (code : BitRAM.Code .standard 12) (T B_rest : ℕ),
      B_tot = stepOverhead U N θ s_abs op + B_rest ∧
      T + totalPotential U V w N' (nextState s_abs op) c' ≤
        totalPotential U V w N s_abs c + stepOverhead U N θ s_abs op ∧
      (∃ ts_rest : List ℕ,
        ts_rest.length = ops.length ∧
        ts_rest.sum ≤ totalPotential U V w N' (nextState s_abs op) c' + B_rest) ∧
      BitRAM.DemonicExecWithin w code x
        (fun y =>
          DictInv U V w N' θ' (nextState s_abs op) c' y ∧
          (∀ u, op = .query u → decodeQueryRegs y = s_abs u) ∧
          ExecTrace U V w ops N' θ' (nextState s_abs op) c' y B_rest)
        T

/-- Every `ExecTrace` decomposes into an explicit sequence of step instruction bounds `ts : List ℕ`
with `ts.length = ops.length` whose sum `ts.sum` is bounded by
`totalPotential U V w N s_abs c + B_tot`. -/
theorem ExecTrace.exists_step_list {U V w : ℕ} {ops : List (Dynamic.Op U)}
    {N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {c : Companion} {x : BitRAM.Data 12}
    {B_tot : ℕ}
    (htrace : ExecTrace U V w ops N θ s_abs c x B_tot) :
    ∃ ts : List ℕ,
      ts.length = ops.length ∧
      ts.sum ≤ totalPotential U V w N s_abs c + B_tot := by
  cases ops with
  | nil =>
    rcases htrace with ⟨_, rfl⟩
    exact ⟨[], rfl, by simp⟩
  | cons op ops =>
    rcases htrace with ⟨_, _, N', θ', c', code, T, B_rest, rfl, hstep, ⟨ts, hlen, hsum⟩, _⟩
    refine ⟨T :: ts, by simp [hlen], ?_⟩
    simp only [List.sum_cons]
    omega

/-- For any valid operation sequence `ops` (`(spec U V).ValidHistory s_abs ops`) and any starting
epoch `(N, θ, s_abs)` with `EpochInv U N (Dynamic.dom s_abs).card`, there exists an amortized
instruction budget `B_tot : ℕ` such that every `(c, x)` satisfying `DictInv U V w N θ s_abs c x`
admits a full demonic execution trace `ExecTrace U V w ops N θ s_abs c x B_tot`. -/
theorem exists_execTrace {U V w : ℕ} (hw : 4 ≤ w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_all : ∀ N' ≤ U, Fits w (dictBitSize U V w N' N'))
    (ops : List (Dynamic.Op U)) :
    ∀ {N : ℕ} (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U},
      EpochInv U N (Dynamic.dom s_abs).card →
      (spec U V).ValidHistory s_abs ops →
      ∃ B_tot : ℕ,
        ∀ {c : Companion} {x : BitRAM.Data 12},
          DictInv U V w N θ s_abs c x →
          ExecTrace U V w ops N θ s_abs c x B_tot := by
  have hw0 : 0 < w := by omega
  induction ops with
  | nil =>
    intro N θ s_abs _ _
    exact ⟨0, fun hinv => ⟨hinv, rfl⟩⟩
  | cons op ops ih =>
    intro N θ s_abs hepoch hvh
    rcases hvh with ⟨hval_op, hvh_rest⟩
    have htsum := tsum_stepOverhead_le hepoch op
    by_cases hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs op)).card
    · obtain ⟨B_rest, hrest⟩ := ih θ hepoch' hvh_rest
      refine ⟨stepOverhead U N θ s_abs op + B_rest, ?_⟩
      intro c x hinv
      obtain ⟨c', code, T, hval_c', hexec, hcost⟩ :=
        step_transition_inEpoch hw hU hV θ hinv op hval_op hepoch'
      have hcan := Companion.dictInv_canonicalData hw0 hU hV hval_c'
      have hts := (hrest hcan).exists_step_list
      refine ⟨hinv, htsum, N, θ, c', code, T, B_rest, rfl, hcost, hts, ?_⟩
      exact hexec.mono (fun y ⟨hinv_y, hq_y⟩ => ⟨hinv_y, hq_y, hrest hinv_y⟩) le_rfl
    · have : Nonempty (Succinct.QuotHashSeed U
          (targetCap U (Dynamic.dom (nextState s_abs op)).card)) := inferInstance
      let θ_re := Classical.arbitrary (Succinct.QuotHashSeed U
        (targetCap U (Dynamic.dom (nextState s_abs op)).card))
      let N' := targetCap U (Dynamic.dom (nextState s_abs op)).card
      have hepoch_re : EpochInv U N' (Dynamic.dom (nextState s_abs op)).card :=
        epochInv_targetCap (card_dom_le_univ (nextState s_abs op))
      obtain ⟨B_rest, hrest⟩ := ih θ_re hepoch_re hvh_rest
      refine ⟨stepOverhead U N θ s_abs op + B_rest, ?_⟩
      intro c x hinv
      obtain ⟨c', code, T, hval_c', hexec, hcost⟩ :=
        step_transition_rebuild hw hU hV hfit_all θ hinv op hval_op hepoch' θ_re
      have hcan := Companion.dictInv_canonicalData hw0 hU hV hval_c'
      have hts := (hrest hcan).exists_step_list
      refine ⟨hinv, htsum, N', θ_re, c', code, T, B_rest, rfl, hcost, hts, ?_⟩
      exact hexec.mono (fun y ⟨hinv_y, hq_y⟩ => ⟨hinv_y, hq_y, hrest hinv_y⟩) le_rfl

/-- **Full operation-sequence theorem from `Dynamic.empty U` (`seq_transition_from_empty`):**
starting from an empty bit-resizable memory (`x₀.bitSize = 0`, `x₀.WellFormed w`), `initDictCode`
followed by any valid operation sequence `ops : List (Dynamic.Op U)`
(`(spec U V).ValidHistory (Dynamic.empty U) ops`) executes on the `w`-bit `BitRAM` under demonic
`.grow` such that:
1. initialization takes `21` machine instructions and allocates `4 * w` bits,
2. at every operation step `t`, the machine state `x_t` satisfies `DictInv` for the current
   abstract state `s_t` and therefore uses at most
   `Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w` bits in the current
   active key count `n_t = (Dynamic.dom s_t).card` (via `DictInv.space_tight`),
3. every `.query u` writes the query answer into registers (`decodeQueryRegs y = s_t u`), and
4. the total number of executed machine instructions across all `ops.length` operations is
   bounded by `B_tot` (`ts.sum ≤ B_tot`, since `totalPotential = 0` at `Dynamic.empty U`), where
   every step's amortized overhead has expectation at most `8034` (`O(1)` expected amortized
   time). -/
theorem seq_transition_from_empty {U V w : ℕ} (hw : 4 ≤ w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_all : ∀ N' ≤ U, Fits w (dictBitSize U V w N' N'))
    (θ₀ : Succinct.QuotHashSeed U 0)
    {x₀ : BitRAM.Data 12} (hx_wf : x₀.WellFormed w) (hx_sz : x₀.bitSize = 0)
    (ops : List (Dynamic.Op U)) (hvh : (spec U V).ValidHistory (Dynamic.empty U) ops) :
    ∃ B_tot : ℕ,
      BitRAM.DemonicExecWithin w (initDictCode U V w θ₀) x₀
        (fun y₀ =>
          DictInv U V w 0 θ₀ (Dynamic.empty U) Companion.empty y₀ ∧
          y₀.bitSize = 4 * w ∧
          ExecTrace U V w ops 0 θ₀ (Dynamic.empty U) Companion.empty y₀ B_tot ∧
          ∃ ts : List ℕ, ts.length = ops.length ∧ ts.sum ≤ B_tot)
        21 := by
  have hw0 : 0 < w := by omega
  have hepoch0 : EpochInv U 0 (Dynamic.dom (Dynamic.empty U)).card := by
    have hdom : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
      have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
        ext k
        simp [Dynamic.empty]
      rw [heq, Finset.card_empty]
    rw [hdom]
    exact Or.inl ⟨rfl, rfl⟩
  have hfit0 : Fits w (dictBitSize U V w 0 0) := hfit_all 0 (Nat.zero_le U)
  obtain ⟨B_tot, htrace_all⟩ := exists_execTrace hw hU hV hfit_all ops θ₀ hepoch0 hvh
  refine ⟨B_tot, ?_⟩
  have hinit := init_transition (U := U) (V := V) (w := w) hw0 hU hV hfit0 θ₀ hx_wf hx_sz
  refine hinit.mono ?_ (le_refl 21)
  intro y₀ ⟨hinv₀, hsz₀, hpot₀⟩
  have htr := htrace_all hinv₀
  obtain ⟨ts, hlen, hsum⟩ := htr.exists_step_list
  rw [hpot₀, zero_add] at hsum
  exact ⟨hinv₀, hsz₀, htr, ts, hlen, hsum⟩

end Cslib.DataStructure.Dictionary.BitResizable
