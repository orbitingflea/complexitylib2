/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.EpochStep

/-!
# Bit-Resizable Dynamic Dictionary Sequences, Multi-Epoch Hysteresis, and Amortized Analysis

This module provides two complementary layers on top of `EpochStep.lean`:

1. **Uniform compiled in-epoch operation-sequence execution (`BitRAM.Code .standard 280`):**
   Using the fixed parameter-free machine programs `initEmptyRegCode` and `inEpochStepRegCode`
   (defined independently of `U, V, w, N, θ, x₀, ops`), any valid operation sequence `ops` keeping
   the active key count inside `EpochInv U N n_t` executes operationally on the `w`-bit `BitRAM`
   under any demonic `.grow` oracle (`DirtyGrowOracle w oracle`) such that:
   * every `.query u` writes `s_t u` into `(r0, r1)` (`OpOutputCorrect`),
   * every post-state `y_t` satisfies `Rep U V w N θ s_t y_t.toBitMemoryState` with exact bit
     allocation `y_t.bitSize = dictBitSize U V w N n_t` bounded by
     `Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`, and
   * the concrete executed instruction counts `ts : List ℕ` satisfy
     `ts.sum + 1967 * inEpochPotential U V w N s_fix_f ≤`
     `1967 * inEpochPotential U V w N s_fix₀ + inEpochSeqOverhead U N θ s_abs ops`,
     where the uniform expectation of `inEpochSeqOverhead U N θ s_abs ops` over
     `θ ← epochSeedPMF U N` is at most `294450 * ops.length` (`O(1)` expected amortized
     instructions per operation).

2. **Pure mathematical multi-epoch hysteresis, reached-capacity fit, rebuild potential, and
   Feistel key recovery (not compiled to `BitRAM.Code` across epoch capacity changes):**
   Across arbitrary unbounded `insert`/`delete`/`query` sequences from `(N = 0, Dynamic.empty U)`:
   * `ReachedEpochsFit` requires `Fits w (dictBitSize U V w N_t N_t)` only for capacities `N_t`
     actually reached along `ops` (holding even for `U = 2 ^ w - 1` and `V = 2 ^ w` whenever
     reached active sizes fit in memory),
   * `nextEpochCap` maintains `EpochInv U N_t n_t` and the succinct space bound
     `dictBitSize U V w N_t n_t ≤ Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t`
     `+ 218 * w` at every step,
   * `epochPotential` (`2660 * epochPotential U N m`) pays for linear `O(N + N' + m + m')` epoch
     rebuilds (`pureMultiEpochStep_amortized_le`), and
   * `rep_feistel_reconstruct_active_slot` and `rep_exists_active_slot_of_some` certify lossless
     key recovery `(b, q) ↔ u` via `feistelReconstruct` from any active `Rep` state during an
     epoch rebuild.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.nextState`: post-operation abstract state.
* `Cslib.DataStructure.Dictionary.BitResizable.targetCap`, `nextEpochCap`, `epochPotential`:
  multi-epoch hysteresis policy and capacity potential.
* `Cslib.DataStructure.Dictionary.BitResizable.InEpochHistory`, `inEpochSeqOverhead`,
  `InEpochOracleTrace`: uniform compiled in-epoch sequence predicates and concrete overhead sum.
* `Cslib.DataStructure.Dictionary.BitResizable.ReachedEpochsFit`, `MaxCardLe`,
  `PureMultiEpochSpaceTrace`: non-vacuous reached-capacity fit and pure multi-epoch trajectory.

## Main results

* `tsum_inEpochSeqOverhead_le`: expected value of `inEpochSeqOverhead` over `epochSeedPMF U N` is
  at most `294450 * ops.length`.
* `inEpochStepRegCode_oracle_seq`: uniform compiled execution of `inEpochStepRegCode` across any
  valid in-epoch operation sequence under any `DirtyGrowOracle w oracle`.
* `initEmptyRegCode_oracle`: uniform compiled empty initialization from `x₀.bitSize = 0` in
  `8 * w + 37` instructions.
* `reachedEpochsFit_of_maxCardLe`: `ReachedEpochsFit` holds whenever active counts stay bounded by
  `M` and capacities `≤ min U (2 * M)` fit in `w` bits.
* `pureMultiEpoch_space_and_hysteresis_from_empty`: pure multi-epoch hysteresis and tight space at
  every step from `(0, Dynamic.empty U)`.
* `pureMultiEpochStep_amortized_le`: pure potential bound paying for `O(N + N' + m + m')` rebuilds.
* `rep_feistel_reconstruct_active_slot`, `rep_exists_active_slot_of_some`: lossless Feistel key
  recovery on `Rep`.
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

/-! ## Section 1: Epoch geometry linear word bound and hysteresis / potential algebra -/

/-- Decidability of the epoch capacity invariant `EpochInv U N m`. -/
instance instDecidableEpochInv (U N m : ℕ) : Decidable (EpochInv U N m) :=
  inferInstanceAs (Decidable ((m = 0 ∧ N = 0) ∨ (1 ≤ m ∧ m ≤ N ∧ N ≤ 4 * m ∧ N ≤ U)))

/-- Next abstract dictionary state after executing operation `op` on `s_abs`. -/
@[expose]
def nextState {U : ℕ} (s_abs : Dynamic.State U) (op : Dynamic.Op U) : Dynamic.State U :=
  (Dynamic.step s_abs op).1

/-- Uniform distribution over the epoch quotient-hash seed type `Succinct.QuotHashSeed U N`. -/
noncomputable abbrev epochSeedPMF (U N : ℕ) : PMF (Succinct.QuotHashSeed U N) :=
  PMF.uniformOfFintype (Succinct.QuotHashSeed U N)

/-- Any single dictionary operation changes the active key count `(Dynamic.dom s_abs).card` by at
most `1`. -/
theorem card_dom_nextState_step_le {U : ℕ} (s_abs : Dynamic.State U) (op : Dynamic.Op U) :
    (Dynamic.dom (nextState s_abs op)).card ≤ (Dynamic.dom s_abs).card + 1 ∧
    (Dynamic.dom s_abs).card ≤ (Dynamic.dom (nextState s_abs op)).card + 1 := by
  cases op with
  | query u =>
    dsimp only [nextState, Dynamic.step]
    omega
  | insert u v =>
    dsimp only [nextState, Dynamic.step]
    by_cases hsome : (s_abs u).isSome
    · have hcard := Dictionary.card_dom_insert_eq_of_isSome hsome v
      change (Dynamic.dom (Function.update s_abs u (some v))).card =
        (Dynamic.dom s_abs).card at hcard
      omega
    · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
      have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
      change (Dynamic.dom (Function.update s_abs u (some v))).card =
        (Dynamic.dom s_abs).card + 1 at hcard
      omega
  | delete u =>
    dsimp only [nextState, Dynamic.step]
    by_cases hsome : (s_abs u).isSome
    · have hpos : 0 < (Dynamic.dom s_abs).card :=
        Finset.card_pos.mpr ⟨u, Dictionary.mem_dom_iff_isSome.mpr hsome⟩
      have hcard := Dynamic.card_dom_delete_eq_of_isSome hsome
      omega
    · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
      have hcard := Dynamic.card_dom_delete_eq_of_eq_none hnone
      omega

/-- Unbounded admissibility `(spec U V).valid s_abs op` preserves `Dynamic.ValuesBounded V`. -/
theorem valuesBounded_nextState {U V : ℕ} {s_abs : Dynamic.State U} {op : Dynamic.Op U}
    (hvb : Dynamic.ValuesBounded V s_abs) (hval : (spec U V).valid s_abs op) :
    Dynamic.ValuesBounded V (nextState s_abs op) := by
  cases op with
  | query _ => exact hvb
  | insert u v =>
    intro k w_val hkw
    change Function.update s_abs u (some v) k = some w_val at hkw
    by_cases hku : k = u
    · subst hku; rw [Function.update_self] at hkw; injection hkw with hvw; subst hvw; exact hval
    · rw [Function.update_of_ne hku] at hkw; exact hvb k w_val hkw
  | delete u =>
    intro k w_val hkw
    change Function.update s_abs u none k = some w_val at hkw
    by_cases hku : k = u
    · subst hku; simp at hkw
    · rw [Function.update_of_ne hku] at hkw; exact hvb k w_val hkw

/-- Whenever `(spec U V).valid s_abs op` holds and the post-operation key count satisfies
`(Dynamic.dom (nextState s_abs op)).card ≤ N`, the bounded-capacity precondition
`(Dynamic.spec U V N).valid s_abs op` holds as well. -/
theorem dynamic_valid_of_spec_valid {U V N : ℕ} {s_abs : Dynamic.State U} {op : Dynamic.Op U}
    (hval : (spec U V).valid s_abs op)
    (hcard' : (Dynamic.dom (nextState s_abs op)).card ≤ N) :
    (Dynamic.spec U V N).valid s_abs op := by
  cases op with
  | query _ => trivial
  | delete _ => trivial
  | insert u v =>
    refine ⟨?_, hval⟩
    by_cases hsome : (s_abs u).isSome
    · exact Or.inr hsome
    · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
      have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
      change (Dynamic.dom (nextState s_abs (.insert u v))).card =
        (Dynamic.dom s_abs).card + 1 at hcard
      exact Or.inl (by omega)

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
  · exact epochInv_targetCap (Dynamic.card_dom_le_univ (nextState s_abs op))

/-! ## Section 2: Uniform compiled in-epoch sequence execution (`BitRAM.Code .standard 280`) -/

/-- Predicate stating that an operation sequence `ops` starts from a capacity-bounded state
(`N ≤ U`, `(Dynamic.dom s_abs).card ≤ N`) and keeps every post-operation active key count
inside the epoch hysteresis window `EpochInv U N (Dynamic.dom s_t).card`. In particular, an
active epoch `N > 0` initialized empty (`card = 0 ≤ N`) enters `EpochInv` on its first
insertion (`1 ≤ N ≤ 4`). -/
@[expose]
def InEpochHistory (U N : ℕ) : Dynamic.State U → List (Dynamic.Op U) → Prop
  | s_abs, [] => N ≤ U ∧ (Dynamic.dom s_abs).card ≤ N
  | s_abs, op :: ops =>
    N ≤ U ∧
    (Dynamic.dom s_abs).card ≤ N ∧
    EpochInv U N (Dynamic.dom (nextState s_abs op)).card ∧
    InEpochHistory U N (nextState s_abs op) ops

/-- `InEpochHistory U N s_abs (op :: ops)` follows from `(Dynamic.dom s_abs).card ≤ N`,
`EpochInv U N (Dynamic.dom (nextState s_abs op)).card`, and
`InEpochHistory U N (nextState s_abs op) ops`. -/
theorem inEpochHistory_cons_of_epochInv {U N : ℕ} {s_abs : Dynamic.State U}
    {op : Dynamic.Op U} {ops : List (Dynamic.Op U)}
    (hcard : (Dynamic.dom s_abs).card ≤ N)
    (hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs op)).card)
    (hrest : InEpochHistory U N (nextState s_abs op) ops) :
    InEpochHistory U N s_abs (op :: ops) :=
  ⟨hepoch'.cap_le_univ, hcard, hepoch', hrest⟩

/-- Concrete total deterministic amortized overhead sum along an operation sequence `ops` under
epoch seed `θ` (with no unconstrained existential budget). -/
@[expose]
noncomputable def inEpochSeqOverhead (U N : ℕ) (θ : Succinct.QuotHashSeed U N) :
    Dynamic.State U → List (Dynamic.Op U) → ℕ
  | _, [] => 0
  | s_abs, op :: ops =>
    inEpochStepOverhead U N θ s_abs op +
      inEpochSeqOverhead U N θ (nextState s_abs op) ops

/-- **Whole-sequence expectation bound (`tsum_inEpochSeqOverhead_le`):**
for any sequence `ops` satisfying `InEpochHistory U N s_abs ops`, the uniform expectation of
`inEpochSeqOverhead U N θ s_abs ops` over `θ ← epochSeedPMF U N` is at most
`294450 * ops.length` (`O(1)` expected amortized instructions per operation). -/
theorem tsum_inEpochSeqOverhead_le {U N : ℕ} {s_abs : Dynamic.State U}
    {ops : List (Dynamic.Op U)} (hhist : InEpochHistory U N s_abs ops) :
    (∑' θ : Succinct.QuotHashSeed U N,
      (epochSeedPMF U N θ : ℝ≥0∞) *
        ((inEpochSeqOverhead U N θ s_abs ops : ℕ) : ℝ≥0∞)) ≤
      294450 * (ops.length : ℝ≥0∞) := by
  induction ops generalizing s_abs with
  | nil =>
    simp [inEpochSeqOverhead]
  | cons op ops ih =>
    rcases hhist with ⟨hNU, hcard, _, hrest⟩
    have hstep := tsum_inEpochStepOverhead_le hNU s_abs hcard op
    have htail := ih hrest
    have hsplit :
        (∑' θ : Succinct.QuotHashSeed U N,
          (epochSeedPMF U N θ : ℝ≥0∞) *
            ((inEpochSeqOverhead U N θ s_abs (op :: ops) : ℕ) : ℝ≥0∞)) =
        (∑' θ : Succinct.QuotHashSeed U N,
          (epochSeedPMF U N θ : ℝ≥0∞) *
            ((inEpochStepOverhead U N θ s_abs op : ℕ) : ℝ≥0∞)) +
        (∑' θ : Succinct.QuotHashSeed U N,
          (epochSeedPMF U N θ : ℝ≥0∞) *
            ((inEpochSeqOverhead U N θ (nextState s_abs op) ops : ℕ) : ℝ≥0∞)) := by
      rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [inEpochSeqOverhead, Nat.cast_add, mul_add]
    rw [hsplit]
    calc
      (∑' θ : Succinct.QuotHashSeed U N,
          (epochSeedPMF U N θ : ℝ≥0∞) *
            ((inEpochStepOverhead U N θ s_abs op : ℕ) : ℝ≥0∞)) +
        (∑' θ : Succinct.QuotHashSeed U N,
          (epochSeedPMF U N θ : ℝ≥0∞) *
            ((inEpochSeqOverhead U N θ (nextState s_abs op) ops : ℕ) : ℝ≥0∞))
        ≤ 294450 + 294450 * (ops.length : ℝ≥0∞) := add_le_add hstep htail
      _ = 294450 * ((op :: ops).length : ℝ≥0∞) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Operational multi-step execution trace of a **single fixed uniform program**
`stepCode : BitRAM.Code .standard 280` under a `.grow` memory oracle `oracle` across `ops`,
binding every step `op` to `DemonicExecWithin`,
`y = evalWithOracle w oracle T stepCode (loadOpRegs op x)`, and
`ExecCodeDistWithOracle w oracle stepCode (loadOpRegs op x) (PMF.pure y) (T : ℝ≥0∞)`, and
checking well-formedness, live `Rep`, exact bit size `dictBitSize U V w N n_t`, tight
`OPT + O(n_t log log n_t) + 218 * w` space, and `OpOutputCorrect` at every step. -/
@[expose]
def InEpochOracleTrace (stepCode : BitRAM.Code .standard 280)
    (U V w N : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (θ : Succinct.QuotHashSeed U N) :
    List (Dynamic.Op U) → Dynamic.State U → BitRAM.Data 280 →
      List ℕ → List (BitRAM.Data 280) → Prop
  | [], _, _, ts, xs => ts = [] ∧ xs = []
  | op :: ops, s_abs, x, ts, xs =>
    ∃ (T : ℕ) (ts_rest : List ℕ) (xs_rest : List (BitRAM.Data 280)),
      let s_abs' := nextState s_abs op
      let n' := (Dynamic.dom s_abs').card
      let y := evalWithOracle w oracle T stepCode (loadOpRegs op x)
      ts = T :: ts_rest ∧
      xs = y :: xs_rest ∧
      BitRAM.DemonicExecWithin w stepCode (loadOpRegs op x)
        (fun y' =>
          y'.WellFormed w ∧
          Rep U V w N θ s_abs' y'.toBitMemoryState ∧
          y'.bitSize = dictBitSize U V w N n' ∧
          OpOutputCorrect s_abs op y'.regs) T ∧
      ExecCodeDistWithOracle w oracle stepCode (loadOpRegs op x) (PMF.pure y) (T : ℝ≥0∞) ∧
      (∀ fuel ≥ T, evalWithOracle w oracle fuel stepCode (loadOpRegs op x) = y) ∧
      y.WellFormed w ∧
      Rep U V w N θ s_abs' y.toBitMemoryState ∧
      y.bitSize = dictBitSize U V w N n' ∧
      y.bitSize ≤ Dynamic.optBits U V n' + 680 * n' * Dynamic.logLogFactor n' + 218 * w ∧
      OpOutputCorrect s_abs op y.regs ∧
      InEpochOracleTrace stepCode U V w N oracle θ ops s_abs' y ts_rest xs_rest

/-- **Uniform compiled in-epoch sequence theorem (`inEpochStepRegCode_oracle_seq`):**
the single fixed parameter-free program `inEpochStepRegCode : BitRAM.Code .standard 280` executes
any valid operation sequence `ops` satisfying `InEpochHistory U N s_abs ops` under any demonic
`.grow` oracle `oracle` (`DirtyGrowOracle w oracle`), producing concrete per-step instruction
counts `ts` and post-states `xs` satisfying `InEpochOracleTrace` and the telescoped potential
bound `ts.sum + 1967 * inEpochPotential U V w N s_fix_f ≤`
`1967 * inEpochPotential U V w N s_fix₀ + inEpochSeqOverhead U N θ s_abs ops`. -/
theorem inEpochStepRegCode_oracle_seq {U V w N : ℕ}
    {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)} (horacle : DirtyGrowOracle w oracle)
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix₀ : Memory.State}
    {x₀ : BitRAM.Data 280} (hinv₀ : EpochDictInv U V w N θ s_abs s_fix₀ x₀)
    (ops : List (Dynamic.Op U))
    (hhist : InEpochHistory U N s_abs ops)
    (hvh : (spec U V).ValidHistory s_abs ops) :
    ∃ (ts : List ℕ) (xs : List (BitRAM.Data 280)) (s_fix_f : Memory.State),
      ts.length = ops.length ∧
      xs.length = ops.length ∧
      InEpochOracleTrace inEpochStepRegCode U V w N oracle θ ops s_abs x₀ ts xs ∧
      ts.sum + 1967 * inEpochPotential U V w N s_fix_f ≤
        1967 * inEpochPotential U V w N s_fix₀ + inEpochSeqOverhead U N θ s_abs ops := by
  induction ops generalizing s_abs s_fix₀ x₀ with
  | nil =>
    exact ⟨[], [], s_fix₀, rfl, rfl, ⟨rfl, rfl⟩, by simp [inEpochSeqOverhead]⟩
  | cons op ops ih =>
    rcases hhist with ⟨_, _, hepoch', hhist_rest⟩
    rcases hvh with ⟨hval_op, hvh_rest⟩
    have hdyn_val : (Dynamic.spec U V N).valid s_abs op :=
      dynamic_valid_of_spec_valid hval_op hepoch'.card_le
    obtain ⟨s_fix₁, T, hExec₁, hcost₁⟩ :=
      inEpochStepRegCode_exec hw hU hV θ hinv₀ hdyn_val
    have hstep_eq : ((Dynamic.spec U V N).stepFn s_abs op).1 = nextState s_abs op := rfl
    obtain ⟨⟨hinv₁, hout₁⟩, hdist₁, hfuel₁⟩ := hExec₁.evalWithOracle_spec_of_le horacle
    rw [hstep_eq] at hinv₁
    have hExec₁_rep : BitRAM.DemonicExecWithin w inEpochStepRegCode (loadOpRegs op x₀)
        (fun y' =>
          y'.WellFormed w ∧
          Rep U V w N θ (nextState s_abs op) y'.toBitMemoryState ∧
          y'.bitSize = dictBitSize U V w N (Dynamic.dom (nextState s_abs op)).card ∧
          OpOutputCorrect s_abs op y'.regs) T :=
      hExec₁.mono (fun y' ⟨hinv', hout'⟩ => by
        rw [hstep_eq] at hinv'
        exact ⟨hinv'.wf, hinv'.rep hepoch', hinv'.bitSize_eq, hout'⟩) le_rfl
    let y₁ := evalWithOracle w oracle T inEpochStepRegCode (loadOpRegs op x₀)
    have hrep₁ : Rep U V w N θ (nextState s_abs op) y₁.toBitMemoryState :=
      hinv₁.rep hepoch'
    have hsz₁ : y₁.bitSize = dictBitSize U V w N (Dynamic.dom (nextState s_abs op)).card :=
      hinv₁.bitSize_eq
    have hspace₁ := EpochDictInv.space_tight hw hU.le hinv₁ hepoch'
    obtain ⟨ts_rest, xs_rest, s_fix_f, hlen_ts, hlen_xs, htrace_rest, hcost_rest⟩ :=
      ih hinv₁ hhist_rest hvh_rest
    refine ⟨T :: ts_rest, y₁ :: xs_rest, s_fix_f,
      by simp [hlen_ts], by simp [hlen_xs],
      ⟨T, ts_rest, xs_rest, rfl, rfl, hExec₁_rep, hdist₁, hfuel₁, hinv₁.wf, hrep₁, hsz₁,
        hspace₁, hout₁, htrace_rest⟩,
      ?_⟩
    simp only [List.sum_cons, inEpochSeqOverhead]
    omega

/-- Deterministic fuel-evaluator corollary of `initEmptyRegCode_exec` from an unallocated machine
state (`x₀.bitSize = 0`) under any `DirtyGrowOracle w oracle`, establishing `EpochDictInv` for
`Dynamic.empty U` at `N = 0` in `8 * w + 37` instructions with `y₀.bitSize = 4 * w` and zero
initial potential. -/
theorem initEmptyRegCode_oracle {U V w : ℕ}
    {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)} (horacle : DirtyGrowOracle w oracle)
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (hfit4w : Fits w (4 * w)) (θ₀ : Succinct.QuotHashSeed U 0)
    {x₀ : BitRAM.Data 280} (hx_wf : x₀.WellFormed w) (hx_sz : x₀.bitSize = 0)
    (hr240 : x₀.regs 240 = U) (hr241 : x₀.regs 241 = V) :
    let T_init := 8 * w + 37
    let y₀ := evalWithOracle w oracle T_init initEmptyRegCode x₀
    ∃ s_fix₀ : Memory.State,
      EpochDictInv U V w 0 θ₀ (Dynamic.empty U) s_fix₀ y₀ ∧
      Rep U V w 0 θ₀ (Dynamic.empty U) y₀.toBitMemoryState ∧
      y₀.bitSize = 4 * w ∧
      inEpochPotential U V w 0 s_fix₀ = 0 ∧
      ExecCodeDistWithOracle w oracle initEmptyRegCode x₀ (PMF.pure y₀) (T_init : ℝ≥0∞) ∧
      (∀ fuel ≥ T_init, evalWithOracle w oracle fuel initEmptyRegCode x₀ = y₀) := by
  intro T_init y₀
  have hExec := initEmptyRegCode_exec hw hU hV hfit4w θ₀ hx_wf hx_sz hr240 hr241
  obtain ⟨⟨hinv₀, hsz₀, hpot₀⟩, hdist₀, hfuel₀⟩ :=
    hExec.evalWithOracle_spec_of_le horacle
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
      ext k; simp [Dynamic.empty]
    rw [heq, Finset.card_empty]
  have hepoch0 : EpochInv U 0 (Dynamic.dom (Dynamic.empty U)).card := by
    rw [hdom0]; exact Or.inl ⟨rfl, rfl⟩
  exact ⟨⟨fun _ => 0, 0⟩, hinv₀, hinv₀.rep hepoch0, hsz₀, hpot₀, hdist₀, hfuel₀⟩

/-! ## Section 3: Pure model-level multi-epoch hysteresis, reached-capacity fit, rebuild potential,
and Feistel key recovery -/

/-- Non-vacuous reached-capacity fit hypothesis along an operation trajectory `ops`: requires
`Fits w (dictBitSize U V w N_t N_t)` only for epoch capacities `N_t` actually reached under
`nextEpochCap`, rather than quantifying over every `N' ≤ U` (which fails at `U = 2 ^ w - 1`). -/
@[expose]
def ReachedEpochsFit (U V w : ℕ) : ℕ → Dynamic.State U → List (Dynamic.Op U) → Prop
  | N, _, [] => Fits w (dictBitSize U V w N N)
  | N, s_abs, op :: ops =>
    Fits w (dictBitSize U V w N N) ∧
    ReachedEpochsFit U V w (nextEpochCap N s_abs op) (nextState s_abs op) ops

/-- Predicate asserting that the active key count `(Dynamic.dom s_t).card` never exceeds `M` along
`ops`. -/
@[expose]
def MaxCardLe {U : ℕ} (M : ℕ) : Dynamic.State U → List (Dynamic.Op U) → Prop
  | s_abs, [] => (Dynamic.dom s_abs).card ≤ M
  | s_abs, op :: ops =>
    (Dynamic.dom s_abs).card ≤ M ∧ MaxCardLe M (nextState s_abs op) ops

/-- `ReachedEpochsFit` holds whenever the active key count stays bounded by `M` along `ops` (with
initial `N ≤ min U (2 * M)`) and every capacity `N' ≤ min U (2 * M)` satisfies
`Fits w (dictBitSize U V w N' N')`. In particular, this holds even when `U = 2 ^ w - 1` and
`V = 2 ^ w` for any bounded-size trajectory fitting in the `2 ^ w`-bit address space. -/
theorem reachedEpochsFit_of_maxCardLe {U V w M : ℕ}
    (hfit_le : ∀ N' ≤ min U (2 * M), Fits w (dictBitSize U V w N' N')) :
    ∀ {N : ℕ} {s_abs : Dynamic.State U} {ops : List (Dynamic.Op U)},
      N ≤ min U (2 * M) →
      MaxCardLe M s_abs ops →
      ReachedEpochsFit U V w N s_abs ops := by
  intro N s_abs ops hN hmax
  induction ops generalizing N s_abs with
  | nil =>
    exact hfit_le N hN
  | cons op ops ih =>
    rcases hmax with ⟨_, hmax_rest⟩
    refine ⟨hfit_le N hN, ih ?_ hmax_rest⟩
    have hm'_le : (Dynamic.dom (nextState s_abs op)).card ≤ M := by
      cases ops with
      | nil => exact hmax_rest
      | cons _ _ => exact hmax_rest.1
    unfold nextEpochCap
    dsimp only
    split_ifs
    · exact hN
    · unfold targetCap
      split_ifs <;> omega

/-- Pure mathematical step cost model for multi-epoch rebuild amortization (not compiled to
`BitRAM.Code` for cross-epoch rebuilds): `1` unit when `EpochInv` continues to hold, and the linear
`O(N + N' + m + m')` rebuild and new-epoch potential setup cost when `¬ EpochInv U N m'` triggers a
rebuild to `N' = targetCap U m'`. -/
@[expose]
def pureMultiEpochRebuildCost (U w N m m' : ℕ) : ℕ :=
  if EpochInv U N m' then 1
  else
    let N' := targetCap U m'
    4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 1102 * m'

/-- **Pure multi-epoch rebuild potential bound (`pureMultiEpochStep_amortized_le`):**
for any valid single-operation transition (`EpochInv U N m`, `m' ≤ U`, `|m' - m| ≤ 1`),
`pureMultiEpochRebuildCost U w N m m' + 2660 * epochPotential U N' m' ≤`
`2660 * epochPotential U N m + 7849`, paying for both in-epoch capacity drift and full linear-cost
epoch rebuilds in `O(1)` amortized cost. -/
theorem pureMultiEpochStep_amortized_le {U w N m m' : ℕ} (hw : 0 < w) (hU : Fits w U)
    (hepoch : EpochInv U N m) (hm'U : m' ≤ U) (h1 : m' ≤ m + 1) (h2 : m ≤ m' + 1) :
    let N' := if EpochInv U N m' then N else targetCap U m'
    pureMultiEpochRebuildCost U w N m m' + 2660 * epochPotential U N' m' ≤
      2660 * epochPotential U N m + 7849 := by
  intro N'
  unfold pureMultiEpochRebuildCost
  split_ifs with hkeep
  · have hd : epochPotential U N m' ≤ epochPotential U N m + 2 := epochPotential_step_le h1 h2
    dsimp only [N']
    rw [ite_eq_left hkeep]
    omega
  · dsimp only [N']
    rw [ite_eq_right hkeep]
    have hNU : N ≤ U := hepoch.cap_le_univ
    have hN'U : targetCap U m' ≤ U := targetCap_le_univ U m'
    have hmeta_N := epochMetaWords_le_linear hw hNU hU
    have hmeta_N' := epochMetaWords_le_linear hw hN'U hU
    obtain ⟨hm_b, hm'_b, hN_b, hN'_b⟩ :=
      rebuild_bounds_of_not_epochInv hepoch hm'U h1 h2 hkeep
    have hepot0 : epochPotential U (targetCap U m') m' = 0 := epochPotential_targetCap U m'
    rw [hepot0]
    omega

/-- Pure model-level multi-epoch trajectory predicate recording that at every step along `ops`:
1. `EpochInv U N_t n_t` holds (`n_t = (Dynamic.dom s_t).card`),
2. `Fits w (dictBitSize U V w N_t N_t)` holds, and
3. the exact layout bit size `dictBitSize U V w N_t n_t` satisfies
   `dictBitSize U V w N_t n_t ≤ Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t`
   `+ 218 * w`. -/
@[expose]
def PureMultiEpochSpaceTrace (U V w : ℕ) :
    ℕ → Dynamic.State U → List (Dynamic.Op U) → Prop
  | N, s_abs, [] =>
    let n := (Dynamic.dom s_abs).card
    EpochInv U N n ∧
    Fits w (dictBitSize U V w N N) ∧
    dictBitSize U V w N n ≤
      Dynamic.optBits U V n + 680 * n * Dynamic.logLogFactor n + 218 * w
  | N, s_abs, op :: ops =>
    let n := (Dynamic.dom s_abs).card
    EpochInv U N n ∧
    Fits w (dictBitSize U V w N N) ∧
    dictBitSize U V w N n ≤
      Dynamic.optBits U V n + 680 * n * Dynamic.logLogFactor n + 218 * w ∧
    PureMultiEpochSpaceTrace U V w (nextEpochCap N s_abs op) (nextState s_abs op) ops

/-- Pure model-level multi-epoch hysteresis and space theorem from any valid starting state. -/
theorem pureMultiEpoch_space_and_hysteresis {U V w : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) :
    ∀ {N : ℕ} {s_abs : Dynamic.State U} (ops : List (Dynamic.Op U)),
      EpochInv U N (Dynamic.dom s_abs).card →
      ReachedEpochsFit U V w N s_abs ops →
      PureMultiEpochSpaceTrace U V w N s_abs ops := by
  intro N s_abs ops hepoch hfit
  induction ops generalizing N s_abs with
  | nil =>
    exact ⟨hepoch, hfit, dictBitSize_le_optBits hw hU hepoch⟩
  | cons op ops ih =>
    rcases hfit with ⟨hfit_cur, hfit_rest⟩
    exact ⟨hepoch, hfit_cur, dictBitSize_le_optBits hw hU hepoch,
      ih (epochInv_nextEpochCap s_abs op) hfit_rest⟩

/-- **Pure model-level multi-epoch hysteresis and tight space from empty
(`pureMultiEpoch_space_and_hysteresis_from_empty`):**
across any operation sequence `ops : List (Dynamic.Op U)` from `(N = 0, Dynamic.empty U)` whose
reached epoch capacities fit in the `2 ^ w`-bit address space (`ReachedEpochsFit`), `nextEpochCap`
maintains `EpochInv U N_t n_t` and `dictBitSize U V w N_t n_t ≤`
`Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w` at every step `t`, with
telescoped pure rebuild-potential cost at most `7849 * ops.length`. -/
theorem pureMultiEpoch_space_and_hysteresis_from_empty {U V w : ℕ} (hw : 0 < w) (hU : Fits w U)
    (ops : List (Dynamic.Op U))
    (hfit : ReachedEpochsFit U V w 0 (Dynamic.empty U) ops) :
    PureMultiEpochSpaceTrace U V w 0 (Dynamic.empty U) ops := by
  have hepoch0 : EpochInv U 0 (Dynamic.dom (Dynamic.empty U)).card := by
    have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
      ext k; simp [Dynamic.empty]
    rw [heq, Finset.card_empty]
    exact Or.inl ⟨rfl, rfl⟩
  exact pureMultiEpoch_space_and_hysteresis hw hU.le ops hepoch0 hfit

/-- **Lossless Feistel key reconstruction from active slots
(`rep_feistel_reconstruct_active_slot`):**
in any active dictionary state (`0 < N`) satisfying `Rep U V w N θ s_abs s_bit`, every occupied
slot `j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b` in bucket `b < numBuckets N` stores a
quotient `q` and value `v` from which
`feistelReconstruct (bucketBits N) (Succinct.hValOfSeed U N θ) b q` recovers a valid key
`u_val < U` with `s_abs ⟨u_val, _⟩ = some v`. -/
theorem rep_feistel_reconstruct_active_slot {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_bit : BitMemory.State}
    (hrep : Rep U V w N θ s_abs s_bit) (hN : 0 < N)
    {b j : ℕ} (hb : b < numBuckets N)
    (hj : j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b) :
    let gm := gmAtBit U w N s_bit.mem
    let phys := Succinct.slotOf N gm b j
    let q := virtualQuotAt U V w N s_bit phys
    let v := virtualValAt U V w N s_bit phys
    let u_val := feistelReconstruct (bucketBits N) (Succinct.hValOfSeed U N θ) b q
    ∃ hu : u_val < U, s_abs ⟨u_val, hu⟩ = some v := by
  intro gm phys q v u_val
  obtain ⟨_, _, L, hb_inv⟩ := hrep.active_inv hN
  have hsome := hb_inv.hmap_some b hb j hj
  change Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs b q = some v at hsome
  unfold Succinct.bucketMapOfState at hsome
  split_ifs at hsome with hcond
  exact ⟨hcond.1, hsome⟩

/-- **Completeness of active-slot Feistel key recovery (`rep_exists_active_slot_of_some`):**
in any active dictionary state (`0 < N`) satisfying `Rep U V w N θ s_abs s_bit`, every present
entry `s_abs u = some v` (`u : Fin U`) appears in bucket
`b = feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u.val < numBuckets N` at a unique
active slot `j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b` whose stored quotient `q` and
value `v'` satisfy `v' = v` and
`feistelReconstruct (bucketBits N) h1 b q = u.val`. -/
theorem rep_exists_active_slot_of_some {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_bit : BitMemory.State}
    (hrep : Rep U V w N θ s_abs s_bit) (hN : 0 < N)
    {u : Fin U} {v : ℕ} (hu : s_abs u = some v) :
    let h1 := Succinct.hValOfSeed U N θ
    let gm := gmAtBit U w N s_bit.mem
    let b := feistelBucket (bucketBits N) h1 u.val
    b < numBuckets N ∧
    ∃ j < Succinct.bCount N gm b,
      let phys := Succinct.slotOf N gm b j
      virtualQuotAt U V w N s_bit phys = keyQuotient (bucketBits N) u.val ∧
      virtualValAt U V w N s_bit phys = v ∧
      feistelReconstruct (bucketBits N) h1 b (virtualQuotAt U V w N s_bit phys) = u.val := by
  intro h1 gm b
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  obtain ⟨_, _, L, hb_inv⟩ := hrep.active_inv hN
  have hB_eq :
      Succinct.bucketMapOfState U N h1 s_abs b (keyQuotient (bucketBits N) u.val) = s_abs u :=
    Succinct.bucketMapOfState_feistelBucket hrep.epoch_inv.cap_le_univ h1 s_abs u
  have his :
      (Succinct.bucketMapOfState U N h1 s_abs b (keyQuotient (bucketBits N) u.val)).isSome := by
    rw [hB_eq, hu]; rfl
  obtain ⟨j, hj_lt, hq_eq⟩ := (hb_inv.hmap_dom b hb_lt (keyQuotient (bucketBits N) u.val)).mp his
  have hmap := hb_inv.hmap_some b hb_lt j hj_lt
  change Succinct.bucketMapOfState U N h1 s_abs b
      (virtualQuotAt U V w N s_bit (Succinct.slotOf N gm b j)) =
    some (virtualValAt U V w N s_bit (Succinct.slotOf N gm b j)) at hmap
  rw [hq_eq, hB_eq, hu] at hmap
  injection hmap with hv_eq
  refine ⟨hb_lt, j, hj_lt, hq_eq, hv_eq.symm, ?_⟩
  rw [hq_eq]
  exact feistelReconstruct_feistelBucket (bucketBits N) h1 u.val

/-- **Faithfulness of `Rep` (`rep_inj`):**
the bit-resizable memory state `s_bit` together with the epoch seed `θ` uniquely determines the
abstract dictionary `s_abs : Dynamic.State U`. -/
theorem rep_inj {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s₁ s₂ : Dynamic.State U} {s_bit : BitMemory.State}
    (hrep₁ : Rep U V w N θ s₁ s_bit) (hrep₂ : Rep U V w N θ s₂ s_bit) :
    s₁ = s₂ := by
  by_cases hN0 : N = 0
  · subst hN0
    have hc₁ : (Dynamic.dom s₁).card = 0 := by
      rcases hrep₁.epoch_inv with ⟨h0, _⟩ | ⟨_, _, _, _⟩ <;> omega
    have hc₂ : (Dynamic.dom s₂).card = 0 := by
      rcases hrep₂.epoch_inv with ⟨h0, _⟩ | ⟨_, _, _, _⟩ <;> omega
    funext u
    have hnone₁ : s₁ u = none := by
      cases h : s₁ u with
      | none => rfl
      | some v =>
        have hmem : u ∈ Dynamic.dom s₁ := Dictionary.mem_dom_iff_isSome.mpr (by rw [h]; rfl)
        have hpos : 0 < (Dynamic.dom s₁).card := Finset.card_pos.mpr ⟨u, hmem⟩
        omega
    have hnone₂ : s₂ u = none := by
      cases h : s₂ u with
      | none => rfl
      | some v =>
        have hmem : u ∈ Dynamic.dom s₂ := Dictionary.mem_dom_iff_isSome.mpr (by rw [h]; rfl)
        have hpos : 0 < (Dynamic.dom s₂).card := Finset.card_pos.mpr ⟨u, hmem⟩
        omega
    rw [hnone₁, hnone₂]
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    have htransfer : ∀ {sa sb : Dynamic.State U},
        Rep U V w N θ sa s_bit → Rep U V w N θ sb s_bit →
        ∀ (u : Fin U) (v : ℕ), sa u = some v → sb u = some v := by
      intro sa sb ha hb u v hsa
      obtain ⟨hb_lt, j, hj_lt, _, hv_eq, hrec⟩ := rep_exists_active_slot_of_some ha hN hsa
      obtain ⟨hu_lt, hsb⟩ := rep_feistel_reconstruct_active_slot hb hN hb_lt hj_lt
      have hfin : (⟨feistelReconstruct (bucketBits N) (Succinct.hValOfSeed U N θ)
          (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u.val)
          (virtualQuotAt U V w N s_bit
            (Succinct.slotOf N (gmAtBit U w N s_bit.mem)
              (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u.val) j)),
          hu_lt⟩ : Fin U) = u :=
        Fin.ext hrec
      rw [hfin, hv_eq] at hsb
      exact hsb
    funext u
    cases h1 : s₁ u with
    | none =>
      cases h2 : s₂ u with
      | none => rfl
      | some v2 =>
        have hc := htransfer hrep₂ hrep₁ u v2 h2
        rw [h1] at hc
        cases hc
    | some v1 =>
      exact (htransfer hrep₁ hrep₂ u v1 h1).symm

end Cslib.DataStructure.Dictionary.BitResizable
