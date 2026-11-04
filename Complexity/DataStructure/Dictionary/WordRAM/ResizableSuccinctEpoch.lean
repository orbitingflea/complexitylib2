/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinct

/-!
# Unbounded-Capacity Epoch Schedule and Client Composition for the Resizable Succinct Dictionary

This module completes the unbounded-capacity word-granular resizable succinct dynamic dictionary
(`Dynamic.spec U V U`, supporting arbitrary key and value universes `U, V < 2 ^ w` without any
capacity cap) on top of `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct`.

## Design choices and architecture

1. **Epoch-based doubling/halving capacity schedule (`EpochValid`, `targetCap`)**:
   To support an unbounded number of insertions and deletions (`Dynamic.spec U V U`) while keeping
   space tight in the **current** live key count `n_t = (Dynamic.dom s_t).card` at every step `t`
   and maintaining `O(1)` expected amortized time:
   - An epoch built at key count `n_init ≤ U` chooses capacity parameter
     `N = targetCap U n_init = min (2 * n_init) U`, maintaining the epoch invariant
     `EpochValid n_t N` (`n_t ≤ N ∧ N ≤ 4 * n_t`) and `N ≤ U`.
   - When `n_{t+1}` leaves `[⌈N / 4⌉, N]`, the dictionary rebuilds into a fresh epoch of capacity
     `N' = targetCap U n_{t+1}` by executing `deallocSuccinctCode`, `allocSuccinctCode` (under
     demonic `DemonicGrow`), `initFresh`, and `buildOps s_{t+1} (List.finRange U)`. The epoch
     potential `2 * C_reb * natDist n_t n_init` is `0` immediately after every rebuild, changes by
     at most `2 * C_reb = O(1)` per operation, and drops by at least `C_reb * (n_{t+1} + 1)` on
     every rebuild (`add_one_le_two_mul_natDist_of_not_epochValid`).
2. **Client composition and immediate reuse of released memory
   (`subroutine_client_reuse_released_memory`, `shrink_and_reuse_in_place`)**:
   In a single linear word-resizable memory `[0, L)` (`RData`), shrinking the dictionary via
   `RCode.shrink` returns released words to the unallocated suffix `[x.frontier, ∞)` so subsequent
   client allocations under demonic `DemonicGrow` reuse the exact same addresses `[base, ...)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.EpochValid`, `targetCap`, `natDist`,
  `buildOps`, `maxOpFactor`, `maxChargeVal`, `rebuildUnitCost`, `resizableChargeVal`,
  `epochTotalPotential`, `runEpochInit`: unbounded-capacity epoch schedule, rebuild operation list,
  and uniform `O(1)` per-operation expected amortized charge.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rebuild_epoch_expected_amortized`,
  `unbounded_step_expected_amortized`, `unbounded_seq_expected_amortized`: end-to-end `O(1)`
  expected amortized time and stepwise `n_t`-tight space across any valid operation sequence under
  `Dynamic.spec U V U` (no capacity cap).
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.shrink_and_reuse_in_place`,
  `subroutine_client_reuse_released_memory`: client theorems demonstrating subroutine composition
  and reuse of released memory in a single linear word-resizable memory `[0, L)`.
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

/-! ## Section 5: Unbounded-Capacity Doubling/Halving Epoch Schedule (`Dynamic.spec U V U`) -/

/-! ### Rebuilding an epoch from `Dynamic.empty U` via `buildOps` -/

/-- Construct the list of `.insert u v` operations for all keys `u ∈ L` present in `s`. -/
@[expose]
def buildOps {U : ℕ} (s : Dynamic.State U) : List (Fin U) → List (Dynamic.Op U)
  | [] => []
  | u :: us =>
    match s u with
    | none => buildOps s us
    | some v => .insert u v :: buildOps s us

/-- Agreement invariant for `buildOps`: `s₀` is `none` on `L` and agrees with `s` outside `L`. -/
def RestrictOut {U : ℕ} (L : List (Fin U)) (s₀ s : Dynamic.State U) : Prop :=
  (∀ u ∈ L, s₀ u = none) ∧ (∀ u, u ∉ L → s₀ u = s u)

private theorem buildOps_spec_aux {U V N : ℕ} {s : Dynamic.State U}
    (hvb : Dynamic.ValuesBounded V s) (hcard : (Dynamic.dom s).card ≤ N) :
    ∀ (L : List (Fin U)) (_hnd : L.Nodup) (s₀ : Dynamic.State U)
      (_hro : RestrictOut L s₀ s),
      ((Dynamic.spec U V N).run s₀ (buildOps s L)).1 = s ∧
      (Dynamic.spec U V N).ValidHistory s₀ (buildOps s L) ∧
      (Dynamic.dom s₀).card + (buildOps s L).length = (Dynamic.dom s).card
  | [], _, s₀, hro => by
    have heq : s₀ = s := funext fun u => hro.2 u (List.not_mem_nil)
    subst heq
    exact ⟨rfl, trivial, by simp [buildOps]⟩
  | u :: us, hnd, s₀, hro => by
    obtain ⟨hu_not, hnd_us⟩ := List.nodup_cons.mp hnd
    have hs₀_u : s₀ u = none := hro.1 u (List.mem_cons_self)
    unfold buildOps
    cases hsu : s u with
    | none =>
      have hro' : RestrictOut us s₀ s := by
        refine ⟨fun x hx => hro.1 x (List.mem_cons_of_mem u hx), fun x hx => ?_⟩
        by_cases hxu : x = u
        · subst hxu; rw [hs₀_u, hsu]
        · exact hro.2 x (by simp [hxu, hx])
      exact buildOps_spec_aux hvb hcard us hnd_us s₀ hro'
    | some v =>
      let s₁ : Dynamic.State U := Function.update s₀ u (some v)
      have hro₁ : RestrictOut us s₁ s := by
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · have hxu : x ≠ u := fun h => hu_not (h ▸ hx)
          dsimp only [s₁]
          rw [Function.update_of_ne hxu]
          exact hro.1 x (List.mem_cons_of_mem u hx)
        · by_cases hxu : x = u
          · subst hxu; simp [s₁, hsu]
          · dsimp only [s₁]
            rw [Function.update_of_ne hxu]
            exact hro.2 x (by simp [hxu, hx])
      have hv_lt : v < V := hvb u v hsu
      have hdom₁ : (Dynamic.dom s₁).card = (Dynamic.dom s₀).card + 1 :=
        Dictionary.card_dom_insert_eq_of_eq_none hs₀_u v
      obtain ⟨hrun, hvh, hlen⟩ := buildOps_spec_aux hvb hcard us hnd_us s₁ hro₁
      have hlt_N : (Dynamic.dom s₀).card < N := by omega
      have hval_u : (Dynamic.spec U V N).valid s₀ (.insert u v) := ⟨Or.inl hlt_N, hv_lt⟩
      refine ⟨hrun, ⟨hval_u, hvh⟩, ?_⟩
      simp only [List.length_cons]
      omega

/-- **Correctness, validity, and exact length of `buildOps s (List.finRange U)`:**
For any `s : Dynamic.State U` with `ValuesBounded V s` and `(Dynamic.dom s).card ≤ N`,
`buildOps s (List.finRange U)` has length `(Dynamic.dom s).card`, is a valid history from
`Dynamic.empty U` under `Dynamic.spec U V N`, and reaches `s`. -/
theorem buildOps_finRange_spec {U V N : ℕ} {s : Dynamic.State U}
    (hvb : Dynamic.ValuesBounded V s) (hcard : (Dynamic.dom s).card ≤ N) :
    ((Dynamic.spec U V N).run (Dynamic.empty U) (buildOps s (List.finRange U))).1 = s ∧
    (Dynamic.spec U V N).ValidHistory (Dynamic.empty U) (buildOps s (List.finRange U)) ∧
    (buildOps s (List.finRange U)).length = (Dynamic.dom s).card := by
  have hro : RestrictOut (List.finRange U) (Dynamic.empty U) s :=
    ⟨fun _ _ => rfl, fun u hu => absurd (List.mem_finRange u) hu⟩
  obtain ⟨hrun, hvh, hlen⟩ :=
    buildOps_spec_aux hvb hcard (List.finRange U) (List.nodup_finRange U) (Dynamic.empty U) hro
  simp only [Dictionary.dom_empty, Finset.card_empty, Nat.zero_add] at hlen
  exact ⟨hrun, hvh, hlen⟩

/-- **Epoch rebuild theorem on `RData` (`rebuild_epoch_expected_amortized`):**
Given any target state `s : Dynamic.State U` with `ValuesBounded V s`, rebuilding the succinct
dictionary into epoch capacity `N = targetCap U (Dynamic.dom s).card` from `x : RData` with
`x.frontier = base` under **demonic** `DemonicGrow`:
1. Allocates and zeroes `[base, base + Succinct.space U V w N)` via `allocSuccinctCode` in
   `4 * Succinct.space U V w N + 8` instructions (`RDemonicExec`),
2. Initializes the hash table and inserts all `(Dynamic.dom s).card` entries of `s` via
   `buildOps s (List.finRange U)` in expected total instruction count at most
   `31 * N + 1092 + (Dynamic.dom s).card * chargeVal U V w N`,
3. Produces a distribution `ν_final` whose support satisfies `ResizableRep U V w N base θ s y`
   with active epoch word footprint `activeEpochWords U V w N (Dynamic.dom s).card ≤
   Dynamic.succinctWords 312 213 U V w (Dynamic.dom s).card`. -/
theorem rebuild_epoch_expected_amortized {U V w base : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    {s : Dynamic.State U} (hvb : Dynamic.ValuesBounded V s)
    (hfit : Fits w (base + Succinct.space U V w (targetCap U (Dynamic.dom s).card)))
    {x : RData (rSuccinct U V w (targetCap U (Dynamic.dom s).card))}
    (hx : x.Bounded w) (hfr : x.frontier = base) :
    let n := (Dynamic.dom s).card
    let N := targetCap U n
    ∃ (x₁ : RData (rSuccinct U V w N))
      (ν₀ ν_final : PMF ((Succinct.impl hw (targetCap_le_univ U n) hU hV hfit).Seed ×
        Data (rSuccinct U V w N)))
      (T_ops : ℝ≥0∞),
      RDemonicExec w (allocSuccinctCode U V w N) x (4 * Succinct.space U V w N + 8) (· = x₁) ∧
      ExecCodeDist w (subroutineCode U V w N).initFresh (x₁.set (frontierReg U V w N) base).toData
        (ν₀.map Prod.snd) (Succinct.impl hw (targetCap_le_univ U n) hU hV hfit).initTime ∧
      (Succinct.impl hw (targetCap_le_univ U n) hU hV hfit).ExecStepsOfFn
        (Dynamic.empty U) (buildOps s (List.finRange U)) ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N)) θ) ∧
      (∀ p ∈ ν_final.support,
        ResizableRep U V w N base p.1 s ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N⟩ ∧
        Modifies (Block.mk base (Succinct.space U V w N)).footprint x.mem p.2.mem) ∧
      (Succinct.impl hw (targetCap_le_univ U n) hU hV hfit).initTime + T_ops +
        (∑' q, ν_final q * (potential U V w N base q.1 q.2 : ℝ≥0∞)) ≤
        ((31 * N + 1092 + n * chargeVal U V w N : ℕ) : ℝ≥0∞) ∧
      EpochValid n N ∧
      activeEpochWords U V w N n ≤ Dynamic.succinctWords 312 213 U V w n := by
  intro n N
  have hnU : n ≤ U := Dynamic.card_dom_le_univ s
  have hNU : N ≤ U := targetCap_le_univ U n
  have hnN : n ≤ N := le_targetCap hnU
  have hN2 : N ≤ 2 * n := targetCap_le_two_mul U n
  obtain ⟨x₁, he_alloc, hx₁_bdd, hx₁_fr, _, _, hx₁_mem, hx₁_zero⟩ :=
    allocSuccinctCode_exec hx hfr hfit
  let x₁' := x₁.set (frontierReg U V w N) base
  have hbase_fits : Fits w base := hfit.of_le (Nat.le_add_right base _)
  have hx₁'_bdd : x₁'.toData.Bounded w := (hx₁_bdd.set hbase_fits).1
  have hx₁'_fr : x₁'.toData.regs (frontierReg U V w N) = base := by simp [x₁']
  obtain ⟨hrun_b, hvh_b, hlen_b⟩ := buildOps_finRange_spec (N := N) hvb hnN
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hsupp_final, hamort⟩ :=
    seq_expected_amortized_modifies hw hNU hU hV hfit (buildOps s (List.finRange U))
      hx₁'_bdd hx₁'_fr hx₁_zero hvh_b
  rw [hrun_b] at hsupp_final
  rw [hlen_b] at hamort
  have hinit_le := Succinct.initTime_impl_le hw hNU hU hV hfit
  have hbound :
      (Succinct.impl hw hNU hU hV hfit).initTime + T_ops +
        (∑' q, ν_final q * (potential U V w N base q.1 q.2 : ℝ≥0∞)) ≤
        ((31 * N + 1092 + n * chargeVal U V w N : ℕ) : ℝ≥0∞) := by
    calc (Succinct.impl hw hNU hU hV hfit).initTime + T_ops +
          (∑' q, ν_final q * (potential U V w N base q.1 q.2 : ℝ≥0∞))
        ≤ (Succinct.impl hw hNU hU hV hfit).initTime + (n * chargeVal U V w N : ℕ) := hamort
      _ ≤ ((initSteps U N + 1 : ℕ) : ℝ≥0∞) + (n * chargeVal U V w N : ℕ) :=
          add_le_add hinit_le.1 le_rfl
      _ ≤ ((31 * N + 1092 + n * chargeVal U V w N : ℕ) : ℝ≥0∞) := by
          norm_cast
          have := hinit_le.2
          omega
  refine ⟨x₁, ν₀, ν_final, T_ops, he_alloc, he_init, hex_steps, hseed_final, ?_, hbound,
    epochValid_targetCap hnU,
    activeEpochWords_le_succinctWords_of_le_two_mul hw hnU hNU (le_of_lt hU) hnN hN2⟩
  intro p hp
  obtain ⟨hrep_p, hmod_p⟩ := hsupp_final p hp
  have hmod_x : Modifies (Block.mk base (Succinct.space U V w N)).footprint x.mem p.2.mem := by
    change Modifies (Block.mk base (Succinct.space U V w N)).footprint x₁.mem p.2.mem at hmod_p
    rwa [hx₁_mem] at hmod_p
  exact ⟨⟨rData_bounded_of_rep_modifies hx₁_bdd hx₁_fr hrep_p hmod_p, rfl, hrep_p⟩, hmod_x⟩

/-! ### Uniform `O(1)` expected amortized charge across all capacities `N ≤ U` -/

/-- Universal within-epoch exchange factor `170000` (`opFactor U V w N = 170000` for all
`U, V, w, N`). -/
abbrev opFactorConst : ℕ := 170000

/-- Universal within-epoch expected amortized operation charge `53494689`
(`313 * 170000 + 284689`). -/
abbrev chargeValConst : ℕ := 53494689

/-- Universal per-item epoch rebuild work factor `53495843` (`chargeValConst + 1154`). -/
abbrev rebuildUnitCostConst : ℕ := 53495843

/-- Universal per-operation expected amortized instruction charge `160486391`
(`chargeValConst + 2 * rebuildUnitCostConst + 16`) across all `U, V, w`. -/
abbrev resizableChargeValConst : ℕ := 160486391

/-- Maximum exchange factor `opFactor U V w N` across all valid epoch capacities `N ∈ [0, U]`. -/
@[expose]
noncomputable def maxOpFactor (U V w : ℕ) : ℕ :=
  (Finset.range (U + 1)).sup fun N => opFactor U V w N

/-- Uniform `O(1)` within-epoch operation charge `313 * maxOpFactor U V w + 284689` dominating
`chargeVal U V w N` for all `N ≤ U`. -/
@[expose]
noncomputable def maxChargeVal (U V w : ℕ) : ℕ :=
  313 * maxOpFactor U V w + 284689

/-- Per-item epoch rebuild work factor `maxChargeVal U V w + 1154`, dominating
`31 * N + 1092 + n * chargeVal U V w N ≤ rebuildUnitCost U V w * (n + 1)` whenever `N ≤ 2 * n`. -/
@[expose]
noncomputable def rebuildUnitCost (U V w : ℕ) : ℕ :=
  maxChargeVal U V w + 1154

/-- Uniform `O(1)` per-operation expected amortized instruction charge for the unbounded-capacity
resizable succinct dictionary (`Dynamic.spec U V U`), combining the within-epoch operation charge
`maxChargeVal U V w`, the `2 * rebuildUnitCost U V w` epoch-rebuild amortization credit, and the
`16`-instruction within-epoch item-region resize bound. -/
@[expose]
noncomputable def resizableChargeVal (U V w : ℕ) : ℕ :=
  maxChargeVal U V w + 2 * rebuildUnitCost U V w + 16

theorem maxOpFactor_eq_const (U V w : ℕ) : maxOpFactor U V w = opFactorConst := by
  unfold maxOpFactor opFactorConst
  apply le_antisymm
  · exact Finset.sup_le fun N _ => le_of_eq (opFactor_eq U V w N)
  · have h0 : 0 ∈ Finset.range (U + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ U)
    calc 170000 = opFactor U V w 0 := (opFactor_eq U V w 0).symm
      _ ≤ (Finset.range (U + 1)).sup fun N => opFactor U V w N :=
          Finset.le_sup (f := fun N => opFactor U V w N) h0

theorem maxChargeVal_eq_const (U V w : ℕ) : maxChargeVal U V w = chargeValConst := by
  unfold maxChargeVal chargeValConst
  rw [maxOpFactor_eq_const]
  rfl

theorem rebuildUnitCost_eq_const (U V w : ℕ) : rebuildUnitCost U V w = rebuildUnitCostConst := by
  unfold rebuildUnitCost rebuildUnitCostConst
  rw [maxChargeVal_eq_const]

theorem resizableChargeVal_eq_const (U V w : ℕ) :
    resizableChargeVal U V w = resizableChargeValConst := by
  unfold resizableChargeVal resizableChargeValConst
  rw [maxChargeVal_eq_const, rebuildUnitCost_eq_const]
  rfl

theorem opFactor_le_maxOpFactor {U V w N : ℕ} (hNU : N ≤ U) :
    opFactor U V w N ≤ maxOpFactor U V w :=
  Finset.le_sup (f := fun k => opFactor U V w k) (Finset.mem_range.mpr (by omega))

theorem chargeVal_le_maxChargeVal {U V w N : ℕ} (hNU : N ≤ U) :
    chargeVal U V w N ≤ maxChargeVal U V w := by
  unfold chargeVal maxChargeVal
  have := opFactor_le_maxOpFactor (V := V) (w := w) hNU
  omega

theorem rebuild_cost_le_rebuildUnitCost {U V w n N : ℕ} (hNU : N ≤ U) (hN2 : N ≤ 2 * n) :
    31 * N + 1092 + n * chargeVal U V w N ≤ rebuildUnitCost U V w * (n + 1) := by
  have hch := chargeVal_le_maxChargeVal (V := V) (w := w) hNU
  have hmul : n * chargeVal U V w N ≤ n * maxChargeVal U V w := Nat.mul_le_mul_left n hch
  unfold rebuildUnitCost
  nlinarith

/-- Combined epoch + slot potential at current live key count `n` in an epoch started at `n_init`:
`potential U V w N base θ x.toData + 2 * rebuildUnitCost U V w * natDist n n_init`. -/
@[expose]
noncomputable def epochTotalPotential (U V w N base n n_init : ℕ)
    (θ : QuotHashSeed U N) (x : RData (rSuccinct U V w N)) : ℕ :=
  potential U V w N base θ x.toData + 2 * rebuildUnitCost U V w * natDist n n_init

/-- **Unbounded-capacity single-step expected amortized theorem
(`unbounded_step_expected_amortized`):**
For any state `s : Dynamic.State U` with `ValuesBounded V s`, current live key count
`n = (Dynamic.dom s).card`, active epoch `N = targetCap U n_init` satisfying `EpochValid n N`, and
any operation `o : Dynamic.Op U` admissible under `Dynamic.spec U V U` (i.e. `v < V` for `insert`,
**no capacity cap**), let `(s', _) = (Dynamic.spec U V U).stepFn s o` and
`n' = (Dynamic.dom s').card`. Then:
1. Regardless of whether `EpochValid n' N` holds (in-place execution in epoch `N`) or fails
   (triggering a full epoch rebuild to `N' = targetCap U n'`), the new epoch parameter `N'`
   satisfies `EpochValid n' N'` and `N' ≤ U`;
2. The new active word footprint at step `t + 1` satisfies
   `activeEpochWords U V w N' n' ≤ Dynamic.succinctWords 1227 213 U V w n'`
   (and in bits, `≤ Dynamic.optBits U V n' + 1227 * n' * Dynamic.logLogFactor n' + 214 * w`);
3. In both cases, the expected instruction cost plus the change in `epochTotalPotential` is bounded
   by the uniform constant `resizableChargeVal U V w = O(1)`. -/
theorem unbounded_step_expected_amortized {U V w n_init : ℕ}
    (hw : 0 < w) (hU : Fits w U)
    {s : Dynamic.State U} (hvb : Dynamic.ValuesBounded V s)
    (o : Dynamic.Op U) (hval : (Dynamic.spec U V U).valid s o)
    (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init)) :
    let n := (Dynamic.dom s).card
    let N := targetCap U n_init
    let s' := ((Dynamic.spec U V U).stepFn s o).1
    let n' := (Dynamic.dom s').card
    let n_init' := if EpochValid n' N then n_init else n'
    let N' := targetCap U n_init'
    EpochValid n' N' ∧
    N' ≤ U ∧
    Dynamic.ValuesBounded V s' ∧
    activeEpochWords U V w N' n' ≤ Dynamic.succinctWords 1227 213 U V w n' ∧
    w * activeEpochWords U V w N' n' ≤
      Dynamic.optBits U V n' + 1227 * n' * Dynamic.logLogFactor n' + 214 * w ∧
    2 * rebuildUnitCost U V w * natDist n' n_init' ≤
      2 * rebuildUnitCost U V w * natDist n n_init + resizableChargeVal U V w ∧
    (if EpochValid n' N then
      chargeVal U V w N + 16 + 2 * rebuildUnitCost U V w * natDist n' n_init' ≤
        2 * rebuildUnitCost U V w * natDist n n_init + resizableChargeVal U V w
    else
      31 * N' + 1092 + n' * chargeVal U V w N' +
        2 * rebuildUnitCost U V w * natDist n' n_init' ≤
        2 * rebuildUnitCost U V w * natDist n n_init + resizableChargeVal U V w) := by
  intro n N s' n' n_init' N'
  have hn'U : n' ≤ U := Dynamic.card_dom_le_univ s'
  have hvb' : Dynamic.ValuesBounded V s' := Dynamic.valuesBounded_step_of_valid hvb hval
  have hdiff := card_dom_step_diff_le_one (V := V) (n_max := U) s o
  have hstep1 : n' ≤ n + 1 := hdiff.1
  have hstep2 : n ≤ n' + 1 := hdiff.2
  have hepoch' : EpochValid n' N' := by
    dsimp only [N', n_init']
    split_ifs with hvalid
    · exact hvalid
    · exact epochValid_targetCap hn'U
  have hN'U : N' ≤ U := targetCap_le_univ U n_init'
  have hspace_words : activeEpochWords U V w N' n' ≤ Dynamic.succinctWords 1227 213 U V w n' :=
    activeEpochWords_le_succinctWords_of_le_four_mul hw hn'U hN'U (le_of_lt hU)
      hepoch'.1 hepoch'.2
  have hspace_bits :
      w * activeEpochWords U V w N' n' ≤
        Dynamic.optBits U V n' + 1227 * n' * Dynamic.logLogFactor n' + 214 * w := by
    calc w * activeEpochWords U V w N' n'
        ≤ w * Dynamic.succinctWords 1227 213 U V w n' := Nat.mul_le_mul_left w hspace_words
      _ ≤ Dynamic.optBits U V n' + 1227 * n' * Dynamic.logLogFactor n' + (213 + 1) * w :=
          succinctWords_mul_w_le_bits 1227 213 U V w n'
      _ = Dynamic.optBits U V n' + 1227 * n' * Dynamic.logLogFactor n' + 214 * w := by ring
  have hd := natDist_step_le (n_init := n_init) hstep1 hstep2
  have hpot_step :
      2 * rebuildUnitCost U V w * natDist n' n_init' ≤
        2 * rebuildUnitCost U V w * natDist n n_init + resizableChargeVal U V w := by
    dsimp only [n_init', resizableChargeVal]
    split_ifs with hvalid
    · nlinarith
    · rw [natDist_self, Nat.mul_zero]
      omega
  refine ⟨hepoch', hN'U, hvb', hspace_words, hspace_bits, hpot_step, ?_⟩
  split_ifs with hvalid
  · have hNU : N ≤ U := targetCap_le_univ U n_init
    have hch := chargeVal_le_maxChargeVal (V := V) (w := w) hNU
    dsimp only [n_init', resizableChargeVal]
    simp only [hvalid, ↓reduceIte]
    nlinarith
  · have hN2 : N' ≤ 2 * n' := by
      dsimp only [N', n_init']
      simp only [hvalid, ↓reduceIte]
      exact targetCap_le_two_mul U n'
    have hreb := rebuild_cost_le_rebuildUnitCost (V := V) (w := w) hN'U hN2
    have hn'N : n' ≤ N + 1 := by
      have hnN : n ≤ N := hepoch.1
      omega
    have hdist_lb :=
      add_one_le_two_mul_natDist_of_not_epochValid (U := U) (n_init := n_init) rfl hn'U hn'N hvalid
    dsimp only [n_init', resizableChargeVal]
    simp only [hvalid, ↓reduceIte, natDist_self, Nat.mul_zero, Nat.add_zero]
    nlinarith

/-- **Unbounded-capacity multi-operation expected amortized & stepwise tight-space theorem
(`unbounded_seq_expected_amortized`):**
Starting from `s₀ = Dynamic.empty U` and `n_init₀ = 0`, across any valid operation sequence
`ops : List (Dynamic.Op U)` under `Dynamic.spec U V U` (no capacity cap, `U, V < 2 ^ w`), at
completion (and by prefix induction at **every intermediate step `t`**):
1. The final state `s_final = ((Dynamic.spec U V U).run (Dynamic.empty U) ops).1` with live size
   `n_final = (Dynamic.dom s_final).card` and epoch capacity `N_final = targetCap U n_init_final`
   satisfies `EpochValid n_final N_final`, `N_final ≤ U`, and `ValuesBounded V s_final`;
2. The active word footprint is at most `Dynamic.succinctWords 1227 213 U V w n_final` words, and
   in bits at most `Dynamic.optBits U V n_final + 1227 * n_final * Dynamic.logLogFactor n_final +
   214 * w` bits (with `214 * w` the explicit word-granular rounding term);
3. The cumulative amortized epoch-rebuild and operation charge across `ops` plus the final epoch
   potential `2 * rebuildUnitCost U V w * natDist n_final n_init_final` is at most
   `ops.length * resizableChargeVal U V w`. -/
theorem unbounded_seq_expected_amortized {U V w : ℕ}
    (hw : 0 < w) (hU : Fits w U)
    (ops : List (Dynamic.Op U))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops) :
    let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops).1
    let n_final := (Dynamic.dom s_final).card
    let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops
    let N_final := targetCap U n_init_final
    EpochValid n_final N_final ∧
    N_final ≤ U ∧
    Dynamic.ValuesBounded V s_final ∧
    activeEpochWords U V w N_final n_final ≤ Dynamic.succinctWords 1227 213 U V w n_final ∧
    w * activeEpochWords U V w N_final n_final ≤
      Dynamic.optBits U V n_final + 1227 * n_final * Dynamic.logLogFactor n_final + 214 * w ∧
    2 * rebuildUnitCost U V w * natDist n_final n_init_final ≤
      ops.length * resizableChargeVal U V w := by
  suffices hgen : ∀ (s : Dynamic.State U) (n_init : ℕ),
      Dynamic.ValuesBounded V s →
      EpochValid (Dynamic.dom s).card (targetCap U n_init) →
      (Dynamic.spec U V U).ValidHistory s ops →
      let s_final := ((Dynamic.spec U V U).run s ops).1
      let n_final := (Dynamic.dom s_final).card
      let n_init_final := runEpochInit V s n_init ops
      let N_final := targetCap U n_init_final
      EpochValid n_final N_final ∧
      N_final ≤ U ∧
      Dynamic.ValuesBounded V s_final ∧
      activeEpochWords U V w N_final n_final ≤ Dynamic.succinctWords 1227 213 U V w n_final ∧
      w * activeEpochWords U V w N_final n_final ≤
        Dynamic.optBits U V n_final + 1227 * n_final * Dynamic.logLogFactor n_final + 214 * w ∧
      2 * rebuildUnitCost U V w * natDist n_final n_init_final ≤
        2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
          ops.length * resizableChargeVal U V w by
    have h0 := hgen (Dynamic.empty U) 0 (Dictionary.valuesBounded_empty U V)
      (by simp [EpochValid, targetCap]) hvh
    simpa only [Dictionary.dom_empty, Finset.card_empty, natDist_self, Nat.mul_zero,
      Nat.zero_add] using h0
  clear hvh
  intro s n_init hvb hepoch hvh_s
  induction ops generalizing s n_init with
  | nil =>
    have hnU : (Dynamic.dom s).card ≤ U := Dynamic.card_dom_le_univ s
    have hNU : targetCap U n_init ≤ U := targetCap_le_univ U n_init
    have hwords := activeEpochWords_le_succinctWords_of_le_four_mul (V := V) hw hnU hNU
      (le_of_lt hU) hepoch.1 hepoch.2
    have hbits :
        w * activeEpochWords U V w (targetCap U n_init) (Dynamic.dom s).card ≤
          Dynamic.optBits U V (Dynamic.dom s).card +
            1227 * (Dynamic.dom s).card * Dynamic.logLogFactor (Dynamic.dom s).card + 214 * w := by
      calc w * activeEpochWords U V w (targetCap U n_init) (Dynamic.dom s).card
          ≤ w * Dynamic.succinctWords 1227 213 U V w (Dynamic.dom s).card :=
            Nat.mul_le_mul_left w hwords
        _ ≤ Dynamic.optBits U V (Dynamic.dom s).card +
              1227 * (Dynamic.dom s).card * Dynamic.logLogFactor (Dynamic.dom s).card +
              (213 + 1) * w :=
            succinctWords_mul_w_le_bits 1227 213 U V w (Dynamic.dom s).card
        _ = Dynamic.optBits U V (Dynamic.dom s).card +
              1227 * (Dynamic.dom s).card * Dynamic.logLogFactor (Dynamic.dom s).card +
              214 * w := by ring
    dsimp only [runEpochInit]
    exact ⟨hepoch, hNU, hvb, hwords, hbits, by simp⟩
  | cons o os ih =>
    obtain ⟨hval, hvh_rest⟩ := hvh_s
    have hstep := unbounded_step_expected_amortized hw hU hvb o hval hepoch
    dsimp only at hstep
    obtain ⟨hepoch1, _, hvb1, _, _, hpot1, _⟩ := hstep
    let s₁ := ((Dynamic.spec U V U).stepFn s o).1
    let n₁ := (Dynamic.dom s₁).card
    let n_init₁ := if EpochValid n₁ (targetCap U n_init) then n_init else n₁
    have hrec := ih s₁ n_init₁ hvb1 hepoch1 hvh_rest
    dsimp only at hrec
    refine ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1, ?_⟩
    have hrec_pot := hrec.2.2.2.2.2
    dsimp only [runEpochInit, StateTransitionSpec.run_cons, s₁, n₁, n_init₁] at hrec_pot ⊢
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Single-step machine-level execution within a valid epoch (`N ≤ U`). -/
private theorem in_epoch_step_machine_aux {U V w N base : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + Succinct.space U V w N))
    {x₀ : RData rResizable}
    {s : Dynamic.State U} (o : Dynamic.Op U) (hv_N : (Dynamic.spec U V N).valid s o)
    (ν : PMF (QuotHashSeed U N × Data (rSuccinct U V w N)))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N)) θ)
    (hsupp : ∀ p ∈ ν.support,
      ResizableRep U V w N base p.1 s
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N⟩ ∧
      ∀ a < base, p.2.mem a = x₀.mem a) :
    ∃ (ν' : PMF (QuotHashSeed U N × Data (rSuccinct U V w N))) (T_step : ℝ≥0∞),
      (∀ θ, (ν'.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N)) θ) ∧
      (∀ q ∈ ν'.support,
        ResizableRep U V w N base q.1 ((Dynamic.spec U V U).stepFn s o).1
          ⟨q.2.regs, q.2.mem, base + Succinct.space U V w N⟩ ∧
        (∀ a < base, q.2.mem a = x₀.mem a) ∧
        decode U V w N o q.2.regs = some ((Dynamic.spec U V N).stepFn s o).2) ∧
      T_step + (∑' q, ν' q * (potential U V w N base q.1 q.2 : ℝ≥0∞)) ≤
        ((chargeVal U V w N : ℕ) : ℝ≥0∞) +
          (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) := by
  let C := Succinct.impl hw hNU hU hV hfit
  let mem_ref (a : ℕ) : ℕ := if a < base then x₀.mem a else 0
  have hmod₀ : ∀ p ∈ ν.support, Modifies (Block.mk base C.space).footprint mem_ref p.2.mem := by
    intro p hp a ha
    have ha' : a ∉ (Block.mk base (Succinct.space U V w N)).footprint := ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha'
    dsimp only [mem_ref]
    split_ifs with hlt
    · exact (hsupp p hp).2 a hlt
    · rcases ha' with h | h
      · omega
      · exact (hsupp p hp).1.1.zero_above h
  obtain ⟨ν', T_step, hex_step, hseed', hrep', hamort⟩ :=
    C.steps_expected_amortized_ofFn [o] ν ⟨hv_N, trivial⟩ hseed fun p hp => (hsupp p hp).1.2.2
  have hmod' := execStepsOfFn_modifies hex_step hmod₀
  have hdec' := execStepsOfFn_singleton_decode hex_step
  have hrep_N : ∀ q ∈ ν'.support,
      Succinct.Rep U V w N base q.1 ((Dynamic.spec U V U).stepFn s o).1 q.2 := hrep'
  have hcost_one : (Dynamic.spec U V N).totalCost C.charge s [o] = chargeVal U V w N := by
    rw [StateTransitionSpec.totalCost_cons, StateTransitionSpec.totalCost_nil, add_zero]
    rfl
  rw [hcost_one] at hamort
  refine ⟨ν', T_step, hseed', ?_, hamort⟩
  intro q hq
  have hrep_q := hrep_N q hq
  have hmod_q : Modifies (Block.mk base (Succinct.space U V w N)).footprint mem_ref q.2.mem :=
    hmod' q hq
  have hzero_above : ∀ a, base + Succinct.space U V w N ≤ a → q.2.mem a = 0 := by
    intro a ha
    have hnot : a ∉ (Block.mk base (Succinct.space U V w N)).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      omega
    rw [hmod_q a hnot]
    simp [mem_ref, show ¬ a < base by omega]
  have hcaller_q : ∀ a < base, q.2.mem a = x₀.mem a := by
    intro a ha
    have hnot : a ∉ (Block.mk base (Succinct.space U V w N)).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      omega
    rw [hmod_q a hnot]
    simp [mem_ref, ha]
  exact ⟨⟨⟨hrep_q.1, hfit, hzero_above⟩, rfl, hrep_q⟩, hcaller_q, hdec' q hq⟩

/-- Coupled single-step machine execution for an unbounded-capacity dynamic dictionary operation
`o : Dynamic.Op U`, handling both in-place execution (`EpochValid n' N`) and full epoch rebuilds
(`¬EpochValid n' N`). -/
private theorem unbounded_step_machine_aux {U V w base n_init n_init' : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (hfit_N : Fits w (base + Succinct.space U V w (targetCap U n_init)))
    (hfit_N' : Fits w (base + Succinct.space U V w (targetCap U n_init')))
    {x₀ : RData rResizable} (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    {s : Dynamic.State U} (hvb : Dynamic.ValuesBounded V s)
    (o : Dynamic.Op U) (hval : (Dynamic.spec U V U).valid s o)
    (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init))
    (hn_init' : n_init' =
      if EpochValid (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card (targetCap U n_init)
      then n_init else (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card)
    (ν : PMF (QuotHashSeed U (targetCap U n_init) × Data (rSuccinct U V w (targetCap U n_init))))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤
      1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U n_init))) θ)
    (hsupp : ∀ p ∈ ν.support,
      ResizableRep U V w (targetCap U n_init) base p.1 s
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U n_init)⟩ ∧
      ∀ a < base, p.2.mem a = x₀.mem a) :
    ∃ (ν' : PMF (QuotHashSeed U (targetCap U n_init') ×
        Data (rSuccinct U V w (targetCap U n_init')))) (T_step : ℝ≥0∞),
      (∀ θ, (ν'.map Prod.fst) θ ≤
        1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U n_init'))) θ) ∧
      (∀ q ∈ ν'.support,
        ResizableRep U V w (targetCap U n_init') base q.1 ((Dynamic.spec U V U).stepFn s o).1
          ⟨q.2.regs, q.2.mem, base + Succinct.space U V w (targetCap U n_init')⟩ ∧
        (∀ a < base, q.2.mem a = x₀.mem a) ∧
        LastOpOutputCorrect V s [o]
          (fun i => q.2.regs (i.cast (rSuccinct_eq_const U V w (targetCap U n_init')).symm))) ∧
      T_step + (∑' q, ν' q * (potential U V w (targetCap U n_init') base q.1 q.2 : ℝ≥0∞)) +
        ((2 * rebuildUnitCost U V w *
          natDist (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card n_init' : ℕ) : ℝ≥0∞) ≤
        (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
            resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
  have hstep_arith := unbounded_step_expected_amortized hw hU hvb o hval hepoch
  dsimp only at hstep_arith
  obtain ⟨_, hN'U, hvb', _, _, _, hbranch_arith⟩ := hstep_arith
  let n := (Dynamic.dom s).card
  let N := targetCap U n_init
  let s' := ((Dynamic.spec U V U).stepFn s o).1
  let n' := (Dynamic.dom s').card
  by_cases hvalid :
      EpochValid (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card (targetCap U n_init)
  · simp only [hvalid, ↓reduceIte] at hn_init' hbranch_arith
    subst n_init'
    have hNU : N ≤ U := targetCap_le_univ U n_init
    have hv_N : (Dynamic.spec U V N).valid s o := valid_of_card_step_le hval hvalid.1
    obtain ⟨ν', T_step, hseed', hsupp', hamort⟩ :=
      in_epoch_step_machine_aux hw hNU hU hV hfit_N o hv_N ν hseed hsupp
    refine ⟨ν', T_step, hseed', fun q hq => ?_, ?_⟩
    · obtain ⟨hrep_q, hcaller_q, hdec_q⟩ := hsupp' q hq
      exact ⟨hrep_q, hcaller_q, lastOpOutputCorrect_singleton_of_decode s o q.2.regs hdec_q⟩
    have h_ineq :
        ((chargeVal U V w N : ℕ) : ℝ≥0∞) +
          ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞) ≤
          ((2 * rebuildUnitCost U V w * natDist n n_init +
            resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
      norm_cast
      dsimp only [n, N, s', n']
      omega
    calc T_step + (∑' q, ν' q * (potential U V w N base q.1 q.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞)
        ≤ ((chargeVal U V w N : ℕ) : ℝ≥0∞) +
            (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞) :=
          add_le_add hamort le_rfl
      _ = (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
            (((chargeVal U V w N : ℕ) : ℝ≥0∞) +
              ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞)) := by ac_rfl
      _ ≤ (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist n n_init +
              resizableChargeVal U V w : ℕ) : ℝ≥0∞) :=
          add_le_add le_rfl h_ineq
  · simp only [hvalid, ↓reduceIte] at hn_init' hbranch_arith
    subst n_init'
    let x₀_N' : RData (rSuccinct U V w (targetCap U n')) :=
      castRData (rSuccinct_eq_const U V w (targetCap U n')).symm x₀
    have hx₀_N'_bdd : x₀_N'.Bounded w :=
      castRData_bounded (rSuccinct_eq_const U V w (targetCap U n')).symm hx₀
    have hx₀_N'_fr : x₀_N'.frontier = base := hfr₀
    obtain ⟨_, _, ν_reb, T_reb, _, _, _, hseed_reb, hsupp_reb, hbound_reb, _, _⟩ :=
      rebuild_epoch_expected_amortized hw hU hV hvb' hfit_N' hx₀_N'_bdd hx₀_N'_fr
    refine ⟨ν_reb,
      (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit_N').initTime + T_reb,
      hseed_reb, ?_, ?_⟩
    · intro q hq
      obtain ⟨hrep_q, hmod_q⟩ := hsupp_reb q hq
      refine ⟨hrep_q, fun a ha => ?_, ?_⟩
      · have hnot : a ∉ (Block.mk base (Succinct.space U V w (targetCap U n'))).footprint := by
          simp only [Block.mem_footprint, Block.Owns]
          omega
        exact hmod_q a hnot
      · cases o with
        | insert _ _ => trivial
        | delete _ => trivial
        | query _ => exact absurd hepoch hvalid
    · have h_ineq :
          ((31 * targetCap U n' + 1092 + n' * chargeVal U V w (targetCap U n') : ℕ) : ℝ≥0∞) +
            ((2 * rebuildUnitCost U V w * natDist n' n' : ℕ) : ℝ≥0∞) ≤
            ((2 * rebuildUnitCost U V w * natDist n n_init +
              resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
        norm_cast
      calc (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit_N').initTime + T_reb +
            (∑' q, ν_reb q * (potential U V w (targetCap U n') base q.1 q.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist n' n' : ℕ) : ℝ≥0∞)
          ≤ ((31 * targetCap U n' + 1092 + n' * chargeVal U V w (targetCap U n') : ℕ) : ℝ≥0∞) +
              ((2 * rebuildUnitCost U V w * natDist n' n' : ℕ) : ℝ≥0∞) :=
            add_le_add hbound_reb le_rfl
        _ ≤ ((2 * rebuildUnitCost U V w * natDist n n_init +
              resizableChargeVal U V w : ℕ) : ℝ≥0∞) := h_ineq
        _ ≤ (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
              ((2 * rebuildUnitCost U V w * natDist n n_init +
                resizableChargeVal U V w : ℕ) : ℝ≥0∞) :=
            le_add_self

/-- **Coupled Machine-State Unbounded Sequence Theorem
(`unbounded_seq_machine_expected_amortized`):**
Starting from any caller state `x₀ : RData rResizable` with `x₀.Bounded w` and `x₀.frontier = base`,
across any valid unbounded-capacity operation sequence `ops : List (Dynamic.Op U)`
(`(Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops`) whose peak epoch capacity
`maxEpochCap V (Dynamic.empty U) 0 ops` (`≤ min (2 * ops.length) U`) fits in `2 ^ w`:
1. The dictionary reaches `s_final = ((Dynamic.spec U V U).run (Dynamic.empty U) ops).1` with live
   key count `n_final = (Dynamic.dom s_final).card` and epoch capacity
   `N_final = targetCap U n_init_final` satisfying `EpochValid n_final N_final`, `N_final ≤ U`, and
   `Dynamic.ValuesBounded V s_final`;
2. The cumulative expected operation and rebuild instruction time `T_ops : ℝ≥0∞` plus the final
   slot and epoch potentials is bounded by `ops.length * resizableChargeValConst` using the
   universal constants `rResizable = 9957`, `rebuildUnitCostConst = 53495843`, and
   `resizableChargeValConst = 160486391`;
3. For every `(θ, y_data) ∈ ν_final.support`, `x_epoch` satisfies `ResizableRep`,
   `LastOpOutputCorrect V (Dynamic.empty U) ops` (decoding output registers `252, 253` to `s_pre u`
   whenever `ops` ends in `.query u`), and contracting the unused item tail via
   `shrinkTailWordsCode` (`2` instructions via `RDemonicExec`) produces a resting machine state
   `x_rest : RData rResizable` whose physical frontier `x_rest.frontier` satisfies
   `x_rest.frontier = base + activeEpochWords U V w N_final n_final`,
   `x_rest.frontier - base ≤ Dynamic.succinctWords 1227 213 U V w n_final`,
   `w * (x_rest.frontier - base) ≤ Dynamic.optBits U V n_final + 1227 * n_final *
   Dynamic.logLogFactor n_final + 214 * w`, and `LastOpOutputCorrect V (Dynamic.empty U) ops
   x_rest.regs`, while preserving all caller memory `< base` (and when `n_final = 0`,
   `deallocSuccinctCode` in `3` instructions produces `x_zero` with `x_zero.frontier = base`). -/
theorem unbounded_seq_machine_expected_amortized {U V w base : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    {x₀ : RData rResizable} (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (ops : List (Dynamic.Op U))
    (hfit : ∀ N ≤ maxEpochCap V (Dynamic.empty U) 0 ops,
      Fits w (base + Succinct.space U V w N))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops) :
    let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops).1
    let n_final := (Dynamic.dom s_final).card
    let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops
    let N_final := targetCap U n_init_final
    EpochValid n_final N_final ∧
    N_final ≤ U ∧
    Dynamic.ValuesBounded V s_final ∧
    ∃ (ν_final : PMF (QuotHashSeed U N_final × Data (rSuccinct U V w N_final)))
      (T_ops : ℝ≥0∞),
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N_final)) θ) ∧
      T_ops + (∑' q, ν_final q * (potential U V w N_final base q.1 q.2 : ℝ≥0∞)) +
        ((2 * rebuildUnitCostConst * natDist n_final n_init_final : ℕ) : ℝ≥0∞) ≤
        ((ops.length * resizableChargeValConst : ℕ) : ℝ≥0∞) ∧
      ∀ p ∈ ν_final.support,
        let x_epoch : RData (rSuccinct U V w N_final) :=
          ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N_final⟩
        ResizableRep U V w N_final base p.1 s_final x_epoch ∧
        (∀ a < base, x_epoch.mem a = x₀.mem a) ∧
        LastOpOutputCorrect V (Dynamic.empty U) ops
          (castRData (rSuccinct_eq_const U V w N_final) x_epoch).regs ∧
        ∃ x_rest : RData rResizable,
          (∃ y_rest : RData (rSuccinct U V w N_final),
            RDemonicExec w
              (shrinkTailWordsCode U V w N_final
                (Succinct.space U V w N_final - activeEpochWords U V w N_final n_final))
              x_epoch 2 (· = y_rest) ∧
            x_rest = castRData (rSuccinct_eq_const U V w N_final) y_rest) ∧
          x_rest.Bounded w ∧
          x_rest.frontier = base + activeEpochWords U V w N_final n_final ∧
          x_rest.frontier - base ≤ Dynamic.succinctWords 1227 213 U V w n_final ∧
          w * (x_rest.frontier - base) ≤
            Dynamic.optBits U V n_final + 1227 * n_final * Dynamic.logLogFactor n_final +
              214 * w ∧
          LastOpOutputCorrect V (Dynamic.empty U) ops x_rest.regs ∧
          (∀ a < base, x_rest.mem a = x₀.mem a) ∧
          (n_final = 0 →
            ∃ x_zero : RData rResizable,
              (∃ y_zero : RData (rSuccinct U V w N_final),
                RDemonicExec w (deallocSuccinctCode U V w N_final) x_epoch 3 (· = y_zero) ∧
                x_zero = castRData (rSuccinct_eq_const U V w N_final) y_zero) ∧
              x_zero.Bounded w ∧
              x_zero.frontier = base ∧
              ∀ a < base, x_zero.mem a = x₀.mem a) := by
  intro s_final n_final n_init_final N_final
  have hmain := unbounded_seq_expected_amortized (V := V) hw hU ops hvh
  dsimp only at hmain
  obtain ⟨hepoch_f, hN_fU, hvb_f, hwords_f, hbits_f, _⟩ := hmain
  refine ⟨hepoch_f, hN_fU, hvb_f, ?_⟩
  have hgen : ∀ (l : List (Dynamic.Op U)) (s : Dynamic.State U) (n_init : ℕ)
      (hvb : Dynamic.ValuesBounded V s)
      (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init))
      (hfit_l : ∀ N ≤ maxEpochCap V s n_init l, Fits w (base + Succinct.space U V w N))
      (hvh_s : (Dynamic.spec U V U).ValidHistory s l)
      (ν : PMF (QuotHashSeed U (targetCap U n_init) × Data (rSuccinct U V w (targetCap U n_init))))
      (hseed : ∀ θ, (ν.map Prod.fst) θ ≤
        1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U n_init))) θ)
      (hsupp : ∀ p ∈ ν.support,
        ResizableRep U V w (targetCap U n_init) base p.1 s
          ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U n_init)⟩ ∧
        ∀ a < base, p.2.mem a = x₀.mem a),
      let sf := ((Dynamic.spec U V U).run s l).1
      let nf := (Dynamic.dom sf).card
      let n_init_f := runEpochInit V s n_init l
      let Nf := targetCap U n_init_f
      ∃ (ν_f : PMF (QuotHashSeed U Nf × Data (rSuccinct U V w Nf))) (T_ops : ℝ≥0∞),
        (∀ θ, (ν_f.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U Nf)) θ) ∧
        (∀ p ∈ ν_f.support,
          ResizableRep U V w Nf base p.1 sf ⟨p.2.regs, p.2.mem, base + Succinct.space U V w Nf⟩ ∧
          (∀ a < base, p.2.mem a = x₀.mem a) ∧
          LastOpOutputCorrect V s l
            (fun i => p.2.regs (i.cast (rSuccinct_eq_const U V w Nf).symm))) ∧
        T_ops + (∑' q, ν_f q * (potential U V w Nf base q.1 q.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist nf n_init_f : ℕ) : ℝ≥0∞) ≤
          (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
              l.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
    intro l
    induction l with
    | nil =>
      intro s n_init _ _ _ _ ν hseed hsupp
      refine ⟨ν, 0, hseed, fun p hp => ⟨(hsupp p hp).1, (hsupp p hp).2, trivial⟩, ?_⟩
      simp only [runEpochInit, List.length_nil, Nat.zero_mul, Nat.add_zero, zero_add]
      exact le_rfl
    | cons o os ih =>
      intro s n_init hvb hepoch hfit_l ⟨hval, hvh_os⟩ ν hseed hsupp
      have hstep_arith := unbounded_step_expected_amortized hw hU hvb o hval hepoch
      dsimp only at hstep_arith
      obtain ⟨hepoch₁, _, hvb₁, _, _, _, _⟩ := hstep_arith
      let s₁ := ((Dynamic.spec U V U).stepFn s o).1
      let n₁ := (Dynamic.dom s₁).card
      let n_init₁ := if EpochValid n₁ (targetCap U n_init) then n_init else n₁
      have hfit_N : Fits w (base + Succinct.space U V w (targetCap U n_init)) :=
        hfit_l (targetCap U n_init) (targetCap_le_maxEpochCap V s n_init (o :: os))
      have hfit_os : ∀ N ≤ maxEpochCap V s₁ n_init₁ os, Fits w (base + Succinct.space U V w N) :=
        fun N hN => hfit_l N (hN.trans (maxEpochCap_tail_le V s n_init o os))
      have hfit_N₁ : Fits w (base + Succinct.space U V w (targetCap U n_init₁)) :=
        hfit_os (targetCap U n_init₁) (targetCap_le_maxEpochCap V s₁ n_init₁ os)
      obtain ⟨ν₁, T₁, hseed₁, hsupp₁, hbound₁⟩ :=
        unbounded_step_machine_aux (n_init' := n_init₁)
          hw hU hV hfit_N hfit_N₁ hx₀ hfr₀ hvb o hval hepoch rfl ν hseed hsupp
      cases os with
      | nil =>
        refine ⟨ν₁, T₁, hseed₁, hsupp₁, ?_⟩
        simp only [runEpochInit, StateTransitionSpec.run_cons, StateTransitionSpec.run_nil,
          List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul]
        exact hbound₁
      | cons o₂ os' =>
        obtain ⟨ν_f, T_rest, hseed_f, hsupp_f, hbound_rest⟩ :=
          ih s₁ n_init₁ hvb₁ hepoch₁ hfit_os hvh_os ν₁ hseed₁
            (fun q hq => ⟨(hsupp₁ q hq).1, (hsupp₁ q hq).2.1⟩)
        refine ⟨ν_f, T₁ + T_rest, hseed_f, hsupp_f, ?_⟩
        dsimp only [runEpochInit, StateTransitionSpec.run_cons, s₁, n₁, n_init₁] at hbound_rest ⊢
        have hlen_eq :
            ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                resizableChargeVal U V w : ℕ) : ℝ≥0∞) +
              (((o₂ :: os').length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) =
              ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                (o :: o₂ :: os').length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
          norm_cast
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        calc (T₁ + T_rest) +
              (∑' q, ν_f q *
                (potential U V w (targetCap U (runEpochInit V s₁ n_init₁ (o₂ :: os')))
                  base q.1 q.2 : ℝ≥0∞)) +
              ((2 * rebuildUnitCost U V w *
                natDist (Dynamic.dom ((Dynamic.spec U V U).run s₁ (o₂ :: os')).1).card
                  (runEpochInit V s₁ n_init₁ (o₂ :: os')) : ℕ) : ℝ≥0∞)
            = T₁ + (T_rest +
                (∑' q, ν_f q *
                  (potential U V w (targetCap U (runEpochInit V s₁ n_init₁ (o₂ :: os')))
                    base q.1 q.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w *
                  natDist (Dynamic.dom ((Dynamic.spec U V U).run s₁ (o₂ :: os')).1).card
                    (runEpochInit V s₁ n_init₁ (o₂ :: os')) : ℕ) : ℝ≥0∞)) := by ac_rfl
          _ ≤ T₁ + ((∑' p, ν₁ p * (potential U V w (targetCap U n_init₁) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist n₁ n_init₁ +
                  (o₂ :: os').length * resizableChargeVal U V w : ℕ) : ℝ≥0∞)) :=
              add_le_add le_rfl hbound_rest
          _ = (T₁ + (∑' p, ν₁ p * (potential U V w (targetCap U n_init₁) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist n₁ n_init₁ : ℕ) : ℝ≥0∞)) +
                (((o₂ :: os').length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
              push_cast
              ac_rfl
          _ ≤ ((∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                  resizableChargeVal U V w : ℕ) : ℝ≥0∞)) +
                (((o₂ :: os').length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) :=
              add_le_add hbound₁ le_rfl
          _ = (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                  (o :: o₂ :: os').length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
              rw [add_assoc, hlen_eq]
  let x₀_0 : RData (rSuccinct U V w (targetCap U 0)) :=
    castRData (rSuccinct_eq_const U V w (targetCap U 0)).symm x₀
  have hx₀_0_bdd : x₀_0.Bounded w :=
    castRData_bounded (rSuccinct_eq_const U V w (targetCap U 0)).symm hx₀
  have hx₀_0_fr : x₀_0.frontier = base := hfr₀
  have hfit0 : Fits w (base + Succinct.space U V w (targetCap U 0)) :=
    hfit (targetCap U 0) (targetCap_le_maxEpochCap V (Dynamic.empty U) 0 ops)
  obtain ⟨_, ν₀_r, _, _, hseed₀_r, hsupp₀_r⟩ :=
    init_resizable_succinct hw (targetCap_le_univ U 0) hU hV hfit0
      hx₀_0_bdd hx₀_0_fr
  let ν₀ : PMF (QuotHashSeed U (targetCap U 0) × Data (rSuccinct U V w (targetCap U 0))) :=
    ν₀_r.map fun p => (p.1, p.2.toData)
  have hseed₀ : ∀ θ, (ν₀.map Prod.fst) θ ≤
      1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U 0))) θ := by
    intro θ
    rw [one_mul]
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact hseed₀_r θ
  have hsupp₀ : ∀ p ∈ ν₀.support,
      ResizableRep U V w (targetCap U 0) base p.1 (Dynamic.empty U)
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U 0)⟩ ∧
      ∀ a < base, p.2.mem a = x₀.mem a := by
    intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hrep_q, _, hmod_q⟩ := hsupp₀_r q hq
    have hfr_q : q.2.frontier = base + Succinct.space U V w (targetCap U 0) := hrep_q.2.1
    have h_eta : (⟨q.2.toData.regs, q.2.toData.mem,
        base + Succinct.space U V w (targetCap U 0)⟩ : RData _) = q.2 := by
      ext a <;> simp [hfr_q]
    rw [h_eta]
    refine ⟨hrep_q, fun a ha => ?_⟩
    have hnot : a ∉ (Block.mk base (Succinct.space U V w (targetCap U 0))).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      omega
    exact hmod_q a hnot
  have hpot₀ : (∑' p, ν₀ p * (potential U V w (targetCap U 0) base p.1 p.2 : ℝ≥0∞)) = 0 := by
    refine tsum_eq_zero_iff.mpr fun p => ?_
    by_cases hp : p ∈ ν₀.support
    · rw [PMF.mem_support_map_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [(hsupp₀_r q hq).2.1, Nat.cast_zero, mul_zero]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul]
  obtain ⟨ν_final, T_ops, hseed_f, hsupp_f, hbound_f⟩ :=
    hgen ops (Dynamic.empty U) 0 (Dictionary.valuesBounded_empty U V)
      (by simp [EpochValid, targetCap]) hfit hvh ν₀ hseed₀ hsupp₀
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    simp [Dynamic.dom, Dynamic.empty, Dictionary.dom_empty]
  rw [hpot₀, zero_add, hdom0, natDist_self, Nat.mul_zero,
    Nat.zero_add, rebuildUnitCost_eq_const, resizableChargeVal_eq_const] at hbound_f
  refine ⟨ν_final, T_ops, hseed_f, hbound_f, fun p hp => ?_⟩
  obtain ⟨hrep_p, hcaller_p, hout_p⟩ := hsupp_f p hp
  let x_epoch : RData (rSuccinct U V w N_final) :=
    ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N_final⟩
  have hsp_ge : activeEpochWords U V w N_final n_final ≤ Succinct.space U V w N_final :=
    activeEpochWords_le_space hepoch_f.1
  let Δ := Succinct.space U V w N_final - activeEpochWords U V w N_final n_final
  obtain ⟨y_rest, he_sh, hy_rest_bdd, hy_rest_fr, hy_rest_regs, _, hy_rest_mem⟩ :=
    shrinkTailWordsCode_exec hrep_p.1 (Δ := Δ)
      (by dsimp only [x_epoch, Δ, N_final, n_final, n_init_final, s_final] at hsp_ge ⊢; omega)
  have hfr_rest : y_rest.frontier = base + activeEpochWords U V w N_final n_final := by
    rw [hy_rest_fr]
    dsimp only [x_epoch, Δ, N_final, n_final, n_init_final, s_final] at hsp_ge ⊢
    omega
  let x_rest : RData rResizable := castRData (rSuccinct_eq_const U V w N_final) y_rest
  have hout_rest : LastOpOutputCorrect V (Dynamic.empty U) ops x_rest.regs := by
    refine (lastOpOutputCorrect_congr V (Dynamic.empty U) ops ?_ ?_).mp hout_p
    · dsimp only [x_rest, castRData, x_epoch]
      have hne : (⟨252, by decide⟩ : Fin rResizable).cast
          (rSuccinct_eq_const U V w N_final).symm ≠ curReg U V w N_final := by
        intro h
        have hv := congrArg Fin.val h
        change 252 = 241 at hv
        omega
      exact (hy_rest_regs _ hne).symm
    · dsimp only [x_rest, castRData, x_epoch]
      have hne : (⟨253, by decide⟩ : Fin rResizable).cast
          (rSuccinct_eq_const U V w N_final).symm ≠ curReg U V w N_final := by
        intro h
        have hv := congrArg Fin.val h
        change 253 = 241 at hv
        omega
      exact (hy_rest_regs _ hne).symm
  refine ⟨hrep_p, hcaller_p, hout_p, x_rest, ⟨y_rest, he_sh, rfl⟩,
    castRData_bounded (rSuccinct_eq_const U V w N_final) hy_rest_bdd, hfr_rest, ?_, ?_,
    hout_rest, ?_, ?_⟩
  · change y_rest.frontier - base ≤ Dynamic.succinctWords 1227 213 U V w n_final
    rw [hfr_rest, Nat.add_sub_cancel_left]
    exact hwords_f
  · change w * (y_rest.frontier - base) ≤ _
    rw [hfr_rest, Nat.add_sub_cancel_left]
    exact hbits_f
  · intro a ha
    have ha_lt : a < x_epoch.frontier - Δ := by
      dsimp only [x_epoch, Δ, N_final, n_final, n_init_final, s_final] at hsp_ge ⊢
      omega
    exact (hy_rest_mem a ha_lt).trans (hcaller_p a ha)
  · intro hn0
    obtain ⟨y_zero, he_de, hy_zero_bdd, hy_zero_fr, _, _, _, hy_zero_caller⟩ :=
      deallocSuccinctCode_exec hrep_p.1 rfl hrep_p.2.2.2.1
    refine ⟨castRData (rSuccinct_eq_const U V w N_final) y_zero, ⟨y_zero, he_de, rfl⟩,
      castRData_bounded (rSuccinct_eq_const U V w N_final) hy_zero_bdd, hy_zero_fr, fun a ha => ?_⟩
    exact (hy_zero_caller a ha).trans (hcaller_p a ha)

/-! ## Section 6: Client Subroutine Theorems and Memory Reuse in `[0, L)` -/

/-- **Client Subroutine Theorem 1 — Full dictionary lifecycle and memory reuse in `[0, L)`
(`subroutine_client_reuse_released_memory`):**
In a single linear word-resizable memory `[0, L)` on `RData (rSuccinct U V w N)` where the caller
already owns a prefix `[0, base)`:
1. **Demonic-grow allocation & initialization:** `allocSuccinctCode U V w N` (under **demonic**
   `DemonicGrow`, `4 * Succinct.space U V w N + 8` instructions) and `initFresh` initialize the
   succinct dictionary at `[base, base + Succinct.space U V w N)` without modifying `[0, base)`;
2. **Subroutine operation sequence:** any valid sequence `ops : List (Dynamic.Op U)` (`insert`,
   `delete`, `query`) executes in expected amortized time `ops.length * chargeVal U V w N`,
   reaching abstract state `((Dynamic.spec U V N).run (Dynamic.empty U) ops).1` while preserving
   all caller memory `< base`;
3. **Deallocation via `.shrink` and immediate address reuse:** `deallocSuccinctCode U V w N`
   shrinks `frontier` from `base + Succinct.space U V w N` back to `base` in `3` instructions, and
   a subsequent client allocation `allocWordsCode U V w N k_client` under **demonic** `DemonicGrow`
   (`4 * k_client + 8` instructions) allocates `[base, base + k_client)`—**reusing the exact same
   memory addresses `[base, ...)` released by the dictionary**—so the final active frontier is
   `base + k_client` (not `base + Succinct.space U V w N + k_client`) while `[0, base)` remains
   intact throughout. -/
theorem subroutine_client_reuse_released_memory {U V w N base k_client : ℕ}
    (hw : 0 < w) (hnU : N ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit_dict : Fits w (base + Succinct.space U V w N))
    (hfit_client : Fits w (base + k_client))
    {x₀ : RData (rSuccinct U V w N)} (ops : List (Dynamic.Op U))
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hv : (Dynamic.spec U V N).ValidHistory (Dynamic.empty U) ops) :
    ∃ (x_alloc : RData (rSuccinct U V w N))
      (ν₀ ν_final : PMF ((Succinct.impl hw hnU hU hV hfit_dict).Seed ×
        Data (rSuccinct U V w N)))
      (T_ops : ℝ≥0∞),
      RDemonicExec w (allocSuccinctCode U V w N) x₀
        (4 * Succinct.space U V w N + 8) (· = x_alloc) ∧
      ExecCodeDist w (subroutineCode U V w N).initFresh
        (x_alloc.set (frontierReg U V w N) base).toData (ν₀.map Prod.snd)
        (Succinct.impl hw hnU hU hV hfit_dict).initTime ∧
      (Succinct.impl hw hnU hU hV hfit_dict).ExecStepsOfFn
        (Dynamic.empty U) ops ν₀ ν_final T_ops ∧
      (Succinct.impl hw hnU hU hV hfit_dict).initTime + T_ops ≤
        (Succinct.impl hw hnU hU hV hfit_dict).initTime +
          (ops.length * chargeVal U V w N : ℕ) ∧
      ∀ p ∈ ν_final.support,
        let x_dict : RData (rSuccinct U V w N) :=
          ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N⟩
        ResizableRep U V w N base p.1 ((Dynamic.spec U V N).run (Dynamic.empty U) ops).1 x_dict ∧
        (∀ a < base, x_dict.mem a = x₀.mem a) ∧
        ∃ x_dealloc x_reused : RData (rSuccinct U V w N),
          RDemonicExec w (deallocSuccinctCode U V w N) x_dict 3 (· = x_dealloc) ∧
          x_dealloc.frontier = base ∧
          RDemonicExec w (allocWordsCode U V w N k_client) x_dealloc
            (4 * k_client + 8) (· = x_reused) ∧
          x_reused.Bounded w ∧
          x_reused.frontier = base + k_client ∧
          (∀ a < base, x_reused.mem a = x₀.mem a) ∧
          (∀ a ∈ (Block.mk base k_client).footprint, x_reused.mem a = 0) := by
  obtain ⟨x_alloc, he_alloc, hx_alloc_bdd, hx_alloc_fr, _, _, hx_alloc_mem, hx_alloc_zero⟩ :=
    allocSuccinctCode_exec hx₀ hfr₀ hfit_dict
  let x_alloc' := x_alloc.set (frontierReg U V w N) base
  have hbase_fits : Fits w base := hfit_dict.of_le (Nat.le_add_right base _)
  have hx_alloc'_bdd : x_alloc'.toData.Bounded w := (hx_alloc_bdd.set hbase_fits).1
  have hx_alloc'_fr : x_alloc'.toData.regs (frontierReg U V w N) = base := by simp [x_alloc']
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, _, hsupp_final, hamort⟩ :=
    seq_expected_amortized_modifies hw hnU hU hV hfit_dict ops
      hx_alloc'_bdd hx_alloc'_fr hx_alloc_zero hv
  have htime_le :
      (Succinct.impl hw hnU hU hV hfit_dict).initTime + T_ops ≤
        (Succinct.impl hw hnU hU hV hfit_dict).initTime +
          (ops.length * chargeVal U V w N : ℕ) :=
    (le_self_add).trans hamort
  have hw2 : 2 ≤ w := two_le_w_of_fits_space hfit_dict
  have h1 : Fits w 1 :=
    lt_of_lt_of_le (by decide : 1 < 2 ^ 2) (Nat.pow_le_pow_right two_pos hw2)
  refine ⟨x_alloc, ν₀, ν_final, T_ops, he_alloc, he_init, hex_steps, htime_le, ?_⟩
  intro p hp x_dict
  obtain ⟨hrep_p, hmod_p⟩ := hsupp_final p hp
  have hx_dict_bdd : x_dict.Bounded w :=
    rData_bounded_of_rep_modifies hx_alloc_bdd hx_alloc_fr hrep_p hmod_p
  have hcaller_preserved : ∀ a < base, x_dict.mem a = x₀.mem a := by
    intro a ha
    have hnot : a ∉ (Block.mk base (Succinct.space U V w N)).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      omega
    exact (hmod_p a hnot).trans (congrFun hx_alloc_mem a)
  obtain ⟨x_dealloc, he_dealloc, hx_dealloc_bdd, hx_dealloc_fr, _, _, _, hdealloc_caller⟩ :=
    deallocSuccinctCode_exec hx_dict_bdd rfl hrep_p.2.1
  obtain ⟨x_reused, he_reused, hx_reused_bdd, hx_reused_fr, _, _, hx_reused_mem, hx_reused_zero⟩ :=
    allocWordsCode_exec hx_dealloc_bdd hx_dealloc_fr h1 hfit_client
  refine ⟨⟨hx_dict_bdd, rfl, hrep_p⟩, hcaller_preserved,
    x_dealloc, x_reused, he_dealloc, hx_dealloc_fr, he_reused,
    hx_reused_bdd, hx_reused_fr, fun a ha => ?_, hx_reused_zero⟩
  rw [hx_reused_mem, hdealloc_caller a ha, hcaller_preserved a ha]

/-- **Client Subroutine Theorem 2 — Partial contraction via `.shrink` and in-place reuse of
released tail words (`shrink_and_reuse_in_place`):**
When deletions reduce the dictionary's active item footprint from `base + sp₁` by `Δ` words to
`base + sp₂` (`sp₁ = sp₂ + Δ`), executing `shrinkTailWordsCode U V w N Δ` (`2` instructions)
followed by a client allocation `growTailWordsCode U V w N k_client` (`4 * k_client + 8`
instructions under **demonic** `DemonicGrow`) places the new client block at
`[base + sp₂, base + sp₂ + k_client)`—directly reusing the `Δ` released words—while preserving the
dictionary's live prefix `[0, base + sp₂)` unchanged. -/
theorem shrink_and_reuse_in_place {U V w N base sp₂ Δ k_client : ℕ}
    {x : RData (rSuccinct U V w N)}
    (hx : x.Bounded w) (hfr : x.frontier = base + sp₂ + Δ)
    (h1 : Fits w 1) (hfit_client : Fits w (base + sp₂ + k_client)) :
    ∃ x_shrunk x_reused : RData (rSuccinct U V w N),
      RDemonicExec w (shrinkTailWordsCode U V w N Δ) x 2 (· = x_shrunk) ∧
      x_shrunk.frontier = base + sp₂ ∧
      RDemonicExec w (growTailWordsCode U V w N k_client) x_shrunk
        (4 * k_client + 8) (· = x_reused) ∧
      x_reused.Bounded w ∧
      x_reused.frontier = base + sp₂ + k_client ∧
      x_reused.regs (baseReg U V w N) = x.regs (baseReg U V w N) ∧
      (∀ a < base + sp₂, x_reused.mem a = x.mem a) ∧
      (∀ a ∈ (Block.mk (base + sp₂) k_client).footprint, x_reused.mem a = 0) := by
  obtain ⟨x_shrunk, he_sh, hx_sh_bdd, hx_sh_fr, hx_sh_regs, _, hx_sh_mem⟩ :=
    shrinkTailWordsCode_exec hx (Δ := Δ) (by omega)
  have hx_sh_base : x_shrunk.regs (baseReg U V w N) = x.regs (baseReg U V w N) :=
    hx_sh_regs (baseReg U V w N) (sReg_ne (by decide))
  have hfr2 : x.frontier - Δ = base + sp₂ := by omega
  rw [hfr2] at hx_sh_fr hx_sh_mem
  obtain ⟨x_reused, he_gr, hx_gr_bdd, hx_gr_fr, hx_gr_base, _, hx_gr_mem⟩ :=
    growTailWordsCode_exec hx_sh_bdd h1 (Δ := k_client) (by rw [hx_sh_fr]; exact hfit_client)
  rw [hx_sh_fr] at hx_gr_fr
  refine ⟨x_shrunk, x_reused, he_sh, hx_sh_fr, he_gr, hx_gr_bdd, hx_gr_fr,
    hx_gr_base.trans hx_sh_base, fun a ha => ?_, fun a ha => ?_⟩
  · rw [hx_gr_mem]
    exact hx_sh_mem a ha
  · simp only [Block.mem_footprint, Block.Owns] at ha
    rw [hx_gr_mem]
    exact hx_sh_bdd.zero_above (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
