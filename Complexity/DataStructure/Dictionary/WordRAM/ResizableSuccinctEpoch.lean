/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinct
public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinctRebuild

/-!
# Unbounded-Capacity Epoch Schedule and Machine-Level Rebuild for the Resizable Succinct Dictionary

This module completes the unbounded-capacity word-granular resizable succinct dynamic dictionary
(`Dynamic.spec U V U`, supporting arbitrary key and value universes `U, V < 2 ^ w` without any
capacity cap) on top of `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct` and
`Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctRebuild`.

## Design choices and architecture

1. **Epoch-based doubling/halving capacity schedule (`EpochValid`, `targetCap`)**:
   To support an unbounded number of insertions and deletions (`Dynamic.spec U V U`) while keeping
   the live compacted footprint tight in the **current** live key count
   `n_t = (Dynamic.dom s_t).card` at every step `t` (`CompactedRep`) and maintaining `O(1)`
   expected amortized time:
   - An epoch built at key count `n_init ≤ U` chooses capacity parameter
     `N = targetCap U n_init = min (2 * n_init) U`, maintaining the epoch invariant
     `EpochValid n_t N` (`n_t ≤ N ∧ N ≤ 4 * n_t`) and `N ≤ U`.
   - When `n_{t+1}` leaves `[⌈N / 4⌉, N]`, the dictionary rebuilds into a fresh epoch of capacity
     `N' = targetCap U n_{t+1}` by extracting the active `(u, v)` pairs from the `n_t` dense slots
     `[0, n_t)` of compacted memory via one-round Feistel inversion (`extractStepRebuildOps`,
     `extractRebuildOps`), executing `allocSuccinctCode` (under demonic `DemonicGrow`), `initFresh`,
     and inserting the `n_{t+1}` extracted entries. The epoch potential
     `2 * C_reb * natDist n_t n_init` is `0` immediately after every rebuild, changes by at most
     `2 * C_reb = O(1)` per operation, and drops by at least `C_reb * (n_{t+1} + 1)` on every
     rebuild (`add_one_le_two_mul_natDist_of_not_epochValid`).
2. **Client composition and immediate reuse of released memory
   (`dictionary_client_memory_reuse`, `subroutine_client_reuse_released_memory`,
   `shrink_and_reuse_in_place`)**:
   In a single linear word-resizable memory `[0, L)` (`RData`), shrinking the dictionary via
   `RCode.shrink` returns released words to the unallocated suffix `[x.frontier, ∞)` so subsequent
   client allocations under demonic `DemonicGrow` reuse the exact same addresses while preserving
   `CompactedRep` on `[base, x.frontier)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.EpochValid`, `targetCap`, `natDist`,
  `extractStepRebuildOps`, `epochPeakWords`, `maxOpFactor`, `maxChargeVal`, `rebuildUnitCost`,
  `resizableChargeVal`, `epochTotalPotential`, `runEpochInit`: unbounded-capacity epoch schedule,
  machine-extracted rebuild operation list, and uniform `O(1)` per-operation expected amortized
  charge.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.extractStepRebuildOps_spec`,
  `rebuild_epoch_expected_amortized`, `unbounded_step_expected_amortized`,
  `unbounded_seq_expected_amortized`, `unbounded_seq_machine_expected_amortized`: end-to-end `O(1)`
  expected amortized time and stepwise `n_t`-tight `CompactedRep` space across any valid operation
  sequence under `Dynamic.spec U V U` (no capacity cap).
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

/-! ### Rebuilding an epoch from `CompactedRep` via `extractStepRebuildOps` -/

/-- Peak word footprint of an epoch of capacity `N`: covers both the virtual workspace
`Succinct.space U V w N` and the compacted layout `compactedEpochWords U V w N n` (`n ≤ N`). -/
@[expose]
def epochPeakWords (U V w N : ℕ) : ℕ :=
  max (Succinct.space U V w N) (compactedEpochWords U V w N N)

theorem space_le_epochPeakWords (U V w N : ℕ) :
    Succinct.space U V w N ≤ epochPeakWords U V w N :=
  Nat.le_max_left _ _

theorem compactedEpochWords_le_epochPeakWords {U V w N n : ℕ} (hnN : n ≤ N) :
    compactedEpochWords U V w N n ≤ epochPeakWords U V w N := by
  refine le_trans ?_ (Nat.le_max_right _ _)
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · rcases Nat.eq_zero_or_pos N with rfl | hN_pos
    · rfl
    · simp only [compactedEpochWords, ite_true, hN_pos.ne', ite_false, offCompItems,
        offDenseToTail, offTailToDense, offCompGM, offCompLM, epochHdrWords]
      omega
  · have hN_pos : 0 < N := lt_of_lt_of_le hn_pos hnN
    simp only [compactedEpochWords, hn_pos.ne', hN_pos.ne', ite_false]
    have hitem_le : (n * (quotientBits U N + valBits V) + w - 1) / w ≤
        (N * (quotientBits U N + valBits V) + w - 1) / w :=
      Nat.div_le_div_right
        (by have := Nat.mul_le_mul_right (quotientBits U N + valBits V) hnN; omega)
    unfold compactedItemWords
    omega

/-- **Unified compaction theorem (`compactedRep_of_epochValid`):**
For any `n, N` satisfying `EpochValid n N` and `N ≤ U`, and any virtual state `y : Data rSuccinct`
satisfying `Succinct.Rep U V w N base θ s y`, the compacted machine state
`x_comp := compactedOfVirt U V w N n base y` satisfies `CompactedRep U V w N n base s x_comp`,
has `x_comp.regs = y.regs`, and preserves caller memory `< base`. -/
theorem compactedRep_of_epochValid {U V w N n base : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (hepoch : EpochValid n N) (hNU : N ≤ U)
    (hfit : Fits w (base + compactedEpochWords U V w N n))
    {s : Dynamic.State U} (hcard : (Dynamic.dom s).card = n)
    (hvals : Dynamic.ValuesBounded V s)
    {θ : QuotHashSeed U N} {y : Data rSuccinct}
    (hrep_y : Succinct.Rep U V w N base θ s y) :
    let x_comp := compactedOfVirt U V w N n base y
    CompactedRep U V w N n base s x_comp ∧
    x_comp.regs = y.regs ∧
    (∀ a < base, x_comp.mem a = y.mem a) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · have hN0 : N = 0 := by have := hepoch.2; omega
    subst hN0
    exact compactedRep_of_zero hrep_y.1 hfit hcard
  · exact compactedRep_of_succinctRep hw hU hV hn_pos hepoch.1 hepoch.2 hNU hfit hcard hvals hrep_y

/-- Machine-extracted rebuild sequence after applying operation `o` to a compacted state `mem`
with `n` active items in epoch `N_old`: scans `d ∈ List.range n` in `mem`, reconstructs each
key `u_d` via Feistel inversion (`reconstructKeyAt`) and value `v_d` (`reconstructValAt`), skips
any slot matching the modified key of `o`, and appends `.insert u v` when `o = .insert u v`. -/
@[expose]
noncomputable def extractStepRebuildOps (U V w N_old n base : ℕ) (θ : QuotHashSeed U N_old)
    (mem : ℕ → ℕ) (o : Dynamic.Op U) : List (Dynamic.Op U) :=
  if hU : 0 < U then
    let uFn : ℕ → Fin U := fun d =>
      ⟨reconstructKeyAt U V w N_old n base θ mem d % U, Nat.mod_lt _ hU⟩
    let vFn : ℕ → ℕ := reconstructValAt U V w N_old n base mem
    match o with
    | .query _ => extractOpsAux uFn vFn (List.range n)
    | .delete u =>
      extractOpsAux uFn vFn ((List.range n).filter (fun d => decide (uFn d ≠ u)))
    | .insert u v =>
      extractOpsAux uFn vFn ((List.range n).filter (fun d => decide (uFn d ≠ u))) ++
        [.insert u v]
  else []

private theorem run_snoc_insert {U V N' : ℕ} {s₀ s₁ : Dynamic.State U}
    {ops : List (Dynamic.Op U)} (u : Fin U) (v : ℕ)
    (hrun : ((Dynamic.spec U V N').run s₀ ops).1 = s₁)
    (hvh : (Dynamic.spec U V N').ValidHistory s₀ ops)
    (hval : (Dynamic.spec U V N').valid s₁ (.insert u v)) :
    ((Dynamic.spec U V N').run s₀ (ops ++ [.insert u v])).1 =
      Function.update s₁ u (some v) ∧
    (Dynamic.spec U V N').ValidHistory s₀ (ops ++ [.insert u v]) := by
  induction ops generalizing s₀ with
  | nil =>
    subst hrun
    exact ⟨rfl, ⟨hval, trivial⟩⟩
  | cons op ops ih =>
    exact ⟨(ih hrun hvh.2).1, ⟨hvh.1, (ih hrun hvh.2).2⟩⟩

private theorem extractOpsAux_filter_spec {U V N' n : ℕ} {s_abs : Dynamic.State U}
    {uFn : ℕ → Fin U} {vFn : ℕ → ℕ}
    (hspec : ∀ d < n, s_abs (uFn d) = some (vFn d) ∧ vFn d < V)
    (hinj : ∀ d₁ < n, ∀ d₂ < n, uFn d₁ = uFn d₂ → d₁ = d₂)
    (hsurj : ∀ u ∈ Dynamic.dom s_abs, ∃ d < n, uFn d = u)
    (u_del : Fin U)
    (hcard_del : (Dynamic.dom (Function.update s_abs u_del none)).card ≤ N') :
    let L := (List.range n).filter (fun d => decide (uFn d ≠ u_del))
    let s_del := Function.update s_abs u_del none
    ((Dynamic.spec U V N').run (Dynamic.empty U) (extractOpsAux uFn vFn L)).1 = s_del ∧
    (Dynamic.spec U V N').ValidHistory (Dynamic.empty U) (extractOpsAux uFn vFn L) ∧
    (extractOpsAux uFn vFn L).length = (Dynamic.dom s_del).card := by
  intro L s_del
  have hnd : L.Nodup := List.Nodup.filter _ List.nodup_range
  have hlt : ∀ d ∈ L, d < n := fun d hd => List.mem_range.mp (List.mem_filter.mp hd).1
  have hne_del : ∀ d ∈ L, uFn d ≠ u_del :=
    fun d hd => of_decide_eq_true (List.mem_filter.mp hd).2
  have hspec_L : ∀ d ∈ L, s_del (uFn d) = some (vFn d) ∧ vFn d < V := by
    intro d hd
    dsimp only [s_del]
    rw [Function.update_of_ne (hne_del d hd)]
    exact hspec d (hlt d hd)
  have hro : DenseRestrictOut uFn L (Dynamic.empty U) s_del := by
    refine And.intro (fun _ _ => rfl) fun u hu => ?_
    dsimp only [s_del]
    by_cases hu_del : u = u_del
    · subst hu_del
      simp [Dynamic.empty, Dictionary.empty]
    · rw [Function.update_of_ne hu_del]
      rcases hsu : s_abs u with _ | v
      · rfl
      · obtain ⟨d, hd_lt, hd_eq⟩ :=
          hsurj u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, by simp [hsu]⟩)
        have hd_L : d ∈ L :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hd_lt, decide_eq_true (hd_eq ▸ hu_del)⟩
        exact absurd hd_eq (hu d hd_L)
  obtain ⟨hrun, hvh, hlen⟩ :=
    extractOpsAux_spec_aux hinj hcard_del L hnd hlt hspec_L (Dynamic.empty U) hro
  simp only [Dictionary.dom_empty, Finset.card_empty, Nat.zero_add] at hlen
  exact ⟨hrun, hvh, by rw [extractOpsAux_length, hlen]⟩

/-- **Specification of `extractStepRebuildOps` (`extractStepRebuildOps_spec`):**
Given any compacted machine state `x` satisfying `CompactedRep U V w N_old n base s_abs x`, any
valid operation `o : Dynamic.Op U`, and any target capacity `N' ≥ n'`, there exists a seed
`θ : QuotHashSeed U N_old` such that `extractStepRebuildOps U V w N_old n base θ x.mem o`
reconstructs `s' = ((Dynamic.spec U V U).stepFn s_abs o).1` from `Dynamic.empty U`, is a valid
operation history under `Dynamic.spec U V N'`, and has exact length `n' = (Dynamic.dom s').card`. -/
theorem extractStepRebuildOps_spec {r U V w N_old N' n base : ℕ}
    {s_abs : Dynamic.State U} {x : RData r}
    (hrep : CompactedRep U V w N_old n base s_abs x)
    (o : Dynamic.Op U) (hval : (Dynamic.spec U V U).valid s_abs o)
    (hn'N' : (Dynamic.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card ≤ N') :
    ∃ θ : QuotHashSeed U N_old,
      let ops_reb := extractStepRebuildOps U V w N_old n base θ x.mem o
      ((Dynamic.spec U V N').run (Dynamic.empty U) ops_reb).1 =
        ((Dynamic.spec U V U).stepFn s_abs o).1 ∧
      (Dynamic.spec U V N').ValidHistory (Dynamic.empty U) ops_reb ∧
      ops_reb.length = (Dynamic.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card := by
  have hU : 0 < U := match o with | .insert u _ | .delete u | .query u => u.pos
  rcases hrep.epoch_inv with ⟨rfl, rfl⟩ | ⟨_, _, _, hNU, x_virt, θ, hinv, _, _, hgm, hST,
    hbij, hq, hv⟩
  · -- Empty old epoch (`n = 0, N_old = 0`): `s_abs = Dynamic.empty U`
    have hempty : s_abs = Dynamic.empty U := by
      have hdom0 : Dynamic.dom s_abs = ∅ := Finset.card_eq_zero.mp hrep.card_eq
      funext u
      rcases hsu : s_abs u with _ | v
      · rfl
      · have hu_mem : u ∈ Dynamic.dom s_abs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ u, by simp [hsu]⟩
        rw [hdom0] at hu_mem
        exact absurd hu_mem (Finset.notMem_empty u)
    subst hempty
    refine ⟨default, ?_⟩
    cases o with
    | query u =>
      dsimp only
      simp only [extractStepRebuildOps, hU, dite_true, List.range_zero, extractOpsAux]
      exact ⟨rfl, trivial, by simp [Dictionary.dom_empty]⟩
    | delete u =>
      have hup : Function.update (Dynamic.empty U) u none = Dynamic.empty U := by
        funext x
        by_cases hx : x = u <;> simp [hx, Dynamic.empty, Dictionary.empty]
      dsimp only
      simp only [extractStepRebuildOps, hU, dite_true, List.range_zero, List.filter_nil,
        extractOpsAux]
      exact ⟨hup.symm, trivial, by rw [hup]; simp [Dictionary.dom_empty]⟩
    | insert u v =>
      have hcard_ins :
          (Dynamic.dom ((Dynamic.spec U V U).stepFn (Dynamic.empty U) (.insert u v)).1).card =
            1 := by
        have h1 := Dictionary.card_dom_insert_eq_of_eq_none (rfl : (Dynamic.empty U) u = none) v
        simp only [Dictionary.dom_empty, Finset.card_empty, Nat.zero_add] at h1
        exact h1
      have hval_N' : (Dynamic.spec U V N').valid (Dynamic.empty U) (.insert u v) := by
        refine ⟨Or.inl ?_, hval.2⟩
        simp only [Dictionary.dom_empty, Finset.card_empty]
        omega
      dsimp only
      simp only [extractStepRebuildOps, hU, dite_true, List.range_zero, List.filter_nil,
        extractOpsAux, List.nil_append]
      exact ⟨rfl, ⟨hval_N', trivial⟩, hcard_ins.symm⟩
  · -- Active old epoch (`1 ≤ n ≤ N_old ≤ 4 * n, N_old ≤ U`)
    refine ⟨θ, ?_⟩
    obtain ⟨h1, hinj, hsurj⟩ :=
      reconstructKeyAt_spec hrep.vals_lt hinv hgm hST hbij hq hv hNU
    let uFn : ℕ → Fin U := fun d =>
      ⟨reconstructKeyAt U V w N_old n base θ x.mem d % U, Nat.mod_lt _ hU⟩
    let vFn : ℕ → ℕ := reconstructValAt U V w N_old n base x.mem
    have huFn_val : ∀ d < n, (uFn d).val = reconstructKeyAt U V w N_old n base θ x.mem d := by
      intro d hd
      exact Nat.mod_eq_of_lt (h1 d hd).1
    have hspec : ∀ d < n, s_abs (uFn d) = some (vFn d) ∧ vFn d < V := by
      intro d hd
      obtain ⟨hu_lt, hs_eq, hv_lt⟩ := h1 d hd
      have hfin : uFn d = ⟨reconstructKeyAt U V w N_old n base θ x.mem d, hu_lt⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hu_lt)
      rw [hfin]
      exact ⟨hs_eq, hv_lt⟩
    have hinj' : ∀ d₁ < n, ∀ d₂ < n, uFn d₁ = uFn d₂ → d₁ = d₂ := by
      intro d₁ hd₁ d₂ hd₂ heq
      have hval_eq := congrArg Fin.val heq
      rw [huFn_val d₁ hd₁, huFn_val d₂ hd₂] at hval_eq
      exact hinj d₁ hd₁ d₂ hd₂ hval_eq
    have hsurj' : ∀ u ∈ Dynamic.dom s_abs, ∃ d < n, uFn d = u := by
      intro u hu
      obtain ⟨d, hd_lt, hd_eq⟩ := hsurj u (Finset.mem_filter.mp hu).2
      exact ⟨d, hd_lt, Fin.ext (by rw [huFn_val d hd_lt, hd_eq])⟩
    cases o with
    | query u =>
      have hro : DenseRestrictOut uFn (List.range n) (Dynamic.empty U) s_abs := by
        refine And.intro (fun _ _ => rfl) fun u' hu' => ?_
        rcases hsu : s_abs u' with _ | v
        · rfl
        · obtain ⟨d, hd_lt, hd_eq⟩ :=
            hsurj' u' (Finset.mem_filter.mpr ⟨Finset.mem_univ u', by simp [hsu]⟩)
          exact absurd hd_eq (hu' d (List.mem_range.mpr hd_lt))
      obtain ⟨hrun, hvh, hlen⟩ :=
        extractOpsAux_spec_aux hinj' hn'N' (List.range n) List.nodup_range
          (fun _ hd => List.mem_range.mp hd) (fun d hd => hspec d (List.mem_range.mp hd))
          (Dynamic.empty U) hro
      simp only [Dictionary.dom_empty, Finset.card_empty, Nat.zero_add] at hlen
      simp only [extractStepRebuildOps, hU, dite_true]
      exact ⟨hrun, hvh, by rw [extractOpsAux_length, List.length_range, hrep.card_eq]⟩
    | delete u =>
      simp only [extractStepRebuildOps, hU, dite_true]
      exact extractOpsAux_filter_spec hspec hinj' hsurj' u hn'N'
    | insert u v =>
      let s_del := Function.update s_abs u none
      let s_ins := Function.update s_abs u (some v)
      have h_idem : Function.update s_del u (some v) = s_ins := by
        simp [s_del, s_ins]
      have hs_del_u : s_del u = none := Function.update_self u none s_abs
      have hcard_ins : (Dynamic.dom s_ins).card = (Dynamic.dom s_del).card + 1 := by
        rw [← h_idem]
        exact Dictionary.card_dom_insert_eq_of_eq_none hs_del_u v
      have hstep_eq : ((Dynamic.spec U V U).stepFn s_abs (.insert u v)).1 = s_ins := rfl
      rw [hstep_eq] at hn'N'
      have hcard_del_lt : (Dynamic.dom s_del).card < N' := by omega
      obtain ⟨hrun_del, hvh_del, hlen_del⟩ :=
        extractOpsAux_filter_spec hspec hinj' hsurj' u (le_of_lt hcard_del_lt)
      have hval_ins : (Dynamic.spec U V N').valid s_del (.insert u v) :=
        ⟨Or.inl hcard_del_lt, hval.2⟩
      obtain ⟨hrun_ins, hvh_ins⟩ := run_snoc_insert u v hrun_del hvh_del hval_ins
      rw [h_idem] at hrun_ins
      simp only [extractStepRebuildOps, hU, dite_true]
      refine ⟨hrun_ins, hvh_ins, ?_⟩
      rw [List.length_append, List.length_singleton, hlen_del]
      exact hcard_ins.symm

/-- **Epoch rebuild theorem on `RData` (`rebuild_epoch_expected_amortized`):**
Given a compacted machine state `x_prev` satisfying
`CompactedRep U V w N_old (Dynamic.dom s).card base s x_prev` and a valid operation
`o : Dynamic.Op U`, rebuilding the post-step state `s' = ((Dynamic.spec U V U).stepFn s o).1` into
epoch capacity `N' = targetCap U (Dynamic.dom s').card` from `x : RData` with `x.frontier = base`
under **demonic** `DemonicGrow`:
1. Extracts the `n' = (Dynamic.dom s').card` operations `extractStepRebuildOps` from `x_prev.mem`
   and `o` by scanning active dense slots `d ∈ List.range n` and inverting `feistelBucket` /
   `keyQuotient`,
2. Allocates and zeroes `[base, base + Succinct.space U V w N')` via `allocSuccinctCode` in
   `4 * Succinct.space U V w N' + 8` instructions (`RDemonicExec`),
3. Initializes the hash table and inserts all `n'` extracted entries via `extractStepRebuildOps`
   in expected total instruction count at most `31 * N' + 1092 + n' * chargeVal`,
4. Produces a distribution `ν_final` whose support satisfies `ResizableRep U V w N' base θ s' y`
   and packs to `CompactedRep U V w N' n' base s' (compactedOfVirt U V w N' n' base y)`. -/
theorem rebuild_epoch_expected_amortized {r_prev U V w N_old base : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    {s : Dynamic.State U} {x_prev : RData r_prev}
    (hrep_prev : CompactedRep U V w N_old (Dynamic.dom s).card base s x_prev)
    (o : Dynamic.Op U) (hval : (Dynamic.spec U V U).valid s o)
    (hfit : Fits w (base + Succinct.space U V w
      (targetCap U (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card)))
    {x : RData rSuccinct}
    (hx : x.Bounded w) (hfr : x.frontier = base) :
    let s' := ((Dynamic.spec U V U).stepFn s o).1
    let n' := (Dynamic.dom s').card
    let N' := targetCap U n'
    ∃ (θ_old : QuotHashSeed U N_old) (x₁ : RData rSuccinct)
      (ν₀ ν_final : PMF ((Succinct.impl hw (targetCap_le_univ U n') hU hV hfit).Seed ×
        Data rSuccinct))
      (T_ops : ℝ≥0∞),
      RDemonicExec w (allocSuccinctCode U V w N') x (4 * Succinct.space U V w N' + 8) (· = x₁) ∧
      ExecCodeDist w (subroutineCode U V w N').initFresh (x₁.set frontierReg base).toData
        (ν₀.map Prod.snd) (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit).initTime ∧
      (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit).ExecStepsOfFn
        (Dynamic.empty U)
        (extractStepRebuildOps U V w N_old (Dynamic.dom s).card base θ_old x_prev.mem o)
        ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N')) θ) ∧
      (∀ p ∈ ν_final.support,
        ResizableRep U V w N' base p.1 s' ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N'⟩ ∧
        Modifies (Block.mk base (Succinct.space U V w N')).footprint x.mem p.2.mem) ∧
      (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit).initTime + T_ops +
        (∑' q, ν_final q * (potential U V w N' base q.1 q.2 : ℝ≥0∞)) ≤
        ((31 * N' + 1092 + n' * chargeVal : ℕ) : ℝ≥0∞) ∧
      EpochValid n' N' ∧
      activeEpochWords U V w N' n' ≤ Dynamic.succinctWords 312 213 U V w n' := by
  intro s' n' N'
  have hn'U : n' ≤ U := Dynamic.card_dom_le_univ s'
  have hN'U : N' ≤ U := targetCap_le_univ U n'
  have hn'N' : n' ≤ N' := le_targetCap hn'U
  have hN'2 : N' ≤ 2 * n' := targetCap_le_two_mul U n'
  obtain ⟨x₁, he_alloc, hx₁_bdd, hx₁_fr, _, _, hx₁_mem, hx₁_zero⟩ :=
    allocSuccinctCode_exec hx hfr hfit
  let x₁' := x₁.set frontierReg base
  have hbase_fits : Fits w base := hfit.of_le (Nat.le_add_right base _)
  have hx₁'_bdd : x₁'.toData.Bounded w := (hx₁_bdd.set hbase_fits).1
  have hx₁'_fr : x₁'.toData.regs frontierReg = base := by simp [x₁']
  obtain ⟨θ_old, hrun_b, hvh_b, hlen_b⟩ :=
    extractStepRebuildOps_spec (N' := N') hrep_prev o hval hn'N'
  let ops_reb := extractStepRebuildOps U V w N_old (Dynamic.dom s).card base θ_old x_prev.mem o
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hsupp_final, hamort⟩ :=
    seq_expected_amortized_modifies hw hN'U hU hV hfit ops_reb
      hx₁'_bdd hx₁'_fr hx₁_zero hvh_b
  rw [hrun_b] at hsupp_final
  rw [hlen_b] at hamort
  have hinit_le := Succinct.initTime_impl_le hw hN'U hU hV hfit
  have hbound :
      (Succinct.impl hw hN'U hU hV hfit).initTime + T_ops +
        (∑' q, ν_final q * (potential U V w N' base q.1 q.2 : ℝ≥0∞)) ≤
        ((31 * N' + 1092 + n' * chargeVal : ℕ) : ℝ≥0∞) := by
    calc (Succinct.impl hw hN'U hU hV hfit).initTime + T_ops +
          (∑' q, ν_final q * (potential U V w N' base q.1 q.2 : ℝ≥0∞))
        ≤ (Succinct.impl hw hN'U hU hV hfit).initTime + (n' * chargeVal : ℕ) := hamort
      _ ≤ ((initSteps U N' + 1 : ℕ) : ℝ≥0∞) + (n' * chargeVal : ℕ) :=
          add_le_add hinit_le.1 le_rfl
      _ ≤ ((31 * N' + 1092 + n' * chargeVal : ℕ) : ℝ≥0∞) := by
          rw [← Nat.cast_add]
          exact Nat.cast_le.mpr (by have := hinit_le.2; omega)
  refine ⟨θ_old, x₁, ν₀, ν_final, T_ops, he_alloc, he_init, hex_steps, hseed_final, ?_, hbound,
    epochValid_targetCap hn'U,
    activeEpochWords_le_succinctWords_of_le_two_mul hw hn'U hN'U (le_of_lt hU) hn'N' hN'2⟩
  intro p hp
  obtain ⟨hrep_p, hmod_p⟩ := hsupp_final p hp
  have hmod_x : Modifies (Block.mk base (Succinct.space U V w N')).footprint x.mem p.2.mem := by
    change Modifies (Block.mk base (Succinct.space U V w N')).footprint x₁.mem p.2.mem at hmod_p
    rwa [hx₁_mem] at hmod_p
  exact ⟨⟨rData_bounded_of_rep_modifies hx₁_bdd hx₁_fr hrep_p hmod_p, rfl, hrep_p⟩, hmod_x⟩

/-! ### Uniform `O(1)` expected amortized charge across all capacities `N ≤ U` -/

/-- Universal within-epoch exchange factor `opFactor`. -/
noncomputable abbrev opFactorConst : ℕ := opFactor

/-- Universal within-epoch expected amortized operation charge `chargeVal`
(`313 * opFactor + 284725`). -/
noncomputable abbrev chargeValConst : ℕ := chargeVal

/-- Universal per-item epoch rebuild work factor `chargeVal + 1154`. -/
noncomputable abbrev rebuildUnitCostConst : ℕ := chargeVal + 1154

/-- Universal per-operation expected amortized instruction charge
`chargeVal + 2 * rebuildUnitCostConst + 16` across all `U, V, w`. -/
noncomputable abbrev resizableChargeValConst : ℕ := chargeVal + 2 * rebuildUnitCostConst + 16

/-- Maximum exchange factor across all valid epoch capacities `N ∈ [0, U]`. -/
@[expose]
noncomputable def maxOpFactor (_U _V _w : ℕ) : ℕ :=
  opFactor

/-- Uniform `O(1)` within-epoch operation charge dominating `chargeVal` for all `N ≤ U`. -/
@[expose]
noncomputable def maxChargeVal (_U _V _w : ℕ) : ℕ :=
  chargeVal

/-- Per-item epoch rebuild work factor `maxChargeVal U V w + 1154`, dominating
`31 * N + 1092 + n * chargeVal ≤ rebuildUnitCost U V w * (n + 1)` whenever `N ≤ 2 * n`. -/
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

theorem maxOpFactor_eq_const (U V w : ℕ) : maxOpFactor U V w = opFactorConst := rfl

theorem maxChargeVal_eq_const (U V w : ℕ) : maxChargeVal U V w = chargeValConst := rfl

theorem rebuildUnitCost_eq_const (U V w : ℕ) : rebuildUnitCost U V w = rebuildUnitCostConst := rfl

theorem resizableChargeVal_eq_const (U V w : ℕ) :
    resizableChargeVal U V w = resizableChargeValConst := rfl

theorem opFactor_le_maxOpFactor {U V w N : ℕ} (_hNU : N ≤ U) :
    opFactor ≤ maxOpFactor U V w := le_rfl

theorem chargeVal_le_maxChargeVal {U V w N : ℕ} (_hNU : N ≤ U) :
    chargeVal ≤ maxChargeVal U V w := le_rfl

theorem rebuild_cost_le_rebuildUnitCost {U V w n N : ℕ} (_hNU : N ≤ U) (hN2 : N ≤ 2 * n) :
    31 * N + 1092 + n * chargeVal ≤ rebuildUnitCost U V w * (n + 1) := by
  unfold rebuildUnitCost maxChargeVal
  nlinarith

/-- Combined epoch + slot potential at current live key count `n` in an epoch started at `n_init`:
`potential U V w N base θ x.toData + 2 * rebuildUnitCost U V w * natDist n n_init`. -/
@[expose]
noncomputable def epochTotalPotential (U V w N base n n_init : ℕ)
    (θ : QuotHashSeed U N) (x : RData rSuccinct) : ℕ :=
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
      chargeVal + 16 + 2 * rebuildUnitCost U V w * natDist n' n_init' ≤
        2 * rebuildUnitCost U V w * natDist n n_init + resizableChargeVal U V w
    else
      31 * N' + 1092 + n' * chargeVal +
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
    (ν : PMF (QuotHashSeed U N × Data rSuccinct))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N)) θ)
    (hsupp : ∀ p ∈ ν.support,
      ResizableRep U V w N base p.1 s
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N⟩ ∧
      ∀ a < base, p.2.mem a = x₀.mem a) :
    ∃ (ν' : PMF (QuotHashSeed U N × Data rSuccinct)) (T_step : ℝ≥0∞),
      (∀ θ, (ν'.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N)) θ) ∧
      (∀ q ∈ ν'.support,
        ResizableRep U V w N base q.1 ((Dynamic.spec U V U).stepFn s o).1
          ⟨q.2.regs, q.2.mem, base + Succinct.space U V w N⟩ ∧
        (∀ a < base, q.2.mem a = x₀.mem a) ∧
        decode o q.2.regs = some ((Dynamic.spec U V N).stepFn s o).2) ∧
      T_step + (∑' q, ν' q * (potential U V w N base q.1 q.2 : ℝ≥0∞)) ≤
        ((chargeVal : ℕ) : ℝ≥0∞) +
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
  have hcost_one : (Dynamic.spec U V N).totalCost C.charge s [o] = chargeVal := by
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
    (hfit_N : Fits w (base + epochPeakWords U V w (targetCap U n_init)))
    (hfit_N' : Fits w (base + epochPeakWords U V w (targetCap U n_init')))
    {x₀ : RData rResizable} (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    {s : Dynamic.State U} (hvb : Dynamic.ValuesBounded V s)
    (o : Dynamic.Op U) (hval : (Dynamic.spec U V U).valid s o)
    (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init))
    (hn_init' : n_init' =
      if EpochValid (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card (targetCap U n_init)
      then n_init else (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card)
    (ν : PMF (QuotHashSeed U (targetCap U n_init) × Data rSuccinct))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤
      1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U n_init))) θ)
    (hsupp : ∀ p ∈ ν.support,
      ResizableRep U V w (targetCap U n_init) base p.1 s
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U n_init)⟩ ∧
      ∀ a < base, p.2.mem a = x₀.mem a) :
    ∃ (ν' : PMF (QuotHashSeed U (targetCap U n_init') ×
        Data rSuccinct)) (T_step : ℝ≥0∞),
      (∀ θ, (ν'.map Prod.fst) θ ≤
        1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U n_init'))) θ) ∧
      (∀ q ∈ ν'.support,
        ResizableRep U V w (targetCap U n_init') base q.1 ((Dynamic.spec U V U).stepFn s o).1
          ⟨q.2.regs, q.2.mem, base + Succinct.space U V w (targetCap U n_init')⟩ ∧
        (∀ a < base, q.2.mem a = x₀.mem a) ∧
        LastOpOutputCorrect V s [o] q.2.regs) ∧
      T_step + (∑' q, ν' q * (potential U V w (targetCap U n_init') base q.1 q.2 : ℝ≥0∞)) +
        ((2 * rebuildUnitCost U V w *
          natDist (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card n_init' : ℕ) : ℝ≥0∞) ≤
        (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
            resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
  have hstep_arith := unbounded_step_expected_amortized hw hU hvb o hval hepoch
  dsimp only at hstep_arith
  obtain ⟨_, hN'U, _, _, _, _, hbranch_arith⟩ := hstep_arith
  let n := (Dynamic.dom s).card
  let N := targetCap U n_init
  let s' := ((Dynamic.spec U V U).stepFn s o).1
  let n' := (Dynamic.dom s').card
  have hfit_sp_N : Fits w (base + Succinct.space U V w N) :=
    hfit_N.of_le (Nat.add_le_add_left (space_le_epochPeakWords U V w N) base)
  by_cases hvalid :
      EpochValid (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card (targetCap U n_init)
  · simp only [hvalid, ↓reduceIte] at hn_init' hbranch_arith
    subst n_init'
    have hNU : N ≤ U := targetCap_le_univ U n_init
    have hv_N : (Dynamic.spec U V N).valid s o := valid_of_card_step_le hval hvalid.1
    obtain ⟨ν', T_step, hseed', hsupp', hamort⟩ :=
      in_epoch_step_machine_aux hw hNU hU hV hfit_sp_N o hv_N ν hseed hsupp
    refine ⟨ν', T_step, hseed', fun q hq => ?_, ?_⟩
    · obtain ⟨hrep_q, hcaller_q, hdec_q⟩ := hsupp' q hq
      exact ⟨hrep_q, hcaller_q, lastOpOutputCorrect_singleton_of_decode s o q.2.regs hdec_q⟩
    have h_ineq :
        ((chargeVal : ℕ) : ℝ≥0∞) +
          ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞) ≤
          ((2 * rebuildUnitCost U V w * natDist n n_init +
            resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr (by dsimp only [n, N, s', n']; omega)
    calc T_step + (∑' q, ν' q * (potential U V w N base q.1 q.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞)
        ≤ ((chargeVal : ℕ) : ℝ≥0∞) +
            (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞) :=
          add_le_add hamort le_rfl
      _ = (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
            (((chargeVal : ℕ) : ℝ≥0∞) +
              ((2 * rebuildUnitCost U V w * natDist n' n_init : ℕ) : ℝ≥0∞)) := by ac_rfl
      _ ≤ (∑' p, ν p * (potential U V w N base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist n n_init +
              resizableChargeVal U V w : ℕ) : ℝ≥0∞) :=
          add_le_add le_rfl h_ineq
  · simp only [hvalid, ↓reduceIte] at hn_init' hbranch_arith
    subst n_init'
    obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
    have hfit_comp_N : Fits w (base + compactedEpochWords U V w N n) :=
      hfit_N.of_le (Nat.add_le_add_left (compactedEpochWords_le_epochPeakWords hepoch.1) base)
    have hrep_prev : CompactedRep U V w N n base s (compactedOfVirt U V w N n base p₀.2) :=
      (compactedRep_of_epochValid hw hU hV hepoch (targetCap_le_univ U n_init)
        hfit_comp_N rfl hvb (hsupp p₀ hp₀).1.2.2).1
    have hfit_sp_N' : Fits w (base + Succinct.space U V w (targetCap U n')) :=
      hfit_N'.of_le (Nat.add_le_add_left (space_le_epochPeakWords U V w (targetCap U n')) base)
    obtain ⟨_, _, _, ν_reb, T_reb, _, _, _, hseed_reb, hsupp_reb, hbound_reb, _, _⟩ :=
      rebuild_epoch_expected_amortized hw hU hV hrep_prev o hval hfit_sp_N' hx₀ hfr₀
    refine ⟨ν_reb,
      (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit_sp_N').initTime + T_reb,
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
          ((31 * targetCap U n' + 1092 + n' * chargeVal : ℕ) : ℝ≥0∞) +
            ((2 * rebuildUnitCost U V w * natDist n' n' : ℕ) : ℝ≥0∞) ≤
            ((2 * rebuildUnitCost U V w * natDist n n_init +
              resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_add]
        exact Nat.cast_le.mpr hbranch_arith
      calc (Succinct.impl hw (targetCap_le_univ U n') hU hV hfit_sp_N').initTime + T_reb +
            (∑' q, ν_reb q * (potential U V w (targetCap U n') base q.1 q.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist n' n' : ℕ) : ℝ≥0∞)
          ≤ ((31 * targetCap U n' + 1092 + n' * chargeVal : ℕ) : ℝ≥0∞) +
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
At completion of `ops` (and by prefix induction at every step `t`), every supported post-step
state packs to `x_comp = compactedOfVirt U V w N_final n_final base p.2` satisfying
`CompactedRep U V w N_final n_final base s_final x_comp`, with live frontier
`x_comp.frontier = base + compactedEpochWords U V w N_final n_final` without post-hoc `.shrink`. -/
theorem unbounded_seq_machine_expected_amortized {U V w base : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    {x₀ : RData rResizable} (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (ops : List (Dynamic.Op U))
    (hfit : ∀ N ≤ maxEpochCap V (Dynamic.empty U) 0 ops,
      Fits w (base + epochPeakWords U V w N))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops) :
    let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops).1
    let n_final := (Dynamic.dom s_final).card
    let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops
    let N_final := targetCap U n_init_final
    EpochValid n_final N_final ∧
    N_final ≤ U ∧
    Dynamic.ValuesBounded V s_final ∧
    ∃ (ν_final : PMF (QuotHashSeed U N_final × Data rSuccinct))
      (T_ops : ℝ≥0∞),
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U N_final)) θ) ∧
      T_ops + (∑' q, ν_final q * (potential U V w N_final base q.1 q.2 : ℝ≥0∞)) +
        ((2 * rebuildUnitCostConst * natDist n_final n_init_final : ℕ) : ℝ≥0∞) ≤
        ((ops.length * resizableChargeValConst : ℕ) : ℝ≥0∞) ∧
      ∀ p ∈ ν_final.support,
        let x_epoch : RData rSuccinct :=
          ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N_final⟩
        let x_comp : RData rSuccinct :=
          compactedOfVirt U V w N_final n_final base p.2
        ResizableRep U V w N_final base p.1 s_final x_epoch ∧
        (∀ a < base, x_epoch.mem a = x₀.mem a) ∧
        LastOpOutputCorrect V (Dynamic.empty U) ops x_epoch.regs ∧
        CompactedRep U V w N_final n_final base s_final x_comp ∧
        x_comp.Bounded w ∧
        x_comp.frontier = base + compactedEpochWords U V w N_final n_final ∧
        x_comp.frontier - base ≤ Dynamic.succinctWords 1355 380 U V w n_final ∧
        w * (x_comp.frontier - base) ≤
          Dynamic.optBits U V n_final + 1355 * n_final * Dynamic.logLogFactor n_final +
            381 * w ∧
        LastOpOutputCorrect V (Dynamic.empty U) ops x_comp.regs ∧
        (∀ a < base, x_comp.mem a = x₀.mem a) ∧
        (n_final = 0 → x_comp.frontier = base + 4) := by
  intro s_final n_final n_init_final N_final
  have hmain := unbounded_seq_expected_amortized (V := V) hw hU ops hvh
  dsimp only at hmain
  obtain ⟨hepoch_f, hN_fU, hvb_f, _, _, _⟩ := hmain
  refine ⟨hepoch_f, hN_fU, hvb_f, ?_⟩
  have hgen : ∀ (l : List (Dynamic.Op U)) (s : Dynamic.State U) (n_init : ℕ)
      (hvb : Dynamic.ValuesBounded V s)
      (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init))
      (hfit_l : ∀ N ≤ maxEpochCap V s n_init l, Fits w (base + epochPeakWords U V w N))
      (hvh_s : (Dynamic.spec U V U).ValidHistory s l)
      (ν : PMF (QuotHashSeed U (targetCap U n_init) × Data rSuccinct))
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
      ∃ (ν_f : PMF (QuotHashSeed U Nf × Data rSuccinct)) (T_ops : ℝ≥0∞),
        Fits w (base + epochPeakWords U V w Nf) ∧
        (∀ θ, (ν_f.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U Nf)) θ) ∧
        (∀ p ∈ ν_f.support,
          ResizableRep U V w Nf base p.1 sf ⟨p.2.regs, p.2.mem, base + Succinct.space U V w Nf⟩ ∧
          (∀ a < base, p.2.mem a = x₀.mem a) ∧
          LastOpOutputCorrect V s l p.2.regs) ∧
        T_ops + (∑' q, ν_f q * (potential U V w Nf base q.1 q.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist nf n_init_f : ℕ) : ℝ≥0∞) ≤
          (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
              l.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
    intro l
    induction l with
    | nil =>
      intro s n_init _ _ hfit_l _ ν hseed hsupp
      refine ⟨ν, 0, hfit_l _ (targetCap_le_maxEpochCap V s n_init []), hseed,
        fun p hp => ⟨(hsupp p hp).1, (hsupp p hp).2, trivial⟩, ?_⟩
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
      have hfit_N : Fits w (base + epochPeakWords U V w (targetCap U n_init)) :=
        hfit_l (targetCap U n_init) (targetCap_le_maxEpochCap V s n_init (o :: os))
      have hfit_os : ∀ N ≤ maxEpochCap V s₁ n_init₁ os, Fits w (base + epochPeakWords U V w N) :=
        fun N hN => hfit_l N (hN.trans (maxEpochCap_tail_le V s n_init o os))
      have hfit_N₁ : Fits w (base + epochPeakWords U V w (targetCap U n_init₁)) :=
        hfit_os (targetCap U n_init₁) (targetCap_le_maxEpochCap V s₁ n_init₁ os)
      obtain ⟨ν₁, T₁, hseed₁, hsupp₁, hbound₁⟩ :=
        unbounded_step_machine_aux (n_init' := n_init₁)
          hw hU hV hfit_N hfit_N₁ hx₀ hfr₀ hvb o hval hepoch rfl ν hseed hsupp
      cases os with
      | nil =>
        refine ⟨ν₁, T₁, hfit_N₁, hseed₁, hsupp₁, ?_⟩
        simp only [runEpochInit, StateTransitionSpec.run_cons, StateTransitionSpec.run_nil,
          List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul]
        exact hbound₁
      | cons o₂ os' =>
        obtain ⟨ν_f, T_rest, hfit_f, hseed_f, hsupp_f, hbound_rest⟩ :=
          ih s₁ n_init₁ hvb₁ hepoch₁ hfit_os hvh_os ν₁ hseed₁
            (fun q hq => ⟨(hsupp₁ q hq).1, (hsupp₁ q hq).2.1⟩)
        refine ⟨ν_f, T₁ + T_rest, hfit_f, hseed_f, hsupp_f, ?_⟩
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
  have hfit0 : Fits w (base + Succinct.space U V w (targetCap U 0)) :=
    (hfit (targetCap U 0) (targetCap_le_maxEpochCap V (Dynamic.empty U) 0 ops)).of_le
      (Nat.add_le_add_left (space_le_epochPeakWords U V w (targetCap U 0)) base)
  obtain ⟨_, ν₀_r, _, _, hseed₀_r, hsupp₀_r⟩ :=
    init_resizable_succinct hw (targetCap_le_univ U 0) hU hV hfit0 hx₀ hfr₀
  let ν₀ : PMF (QuotHashSeed U (targetCap U 0) × Data rSuccinct) :=
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
  obtain ⟨ν_final, T_ops, hfit_f, hseed_f, hsupp_f, hbound_f⟩ :=
    hgen ops (Dynamic.empty U) 0 (Dictionary.valuesBounded_empty U V)
      (by simp [EpochValid, targetCap]) hfit hvh ν₀ hseed₀ hsupp₀
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    simp [Dynamic.dom, Dynamic.empty, Dictionary.dom_empty]
  rw [hpot₀, zero_add, hdom0, natDist_self, Nat.mul_zero,
    Nat.zero_add, rebuildUnitCost_eq_const, resizableChargeVal_eq_const] at hbound_f
  refine ⟨ν_final, T_ops, hseed_f, hbound_f, fun p hp => ?_⟩
  obtain ⟨hrep_p, hcaller_p, hout_p⟩ := hsupp_f p hp
  have hfit_comp_f : Fits w (base + compactedEpochWords U V w N_final n_final) :=
    hfit_f.of_le (Nat.add_le_add_left (compactedEpochWords_le_epochPeakWords hepoch_f.1) base)
  have hrep_p_virt : Succinct.Rep U V w N_final base p.1 s_final p.2 := hrep_p.2.2
  obtain ⟨hcomp_rep, hcomp_regs, hcomp_caller⟩ :=
    compactedRep_of_epochValid (n := n_final) hw hU hV hepoch_f hN_fU hfit_comp_f rfl hvb_f
      hrep_p_virt
  have hout_comp : LastOpOutputCorrect V (Dynamic.empty U) ops
      (compactedOfVirt U V w N_final n_final base p.2).regs := hcomp_regs ▸ hout_p
  refine ⟨hrep_p, hcaller_p, hout_p, hcomp_rep, hcomp_rep.bounded, hcomp_rep.frontier_eq,
    hcomp_rep.frontier_sub_base_le_succinctWords hw (le_of_lt hU),
    hcomp_rep.w_mul_frontier_sub_base_le_bits hw (le_of_lt hU), hout_comp,
    fun a ha => (hcomp_caller a ha).trans (hcaller_p a ha),
    fun hn0 => by rw [hcomp_rep.frontier_eq, hn0]; simp [compactedEpochWords]⟩

/-! ## Section 6: Client Subroutine Theorems and Memory Reuse in `[0, L)` -/

theorem subroutine_client_reuse_released_memory {U V w N base k_client : ℕ}
    (hw : 0 < w) (hnU : N ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit_dict : Fits w (base + Succinct.space U V w N))
    (hfit_client : Fits w (base + k_client))
    {x₀ : RData rSuccinct} (ops : List (Dynamic.Op U))
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hv : (Dynamic.spec U V N).ValidHistory (Dynamic.empty U) ops) :
    ∃ (x_alloc : RData rSuccinct)
      (ν₀ ν_final : PMF ((Succinct.impl hw hnU hU hV hfit_dict).Seed ×
        Data rSuccinct))
      (T_ops : ℝ≥0∞),
      RDemonicExec w (allocSuccinctCode U V w N) x₀
        (4 * Succinct.space U V w N + 8) (· = x_alloc) ∧
      ExecCodeDist w (subroutineCode U V w N).initFresh
        (x_alloc.set frontierReg base).toData (ν₀.map Prod.snd)
        (Succinct.impl hw hnU hU hV hfit_dict).initTime ∧
      (Succinct.impl hw hnU hU hV hfit_dict).ExecStepsOfFn
        (Dynamic.empty U) ops ν₀ ν_final T_ops ∧
      (Succinct.impl hw hnU hU hV hfit_dict).initTime + T_ops ≤
        (Succinct.impl hw hnU hU hV hfit_dict).initTime +
          (ops.length * chargeVal : ℕ) ∧
      ∀ p ∈ ν_final.support,
        let x_dict : RData rSuccinct :=
          ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N⟩
        ResizableRep U V w N base p.1 ((Dynamic.spec U V N).run (Dynamic.empty U) ops).1 x_dict ∧
        (∀ a < base, x_dict.mem a = x₀.mem a) ∧
        ∃ x_dealloc x_reused : RData rSuccinct,
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
  let x_alloc' := x_alloc.set frontierReg base
  have hbase_fits : Fits w base := hfit_dict.of_le (Nat.le_add_right base _)
  have hx_alloc'_bdd : x_alloc'.toData.Bounded w := (hx_alloc_bdd.set hbase_fits).1
  have hx_alloc'_fr : x_alloc'.toData.regs frontierReg = base := by simp [x_alloc']
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, _, hsupp_final, hamort⟩ :=
    seq_expected_amortized_modifies hw hnU hU hV hfit_dict ops
      hx_alloc'_bdd hx_alloc'_fr hx_alloc_zero hv
  have htime_le :
      (Succinct.impl hw hnU hU hV hfit_dict).initTime + T_ops ≤
        (Succinct.impl hw hnU hU hV hfit_dict).initTime +
          (ops.length * chargeVal : ℕ) :=
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

theorem shrink_and_reuse_in_place {U V w N base sp₂ Δ k_client : ℕ}
    {x : RData rSuccinct}
    (hx : x.Bounded w) (hfr : x.frontier = base + sp₂ + Δ)
    (h1 : Fits w 1) (hfit_client : Fits w (base + sp₂ + k_client)) :
    ∃ x_shrunk x_reused : RData rSuccinct,
      RDemonicExec w (shrinkTailWordsCode U V w N Δ) x 2 (· = x_shrunk) ∧
      x_shrunk.frontier = base + sp₂ ∧
      RDemonicExec w (growTailWordsCode U V w N k_client) x_shrunk
        (4 * k_client + 8) (· = x_reused) ∧
      x_reused.Bounded w ∧
      x_reused.frontier = base + sp₂ + k_client ∧
      x_reused.regs baseReg = x.regs baseReg ∧
      (∀ a < base + sp₂, x_reused.mem a = x.mem a) ∧
      (∀ a ∈ (Block.mk (base + sp₂) k_client).footprint, x_reused.mem a = 0) := by
  obtain ⟨x_shrunk, he_sh, hx_sh_bdd, hx_sh_fr, hx_sh_regs, _, hx_sh_mem⟩ :=
    shrinkTailWordsCode_exec hx (U := U) (V := V) (N := N) (Δ := Δ) (by omega)
  have hx_sh_base : x_shrunk.regs baseReg = x.regs baseReg :=
    hx_sh_regs baseReg (sReg_ne (by decide))
  have hfr2 : x.frontier - Δ = base + sp₂ := by omega
  rw [hfr2] at hx_sh_fr hx_sh_mem
  obtain ⟨x_reused, he_gr, hx_gr_bdd, hx_gr_fr, hx_gr_base, _, hx_gr_mem⟩ :=
    growTailWordsCode_exec hx_sh_bdd h1 (U := U) (V := V) (N := N) (Δ := k_client)
      (by rw [hx_sh_fr]; exact hfit_client)
  rw [hx_sh_fr] at hx_gr_fr
  refine ⟨x_shrunk, x_reused, he_sh, hx_sh_fr, he_gr, hx_gr_bdd, hx_gr_fr,
    hx_gr_base.trans hx_sh_base, fun a ha => ?_, fun a ha => ?_⟩
  · rw [hx_gr_mem]
    exact hx_sh_mem a ha
  · simp only [Block.mem_footprint, Block.Owns] at ha
    rw [hx_gr_mem]
    exact hx_sh_bdd.zero_above (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
